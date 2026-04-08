using System;
using System.Collections.Concurrent;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.IO;
using System.Linq;
using System.Threading;
using System.Threading.Tasks;
using VC;
using System.Runtime.Caching;
using System.Diagnostics;
using VCGeneration;
using System.Reflection;

namespace Microsoft.Boogie
{
  public record ProcessedProgram(Program Program, Action<VerificationConditionGenerator, Implementation, ImplementationRunResult> PostProcessResult) {
    public ProcessedProgram(Program program) : this(program, (_, _, _) => { }) {
    }
  }

  public class ExecutionEngine : IDisposable
  {
    /// <summary>
    /// Boogie traverses the Boogie and VCExpr AST using the call-stack,
    /// so it needs to use a large stack to prevent stack overflows.
    /// </summary>
    public TaskFactory LargeThreadTaskFactory { get; }

    static int autoRequestIdCount;

    private const string AutoRequestIdPrefix = "auto_request_id_";

    public static string FreshRequestId() {
      var id = Interlocked.Increment(ref autoRequestIdCount);
      return AutoRequestIdPrefix + id;
    }

    public static int AutoRequestId(string id) {
      if (id.StartsWith(AutoRequestIdPrefix)) {
        if (int.TryParse(id.Substring(AutoRequestIdPrefix.Length), out var result)) {
          return result;
        }
      }

      return -1;
    }

    public readonly IVerificationResultCache Cache;

    static readonly CacheItemPolicy policy = new CacheItemPolicy
      { SlidingExpiration = new TimeSpan(0, 10, 0), Priority = CacheItemPriority.Default };

    public const int StackSize = 16 * 1024 * 1024;

    public ExecutionEngine(ExecutionEngineOptions options, IVerificationResultCache cache, TaskScheduler scheduler, bool disposeScheduler = false) {
      Options = options;
      Cache = cache;
      CheckerPool = new CheckerPool(options);
      verifyImplementationSemaphore = new SemaphoreSlim(Options.VcsCores);

      largeThreadScheduler = scheduler;
      this.disposeScheduler = disposeScheduler;
      LargeThreadTaskFactory = new(CancellationToken.None, TaskCreationOptions.None, TaskContinuationOptions.None, largeThreadScheduler);
    }

    public static ExecutionEngine CreateWithoutSharedCache(ExecutionEngineOptions options) {
      return new ExecutionEngine(options, new VerificationResultCache(),
        CustomStackSizePoolTaskScheduler.Create(StackSize, options.VcsCores), true);
    }

    public ExecutionEngineOptions Options { get; }
    public CheckerPool CheckerPool { get; }
    private readonly SemaphoreSlim verifyImplementationSemaphore;

    static DateTime FirstRequestStart;

    static readonly ConcurrentDictionary<string, TimeSpan> TimePerRequest = new();

    static readonly ConcurrentDictionary<string, PipelineStatistics> StatisticsPerRequest = new();

    static readonly ConcurrentDictionary<string, CancellationTokenSource> ImplIdToCancellationTokenSource = new();

    private readonly TaskScheduler largeThreadScheduler;
    private readonly bool disposeScheduler;

    public async Task<bool> ProcessFiles(TextWriter output, IList<string> fileNames, bool lookForSnapshots = true,
      string programId = null, CancellationToken cancellationToken = default) {
      Contract.Requires(Cce.NonNullElements(fileNames));

      if (Options.VerifySeparately && 1 < fileNames.Count) {
        var success = true;
        foreach (var fileName in fileNames) {
          cancellationToken.ThrowIfCancellationRequested();
          success &= await ProcessFiles(output, new List<string> { fileName }, lookForSnapshots, fileName, cancellationToken: cancellationToken);
        }
        return success;
      }

      if (0 <= Options.VerifySnapshots && lookForSnapshots) {
        var snapshotsByVersion = LookForSnapshots(fileNames);
        var success = true;
        foreach (var snapshots in snapshotsByVersion) {
          cancellationToken.ThrowIfCancellationRequested();
          // BUG: Reusing checkers during snapshots doesn't work, even though it should. We create a new engine (and thus checker pool) to workaround this.
          using var engine = new ExecutionEngine(Options, Cache,
            CustomStackSizePoolTaskScheduler.Create(StackSize, Options.VcsCores), true);
          success &= await engine.ProcessFiles(output, new List<string>(snapshots), false, programId, cancellationToken: cancellationToken);
        }
        return success;
      }

      return await ProcessProgramFiles(output, fileNames, programId, cancellationToken);
    }

    private Task<bool> ProcessProgramFiles(TextWriter output, IList<string> fileNames, string programId,
      CancellationToken cancellationToken)
    {
      using XmlFileScope xf = new XmlFileScope(Options.XmlSink, fileNames[^1]);
      Program program = ParseBoogieProgram(fileNames, false);
      var bplFileName = fileNames[^1];
      if (program == null)
      {
        return Task.FromResult(true);
      }

      return ProcessProgram(output, program, bplFileName, programId, cancellationToken: cancellationToken);
    }

    [Obsolete("Please inline this method call")]
    public bool ProcessProgram(Program program, string bplFileName,
      string programId = null) {
      return ProcessProgram(Options.OutputWriter, program, bplFileName, programId).Result;
    }

    public async Task<bool> ProcessProgram(TextWriter output, Program program, string bplFileName, string programId = null, CancellationToken cancellationToken = default)
    {
      if (programId == null)
      {
        programId = "main_program_id";
      }

      if (Options.PrintFile != null) {
        PrintBplFile(Options.PrintFile, program, false, true, Options.PrettyPrint);
      }
      
      PipelineOutcome outcome = ResolveAndTypecheck(program, bplFileName, out var civlTypeChecker);
      if (outcome != PipelineOutcome.ResolvedAndTypeChecked) {
        return true;
      }

      if (Options.PrintCFGPrefix != null) {
        foreach (var impl in program.Implementations) {
          await using StreamWriter sw = new StreamWriter(Options.PrintCFGPrefix + "." + impl.Name + ".dot");
          await sw.WriteAsync(program.ProcessLoops(Options, impl).ToDot());
        }
      }

      CivlRewriter.Transform(Options, civlTypeChecker);
      if (Options.CivlDesugaredFile != null) {
        int oldPrintUnstructured = Options.PrintUnstructured;
        Options.PrintUnstructured = 1;
        PrintBplFile(Options.CivlDesugaredFile, program, false, false,
          Options.PrettyPrint);
        Options.PrintUnstructured = oldPrintUnstructured;
      }

      EliminateDeadVariables(program);

      CoalesceBlocks(program);

      Inline(program);

      var stats = new PipelineStatistics();
      outcome = await InferAndVerify(output, program, stats, 1 < Options.VerifySnapshots ? programId : null, cancellationToken: cancellationToken);
      switch (outcome) {
        case PipelineOutcome.Done:
        case PipelineOutcome.VerificationCompleted:
          Options.Printer.WriteTrailer(output, stats);
          return true;
        case PipelineOutcome.FatalError:
          return false;
        default:
          Debug.Assert(false, "Unreachable code");
          return false;
      }
    }

    private static Dictionary<Tuple<Action, Action>, bool> GetChecksToCache(
      IEnumerable<Tuple<Action, Action>> currentChecks,
      string verifierOutput)
    {
      var checkList = currentChecks.ToList();

      var commResults = new Dictionary<Tuple<Action, Action>, bool>();
      var gateResults = new Dictionary<Tuple<Action, Action>, bool>();

      Tuple<Action, Action> FindPairByNames(string firstName, string secondName)
      {
        return checkList.FirstOrDefault(pair =>
          pair.Item1.ActionDecl.Name == firstName &&
          pair.Item2.ActionDecl.Name == secondName);
      }

      string pendingKind = null;
      Tuple<Action, Action> pendingPair = null;

      foreach (var rawLine in verifierOutput.Split(new[] { "\r\n", "\n" }, StringSplitOptions.None))
      {
        var line = rawLine.TrimEnd();

        if (line.StartsWith("Verifying Civl_CommutativityChecker_"))
        {
          var suffix = line.Substring("Verifying Civl_CommutativityChecker_".Length);
          if (suffix.EndsWith(" ..."))
          {
            suffix = suffix.Substring(0, suffix.Length - " ...".Length);
          }

          var split = suffix.LastIndexOf('_');
          if (split >= 0)
          {
            var firstName = suffix.Substring(0, split);
            var secondName = suffix.Substring(split + 1);
            pendingPair = FindPairByNames(firstName, secondName);
            pendingKind = pendingPair == null ? null : "comm";
          }
          else
          {
            pendingPair = null;
            pendingKind = null;
          }

          continue;
        }

        if (line.StartsWith("Verifying Civl_GatePreservationChecker_"))
        {
          var suffix = line.Substring("Verifying Civl_GatePreservationChecker_".Length);
          if (suffix.EndsWith(" ..."))
          {
            suffix = suffix.Substring(0, suffix.Length - " ...".Length);
          }

          var split = suffix.LastIndexOf('_');
          if (split >= 0)
          {
            var firstName = suffix.Substring(0, split);
            var secondName = suffix.Substring(split + 1);

            // GatePreservationChecker(y, x) contributes to cache entry (x, y)
            pendingPair = FindPairByNames(secondName, firstName);
            pendingKind = pendingPair == null ? null : "gate";
          }
          else
          {
            pendingPair = null;
            pendingKind = null;
          }

          continue;
        }

        if (pendingPair != null)
        {
          bool? passed = null;

          if (line.Contains("]  verified") || line.Trim() == "verified")
          {
            passed = true;
          }
          else if (
            line.Contains("]  error") ||
            line.Trim() == "error" ||
            line.Contains("]  timed out") ||
            line.Contains("]  inconclusive") ||
            line.Contains("]  out of resource") ||
            line.Contains("]  out of memory") ||
            line.Contains("]  solver exception"))
          {
            passed = false;
          }

          if (passed.HasValue)
          {
            if (pendingKind == "comm")
            {
              commResults[pendingPair] = passed.Value;
            }
            else if (pendingKind == "gate")
            {
              gateResults[pendingPair] = passed.Value;
            }

            pendingPair = null;
            pendingKind = null;
          }
        }
      }

      var checksToCache = new Dictionary<Tuple<Action, Action>, bool>();

      foreach (var pair in checkList)
      {
        var comm = commResults.TryGetValue(pair, out var c) ? c : true;
        var gate = gateResults.TryGetValue(pair, out var g) ? g : true;

        checksToCache[pair] = comm && gate;

        // Immediate asymmetric consequence for pair (X, Y):
        // if either comm or gate fails, then X is not right and Y is not left.
        if (!comm || !gate)
        {
          Console.WriteLine($"[MoverInference] {pair.Item1.ActionDecl.Name} is non-right and {pair.Item2.ActionDecl.Name} is non-left");
          MoverCheck.ApplyRightCheckResult(pair.Item1, false);
          MoverCheck.ApplyLeftCheckResult(pair.Item2, false);
        }
      }

      return checksToCache;
    }
    private HashSet<Declaration> GetOriginalCivlDecls(Program program)
    {
      var origActionDecls = program.TopLevelDeclarations.OfType<ActionDecl>();
      var origActionImpls = program.TopLevelDeclarations.OfType<Implementation>()
          .Where(impl => impl.Proc is ActionDecl);
      var origYieldProcs = program.TopLevelDeclarations.OfType<YieldProcedureDecl>();
      var origYieldImpls = program.TopLevelDeclarations.OfType<Implementation>()
          .Where(impl => impl.Proc is YieldProcedureDecl);
      var origYieldInvariants = program.TopLevelDeclarations.OfType<YieldInvariantDecl>();

      return origActionDecls.Union<Declaration>(origActionImpls)
          .Union(origYieldProcs)
          .Union(origYieldImpls)
          .Union(origYieldInvariants)
          .ToHashSet();
    }

    private static void RemoveDeclarations(Program program, HashSet<Declaration> decls)
    {
      program.RemoveTopLevelDeclarations(x => decls.Contains(x));
    }

    private static void RestoreDeclarations(Program program, HashSet<Declaration> decls)
    {
      foreach (var decl in decls)
      {
        program.AddTopLevelDeclaration(decl);
      }
    }
    public async Task<bool> checkRightMover(Action action, CivlTypeChecker civlTypeChecker, Dictionary<Tuple<Action, Action>, bool> previousChecksCache) 
    {
        List<Declaration> rdecls = new List<Declaration>();
        Program program = civlTypeChecker.linearTypeChecker.program;
        var originalDecls = GetOriginalCivlDecls(program);

        civlTypeChecker.AtomicActions.ForEach(x =>
        {
            rdecls.AddRange(new Declaration[] { x.Impl, x.Impl.Proc, x.InputOutputRelation });
            if (x.ImplWithChoice != null)
            {
              rdecls.AddRange(new Declaration[]
                  { x.ImplWithChoice, x.ImplWithChoice.Proc, x.InputOutputRelationWithChoice });
            }
        });

        MoverCheck moverChecking = new MoverCheck(civlTypeChecker, rdecls, previousChecksCache);
        List<Tuple<Action, Action>> currentChecks = new List<Tuple<Action, Action>>();
        foreach (var other in civlTypeChecker.MoverActions.Where(a => a.LayerRange.OverlapsWith(action.LayerRange)))
        {
            bool? previousCheckResult = moverChecking.GetPreviousCheck(action, other);
            if (previousCheckResult.HasValue) {
              if (previousCheckResult.Value == false) {
                return false;
              }
            }
            else {
              moverChecking.CreateRightMoverCheckers(action, other);
              currentChecks.Add(Tuple.Create(action, other));
            }
        }

        RemoveDeclarations(program, originalDecls);
        try
        {
          program.AddTopLevelDeclarations(rdecls);
          new LinearTypeChecker.LinearTypeEraser().VisitProgram(program);

          UnusedVarEliminator.Eliminate(program);
          BlockCoalescer.CoalesceBlocks(program);
          Inline(program);

          TextWriter output = new StringWriter();
          var rightStats = new PipelineStatistics();
          var outcome = await InferAndVerify(output, program, rightStats, null);

          var checksToCache = GetChecksToCache(currentChecks, output.ToString());
          foreach (var kv in checksToCache)
          {
            previousChecksCache[kv.Key] = kv.Value;
            if (Options.Trace)
            {
              Console.WriteLine($"Caching result for pair ({kv.Key.Item1.ActionDecl.Name}, {kv.Key.Item2.ActionDecl.Name}): {kv.Value}");
            }
          }
          if (Options.Trace)
          {
            Console.WriteLine(output.ToString());
          }

          return outcome == PipelineOutcome.VerificationCompleted && rightStats.ErrorCount == 0;
        }
        finally
        {
          program.RemoveTopLevelDeclarations(x => rdecls.Contains(x));
          RestoreDeclarations(program, originalDecls);
        }
    }
    public async Task<bool> checkLeftMover(Action action, CivlTypeChecker civlTypeChecker, Dictionary<Tuple<Action, Action>, bool> previousChecksCache) 
    {
      var program = civlTypeChecker.linearTypeChecker.program;
      var originalDecls = GetOriginalCivlDecls(program);
      
      List<Declaration> ldecls = new List<Declaration>();

      civlTypeChecker.AtomicActions.ForEach(x =>
      {
          ldecls.AddRange(new Declaration[] { x.Impl, x.Impl.Proc, x.InputOutputRelation });
          if (x.ImplWithChoice != null)
          {
            ldecls.AddRange(new Declaration[]
                { x.ImplWithChoice, x.ImplWithChoice.Proc, x.InputOutputRelationWithChoice });
          }
      });

      List<Tuple<Action, Action>> currentChecks = new List<Tuple<Action, Action>>();
      var lmoverChecking = new MoverCheck(civlTypeChecker, ldecls, previousChecksCache);
      if (!action.ActionDecl.HasPreconditions) {
        foreach (var other in civlTypeChecker.MoverActions.Where(a => a.LayerRange.OverlapsWith(action.LayerRange)))
        {
            bool? previousCheckResult = lmoverChecking.GetPreviousCheck(other, action);
            if (previousCheckResult.HasValue) {
              if (previousCheckResult.Value == false) {
                return false;
              }
              else {
                lmoverChecking.CreateFailurePreservationChecker(other, action);
              }
            }
            else {
              lmoverChecking.CreateLeftMoverCheckers(other, action);
              currentChecks.Add(Tuple.Create(other, action));
            }
        }
        lmoverChecking.CreateNonblockingChecker(action);
      }
      else
      {
        var layer = action.ActionDecl.LayerRange.UpperLayer;
        var subst1 = Substituter.SubstitutionFromDictionary(
          action.ActionDecl.InParams.Zip(action.SecondImpl.InParams.Select(x => (Expr)Expr.Ident(x))).ToDictionary(x => x.Item1, x => x.Item2));
        var moverCheckContext1 = new MoverCheck.MoverCheckContext
        {
          layer = layer,
          extraAssumptions = action.Preconditions(layer, subst1).Select(assertCmd => assertCmd.Expr),
        };
        foreach (var other in civlTypeChecker.MoverActions.Where(a => a.LayerRange.OverlapsWith(action.LayerRange)))
        {
          var subst2 = Substituter.SubstitutionFromDictionary(
                      action.ActionDecl.InParams.Zip(action.FirstImpl.InParams.Select(x => (Expr)Expr.Ident(x))).ToDictionary(x => x.Item1, x => x.Item2));
          var moverCheckContext2 = new MoverCheck.MoverCheckContext
          {
            layer = layer,
            extraAssumptions = action.Preconditions(layer, subst2).Select(assertCmd => assertCmd.Expr),
          };
          lmoverChecking.CreateCommutativityChecker(other, action, moverCheckContext1);
          lmoverChecking.CreateGatePreservationChecker(action, other, moverCheckContext2);
          lmoverChecking.CreateFailurePreservationChecker(other, action, moverCheckContext1);
        }
        
        var subst = Substituter.SubstitutionFromDictionary(
            action.ActionDecl.InParams.Zip(action.Impl.InParams.Select(x => (Expr)Expr.Ident(x))).ToDictionary(x => x.Item1, x => x.Item2));
        var moverCheckContext = new MoverCheck.MoverCheckContext
        {
          layer = layer,
          extraAssumptions = action.Preconditions(layer, subst).Select(assertCmd => assertCmd.Expr),
        };
        lmoverChecking.CreateNonblockingChecker(action, moverCheckContext);
      }

      RemoveDeclarations(program, originalDecls);
      try
      {
        program.AddTopLevelDeclarations(ldecls);
        new LinearTypeChecker.LinearTypeEraser().VisitProgram(program);

        UnusedVarEliminator.Eliminate(program);
        BlockCoalescer.CoalesceBlocks(program);
        Inline(program);

        // TODO: Remove this piece of code once I figure out what is not working in the GC.bpl
        if (action.ActionDecl.Name == "AtomicSweepNext")
        { int oldPrintUnstructured = Options.PrintUnstructured;
        Options.PrintUnstructured = 1;
        PrintBplFile("AtomicSweepNext.bpl", program, false, false,
          Options.PrettyPrint);
        Options.PrintUnstructured = oldPrintUnstructured; }


        var output = new StringWriter();
        var leftStats = new PipelineStatistics();
        var outcome = await InferAndVerify(output , program, leftStats, null);

        var checksToCache = GetChecksToCache(currentChecks, output.ToString());
        foreach (var kv in checksToCache)
        {
          previousChecksCache[kv.Key] = kv.Value;
        }
        if (Options.Trace)
        {
          Console.WriteLine(output.ToString());
        }

        return outcome == PipelineOutcome.VerificationCompleted && leftStats.ErrorCount == 0;
      }
      finally
      {
        program.RemoveTopLevelDeclarations(x => ldecls.Contains(x));
        RestoreDeclarations(program, originalDecls);
      }
    }
    private Dictionary<Action, (bool, bool)> CollectObligations(CivlTypeChecker civlTypeChecker)
    {
      var result = new Dictionary<Action, (bool, bool)>();

      foreach (var impl in civlTypeChecker.program.Implementations.Where(impl => impl.Proc is YieldProcedureDecl))
      {
        var yieldingProc = (YieldProcedureDecl)impl.Proc;
        impl.PruneUnreachableBlocks(Options);

        foreach (int layerNum in civlTypeChecker.AllRefinementLayers.Where(l => l <= yieldingProc.Layer))
        {
          var graph = YieldRegionExtractor.BuildGraph(civlTypeChecker, yieldingProc, impl, layerNum);
          var regions = YieldRegionExtractor.ExtractRegions(graph);

          foreach (var region in regions)
          {
            var obligations = YieldRegionExtractor.AnalyzeRegion(region);

            foreach (var action in obligations.MustCheckRightActions)
            {
              var current = result.TryGetValue(action, out var x) ? x : (false, false);
              result[action] = (true, current.Item2);
            }

            foreach (var action in obligations.MustCheckLeftActions)
            {
              var current = result.TryGetValue(action, out var x) ? x : (false, false);
              result[action] = (current.Item1, true);
            }
          }
        }
      }

      return result;
    }
    private Action PickFirstUncheckedCheckAction(CivlTypeChecker civlTypeChecker)
    {
      foreach (var impl in civlTypeChecker.program.Implementations.Where(impl => impl.Proc is YieldProcedureDecl))
      {
        var yieldingProc = (YieldProcedureDecl)impl.Proc;
        impl.PruneUnreachableBlocks(Options);

        foreach (int layerNum in civlTypeChecker.AllRefinementLayers.Where(l => l <= yieldingProc.Layer))
        {
          var graph = YieldRegionExtractor.BuildGraph(civlTypeChecker, yieldingProc, impl, layerNum);
          var regions = YieldRegionExtractor.ExtractRegions(graph);

          foreach (var region in regions)
          {
            var unresolved = YieldRegionExtractor.OrderedCheckEdges(region)
              .Where(edge =>
              {
                var action = edge.Action;
                if (action == null)
                {
                  return false;
                }

                var status = action.ActionDecl.moverCheckStatus;
                return !status.checkedRight && !status.checkedLeft;
              })
              .ToList();

            // Do not use fallback if there is only one unresolved check edge left in this region.
            if (unresolved.Count < 2)
            {
              continue;
            }

            return unresolved[0].Action;
          }
        }
      }

      return null;
    }

    private async Task<bool> ProcessOneMoverInferenceStep(
      CivlTypeChecker civlTypeChecker,
      Dictionary<Tuple<Action, Action>, bool> previousChecksCache)
    {
      var obligations = CollectObligations(civlTypeChecker);

      foreach (var kv in obligations)
      {
        var action = kv.Key;
        var needRight = kv.Value.Item1;
        var needLeft = kv.Value.Item2;
        var status = action.ActionDecl.moverCheckStatus;

        if (needRight && !status.checkedRight)
        {
          var passed = await checkRightMover(action, civlTypeChecker, previousChecksCache);
          MoverCheck.ApplyRightCheckResult(action, passed);

          if (Options.Trace)
          {
            Options.OutputWriter.WriteLine($"[MoverInference] Required right check for {action.ActionDecl.Name}: {passed}");
          }
          return true;
        }

        if (needLeft && !status.checkedLeft)
        {
          var passed = await checkLeftMover(action, civlTypeChecker, previousChecksCache);
          MoverCheck.ApplyLeftCheckResult(action, passed);

          if (Options.Trace)
          {
            Options.OutputWriter.WriteLine($"[MoverInference] Required left check for {action.ActionDecl.Name}: {passed}");
          }
          return true;
        }
      }

      var fallback = PickFirstUncheckedCheckAction(civlTypeChecker);
      if (fallback != null)
      {
        var status = fallback.ActionDecl.moverCheckStatus;

        if (!status.checkedRight)
        {
          var passed = await checkRightMover(fallback, civlTypeChecker, previousChecksCache);
          MoverCheck.ApplyRightCheckResult(fallback, passed);

          if (Options.Trace)
          {
            Options.OutputWriter.WriteLine($"[MoverInference] Fallback right check for {fallback.ActionDecl.Name}: {passed}");
          }
          return true;
        }

        if (!status.checkedLeft)
        {
          var passed = await checkLeftMover(fallback, civlTypeChecker, previousChecksCache);
          MoverCheck.ApplyLeftCheckResult(fallback, passed);

          if (Options.Trace)
          {
            Options.OutputWriter.WriteLine($"[MoverInference] Fallback left check for {fallback.ActionDecl.Name}: {passed}");
          }
          return true;
        }
      }

      return false;
    }

    private List<(Action action, string implName, int layerNum)> CollectUnsafeUnresolvedActions(CivlTypeChecker civlTypeChecker)
    {
      var bad = new List<(Action action, string implName, int layerNum)>();

      foreach (var impl in civlTypeChecker.program.Implementations.Where(impl => impl.Proc is YieldProcedureDecl))
      {
        var yieldingProc = (YieldProcedureDecl)impl.Proc;
        impl.PruneUnreachableBlocks(Options);

        foreach (int layerNum in civlTypeChecker.AllRefinementLayers.Where(l => l <= yieldingProc.Layer))
        {
          var graph = YieldRegionExtractor.BuildGraph(civlTypeChecker, yieldingProc, impl, layerNum);
          var regions = YieldRegionExtractor.ExtractRegions(graph);

          foreach (var region in regions)
          {
            var unresolved = YieldRegionExtractor.OrderedCheckEdges(region)
              .Select(e => e.Action)
              .Where(a => a != null && a.ActionDecl.MoverType == MoverType.Check)
              .Distinct()
              .ToList();

            if (unresolved.Count > 1)
            {
              foreach (var action in unresolved)
              {
                bad.Add((action, impl.Name, layerNum));
              }
            }
          }
        }
      }

      return bad;
    }
    private void DebugPrintRegionsForInference(CivlTypeChecker civlTypeChecker)
    {
      if (!Options.Trace)
      {
        return;
      }

      foreach (var impl in civlTypeChecker.program.Implementations.Where(impl => impl.Proc is YieldProcedureDecl))
      {
        var yieldingProc = (YieldProcedureDecl)impl.Proc;
        impl.PruneUnreachableBlocks(Options);

        foreach (int layerNum in civlTypeChecker.AllRefinementLayers.Where(l => l <= yieldingProc.Layer))
        {
          var graph = YieldRegionExtractor.BuildGraph(civlTypeChecker, yieldingProc, impl, layerNum);
          var yieldEdgeCount = graph.Edges.Count(e => e.Label == "Y");
          var checkEdgeCount = graph.Edges.Count(e => e.Label == "C" && e.Action != null);
          var regions = YieldRegionExtractor.ExtractRegions(graph);

          Options.OutputWriter.WriteLine(
            $"[MoverInference][Graph] Impl={impl.Name}, Layer={layerNum}, " +
            $"YieldEdges={yieldEdgeCount}, CheckEdges={checkEdgeCount}, Regions={regions.Count}");

          int i = 0;
          foreach (var region in regions)
          {
            var unresolved = YieldRegionExtractor.OrderedCheckEdges(region)
              .Select(e => e.Action)
              .Where(a => a != null)
              .Distinct()
              .Where(a =>
              {
                var s = a.ActionDecl.moverCheckStatus;
                return !s.checkedRight || !s.checkedLeft || a.ActionDecl.MoverType == MoverType.Check;
              })
              .Select(a => a.ActionDecl.Name)
              .OrderBy(x => x)
              .ToList();

            var entry = region.EntryYieldEdge == null ? "ENTRY" : region.EntryYieldEdge.Id.ToString();
            var exit = region.ExitYieldEdge == null ? "EXIT" : region.ExitYieldEdge.Id.ToString();

            Options.OutputWriter.WriteLine(
              $"  [Region {i++}] Entry={entry}, Exit={exit}, " +
              $"CheckEdges={YieldRegionExtractor.OrderedCheckEdges(region).Count}, " +
              $"Unresolved={((unresolved.Count == 0) ? "-" : string.Join(", ", unresolved))}");
          }
        }
      }
    }

    private void DebugPrintUnsafeUnresolved(CivlTypeChecker civlTypeChecker)
    {
      if (!Options.Trace)
      {
        return;
      }

      var bad = CollectUnsafeUnresolvedActions(civlTypeChecker);

      if (!bad.Any())
      {
        Options.OutputWriter.WriteLine("[MoverInference][Unsafe] No unsafe unresolved actions found.");
        return;
      }

      Options.OutputWriter.WriteLine("[MoverInference][Unsafe] Unsafe unresolved actions:");
      foreach (var x in bad
        .OrderBy(t => t.implName)
        .ThenBy(t => t.layerNum)
        .ThenBy(t => t.action.ActionDecl.Name))
      {
        Options.OutputWriter.WriteLine(
          $"  Action={x.action.ActionDecl.Name}, Impl={x.implName}, Layer={x.layerNum}");
      }
    }

    public async Task InferMoverTypes(CivlTypeChecker civlTypeChecker)
    {
      Dictionary<Tuple<Action, Action>, bool> previousChecksCache = new Dictionary<Tuple<Action, Action>, bool>();

      foreach (var action in civlTypeChecker.MoverActions.Where(a => a.IsToBeCheckedMover))
      {
        action.ActionDecl.MoverType = MoverType.Check;
        action.ActionDecl.moverCheckStatus.checkedLeft = false;
        action.ActionDecl.moverCheckStatus.checkedRight = false;
        action.ActionDecl.moverCheckStatus.isGiven = false;
      }

      while (await ProcessOneMoverInferenceStep(civlTypeChecker, previousChecksCache))
      {
      }

      DebugPrintRegionsForInference(civlTypeChecker);

      foreach (var action in civlTypeChecker.MoverActions.Where(a => a.IsToBeCheckedMover))
      {
        var status = action.ActionDecl.moverCheckStatus;

        bool rightPassed =
          status.checkedRight &&
          (action.ActionDecl.MoverType == MoverType.Right ||
          action.ActionDecl.MoverType == MoverType.Both);

        bool leftPassed =
          status.checkedLeft &&
          (action.ActionDecl.MoverType == MoverType.Left ||
          action.ActionDecl.MoverType == MoverType.Both);

        if (rightPassed && leftPassed)
        {
          action.ActionDecl.MoverType = MoverType.Both;
        }
        else if (rightPassed)
        {
          action.ActionDecl.MoverType = MoverType.Right;
        }
        else if (leftPassed)
        {
          action.ActionDecl.MoverType = MoverType.Left;
        }
        else
        {
          action.ActionDecl.MoverType = MoverType.Check;
        }
      }

      DebugPrintUnsafeUnresolved(civlTypeChecker);

      var bad = CollectUnsafeUnresolvedActions(civlTypeChecker);
      if (bad.Any())
      {
        var msg = string.Join(
          ", ",
          bad.Select(x => $"{x.action.ActionDecl.Name} in {x.implName} at layer {x.layerNum}").Distinct());

        throw new Exception(
          "Mover inference left multiple unresolved actions in the same yield-to-yield region; " +
          "they cannot all be finalized as non-movers. Offending actions: " + msg);
      }

      foreach (var action in civlTypeChecker.MoverActions.Where(a => a.IsToBeCheckedMover))
      {
        if (action.ActionDecl.MoverType == MoverType.Check)
        {
          action.ActionDecl.MoverType = MoverType.Atomic;
        }

        if (Options.Trace)
        {
          var status = action.ActionDecl.moverCheckStatus;
          Options.OutputWriter.WriteLine(
            $"[MoverInference] Final {action.ActionDecl.Name}: " +
            $"MoverType={action.ActionDecl.MoverType}, " +
            $"checkedRight={status.checkedRight}, checkedLeft={status.checkedLeft}");
        }
      }
    }
    public async Task InferMoverTypesBrute(CivlTypeChecker civlTypeChecker)
    {
      Dictionary<Tuple<Action, Action>, bool> previousChecksCache = new Dictionary<Tuple<Action, Action>, bool>();
      Program program = civlTypeChecker.linearTypeChecker.program;
      var origActionDecls = program.TopLevelDeclarations.OfType<ActionDecl>();
      var origActionImpls = program.TopLevelDeclarations.OfType<Implementation>()
          .Where(impl => impl.Proc is ActionDecl);
      var origYieldProcs = program.TopLevelDeclarations.OfType<YieldProcedureDecl>();
      var origYieldImpls = program.TopLevelDeclarations.OfType<Implementation>()
          .Where(impl => impl.Proc is YieldProcedureDecl);
      var origYieldInvariants = program.TopLevelDeclarations.OfType<YieldInvariantDecl>();
      var originalDecls = origActionDecls.Union<Declaration>(origActionImpls).Union(origYieldProcs)
          .Union(origYieldImpls).Union(origYieldInvariants).ToHashSet();
      program.RemoveTopLevelDeclarations(x => originalDecls.Contains(x));
      foreach (var action in civlTypeChecker.MoverActions.Where(a => a.IsToBeCheckedMover))
      {              
          bool rightMover = await checkRightMover(action, civlTypeChecker, previousChecksCache);  
          bool leftMover = await checkLeftMover(action, civlTypeChecker, previousChecksCache);

          action.ActionDecl.moverCheckStatus.checkedLeft = true;
          action.ActionDecl.moverCheckStatus.checkedRight = true;

          if (rightMover && leftMover)
          {
              Console.WriteLine($"Action {action.ActionDecl.Name} is a both-mover");
              action.ActionDecl.MoverType = MoverType.Both;
          }
          else if (rightMover)
          {
              Console.WriteLine($"Action {action.ActionDecl.Name} is a right-mover");
              action.ActionDecl.MoverType = MoverType.Right;
          }
          else if (leftMover)
          {
              Console.WriteLine($"Action {action.ActionDecl.Name} is a left-mover");
              action.ActionDecl.MoverType = MoverType.Left;
          }
          else
          {
              Console.WriteLine($"Action {action.ActionDecl.Name} is a non-mover");
              action.ActionDecl.MoverType = MoverType.Atomic;
          }

      }

      // bring back original declarations after all checks are done
      foreach (var decl in originalDecls)
      {
          program.AddTopLevelDeclaration(decl);
      }
      
    }

    public static IList<IList<string>> LookForSnapshots(IList<string> fileNames)
    {
      Contract.Requires(fileNames != null);

      var result = new List<IList<string>>();
      for (int version = 0; true; version++)
      {
        var nextSnapshot = new List<string>();
        foreach (var name in fileNames)
        {
          var versionedName = name.Replace(Path.GetExtension(name), ".v" + version + Path.GetExtension(name));
          if (File.Exists(versionedName))
          {
            nextSnapshot.Add(versionedName);
          }
        }

        if (nextSnapshot.Any())
        {
          result.Add(nextSnapshot);
        }
        else
        {
          break;
        }
      }

      return result;
    }

    public void CoalesceBlocks(Program program)
    {
      if (Options.CoalesceBlocks)
      {
        if (Options.Trace)
        {
          Options.OutputWriter.WriteLine("Coalescing blocks...");
        }

        BlockCoalescer.CoalesceBlocks(program);
      }
    }


    public void CollectModifies(Program program)
    {
      if (Options.InferModifies)
      {
        new ModSetCollector(Options).CollectModifies(program);
      }
    }


    public void EliminateDeadVariables(Program program)
    {
      UnusedVarEliminator.Eliminate(program);
    }
    
    public void PrintBplFile(string filename, Program program, 
      bool allowPrintDesugaring, bool setTokens = true,
      bool pretty = false) {
      PrintBplFile(Options, filename, program, allowPrintDesugaring, setTokens, pretty);
    }

    public static void PrintBplFile(ExecutionEngineOptions options, string filename, Program program, 
      bool allowPrintDesugaring, bool setTokens = true,
      bool pretty = false)

    {
      Contract.Requires(program != null);
      Contract.Requires(filename != null);
      bool oldPrintDesugaring = options.PrintDesugarings;
      if (!allowPrintDesugaring)
      {
        options.PrintDesugarings = false;
      }

      using (TokenTextWriter writer = filename == "-"
        ? new TokenTextWriter("<console>", options.OutputWriter, setTokens, pretty, options)
        : new TokenTextWriter(filename, setTokens, pretty, options))
      {
        if (options.ShowEnv != ExecutionEngineOptions.ShowEnvironment.Never)
        {
          writer.WriteLine("// " + options.Version);
          writer.WriteLine("// " + options.Environment);
        }

        writer.WriteLine();
        program.Emit(writer);
      }

      options.PrintDesugarings = oldPrintDesugaring;
    }


    /// <summary>
    /// Parse the given files into one Boogie program.  If an I/O or parse error occurs, an error will be printed
    /// and null will be returned.  On success, a non-null program is returned.
    /// </summary>
    public Program ParseBoogieProgram(IList<string> fileNames, bool suppressTraceOutput)
    {
      Contract.Requires(Cce.NonNullElements(fileNames));

      Program program = new Program();
      bool okay = true;
      
      for (int fileId = 0; fileId < fileNames.Count; fileId++)
      {
        string bplFileName = fileNames[fileId];
        if (!suppressTraceOutput)
        {
          if (Options.XmlSink != null)
          {
            Options.XmlSink.WriteFileFragment(bplFileName);
          }

          if (Options.Trace)
          {
            Options.OutputWriter.WriteLine("Parsing " + GetFileNameForConsole(Options, bplFileName));
          }
        }

        try
        {
          var defines = new List<string>() {"FILE_" + fileId};
          int errorCount = Parser.Parse(bplFileName, defines, out Program programSnippet,
            Options.UseBaseNameForFileName);
          if (programSnippet == null || errorCount != 0)
          {
            Options.OutputWriter.WriteLine("{0} parse errors detected in {1}", errorCount, GetFileNameForConsole(Options, bplFileName));
            okay = false;
          }
          else
          {
            program.AddTopLevelDeclarations(programSnippet.TopLevelDeclarations);
          }
        }
        catch (IOException e)
        {
          Options.Printer.ErrorWriteLine(Options.OutputWriter, "Error opening file \"{0}\": {1}",
            GetFileNameForConsole(Options, bplFileName), e.Message);
          okay = false;
        }
      }

      if (!okay)
      {
        return null;
      }

      if (program.TopLevelDeclarations.Any(d => d.HasCivlAttribute()))
      {
        Options.Libraries.Add("base");
        Options.InferModifies = true;
      }
      foreach (var libraryName in Options.Libraries)
      {
        var library = ParseLibrary(libraryName);
        if (library == null)
        {
          okay = false;
          continue;
        }
        program.AddTopLevelDeclarations(library.TopLevelDeclarations);
      }

      if (!okay)
      {
        return null;
      }
      return program;
    }

    private Program ParseLibrary(string libraryName)
    {
      string libraryFileName = $"{libraryName}.bpl";
      Assembly asm = Assembly.Load("Boogie.Core");
      var resourceName = $"Core.{libraryFileName}";
      using Stream resourceStream = asm.GetManifestResourceStream(resourceName);
      if (resourceStream == null)
      {
        Options.Printer.ErrorWriteLine(Options.OutputWriter, $"Error locating library: {resourceName} not found");
        return null;
      }
      Parser.Parse(new StreamReader(resourceStream), libraryFileName, new List<string>(), out Program library);
      return library;
    }

    internal static string GetFileNameForConsole(ExecutionEngineOptions options, string filename)
    {
      return options.UseBaseNameForFileName && !string.IsNullOrEmpty(filename) &&
             filename != "<console>"
        ? Path.GetFileName(filename)
        : filename;
    }


    /// <summary>
    /// Resolves and type checks the given Boogie program.  Any errors are reported to the
    /// console.  Returns:
    ///  - Done if no errors occurred, and command line specified no resolution or no type checking.
    ///  - ResolutionError if a resolution error occurred
    ///  - TypeCheckingError if a type checking error occurred
    ///  - ResolvedAndTypeChecked if both resolution and type checking succeeded
    /// </summary>
    public PipelineOutcome ResolveAndTypecheck(Program program, string bplFileName,
      out CivlTypeChecker civlTypeChecker)
    {
      Contract.Requires(program != null);
      Contract.Requires(bplFileName != null);

      civlTypeChecker = null;

      // ---------- Resolve ------------------------------------------------------------

      if (Options.NoResolve)
      {
        return PipelineOutcome.Done;
      }

      var errorCount = program.Resolve(Options);
      if (errorCount != 0)
      {
        Options.OutputWriter.WriteLine("{0} name resolution errors detected in {1}", errorCount, GetFileNameForConsole(Options, bplFileName));
        return PipelineOutcome.ResolutionError;
      }

      // ---------- Type check ------------------------------------------------------------

      if (Options.NoTypecheck)
      {
        return PipelineOutcome.Done;
      }

      if (!FunctionDependencyChecker.Check(program))
      {
        return PipelineOutcome.TypeCheckingError;
      }
      
      CollectModifies(program);

      errorCount = program.Typecheck(Options);
      if (errorCount != 0)
      {
        Options.OutputWriter.WriteLine("{0} type checking errors detected in {1}", errorCount, GetFileNameForConsole(Options, bplFileName));
        return PipelineOutcome.TypeCheckingError;
      }

      if (MonomorphismChecker.IsMonomorphic(program))
      {
        Options.TypeEncodingMethod = CoreOptions.TypeEncoding.Monomorphic;
      }
      else if (Options.TypeEncodingMethod == CoreOptions.TypeEncoding.Monomorphic)
      {
        var monomorphizableStatus = Monomorphizer.Monomorphize(Options, program);
        if (monomorphizableStatus == MonomorphizableStatus.Monomorphizable)
        {
          // all ok
        }
        else if (monomorphizableStatus == MonomorphizableStatus.UnhandledPolymorphism)
        {
          Options.OutputWriter.WriteLine("Unable to monomorphize input program: unhandled polymorphic features detected");
          return PipelineOutcome.FatalError;
        }
        else
        {
          Options.OutputWriter.WriteLine("Unable to monomorphize input program: expanding type cycle detected");
          return PipelineOutcome.FatalError;
        }
      }
      else if (program.TopLevelDeclarations.OfType<DatatypeTypeCtorDecl>().Any())
      {
        Options.OutputWriter.WriteLine("Datatypes only supported with monomorphic encoding");
        return PipelineOutcome.FatalError;
      }
      else if (program.TopLevelDeclarations.OfType<Function>().Any(f => f.Attributes.FindBoolAttribute("define")))
      {
        Options.OutputWriter.WriteLine("Functions with :define attribute only supported with monomorphic encoding");
        return PipelineOutcome.FatalError;
      }

      civlTypeChecker = new CivlTypeChecker(Options, program);
      civlTypeChecker.TypeCheck();
      if (civlTypeChecker.checkingContext.ErrorCount != 0)
      {
        Options.OutputWriter.WriteLine("{0} type checking errors detected in {1}", civlTypeChecker.checkingContext.ErrorCount,
          GetFileNameForConsole(Options, bplFileName));
        return PipelineOutcome.TypeCheckingError;
      }

      if (Options.Trace)
      {
        foreach (var impl in civlTypeChecker.program.Implementations
          .Where(impl => impl.Proc is YieldProcedureDecl && impl.Name == "SlowAdd"))
        {
          var yieldingProc = (YieldProcedureDecl)impl.Proc;
          impl.PruneUnreachableBlocks(Options);

          foreach (int layerNum in civlTypeChecker.AllRefinementLayers.Where(l => l <= yieldingProc.Layer))
          {
            Options.OutputWriter.WriteLine($"[YieldingLoops] Impl={impl.Name}, Layer={layerNum}");
            foreach (var kv in yieldingProc.YieldingLoops)
            {
              Options.OutputWriter.WriteLine(
                $"  Header={kv.Key.Label}, YieldLayer={kv.Value.Layer}, InvCount={kv.Value.YieldInvariants.Count}");
            }

            var graph = YieldRegionExtractor.BuildGraph(civlTypeChecker, yieldingProc, impl, layerNum);
            Options.OutputWriter.WriteLine($"=== Graph for {impl.Name} at layer {layerNum} ===");
            Options.OutputWriter.WriteLine(YieldRegionExtractor.PrintGraph(graph));

            var regions = YieldRegionExtractor.ExtractRegions(graph);
            YieldRegionExtractor.ValidateRegions(regions);

            Options.OutputWriter.WriteLine($"=== Regions for {impl.Name} at layer {layerNum}: {regions.Count} ===");
            int i = 0;
            foreach (var region in regions)
            {
              Options.OutputWriter.WriteLine($"Region {i++}:");
              Options.OutputWriter.WriteLine(YieldRegionExtractor.PrintRegion(region));

              var obligations = YieldRegionExtractor.AnalyzeRegion(region);
              Options.OutputWriter.WriteLine(YieldRegionExtractor.PrintObligations(obligations));
            }
          }
        }
      }
      
      if(Options.InferMoverTypes)
      {
        InferMoverTypes(civlTypeChecker).GetAwaiter().GetResult();     
      }

      YieldSufficiencyChecker.TypeCheck(civlTypeChecker);
      if (Options.PrintFile != null && Options.PrintDesugarings)
      {
        // if PrintDesugaring option is engaged, print the file here, after resolution and type checking
        PrintBplFile(Options.PrintFile, program, true, true, Options.PrettyPrint);
      }

      return PipelineOutcome.ResolvedAndTypeChecked;
    }


    public void Inline(Program program)
    {
      Contract.Requires(program != null);

      if (Options.Trace)
      {
        Options.OutputWriter.WriteLine("Inlining...");
      }

      // Inline
      var TopLevelDeclarations = Cce.NonNull(program.TopLevelDeclarations);

      if (Options.ProcedureInlining != CoreOptions.Inlining.None)
      {
        bool inline = false;
        foreach (var d in TopLevelDeclarations)
        {
          if ((d is Procedure || d is Implementation) && d.FindExprAttribute("inline") != null)
          {
            inline = true;
          }
        }

        if (inline)
        {
          foreach (var impl in TopLevelDeclarations.OfType<Implementation>())
          {
            impl.OriginalBlocks = impl.Blocks;
            impl.OriginalLocVars = impl.LocVars;
          }

          foreach (var impl in TopLevelDeclarations.OfType<Implementation>())
          {
            if (Options.UserWantsToCheckRoutine(impl.VerboseName) && !impl.IsSkipVerification(Options))
            {
              Inliner.ProcessImplementation(Options, program, impl);
            }
          }

          foreach (var impl in TopLevelDeclarations.OfType<Implementation>())
          {
            impl.OriginalBlocks = null;
            impl.OriginalLocVars = null;
          }
        }
      }
    }

    [Obsolete("Please inline this method call")]
    public PipelineOutcome InferAndVerify(
      Program program,
      PipelineStatistics stats,
      string programId = null,
      ErrorReporterDelegate er = null, string requestId = null) {
      return InferAndVerify(Options.OutputWriter, program, stats, programId, er, requestId).Result;
    }

    /// <summary>
    /// Given a resolved and type checked Boogie program, infers invariants for the program
    /// and then attempts to verify it.  Returns:
    ///  - Done if command line specified no verification
    ///  - FatalError if a fatal error occurred, in which case an error has been printed to console
    ///  - VerificationCompleted if inference and verification completed, in which the out
    ///    parameters contain meaningful values
    /// </summary>
    public async Task<PipelineOutcome> InferAndVerify(
      TextWriter output,
      Program program,
      PipelineStatistics stats,
      string programId = null,
      ErrorReporterDelegate er = null, string requestId = null, 
      CancellationToken cancellationToken = default)
    {
      Contract.Requires(program != null);
      Contract.Requires(stats != null);
      Contract.Ensures(0 <= Contract.ValueAtReturn(out stats.InconclusiveCount) &&
                       0 <= Contract.ValueAtReturn(out stats.TimeoutCount));

      requestId ??= FreshRequestId();


      var start = DateTime.UtcNow;

      var processedProgram = await PreProcessProgramVerification(program, cancellationToken);

      foreach (var action in Options.UseResolvedProgram) {
        action(Options, processedProgram);
      }

      if (!Options.Verify)
      {
        return PipelineOutcome.Done;
      }

      if (Options.ContractInfer)
      {
        return await RunHoudini(program, stats, er, cancellationToken);
      }
      var stablePrioritizedImpls = GetPrioritizedImplementations(program);

      if (1 < Options.VerifySnapshots)
      {
        CachedVerificationResultInjector.Inject(this, program, stablePrioritizedImpls, requestId, programId,
          out stats.CachingActionCounts);
      }

      var outcome = await VerifyEachImplementation(output, processedProgram, stats, 
        programId, er, stablePrioritizedImpls, cancellationToken);

      if (1 < Options.VerifySnapshots && programId != null)
      {
        program.FreezeTopLevelDeclarations();
        this.Cache.SetProgram(programId, program, policy);
      }

      TraceCachingForBenchmarking(stats, requestId, start);

      return outcome;
    }

    private Task<ProcessedProgram> PreProcessProgramVerification(Program program, CancellationToken cancellationToken)
    {
      return LargeThreadTaskFactory.StartNew(() =>
      {
        // Doing lambda expansion before abstract interpretation means that the abstract interpreter
        // never needs to see any lambda expressions.  (On the other hand, if it were useful for it
        // to see lambdas, then it would be better to more lambda expansion until after inference.)
        if (Options.ExpandLambdas)
        {
          LambdaHelper.ExpandLambdas(Options, program);
          if (Options.PrintFile != null && Options.PrintLambdaLifting)
          {
            PrintBplFile(Options.PrintFile, program, false, true, Options.PrettyPrint);
          }
        }

        if (Options.UseAbstractInterpretation)
        {
          new AbstractInterpretation.NativeAbstractInterpretation(Options).RunAbstractInterpretation(program);
        }

        if (Options.LoopUnrollCount != -1)
        {
          program.UnrollLoops(Options.LoopUnrollCount, Options.SoundLoopUnrolling);
        }

        var processedProgram = Options.ExtractLoops ? ExtractLoops(program) : new ProcessedProgram(program);
        if (Options.WarnVacuousProofs) {
          processedProgram = AddVacuityChecking(processedProgram);
        }

        if (Options.PrintInstrumented)
        {
          program.Emit(new TokenTextWriter(Options.OutputWriter, Options.PrettyPrint, Options));
        }

        program.DeclarationDependencies = Pruner.ComputeDeclarationDependencies(Options, program);
        return processedProgram;
      }, cancellationToken);
    }

    private ProcessedProgram ExtractLoops(Program program)
    {
      var extractLoopMappingInfo = LoopExtractor.ExtractLoops(Options, program);
      return new ProcessedProgram(program, (vcgen, impl, result) =>
      {
        if (result.Errors != null) {
          for (int i = 0; i < result.Errors.Count; i++) {
            result.Errors[i] = vcgen.ExtractLoopTrace(result.Errors[i], impl.Name, program, extractLoopMappingInfo);
          }
        }
      });
    }

    private ProcessedProgram AddVacuityChecking(ProcessedProgram processedProgram)
    {
      Program program = processedProgram.Program;
      CoverageAnnotator annotator = new CoverageAnnotator();
      foreach (var impl in program.Implementations) {
        annotator.VisitImplementation(impl);
      }
      return new ProcessedProgram(program, (vcgen, impl, result) =>
        {
          CheckVacuity(annotator, impl, result);
          processedProgram.PostProcessResult(vcgen, impl, result);
        }
      );
    }

    private void CheckVacuity(CoverageAnnotator annotator, Implementation impl, ImplementationRunResult verificationResult)
    {
      var covered = verificationResult
        .RunResults
        .SelectMany(r => r.CoveredElements)
        .ToHashSet();
      foreach (var goalId in annotator.GetImplementationGoalIds(impl.Name)) {
        if (!CoveredId(goalId, covered)) {
          var node = annotator.GetIdNode(goalId);
          Options.Printer.AdvisoryWriteLine(Options.OutputWriter,
            $"{node.tok.filename}({node.tok.line},{node.tok.col - 1}): Warning: Proved vacuously");
        }
      }
    }

    private static bool CoveredId(string goalId, HashSet<TrackedNodeComponent> covered)
    {
      foreach (var component in covered) {
        if (component is LabeledNodeComponent { id: var id } && id == goalId) {
          return true;
        }

        if (component is TrackedInvariantEstablished { invariantId: var eid } && eid == goalId) {
          return true;
        }

        if (component is TrackedInvariantMaintained { invariantId: var mid } && mid == goalId) {
          return true;
        }
      }

      return false;
    }

    private Implementation[] GetPrioritizedImplementations(Program program)
    {
      var impls = program.Implementations.Where(
        impl => impl != null && Options.UserWantsToCheckRoutine(Cce.NonNull(impl.VerboseName)) &&
                !impl.IsSkipVerification(Options)).ToArray();

      // operate on a stable copy, in case it gets updated while we're running
      Implementation[] stablePrioritizedImpls = null;

      if (0 < Options.VerifySnapshots) {
        OtherDefinitionAxiomsCollector.Collect(Options, program.Axioms);
        DependencyCollector.Collect(Options, program);
        stablePrioritizedImpls = impls.OrderByDescending(
          impl => impl.Priority != 1 ? impl.Priority : Cache.VerificationPriority(impl, Options.RunDiagnosticsOnTimeout)).ToArray();
      } else {
        stablePrioritizedImpls = impls.OrderByDescending(impl => impl.Priority).ToArray();
      }

      return stablePrioritizedImpls;
    }

    private async Task<PipelineOutcome> VerifyEachImplementation(TextWriter outputWriter, ProcessedProgram processedProgram,
      PipelineStatistics stats,
      string programId, ErrorReporterDelegate er, Implementation[] stablePrioritizedImpls,
      CancellationToken cancellationToken)
    {
      var consoleCollector = new ConcurrentToSequentialWriteManager(outputWriter);
      
      var tasks = stablePrioritizedImpls.Select(async (impl, index) => {
        await using var taskWriter = consoleCollector.AppendWriter();
        var implementation = stablePrioritizedImpls[index];
        var result = await EnqueueVerifyImplementation(processedProgram, stats, programId, er,
          implementation, cancellationToken, taskWriter);
        var output = result.GetOutput(Options.Printer, this, stats, er);
        await taskWriter.WriteAsync(output);
        return result;
      }).ToList();
      var outcome = PipelineOutcome.VerificationCompleted;

      try {
        await Task.WhenAll(tasks);
        foreach (var task in tasks) {
          task.Result.ProcessXml(this);
        }
      } catch(TaskCanceledException) {
        outcome = PipelineOutcome.Cancelled;
      } catch(ProverException e) {
        Options.Printer.ErrorWriteLine(outputWriter, "Fatal Error: ProverException: {0}", e.Message);
        outcome = PipelineOutcome.FatalError;
      }

      if (Options.Trace && Options.TrackVerificationCoverage && processedProgram.Program.AllCoveredElements.Any()) {
        Options.OutputWriter.WriteLine("Proof dependencies of whole program:\n  {0}",
          string.Join("\n  ",
            processedProgram
              .Program
              .AllCoveredElements
              .Select(elt => elt.Description)
              .OrderBy(s => s)));
      }

      Cce.NonNull(Options.TheProverFactory).Close();

      return outcome;

    }

    class CollectingErrorSink : IErrorSink
    {
      public readonly List<(IToken Token, string Message)> Errors = new();
      
      public void Error(IToken tok, string msg)
      {
        Errors.Add((tok, msg));
      }
    }
    
    public async Task<IReadOnlyList<IVerificationTask>> GetVerificationTasks(Program program, CancellationToken cancellationToken = default)
    {
      var sink = new CollectingErrorSink();
      var resolutionErrors = program.Resolve(Options, sink);
      
      string GetErrorsString() => string.Join("\n", sink.Errors.Select(t => $"{t.Token}: {t.Message}"));
      if (resolutionErrors > 0)
      {
        throw new ArgumentException($"Boogie program had {resolutionErrors} resolution errors:\n{GetErrorsString()}");
      }
      var typeErrors = program.Typecheck(Options, sink);
      if (typeErrors > 0)
      {
        throw new ArgumentException($"Boogie program had {typeErrors} type errors:\n{GetErrorsString()}");
      }

      EliminateDeadVariables(program);
      CollectModifies(program);
      CoalesceBlocks(program);
      Inline(program);

      var processedProgram = await PreProcessProgramVerification(program, cancellationToken);
      return GetPrioritizedImplementations(program).SelectMany(implementation =>
      {
        var writer = TextWriter.Null;
        var vcGenerator = new VerificationConditionGenerator(processedProgram.Program, CheckerPool);
        
        var run = new ImplementationRun(implementation, writer);
        var collector = new VerificationResultCollector(Options);
        vcGenerator.PrepareImplementation(run, collector, out _,
          out var modelViewInfo);

        ConditionGeneration.ResetPredecessors(run.Implementation.Blocks);
        var splits = ManualSplitFinder.GetParts(Options, run,  
          (token, blocks) => new ManualSplit(Options, () => blocks, vcGenerator, run, token)).ToList();
        for (var index = 0; index < splits.Count; index++) {
          var split = splits[index];
          split.SplitIndex = index;
        }

        return splits.Select(split => new VerificationTask(this, processedProgram, split, modelViewInfo));
      }).ToList();
    }

    /// <returns>
    /// The outer task is to wait for a semaphore to let verification start
    /// The inner task is the actual verification of the implementation
    /// </returns>
    public Task<ImplementationRunResult> EnqueueVerifyImplementation(
      ProcessedProgram processedProgram, PipelineStatistics stats,
      string programId, ErrorReporterDelegate errorReporterDelegate, Implementation implementation,
      CancellationTokenSource cts,
      TextWriter taskWriter)
    {
      var id = implementation.Id;
      if (ImplIdToCancellationTokenSource.TryGetValue(id, out var old)) {
        old.Cancel();
      }

      try
      {
        return EnqueueVerifyImplementation(processedProgram, stats, programId, errorReporterDelegate, implementation,
          cts.Token, taskWriter);
      }
      finally
      {
        ImplIdToCancellationTokenSource.TryRemove(id, out old);
      }
    }

    /// <returns>
    /// The outer task is to wait for a semaphore to let verification start
    /// The inner task is the actual verification of the implementation
    /// </returns>
    private async Task<ImplementationRunResult> EnqueueVerifyImplementation(
      ProcessedProgram processedProgram, PipelineStatistics stats,
      string programId, ErrorReporterDelegate errorReporterDelegate, Implementation implementation,
      CancellationToken cancellationToken,
      TextWriter taskWriter)
    {
      await verifyImplementationSemaphore.WaitAsync(cancellationToken);
      try
      {
        return await VerifyImplementationWithCaching(processedProgram, stats, errorReporterDelegate, 
          cancellationToken, implementation, programId, taskWriter);
      }
      finally
      {
        verifyImplementationSemaphore.Release();
      }
    }

    private void TraceCachingForBenchmarking(PipelineStatistics stats,
      string requestId, DateTime start)
    {
      if (0 <= Options.VerifySnapshots && Options.TraceCachingForBenchmarking) {
        var end = DateTime.UtcNow;
        if (TimePerRequest.Count == 0) {
          FirstRequestStart = start;
        }

        TimePerRequest[requestId] = end.Subtract(start);
        StatisticsPerRequest[requestId] = stats;

        var printTimes = true;

        Options.OutputWriter.WriteLine(CachedVerificationResultInjector.Statistics.Output(printTimes));

        Options.OutputWriter.WriteLine("Statistics per request as CSV:");
        var actions = string.Join(", ", Enum.GetNames(typeof(VC.ConditionGeneration.CachingAction)));
        Options.OutputWriter.WriteLine(
          "Request ID{0}, Error, E (C), Inconclusive, I (C), Out of Memory, OoM (C), Timeout, T (C), Verified, V (C), {1}",
          printTimes ? ", Time (ms)" : "", actions);
        foreach (var kv in TimePerRequest.OrderBy(kv => ExecutionEngine.AutoRequestId(kv.Key))) {
          var s = StatisticsPerRequest[kv.Key];
          var cacs = s.CachingActionCounts;
          IEnumerable<string> tempQualifier = cacs.Select(ac => $"{ac,3}");
          var c = cacs != null ? ", " + string.Join(", ", tempQualifier) : "";
          var t = printTimes ? $", {kv.Value.TotalMilliseconds,8:F0}" : "";
          Options.OutputWriter.WriteLine(
            "{0,-19}{1}, {2,2}, {3,2}, {4,2}, {5,2}, {6,2}, {7,2}, {8,2}, {9,2}, {10,2}, {11,2}{12}", kv.Key, t,
            s.ErrorCount, s.CachedErrorCount, s.InconclusiveCount, s.CachedInconclusiveCount, s.OutOfMemoryCount,
            s.CachedOutOfMemoryCount, s.TimeoutCount, s.CachedTimeoutCount, s.VerifiedCount, s.CachedVerifiedCount, c);
        }

        if (printTimes) {
          Options.OutputWriter.WriteLine();
          Options.OutputWriter.WriteLine("Total time (ms) since first request: {0:F0}",
            end.Subtract(FirstRequestStart).TotalMilliseconds);
        }
      }
    }

    private async Task<ImplementationRunResult> VerifyImplementationWithCaching(
      ProcessedProgram processedProgram,
      PipelineStatistics stats,
      ErrorReporterDelegate er,
      CancellationToken cancellationToken,
      Implementation implementation,
      string programId,
      TextWriter traceWriter)
    {
      ImplementationRunResult implementationRunResult = GetCachedVerificationResult(implementation, traceWriter);
      if (implementationRunResult != null) {
        UpdateCachedStatistics(stats, implementationRunResult.VcOutcome, implementationRunResult.Errors);
        return implementationRunResult;
      }
      Options.Printer.Inform("", traceWriter); // newline
      Options.Printer.Inform($"Verifying {implementation.VerboseName} ...", traceWriter);

      var result = await VerifyImplementationWithLargeThread(processedProgram, stats, er, cancellationToken,
        programId, implementation, traceWriter);
      if (0 < Options.VerifySnapshots && !string.IsNullOrEmpty(implementation.Checksum))
      {
        Cache.Insert(implementation, result);
      }
      Options.Printer.ReportEndVerifyImplementation(implementation, result);

      return result;
    }

    public ImplementationRunResult GetCachedVerificationResult(Implementation impl, TextWriter output)
    {
      if (0 >= Options.VerifySnapshots)
      {
        return null;
      }

      var cachedResults = Cache.Lookup(impl, Options.RunDiagnosticsOnTimeout, out var priority);
      if (cachedResults == null || priority != Priority.SKIP)
      {
        return null;
      }

      if (Options.VerifySnapshots < 3 ||
          cachedResults.VcOutcome == VcOutcome.Correct) {
        Options.Printer.Inform($"Retrieving cached verification result for implementation {impl.VerboseName}...", output);
        return cachedResults;
      }

      return null;
    }

    private Task<ImplementationRunResult> VerifyImplementationWithLargeThread(ProcessedProgram processedProgram,
      PipelineStatistics stats, ErrorReporterDelegate er, CancellationToken cancellationToken,
      string programId, Implementation impl, TextWriter traceWriter)
    {

      var resultTask = LargeThreadTaskFactory.StartNew(async () =>
      {
        var verificationResult = new ImplementationRunResult(impl, programId);
        var vcGen = new VerificationConditionGenerator(processedProgram.Program, CheckerPool);
        vcGen.CachingActionCounts = stats.CachingActionCounts;
        verificationResult.ProofObligationCountBefore = vcGen.CumulativeAssertionCount;
        verificationResult.Start = DateTime.UtcNow;

        try
        {
          (verificationResult.VcOutcome, verificationResult.Errors, verificationResult.RunResults) =
            await vcGen.VerifyImplementationDirectly(new ImplementationRun(impl, traceWriter), cancellationToken);
          processedProgram.PostProcessResult(vcGen, impl, verificationResult);
        }
        catch (VCGenException e)
        {
          string msg = $"{e.Message} (encountered in implementation {impl.VerboseName}).";
          var errorInfo = ErrorInformation.Create(impl.tok, msg, null);
          errorInfo.ImplementationName = impl.VerboseName;
          verificationResult.ErrorBeforeVerification = errorInfo;
          if (er != null)
          {
            lock (er)
            {
              er(errorInfo);
            }
          }

          verificationResult.Errors = null;
          verificationResult.VcOutcome = VcOutcome.Inconclusive;
        }
        catch (ProverDiedException)
        {
          throw;
        }
        catch (UnexpectedProverOutputException upo)
        {
          Options.Printer.AdvisoryWriteLine(traceWriter,
            "Advisory: {0} SKIPPED because of internal error: unexpected prover output: {1}",
            impl.VerboseName, upo.Message);
          verificationResult.Errors = null;
          verificationResult.VcOutcome = VcOutcome.Inconclusive;
        }
        catch (IOException e)
        {
          Options.Printer.AdvisoryWriteLine(traceWriter, "Advisory: {0} SKIPPED due to I/O exception: {1}",
            impl.VerboseName, e.Message);
          verificationResult.Errors = null;
          verificationResult.VcOutcome = VcOutcome.SolverException;
        }

        verificationResult.ProofObligationCountAfter = vcGen.CumulativeAssertionCount;
        verificationResult.End = DateTime.UtcNow;
        // `TotalProverElapsedTime` does not include the initial cost of starting
        // the SMT solver (unlike `End - Start` in `VerificationResult`).  It
        // may still include the time taken to restart the prover when running
        // with `vcsCores > 1`.
        verificationResult.Elapsed = vcGen.TotalProverElapsedTime;
        verificationResult.ResourceCount = vcGen.ResourceCount;
        return verificationResult;
      }, cancellationToken).Unwrap();

      return resultTask;
    }

    #region Houdini

    private async Task<PipelineOutcome> RunHoudini(Program program, PipelineStatistics stats, ErrorReporterDelegate er,
      CancellationToken cancellationToken)
    {
      Contract.Requires(stats != null);
      
      if (Options.StagedHoudini != null)
      {
        return await RunStagedHoudini(program, stats, er);
      }

      var houdiniStats = new Houdini.HoudiniSession.HoudiniStatistics();
      var outputWriter = Options.OutputWriter;
      var houdini = new Houdini.Houdini(outputWriter, Options, program, houdiniStats);
      var outcome = await houdini.PerformHoudiniInference();
      houdini.Close();

      if (Options.PrintAssignment)
      {
        await outputWriter.WriteLineAsync("Assignment computed by Houdini:");
        foreach (var x in outcome.assignment)
        {
          await outputWriter.WriteLineAsync(x.Key + " = " + x.Value);
        }
      }

      if (Options.Trace)
      {
        int numTrueAssigns = 0;
        foreach (var x in outcome.assignment)
        {
          if (x.Value)
          {
            numTrueAssigns++;
          }
        }

        await outputWriter.WriteLineAsync("Number of true assignments = " + numTrueAssigns);
        await outputWriter.WriteLineAsync("Number of false assignments = " + (outcome.assignment.Count - numTrueAssigns));
        await outputWriter.WriteLineAsync("Prover time = " + houdiniStats.proverTime.ToString("F2"));
        await outputWriter.WriteLineAsync("Unsat core prover time = " + houdiniStats.unsatCoreProverTime.ToString("F2"));
        await outputWriter.WriteLineAsync("Number of prover queries = " + houdiniStats.numProverQueries);
        await outputWriter.WriteLineAsync("Number of unsat core prover queries = " + houdiniStats.numUnsatCoreProverQueries);
        await outputWriter.WriteLineAsync("Number of unsat core prunings = " + houdiniStats.numUnsatCorePrunings);
      }

      foreach (Houdini.VCGenOutcome x in outcome.implementationOutcomes.Values)
      {
        ProcessOutcome(Options.Printer, x.VcOutcome, x.errors, "", stats, outputWriter, Options.TimeLimit, er);
        ProcessErrors(Options.Printer, x.errors, x.VcOutcome, outputWriter, er);
      }

      return PipelineOutcome.Done;
    }

    public Program ProgramFromFile(string filename)
    {
      Program p = ParseBoogieProgram( new List<string> {filename}, false);
      Debug.Assert(p != null);
      PipelineOutcome oc = ResolveAndTypecheck(p, filename, out var civlTypeChecker);
      Debug.Assert(oc == PipelineOutcome.ResolvedAndTypeChecked);
      return p;
    }

    private async Task<PipelineOutcome> RunStagedHoudini(Program program, PipelineStatistics stats, ErrorReporterDelegate er)
    {
      Houdini.HoudiniSession.HoudiniStatistics houdiniStats = new Houdini.HoudiniSession.HoudiniStatistics();
      var stagedHoudini = new Houdini.StagedHoudini(Options.OutputWriter, Options, program, houdiniStats, ProgramFromFile);
      Houdini.HoudiniOutcome outcome = await stagedHoudini.PerformStagedHoudiniInference();

      if (Options.PrintAssignment)
      {
        await Options.OutputWriter.WriteLineAsync("Assignment computed by Houdini:");
        foreach (var x in outcome.assignment)
        {
          await Options.OutputWriter.WriteLineAsync(x.Key + " = " + x.Value);
        }
      }

      if (Options.Trace)
      {
        int numTrueAssigns = 0;
        foreach (var x in outcome.assignment)
        {
          if (x.Value)
          {
            numTrueAssigns++;
          }
        }

        await Options.OutputWriter.WriteLineAsync("Number of true assignments = " + numTrueAssigns);
        await Options.OutputWriter.WriteLineAsync("Number of false assignments = " + (outcome.assignment.Count - numTrueAssigns));
        await Options.OutputWriter.WriteLineAsync("Prover time = " + houdiniStats.proverTime.ToString("F2"));
        await Options.OutputWriter.WriteLineAsync("Unsat core prover time = " + houdiniStats.unsatCoreProverTime.ToString("F2"));
        await Options.OutputWriter.WriteLineAsync("Number of prover queries = " + houdiniStats.numProverQueries);
        await Options.OutputWriter.WriteLineAsync("Number of unsat core prover queries = " + houdiniStats.numUnsatCoreProverQueries);
        await Options.OutputWriter.WriteLineAsync("Number of unsat core prunings = " + houdiniStats.numUnsatCorePrunings);
      }

      foreach (Houdini.VCGenOutcome x in outcome.implementationOutcomes.Values)
      {
        ProcessOutcome(Options.Printer, x.VcOutcome, x.errors, "", stats, Options.OutputWriter, Options.TimeLimit, er);
        ProcessErrors(Options.Printer, x.errors, x.VcOutcome, Options.OutputWriter, er);
      }

      return PipelineOutcome.Done;
    }

    #endregion

    public void ProcessOutcome(OutputPrinter printer, VcOutcome vcOutcome, List<Counterexample> errors, string timeIndication,
      PipelineStatistics stats, TextWriter tw, uint timeLimit, ErrorReporterDelegate er = null, string implName = null,
      IToken implTok = null, string msgIfVerifies = null)
    {
      Contract.Requires(stats != null);

      UpdateStatistics(stats, vcOutcome, errors);

      printer.Inform(timeIndication + OutcomeIndication(vcOutcome, errors), tw);

      ReportOutcome(printer, vcOutcome, er, implName, implTok, msgIfVerifies, tw, timeLimit, errors);
    }

    public void ReportOutcome(OutputPrinter printer,
      VcOutcome vcOutcome, ErrorReporterDelegate er, string implName,
      IToken implTok, string msgIfVerifies, TextWriter tw, uint timeLimit, List<Counterexample> errors) {

      var errorInfo = GetOutcomeError(Options, vcOutcome, implName, implTok, msgIfVerifies, tw, timeLimit, errors);
      if (errorInfo != null)
      {
        errorInfo.ImplementationName = implName;
        if (er != null)
        {
          lock (er)
          {
            er(errorInfo);
          }
        } else {
          printer.WriteErrorInformation(errorInfo, tw);
        }
      }
    }

    internal static ErrorInformation GetOutcomeError(ExecutionEngineOptions options, VcOutcome vcOutcome, string implName, IToken implTok, string msgIfVerifies,
      TextWriter tw, uint timeLimit, List<Counterexample> errors)
    {
      ErrorInformation errorInfo = null;

      switch (vcOutcome) {
        case VcOutcome.Correct:
          if (msgIfVerifies != null) {
            tw.WriteLine(msgIfVerifies);
          }
          break;
        case VcOutcome.Errors:
        case VcOutcome.TimedOut:
          if (implName != null && implTok != null) {
            if (vcOutcome == VcOutcome.TimedOut ||
                (errors != null && errors.Any(e => e.IsAuxiliaryCexForDiagnosingTimeouts))) {
              string msg = string.Format("Verification of '{1}' timed out after {0} seconds", timeLimit, implName);
              errorInfo = ErrorInformation.Create(implTok, msg);
            }

            //  Report timed out assertions as auxiliary info.
            if (errors != null) {
              var cmpr = new CounterexampleComparer();
              var timedOutAssertions = errors.Where(e => e.IsAuxiliaryCexForDiagnosingTimeouts).Distinct(cmpr).ToList();
              timedOutAssertions.Sort(cmpr);
              if (0 < timedOutAssertions.Count) {
                errorInfo.Msg += $" with {timedOutAssertions.Count} check(s) that timed out individually";
              }

              foreach (Counterexample error in timedOutAssertions) {
                var callError = error as CallCounterexample;
                var returnError = error as ReturnCounterexample;
                var assertError = error as AssertCounterexample;
                IToken tok = null;
                string msg = null;
                if (callError != null) {
                  tok = callError.FailingCall.tok;
                  msg = callError.FailingCall.Description.FailureDescription;
                } else if (returnError != null) {
                  tok = returnError.FailingReturn.tok;
                  msg = returnError.FailingReturn.Description.FailureDescription;
                } else {
                  tok = assertError.FailingAssert.tok;
                  if (!(assertError.FailingAssert.ErrorMessage == null || options.ForceBplErrors)) {
                    msg = assertError.FailingAssert.ErrorMessage;
                  }

                  msg ??= assertError.FailingAssert.Description.FailureDescription;
                }

                errorInfo.AddAuxInfo(tok, msg, "Unverified check due to timeout");
              }
            }
          }
          break;
        case VcOutcome.OutOfResource:
          if (implName != null && implTok != null) {
            string msg = "Verification out of resource (" + implName + ")";
            errorInfo = ErrorInformation.Create(implTok, msg);
          }
          break;
        case VcOutcome.OutOfMemory:
          if (implName != null && implTok != null) {
            string msg = "Verification out of memory (" + implName + ")";
            errorInfo = ErrorInformation.Create(implTok, msg);
          }
          break;
        case VcOutcome.SolverException:
          if (implName != null && implTok != null) {
            string msg = "Verification encountered solver exception (" + implName + ")";
            errorInfo = ErrorInformation.Create(implTok, msg);
          }
          break;

        case VcOutcome.Inconclusive:
          if (implName != null && implTok != null) {
            string msg = "Verification inconclusive (" + implName + ")";
            errorInfo = ErrorInformation.Create(implTok, msg);
          }
          break;
      }

      return errorInfo;
    }


    private static string OutcomeIndication(VcOutcome vcOutcome, List<Counterexample> errors)
    {
      string traceOutput = "";
      switch (vcOutcome)
      {
        default:
          Contract.Assert(false); // unexpected outcome
          throw new Cce.UnreachableException();
        case VcOutcome.Correct:
          traceOutput = "verified";
          break;
        case VcOutcome.TimedOut:
          traceOutput = "timed out";
          break;
        case VcOutcome.OutOfResource:
          traceOutput = "out of resource";
          break;
        case VcOutcome.OutOfMemory:
          traceOutput = "out of memory";
          break;
        case VcOutcome.SolverException:
          traceOutput = "solver exception";
          break;
        case VcOutcome.Inconclusive:
          traceOutput = "inconclusive";
          break;
        case VcOutcome.Errors:
          Contract.Assert(errors != null);
          traceOutput = string.Format("error{0}", errors.Count == 1 ? "" : "s");
          break;
      }

      return traceOutput;
    }


    private static void UpdateStatistics(PipelineStatistics stats, VcOutcome vcOutcome, List<Counterexample> errors)
    {
      Contract.Requires(stats != null);

      switch (vcOutcome)
      {
        default:
          Contract.Assert(false); // unexpected outcome
          throw new Cce.UnreachableException();
        case VcOutcome.Correct:
          Interlocked.Increment(ref stats.VerifiedCount);
          break;
        case VcOutcome.TimedOut:
          Interlocked.Increment(ref stats.TimeoutCount);
          break;
        case VcOutcome.OutOfResource:
          Interlocked.Increment(ref stats.OutOfResourceCount);
          break;
        case VcOutcome.OutOfMemory:
          Interlocked.Increment(ref stats.OutOfMemoryCount);
          break;
        case VcOutcome.SolverException:
          Interlocked.Increment(ref stats.SolverExceptionCount);
          break;
        case VcOutcome.Inconclusive:
          Interlocked.Increment(ref stats.InconclusiveCount);
          break;
        case VcOutcome.Errors:
          int cnt = errors.Count(e => !e.IsAuxiliaryCexForDiagnosingTimeouts);
          Interlocked.Add(ref stats.ErrorCount, cnt);
          break;
      }
    }

    private static void UpdateCachedStatistics(PipelineStatistics stats, VcOutcome vcOutcome, List<Counterexample> errors) {
      Contract.Requires(stats != null);

      switch (vcOutcome)
      {
        default:
          Contract.Assert(false); // unexpected outcome
          throw new Cce.UnreachableException();
        case VcOutcome.Correct:
          Interlocked.Increment(ref stats.CachedVerifiedCount);
          break;
        case VcOutcome.TimedOut:
          Interlocked.Increment(ref stats.CachedTimeoutCount);
          break;
        case VcOutcome.OutOfResource:
          Interlocked.Increment(ref stats.CachedOutOfResourceCount);
          break;
        case VcOutcome.OutOfMemory:
          Interlocked.Increment(ref stats.CachedOutOfMemoryCount);
          break;
        case VcOutcome.SolverException:
          Interlocked.Increment(ref stats.CachedSolverExceptionCount);
          break;
        case VcOutcome.Inconclusive:
          Interlocked.Increment(ref stats.CachedInconclusiveCount);
          break;
        case VcOutcome.Errors:
          int cnt = errors.Count(e => !e.IsAuxiliaryCexForDiagnosingTimeouts);
          Interlocked.Add(ref stats.CachedErrorCount, cnt);
          break;
      }
    }

    public void ProcessErrors(OutputPrinter printer,
      List<Counterexample> errors,
      VcOutcome vcOutcome, TextWriter tw,
      ErrorReporterDelegate er, Implementation impl = null)
    {
      var implName = impl?.VerboseName;

      if (errors == null)
      {
        return;
      }

      // When an assertion fails on multiple paths, only show an error for one of them.
      errors = errors.DistinctBy(e => e.FailingAssert).ToList();
      errors.Sort(new CounterexampleComparer());
      foreach (Counterexample error in errors)
      {
        if (error.IsAuxiliaryCexForDiagnosingTimeouts)
        {
          continue;
        }

        var errorInfo = error.CreateErrorInformation(vcOutcome, Options.ForceBplErrors);
        errorInfo.ImplementationName = implName;

        if (Options.XmlSink != null)
        {
          WriteErrorInformationToXmlSink(Options.XmlSink, errorInfo, error.Trace);
        }

        if (Options.ErrorTrace > 0)
        {
          errorInfo.Out.WriteLine("Execution trace:");
          error.Print(4, errorInfo.Out, b => { errorInfo.AddAuxInfo(b.tok, b.Label, "Execution trace"); });
          if (Options.EnhancedErrorMessages == 1 && error.AugmentedTrace != null && error.AugmentedTrace.Count > 0)
          {
            errorInfo.Out.WriteLine("Augmented execution trace:");
            error.AugmentedTrace.ForEach(elem => errorInfo.Out.Write(elem));
          }
          if (Options.PrintErrorModel >= 1 && error.Model != null)
          {
            error.Model.Write(Options.ModelWriter ?? errorInfo.Out);
          }
        }

        if (Options.ModelViewFile != null) {
          error.PrintModel(errorInfo.ModelWriter, error);
        }

        printer.WriteErrorInformation(errorInfo, tw);

        if (er != null)
        {
          lock (er)
          {
            er(errorInfo);
          }
        }
      }
    }

    private static void WriteErrorInformationToXmlSink(XmlSink sink, ErrorInformation errorInfo, List<Block> trace)
    {
      var msg = "assertion violation";
      switch (errorInfo.Kind)
      {
        case ErrorKind.Precondition:
          msg = "precondition violation";
          break;

        case ErrorKind.Postcondition:
          msg = "postcondition violation";
          break;

        case ErrorKind.InvariantEntry:
          msg = "loop invariant entry violation";
          break;

        case ErrorKind.InvariantMaintainance:
          msg = "loop invariant maintenance violation";
          break;
      }

      var relatedError = errorInfo.Aux.FirstOrDefault();
      sink.WriteError(msg, errorInfo.Tok, relatedError.Tok, trace);
    }

    public void Dispose()
    {
      CheckerPool.Dispose();
      if (disposeScheduler) {
        (largeThreadScheduler as IDisposable)?.Dispose();
      }
    }
  }
}