using System.Collections.Generic;
using System.Linq;
using Microsoft.Boogie;

public class YieldRegionExtractor
{
  public class CivlEdge
  {
    public int Id;
    public Absy Source;
    public Absy Target;
    public string Label;      // P, Y, R, L, B, N, C
    public CallCmd CallCmd;   // null if this is not a call edge
    public Action Action;     // null unless this edge corresponds to an action call
  }

  public class CivlGraph
  {
    public HashSet<Absy> Nodes = new();
    public List<CivlEdge> Edges = new();
    public Dictionary<Absy, List<CivlEdge>> OutEdges = new();
    public Dictionary<Absy, List<CivlEdge>> InEdges = new();
    public Absy InitialState;
    public HashSet<Absy> FinalStates = new();
  }

  public class YieldRegion
  {
    public CivlEdge EntryYieldEdge;
    public CivlEdge ExitYieldEdge;
    public Absy EntryNode;   // usually EntryYieldEdge.Target
    public Absy ExitNode;    // usually ExitYieldEdge.Source

    public HashSet<Absy> Nodes = new();
    public List<CivlEdge> InternalEdges = new();
    public Dictionary<Absy, List<CivlEdge>> OutEdges = new();
    public Dictionary<Absy, List<CivlEdge>> InEdges = new();
  }
  private static void AddEdge(CivlGraph graph, CivlEdge edge)
  {
    graph.Nodes.Add(edge.Source);
    graph.Nodes.Add(edge.Target);
    graph.Edges.Add(edge);

    if (!graph.OutEdges.ContainsKey(edge.Source))
    {
      graph.OutEdges[edge.Source] = new List<CivlEdge>();
    }
    graph.OutEdges[edge.Source].Add(edge);

    if (!graph.InEdges.ContainsKey(edge.Target))
    {
      graph.InEdges[edge.Target] = new List<CivlEdge>();
    }
    graph.InEdges[edge.Target].Add(edge);
  }
  private static IEnumerable<CivlEdge> Outgoing(CivlGraph graph, Absy node)
  {
    return graph.OutEdges.TryGetValue(node, out var edges) ? edges : Enumerable.Empty<CivlEdge>();
  }
  private static bool IsYield(CivlEdge edge) => edge.Label == "Y";
  private const string Y = "Y";
  private const string B = "B";
  private const string L = "L";
  private const string R = "R";
  private const string N = "N";
  private const string P = "P";
  private const string C = "C";

  private static string MoverTypeToLabel(MoverType moverType)
  {
    switch (moverType)
    {
      case MoverType.Atomic:
        return N;
      case MoverType.Both:
        return B;
      case MoverType.Left:
        return L;
      case MoverType.Right:
        return R;
      case MoverType.Check:
        return C;
      default:
        return P;
    }
  }

  private static Action TryGetAction(CivlTypeChecker civlTypeChecker, Procedure proc)
  {
    return civlTypeChecker.MoverActions.FirstOrDefault(a => a.ActionDecl == proc);
  }

  private static (string label, Action action) CallCmdInfo(
    CivlTypeChecker civlTypeChecker,
    CallCmd callCmd,
    int currLayerNum)
  {
    if (callCmd.Proc.IsPure)
    {
      return (P, null);
    }

    if (callCmd.Proc is YieldInvariantDecl yieldInvariant)
    {
      return (yieldInvariant.Layer == currLayerNum ? Y : P, null);
    }

    var callee = (YieldProcedureDecl)callCmd.Proc;

    if (callCmd.IsAsync)
    {
      if (callee.HasMoverType && callee.Layer == currLayerNum)
      {
        return (MoverTypeToLabel(callee.MoverType), TryGetAction(civlTypeChecker, callee));
      }

      if (!callee.HasMoverType && callee.Layer < currLayerNum && callCmd.HasAttribute(CivlAttributes.SYNC))
      {
        var refined = callee.RefinedActionAtLayer(currLayerNum);
        return (MoverTypeToLabel(refined.MoverType), TryGetAction(civlTypeChecker, refined));
      }

      return (L, TryGetAction(civlTypeChecker, callee));
    }
    else
    {
      if (callee.HasMoverType && callee.Layer == currLayerNum)
      {
        return (MoverTypeToLabel(callee.MoverType), TryGetAction(civlTypeChecker, callee));
      }

      if (!callee.HasMoverType && callee.Layer < currLayerNum)
      {
        var refined = callee.RefinedActionAtLayer(currLayerNum);
        return (MoverTypeToLabel(refined.MoverType), TryGetAction(civlTypeChecker, refined));
      }

      return (Y, TryGetAction(civlTypeChecker, callee));
    }
  }

  private static int AddParCallCmdEdges(
    CivlGraph graph,
    CivlTypeChecker civlTypeChecker,
    ParCallCmd parCallCmd,
    Absy next,
    int currLayerNum,
    int nextEdgeId)
  {
    if (parCallCmd.CallCmds.Count == 0)
    {
      return nextEdgeId;
    }

    AddEdge(graph, new CivlEdge
    {
      Id = nextEdgeId++,
      Source = parCallCmd,
      Target = parCallCmd.CallCmds[0],
      Label = P,
      CallCmd = null,
      Action = null
    });

    for (int i = 0; i < parCallCmd.CallCmds.Count; i++)
    {
      var callCmd = parCallCmd.CallCmds[i];
      var target = i + 1 < parCallCmd.CallCmds.Count
        ? (Absy)parCallCmd.CallCmds[i + 1]
        : next;

      var (label, action) = CallCmdInfo(civlTypeChecker, callCmd, currLayerNum);

      AddEdge(graph, new CivlEdge
      {
        Id = nextEdgeId++,
        Source = callCmd,
        Target = target,
        Label = label,
        CallCmd = callCmd,
        Action = action
      });
    }

    return nextEdgeId;
  }
  private static IEnumerable<CivlEdge> YieldEdges(CivlGraph graph)
  {
    return graph.Edges.Where(IsYield);
  }
  public static string PrintGraph(CivlGraph graph)
  {
    var sb = new System.Text.StringBuilder();
    sb.AppendLine("Graph:");
    foreach (var edge in graph.Edges.OrderBy(e => e.Id))
    {
      var actionName = edge.Action?.ActionDecl?.Name ?? "-";
      sb.AppendLine($"{edge.Id}: {edge.Source} --{edge.Label}--> {edge.Target}  action={actionName}");
    }
    sb.AppendLine($"Initial: {graph.InitialState}");
    sb.AppendLine($"Finals: {string.Join(", ", graph.FinalStates)}");
    return sb.ToString();
  }
  public static CivlGraph BuildGraph(
    CivlTypeChecker civlTypeChecker,
    YieldProcedureDecl yieldingProc,
    Implementation impl,
    int currLayerNum)
  {
    var graph = new CivlGraph();
    graph.InitialState = impl.Blocks[0];

    int nextEdgeId = 0;

    foreach (Block block in impl.Blocks)
    {
      Absy blockEntry = block.Cmds.Count == 0 ? (Absy) block.TransferCmd : block.Cmds[0];
      var entryLabel = yieldingProc.IsYieldingLoopHeader(block, currLayerNum) ? "Y" : "P";
      AddEdge(graph, new CivlEdge
      {
        Id = nextEdgeId++,
        Source = block,
        Target = blockEntry,
        Label = entryLabel,
        CallCmd = null,
        Action = null
      });

      if (block.TransferCmd is GotoCmd gotoCmd)
      {
        foreach (Block successor in gotoCmd.LabelTargets)
        {
          AddEdge(graph, new CivlEdge
          {
            Id = nextEdgeId++,
            Source = block.TransferCmd,
            Target = successor,
            Label = "P",
            CallCmd = null,
            Action = null
          });
        }
      }
      else if (block.TransferCmd is ReturnCmd)
      {
        graph.FinalStates.Add(block.TransferCmd);
      }

      for (int i = 0; i < block.Cmds.Count; i++)
      {
        Cmd cmd = block.Cmds[i];
        Absy next = (i + 1 == block.Cmds.Count) ? (Absy) block.TransferCmd : block.Cmds[i + 1];

        if (cmd is CallCmd callCmd)
        {
          var (label, action) = CallCmdInfo(civlTypeChecker, callCmd, currLayerNum);
          AddEdge(graph, new CivlEdge
          {
            Id = nextEdgeId++,
            Source = cmd,
            Target = next,
            Label = label,
            CallCmd = callCmd,
            Action = action
          });
        }
        else if (cmd is ParCallCmd parCallCmd)
        {
          nextEdgeId = AddParCallCmdEdges(graph, civlTypeChecker, parCallCmd, next, currLayerNum, nextEdgeId);
        }
        else
        {
          AddEdge(graph, new CivlEdge
          {
            Id = nextEdgeId++,
            Source = cmd,
            Target = next,
            Label = "P",
            CallCmd = null,
            Action = null
          });
        }
      }
    }

    return graph;
  }
  private static HashSet<Absy> ForwardReachableInternal(Absy start, IEnumerable<CivlEdge> edges)
  {
    var outMap = new Dictionary<Absy, List<CivlEdge>>();
    foreach (var edge in edges)
    {
      if (!outMap.TryGetValue(edge.Source, out var list))
      {
        list = new List<CivlEdge>();
        outMap[edge.Source] = list;
      }
      list.Add(edge);
    }

    var visited = new HashSet<Absy> { start };
    var worklist = new Queue<Absy>();
    worklist.Enqueue(start);

    while (worklist.Count > 0)
    {
      var node = worklist.Dequeue();
      if (!outMap.TryGetValue(node, out var nextEdges))
      {
        continue;
      }

      foreach (var edge in nextEdges)
      {
        if (visited.Add(edge.Target))
        {
          worklist.Enqueue(edge.Target);
        }
      }
    }

    return visited;
  }

  private static HashSet<Absy> BackwardReachableInternal(Absy target, IEnumerable<CivlEdge> edges)
  {
    var inMap = new Dictionary<Absy, List<CivlEdge>>();
    foreach (var edge in edges)
    {
      if (!inMap.TryGetValue(edge.Target, out var list))
      {
        list = new List<CivlEdge>();
        inMap[edge.Target] = list;
      }
      list.Add(edge);
    }

    var visited = new HashSet<Absy> { target };
    var worklist = new Queue<Absy>();
    worklist.Enqueue(target);

    while (worklist.Count > 0)
    {
      var node = worklist.Dequeue();
      if (!inMap.TryGetValue(node, out var prevEdges))
      {
        continue;
      }

      foreach (var edge in prevEdges)
      {
        if (visited.Add(edge.Source))
        {
          worklist.Enqueue(edge.Source);
        }
      }
    }

    return visited;
  }
  private static YieldRegion SliceRegion(
    CivlGraph graph,
    CivlEdge entryYield,
    CivlEdge exitYield,
    HashSet<Absy> candidateNodes,
    HashSet<CivlEdge> candidateEdges)
  {
    var entryNode = entryYield.Target;
    var exitNode = exitYield.Source;

    var forward = ForwardReachableInternal(entryNode, candidateEdges);
    if (!forward.Contains(exitNode))
    {
      return null;
    }

    var backward = BackwardReachableInternal(exitNode, candidateEdges);

    var regionNodes = new HashSet<Absy>(forward.Intersect(backward));
    var regionEdges = candidateEdges
      .Where(e => regionNodes.Contains(e.Source) && regionNodes.Contains(e.Target))
      .ToList();

    var region = new YieldRegion
    {
      EntryYieldEdge = entryYield,
      ExitYieldEdge = exitYield,
      EntryNode = entryNode,
      ExitNode = exitNode,
      Nodes = regionNodes,
      InternalEdges = regionEdges
    };

    foreach (var edge in regionEdges)
    {
      if (!region.OutEdges.TryGetValue(edge.Source, out var outList))
      {
        outList = new List<CivlEdge>();
        region.OutEdges[edge.Source] = outList;
      }
      outList.Add(edge);

      if (!region.InEdges.TryGetValue(edge.Target, out var inList))
      {
        inList = new List<CivlEdge>();
        region.InEdges[edge.Target] = inList;
      }
      inList.Add(edge);
    }

    return region;
  }

  public static List<YieldRegion> ExtractRegions(CivlGraph graph)
  {
    var regions = new List<YieldRegion>();

    foreach (var entryYield in YieldEdges(graph))
    {
      var exits = new HashSet<CivlEdge>();
      var reachableInternalNodes = new HashSet<Absy>();
      var reachableInternalEdges = new HashSet<CivlEdge>();
      var worklist = new Queue<Absy>();

      var entryNode = entryYield.Target;
      reachableInternalNodes.Add(entryNode);
      worklist.Enqueue(entryNode);

      while (worklist.Count > 0)
      {
        var node = worklist.Dequeue();
        foreach (var edge in Outgoing(graph, node))
        {
          if (IsYield(edge))
          {
            exits.Add(edge);
            continue;
          }

          if (reachableInternalEdges.Add(edge))
          {
            reachableInternalNodes.Add(edge.Source);
            if (reachableInternalNodes.Add(edge.Target))
            {
              worklist.Enqueue(edge.Target);
            }
          }
        }
      }

      foreach (var exitYield in exits)
      {
        var region = SliceRegion(graph, entryYield, exitYield, reachableInternalNodes, reachableInternalEdges);
        if (region != null)
        {
          regions.Add(region);
        }
      }
    }

    return regions;
  }
  public static void ValidateRegion(YieldRegion region)
  {
    if (region.EntryYieldEdge == null || region.EntryYieldEdge.Label != Y)
    {
      throw new System.Exception("Region entry edge is not a yield edge");
    }

    if (region.ExitYieldEdge == null || region.ExitYieldEdge.Label != Y)
    {
      throw new System.Exception("Region exit edge is not a yield edge");
    }

    foreach (var edge in region.InternalEdges)
    {
      if (edge.Label == Y)
      {
        throw new System.Exception($"Region contains internal yield edge {edge.Id}");
      }
    }

    if (!region.Nodes.Contains(region.EntryNode))
    {
      throw new System.Exception("Region does not contain entry node");
    }

    if (!region.Nodes.Contains(region.ExitNode))
    {
      throw new System.Exception("Region does not contain exit node");
    }
  }

  public static void ValidateRegions(IEnumerable<YieldRegion> regions)
  {
    foreach (var region in regions)
    {
      ValidateRegion(region);
    }
  }
  
  public static IEnumerable<CivlEdge> CheckEdges(YieldRegion region)
  {
    return region.InternalEdges.Where(e => e.Label == C && e.Action != null);
  }
  public static string PrintRegion(YieldRegion region)
  {
    var sb = new System.Text.StringBuilder();
    sb.AppendLine(
      $"EntryYield={region.EntryYieldEdge.Id}, ExitYield={region.ExitYieldEdge.Id}, " +
      $"EntryNode={region.EntryNode}, ExitNode={region.ExitNode}");

    foreach (var edge in region.InternalEdges.OrderBy(e => e.Id))
    {
      var actionName = edge.Action?.ActionDecl?.Name ?? "-";
      sb.AppendLine(
        $"  {edge.Id}: {edge.Source} --{edge.Label}--> {edge.Target} action={actionName}");
    }

    var checkActions = CheckEdges(region).Select(e => e.Action.ActionDecl.Name).Distinct().ToList();
    sb.AppendLine($"  CheckActions: {(checkActions.Count == 0 ? "-" : string.Join(", ", checkActions))}");

    return sb.ToString();
  }

  public static IEnumerable<CivlEdge> Outgoing(YieldRegion region, Absy node)
  {
    return region.OutEdges.TryGetValue(node, out var edges) ? edges : Enumerable.Empty<CivlEdge>();
  }

  public static IEnumerable<CivlEdge> Incoming(YieldRegion region, Absy node)
  {
    return region.InEdges.TryGetValue(node, out var edges) ? edges : Enumerable.Empty<CivlEdge>();
  }

  public static HashSet<CivlEdge> BackwardReachableEdgesFromEdge(YieldRegion region, CivlEdge startEdge)
  {
    var result = new HashSet<CivlEdge> { startEdge };
    var worklist = new Queue<Absy>();
    var visitedNodes = new HashSet<Absy> { startEdge.Source };
    worklist.Enqueue(startEdge.Source);

    while (worklist.Count > 0)
    {
      var node = worklist.Dequeue();
      foreach (var edge in Incoming(region, node))
      {
        if (result.Add(edge) && visitedNodes.Add(edge.Source))
        {
          worklist.Enqueue(edge.Source);
        }
      }
    }

    return result;
  }

  public static HashSet<CivlEdge> ForwardReachableEdgesFromEdge(YieldRegion region, CivlEdge startEdge)
  {
    var result = new HashSet<CivlEdge> { startEdge };
    var worklist = new Queue<Absy>();
    var visitedNodes = new HashSet<Absy> { startEdge.Target };
    worklist.Enqueue(startEdge.Target);

    while (worklist.Count > 0)
    {
      var node = worklist.Dequeue();
      foreach (var edge in Outgoing(region, node))
      {
        if (result.Add(edge) && visitedNodes.Add(edge.Target))
        {
          worklist.Enqueue(edge.Target);
        }
      }
    }

    return result;
  }
  public class RegionObligations
  {
    public YieldRegion Region;

    public HashSet<CivlEdge> MustCheckRightEdges = new();
    public HashSet<CivlEdge> MustCheckLeftEdges = new();

    public HashSet<Action> MustCheckRightActions = new();
    public HashSet<Action> MustCheckLeftActions = new();
  }
  public static RegionObligations AnalyzeRegion(
    YieldRegion region)
  {
    var obligations = new RegionObligations();
    obligations.Region = region;

    foreach (var edge in region.InternalEdges)
    {
      if (MoverCheck.IsKnownNonLeft(edge))
      {
        foreach (var predEdge in BackwardReachableEdgesFromEdge(region, edge))
        {
          if (predEdge == edge)
          {
            continue;
          }

          if (predEdge.Label == "C" && predEdge.Action != null)
          {
            obligations.MustCheckRightEdges.Add(predEdge);
            obligations.MustCheckRightActions.Add(predEdge.Action);
          }
        }
      }

      if (MoverCheck.IsKnownNonRight(edge))
      {
        foreach (var succEdge in ForwardReachableEdgesFromEdge(region, edge))
        {
          if (succEdge == edge)
          {
            continue;
          }

          if (succEdge.Label == "C" && succEdge.Action != null)
          {
            obligations.MustCheckLeftEdges.Add(succEdge);
            obligations.MustCheckLeftActions.Add(succEdge.Action);
          }
        }
      }
    }

    return obligations;
  }

  public static string PrintObligations(RegionObligations obligations)
  {
    var sb = new System.Text.StringBuilder();

    var rightEdges = obligations.MustCheckRightEdges
      .OrderBy(e => e.Id)
      .Select(e => $"{e.Id}:{e.Action?.ActionDecl?.Name ?? "-"}");
    var leftEdges = obligations.MustCheckLeftEdges
      .OrderBy(e => e.Id)
      .Select(e => $"{e.Id}:{e.Action?.ActionDecl?.Name ?? "-"}");

    sb.AppendLine($"  MustCheckRightEdges: {(rightEdges.Any() ? string.Join(", ", rightEdges) : "-")}");
    sb.AppendLine($"  MustCheckLeftEdges: {(leftEdges.Any() ? string.Join(", ", leftEdges) : "-")}");

    var rightActions = obligations.MustCheckRightActions
      .Select(a => a.ActionDecl.Name)
      .Distinct()
      .OrderBy(x => x);
    var leftActions = obligations.MustCheckLeftActions
      .Select(a => a.ActionDecl.Name)
      .Distinct()
      .OrderBy(x => x);

    sb.AppendLine($"  MustCheckRightActions: {(rightActions.Any() ? string.Join(", ", rightActions) : "-")}");
    sb.AppendLine($"  MustCheckLeftActions: {(leftActions.Any() ? string.Join(", ", leftActions) : "-")}");

    return sb.ToString();
  }

  public static List<CivlEdge> OrderedCheckEdges(YieldRegion region)
  {
    return region.InternalEdges
      .Where(e => e.Label == C && e.Action != null)
      .OrderBy(e => e.Id)
      .ToList();
  }
}