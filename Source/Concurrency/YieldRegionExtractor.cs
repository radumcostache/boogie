using System;
using System.Collections.Generic;
using System.Linq;
using System.Runtime.CompilerServices;
using Microsoft.Boogie;

using BoogieAction = Microsoft.Boogie.Action;

public class YieldRegionExtractor
{
  public sealed class CivlNode : IEquatable<CivlNode>
  {
    public Absy Original;
    public int LoopId;   // -1 for non-cloned/original nodes
    public int CopyId;   // 0 = original, 1 = cloned unroll copy

    public bool IsClone => LoopId >= 0 && CopyId > 0;

    public override string ToString()
    {
      if (!IsClone)
      {
        return Original.ToString();
      }
      return $"{Original}_L{LoopId}_C{CopyId}";
    }

    public bool Equals(CivlNode other)
    {
      if (other == null)
      {
        return false;
      }

      return ReferenceEquals(Original, other.Original) &&
             LoopId == other.LoopId &&
             CopyId == other.CopyId;
    }

    public override bool Equals(object obj)
    {
      return Equals(obj as CivlNode);
    }

    public override int GetHashCode()
    {
      unchecked
      {
        int h = RuntimeHelpers.GetHashCode(Original);
        h = (h * 397) ^ LoopId;
        h = (h * 397) ^ CopyId;
        return h;
      }
    }
  }

  private sealed class NodeFactory
  {
    private readonly Dictionary<(Absy, int, int), CivlNode> cache = new();

    public CivlNode Get(Absy absy, int loopId = -1, int copyId = 0)
    {
      var key = (absy, loopId, copyId);
      if (!cache.TryGetValue(key, out var node))
      {
        node = new CivlNode
        {
          Original = absy,
          LoopId = loopId,
          CopyId = copyId
        };
        cache[key] = node;
      }
      return node;
    }
  }

  public class CivlEdge
  {
    public int Id;
    public CivlNode Source;
    public CivlNode Target;
    public string Label;      // P, Y, R, L, B, N, C
    public CallCmd CallCmd;   // null if this is not a call edge
    public BoogieAction Action; // null unless this edge corresponds to an action call
  }

  public class CivlGraph
  {
    public HashSet<CivlNode> Nodes = new();
    public List<CivlEdge> Edges = new();
    public Dictionary<CivlNode, List<CivlEdge>> OutEdges = new();
    public Dictionary<CivlNode, List<CivlEdge>> InEdges = new();
    public CivlNode InitialState;
    public HashSet<CivlNode> FinalStates = new();
  }

  public class YieldRegion
  {
    public CivlEdge EntryYieldEdge;
    public CivlEdge ExitYieldEdge;
    public CivlNode EntryNode;
    public CivlNode ExitNode;

    public HashSet<CivlNode> Nodes = new();
    public List<CivlEdge> InternalEdges = new();
    public Dictionary<CivlNode, List<CivlEdge>> OutEdges = new();
    public Dictionary<CivlNode, List<CivlEdge>> InEdges = new();
    public List<CivlNode> TopologicalNodes = new();
  }

  private sealed class LoopInfo
  {
    public int LoopId;
    public Block Header;
    public HashSet<Block> Blocks = new();
    public HashSet<(Block Source, Block Target)> BackEdges = new();

    public override string ToString()
    {
      return $"Loop {LoopId}, Header={Header}";
    }
  }

  private static void AddEdge(CivlGraph graph, CivlEdge edge)
  {
    graph.Nodes.Add(edge.Source);
    graph.Nodes.Add(edge.Target);
    graph.Edges.Add(edge);

    if (!graph.OutEdges.TryGetValue(edge.Source, out var outList))
    {
      outList = new List<CivlEdge>();
      graph.OutEdges[edge.Source] = outList;
    }
    outList.Add(edge);

    if (!graph.InEdges.TryGetValue(edge.Target, out var inList))
    {
      inList = new List<CivlEdge>();
      graph.InEdges[edge.Target] = inList;
    }
    inList.Add(edge);
  }

  private static IEnumerable<CivlEdge> Outgoing(CivlGraph graph, CivlNode node)
  {
    return graph.OutEdges.TryGetValue(node, out var edges) ? edges : Enumerable.Empty<CivlEdge>();
  }

  public static IEnumerable<CivlEdge> Outgoing(YieldRegion region, CivlNode node)
  {
    return region.OutEdges.TryGetValue(node, out var edges) ? edges : Enumerable.Empty<CivlEdge>();
  }

  public static IEnumerable<CivlEdge> Incoming(YieldRegion region, CivlNode node)
  {
    return region.InEdges.TryGetValue(node, out var edges) ? edges : Enumerable.Empty<CivlEdge>();
  }

  private static bool IsYield(CivlEdge edge) => edge.Label == Y;

  private const string Y = "Y";
  private const string B = "B";
  private const string L = "L";
  private const string R = "R";
  private const string N = "N";
  private const string P = "P";
  private const string C = "C";
  public static bool IsCurrentlyCheckEdge(CivlEdge edge)
  {
    if (edge.Action == null)
    {
      return edge.Label == C;
    }

    return edge.Action.ActionDecl.MoverType == MoverType.Check;
  }

  public static bool IsCurrentlyLeftEdge(CivlEdge edge)
  {
    if (edge.Action == null)
    {
      return edge.Label == L;
    }

    return MoverCheck.LeftPassed(edge.Action);
  }

  public static bool IsCurrentlyRightEdge(CivlEdge edge)
  {
    if (edge.Action == null)
    {
      return edge.Label == R;
    }

    return MoverCheck.RightPassed(edge.Action);
  }

  public static bool IsCurrentlyBothEdge(CivlEdge edge)
  {
    if (edge.Action == null)
    {
      return edge.Label == B;
    }

    return MoverCheck.LeftPassed(edge.Action) && MoverCheck.RightPassed(edge.Action);
  }

  public static bool IsCurrentlyAtomicEdge(CivlEdge edge)
  {
    if (edge.Action == null)
    {
      return edge.Label == N;
    }

    return MoverCheck.IsKnownNonLeft(edge) && MoverCheck.IsKnownNonRight(edge);
  }

  public static string CurrentLabel(CivlEdge edge)
  {
    if (edge.Action == null)
    {
      return edge.Label;
    }

    if (IsCurrentlyBothEdge(edge))
    {
      return B;
    }

    if (IsCurrentlyLeftEdge(edge))
    {
      return L;
    }

    if (IsCurrentlyRightEdge(edge))
    {
      return R;
    }

    if (IsCurrentlyAtomicEdge(edge))
    {
      return N;
    }

    return C;
  }

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

  private static BoogieAction TryGetAction(CivlTypeChecker civlTypeChecker, Procedure proc)
  {
    return civlTypeChecker.MoverActions.FirstOrDefault(a => a.ActionDecl == proc);
  }

  private static (string label, BoogieAction action) CallCmdInfo(
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

  private static Dictionary<Block, List<Block>> ComputeSuccessors(Implementation impl)
  {
    var result = impl.Blocks.ToDictionary(b => b, _ => new List<Block>());
    foreach (var block in impl.Blocks)
    {
      if (block.TransferCmd is GotoCmd gotoCmd)
      {
        foreach (Block succ in gotoCmd.LabelTargets)
        {
          result[block].Add(succ);
        }
      }
    }
    return result;
  }

  private static Dictionary<Block, List<Block>> ComputePredecessors(Implementation impl)
  {
    var succ = ComputeSuccessors(impl);
    var pred = impl.Blocks.ToDictionary(b => b, _ => new List<Block>());
    foreach (var kv in succ)
    {
      foreach (var s in kv.Value)
      {
        pred[s].Add(kv.Key);
      }
    }
    return pred;
  }

  private static Dictionary<Block, HashSet<Block>> ComputeDominators(Implementation impl)
  {
    var entry = impl.Blocks[0];
    var pred = ComputePredecessors(impl);
    var all = new HashSet<Block>(impl.Blocks);

    var dom = new Dictionary<Block, HashSet<Block>>();
    foreach (var b in impl.Blocks)
    {
      dom[b] = b == entry ? new HashSet<Block> { b } : new HashSet<Block>(all);
    }

    bool changed = true;
    while (changed)
    {
      changed = false;
      foreach (var b in impl.Blocks)
      {
        if (b == entry)
        {
          continue;
        }

        HashSet<Block> newDom;
        if (pred[b].Count == 0)
        {
          newDom = new HashSet<Block> { b };
        }
        else
        {
          newDom = new HashSet<Block>(dom[pred[b][0]]);
          foreach (var p in pred[b].Skip(1))
          {
            newDom.IntersectWith(dom[p]);
          }
          newDom.Add(b);
        }

        if (!newDom.SetEquals(dom[b]))
        {
          dom[b] = newDom;
          changed = true;
        }
      }
    }

    return dom;
  }

  private static List<LoopInfo> DiscoverNonYieldingLoops(
    YieldProcedureDecl yieldingProc,
    Implementation impl,
    int currLayerNum)
  {
    var succ = ComputeSuccessors(impl);
    var pred = ComputePredecessors(impl);
    var dom = ComputeDominators(impl);

    var loopsByHeader = new Dictionary<Block, LoopInfo>();
    int nextLoopId = 0;

    foreach (var source in impl.Blocks)
    {
      foreach (var target in succ[source])
      {
        // Natural-loop backedge: target dominates source
        if (!dom[source].Contains(target))
        {
          continue;
        }

        // Only unroll non-yielding loop headers
        if (yieldingProc.IsYieldingLoopHeader(target, currLayerNum))
        {
          continue;
        }

        if (!loopsByHeader.TryGetValue(target, out var loop))
        {
          loop = new LoopInfo
          {
            LoopId = nextLoopId++,
            Header = target
          };
          loop.Blocks.Add(target);
          loopsByHeader[target] = loop;
        }

        loop.BackEdges.Add((source, target));

        var stack = new Stack<Block>();
        stack.Push(source);
        while (stack.Count > 0)
        {
          var b = stack.Pop();
          if (!loop.Blocks.Add(b))
          {
            continue;
          }

          foreach (var p in pred[b])
          {
            if (!loop.Blocks.Contains(p))
            {
              stack.Push(p);
            }
          }
        }
      }
    }

    return loopsByHeader.Values.ToList();
  }

  private static Dictionary<Block, LoopInfo> BuildLoopMembership(List<LoopInfo> loops)
  {
    var membership = new Dictionary<Block, LoopInfo>();
    foreach (var loop in loops.OrderBy(l => l.Blocks.Count))
    {
      foreach (var block in loop.Blocks)
      {
        // Prefer innermost/smaller loop if overlapping loops exist.
        if (!membership.ContainsKey(block))
        {
          membership[block] = loop;
        }
      }
    }
    return membership;
  }

  private static bool IsBackEdgeOfLoop(LoopInfo loop, Block source, Block target)
  {
    return loop != null && loop.BackEdges.Contains((source, target));
  }

  private static IEnumerable<int> CopiesForBlock(Block block, Dictionary<Block, LoopInfo> membership)
  {
    yield return 0;
    if (membership.ContainsKey(block))
    {
      yield return 1;
    }
  }

  private static CivlNode MapNode(
    NodeFactory factory,
    Absy absy,
    LoopInfo loop,
    int copyId)
  {
    if (loop == null || copyId == 0)
    {
      return factory.Get(absy);
    }
    return factory.Get(absy, loop.LoopId, copyId);
  }

  private static int AddParCallCmdEdges(
    CivlGraph graph,
    CivlTypeChecker civlTypeChecker,
    ParCallCmd parCallCmd,
    CivlNode parCallNode,
    CivlNode next,
    int currLayerNum,
    int nextEdgeId,
    NodeFactory factory,
    LoopInfo loop,
    int copyId)
  {
    if (parCallCmd.CallCmds.Count == 0)
    {
      return nextEdgeId;
    }

    AddEdge(graph, new CivlEdge
    {
      Id = nextEdgeId++,
      Source = parCallNode,
      Target = MapNode(factory, parCallCmd.CallCmds[0], loop, copyId),
      Label = P,
      CallCmd = null,
      Action = null
    });

    for (int i = 0; i < parCallCmd.CallCmds.Count; i++)
    {
      var callCmd = parCallCmd.CallCmds[i];
      var target = i + 1 < parCallCmd.CallCmds.Count
        ? MapNode(factory, parCallCmd.CallCmds[i + 1], loop, copyId)
        : next;

      var (label, action) = CallCmdInfo(civlTypeChecker, callCmd, currLayerNum);

      AddEdge(graph, new CivlEdge
      {
        Id = nextEdgeId++,
        Source = MapNode(factory, callCmd, loop, copyId),
        Target = target,
        Label = label,
        CallCmd = callCmd,
        Action = action
      });
    }

    return nextEdgeId;
  }

  private static CivlNode SuccessorBlockNodeForEdge(
    NodeFactory factory,
    Dictionary<Block, LoopInfo> membership,
    Block sourceBlock,
    int sourceCopyId,
    Block targetBlock)
  {
    membership.TryGetValue(sourceBlock, out var sourceLoop);
    membership.TryGetValue(targetBlock, out var targetLoop);

    // Original copy of a loop: redirect loop backedge into the clone
    if (sourceLoop != null && sourceCopyId == 0 &&
        ReferenceEquals(sourceLoop, targetLoop) &&
        IsBackEdgeOfLoop(sourceLoop, sourceBlock, targetBlock))
    {
      return factory.Get(targetBlock, sourceLoop.LoopId, 1);
    }

    // Cloned copy of a loop: remain in the clone for intra-loop edges, except drop the backedge
    if (sourceLoop != null && sourceCopyId == 1 &&
        ReferenceEquals(sourceLoop, targetLoop))
    {
      return factory.Get(targetBlock, sourceLoop.LoopId, 1);
    }

    // Otherwise return the original target
    return factory.Get(targetBlock);
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
      sb.AppendLine($"{edge.Id}: {edge.Source} --{CurrentLabel(edge)}--> {edge.Target}  action={actionName}");
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
    var factory = new NodeFactory();

    var loops = DiscoverNonYieldingLoops(yieldingProc, impl, currLayerNum);
    var membership = BuildLoopMembership(loops);

    graph.InitialState = factory.Get(impl.Blocks[0]);

    int nextEdgeId = 0;

    foreach (Block block in impl.Blocks)
    {
      membership.TryGetValue(block, out var loop);

      foreach (int copyId in CopiesForBlock(block, membership))
      {
        var blockNode = MapNode(factory, block, loop, copyId);

        Absy blockEntryAbsy = block.Cmds.Count == 0 ? (Absy)block.TransferCmd : block.Cmds[0];
        var blockEntryNode = MapNode(factory, blockEntryAbsy, loop, copyId);

        var entryLabel = yieldingProc.IsYieldingLoopHeader(block, currLayerNum) ? Y : P;
        AddEdge(graph, new CivlEdge
        {
          Id = nextEdgeId++,
          Source = blockNode,
          Target = blockEntryNode,
          Label = entryLabel,
          CallCmd = null,
          Action = null
        });

        for (int i = 0; i < block.Cmds.Count; i++)
        {
          var cmd = block.Cmds[i];
          var cmdNode = MapNode(factory, cmd, loop, copyId);
          CivlNode nextNode;

          if (i + 1 == block.Cmds.Count)
          {
            nextNode = MapNode(factory, block.TransferCmd, loop, copyId);
          }
          else
          {
            nextNode = MapNode(factory, block.Cmds[i + 1], loop, copyId);
          }

          if (cmd is CallCmd callCmd)
          {
            var (label, action) = CallCmdInfo(civlTypeChecker, callCmd, currLayerNum);
            AddEdge(graph, new CivlEdge
            {
              Id = nextEdgeId++,
              Source = cmdNode,
              Target = nextNode,
              Label = label,
              CallCmd = callCmd,
              Action = action
            });
          }
          else if (cmd is ParCallCmd parCallCmd)
          {
            nextEdgeId = AddParCallCmdEdges(
              graph,
              civlTypeChecker,
              parCallCmd,
              cmdNode,
              nextNode,
              currLayerNum,
              nextEdgeId,
              factory,
              loop,
              copyId);
          }
          else
          {
            AddEdge(graph, new CivlEdge
            {
              Id = nextEdgeId++,
              Source = cmdNode,
              Target = nextNode,
              Label = P,
              CallCmd = null,
              Action = null
            });
          }
        }

        if (block.TransferCmd is GotoCmd gotoCmd)
        {
          var transferNode = MapNode(factory, block.TransferCmd, loop, copyId);
          foreach (Block successor in gotoCmd.LabelTargets)
          {
            // Drop cloned backedges to make the clone acyclic
            if (loop != null && copyId == 1 && IsBackEdgeOfLoop(loop, block, successor))
            {
              continue;
            }

            var targetNode = SuccessorBlockNodeForEdge(factory, membership, block, copyId, successor);

            AddEdge(graph, new CivlEdge
            {
              Id = nextEdgeId++,
              Source = transferNode,
              Target = targetNode,
              Label = P,
              CallCmd = null,
              Action = null
            });
          }
        }
        else if (block.TransferCmd is ReturnCmd)
        {
          graph.FinalStates.Add(MapNode(factory, block.TransferCmd, loop, copyId));
        }
      }
    }

    return graph;
  }
  private static List<CivlNode> ComputeTopologicalNodes(YieldRegion region)
  {
    var indegree = region.Nodes.ToDictionary(node => node, _ => 0);

    foreach (var edge in region.InternalEdges)
    {
      indegree[edge.Target]++;
    }

    var ready = new List<CivlNode>(region.Nodes.Where(node => indegree[node] == 0));
    ready.Sort((x, y) => string.CompareOrdinal(x.ToString(), y.ToString()));

    var result = new List<CivlNode>();

    while (ready.Count > 0)
    {
      var node = ready[0];
      ready.RemoveAt(0);
      result.Add(node);

      var newlyReady = new List<CivlNode>();
      foreach (var edge in Outgoing(region, node))
      {
        indegree[edge.Target]--;
        if (indegree[edge.Target] == 0)
        {
          newlyReady.Add(edge.Target);
        }
      }

      newlyReady.Sort((x, y) => string.CompareOrdinal(x.ToString(), y.ToString()));
      ready.AddRange(newlyReady);
    }

    if (result.Count != region.Nodes.Count)
    {
      throw new Exception("Yield region is not acyclic, so topological order could not be computed.");
    }

    return result;
  }

  private static HashSet<CivlNode> ForwardReachableInternal(CivlNode start, IEnumerable<CivlEdge> edges)
  {
    var outMap = new Dictionary<CivlNode, List<CivlEdge>>();
    foreach (var edge in edges)
    {
      if (!outMap.TryGetValue(edge.Source, out var list))
      {
        list = new List<CivlEdge>();
        outMap[edge.Source] = list;
      }
      list.Add(edge);
    }

    var visited = new HashSet<CivlNode> { start };
    var worklist = new Queue<CivlNode>();
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

  private static YieldRegion SliceBoundaryRegion(
    CivlGraph graph,
    CivlNode entryNode,
    CivlNode exitNode,
    HashSet<CivlEdge> candidateEdges)
  {
    var forward = ForwardReachableInternal(entryNode, candidateEdges);
    if (!forward.Contains(exitNode))
    {
      return null;
    }

    var regionNodes = new HashSet<CivlNode>();
    var regionEdges = candidateEdges
      .Where(e => forward.Contains(e.Source) && forward.Contains(e.Target))
      .ToList();

    foreach (var edge in regionEdges)
    {
      regionNodes.Add(edge.Source);
      regionNodes.Add(edge.Target);
    }

    var region = new YieldRegion
    {
      EntryYieldEdge = null,
      ExitYieldEdge = null,
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

    region.TopologicalNodes = ComputeTopologicalNodes(region);

    return region;
  }

  private static YieldRegion SliceRegion(
    CivlGraph graph,
    CivlEdge entryYield,
    CivlEdge exitYield,
    HashSet<CivlEdge> candidateEdges)
  {
    var entryNode = entryYield.Target;
    var exitNode = exitYield.Source;

    var forward = ForwardReachableInternal(entryNode, candidateEdges);
    if (!forward.Contains(exitNode))
    {
      return null;
    }

    // Keep the whole candidate subgraph reachable from the entry yield.
    var regionNodes = new HashSet<CivlNode>();
    var regionEdges = candidateEdges
      .Where(e => forward.Contains(e.Source) && forward.Contains(e.Target))
      .ToList();

    foreach (var edge in regionEdges)
    {
      regionNodes.Add(edge.Source);
      regionNodes.Add(edge.Target);
    }

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

    region.TopologicalNodes = ComputeTopologicalNodes(region);

    return region;
  }

  public static List<YieldRegion> ExtractRegions(CivlGraph graph)
  {
    var regions = new List<YieldRegion>();
    var yieldEdges = YieldEdges(graph).ToList();

    if (!yieldEdges.Any())
    {
      var candidateEdges = new HashSet<CivlEdge>(graph.Edges);
      foreach (var finalState in graph.FinalStates)
      {
        var region = SliceBoundaryRegion(graph, graph.InitialState, finalState, candidateEdges);
        if (region != null && region.Nodes.Count > 1)
        {
          regions.Add(region);
        }
      }
      return regions;
    }

    foreach (var entryYield in yieldEdges)
    {
      var exits = new HashSet<CivlEdge>();
      var reachableInternalNodes = new HashSet<CivlNode>();
      var reachableInternalEdges = new HashSet<CivlEdge>();
      var worklist = new Queue<CivlNode>();

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
        var region = SliceRegion(graph, entryYield, exitYield, reachableInternalEdges);
        if (region != null && region.Nodes.Count > 1)
        {
          regions.Add(region);
        }
      }
    }

    {
      var exits = new HashSet<CivlEdge>();
      var reachableInternalNodes = new HashSet<CivlNode>();
      var reachableInternalEdges = new HashSet<CivlEdge>();
      var worklist = new Queue<CivlNode>();

      reachableInternalNodes.Add(graph.InitialState);
      worklist.Enqueue(graph.InitialState);

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
        var region = SliceBoundaryRegion(graph, graph.InitialState, exitYield.Source, reachableInternalEdges);
        if (region != null && region.Nodes.Count > 1)
        {
          regions.Add(region);
        }
      }
    }

    foreach (var entryYield in yieldEdges)
    {
      var candidateEdges = new HashSet<CivlEdge>();
      var worklist = new Queue<CivlNode>();
      var visitedNodes = new HashSet<CivlNode>();

      var entryNode = entryYield.Target;
      visitedNodes.Add(entryNode);
      worklist.Enqueue(entryNode);

      while (worklist.Count > 0)
      {
        var node = worklist.Dequeue();
        foreach (var edge in Outgoing(graph, node))
        {
          if (IsYield(edge))
          {
            continue;
          }

          if (candidateEdges.Add(edge) && visitedNodes.Add(edge.Target))
          {
            worklist.Enqueue(edge.Target);
          }
        }
      }

      foreach (var finalState in graph.FinalStates)
      {
        var region = SliceBoundaryRegion(graph, entryNode, finalState, candidateEdges);
        if (region != null && region.Nodes.Count > 1)
        {
          regions.Add(region);
        }
      }
    }

    return regions;
  }

  public static void ValidateRegion(YieldRegion region)
  {
    if (region.EntryYieldEdge != null && region.EntryYieldEdge.Label != Y)
    {
      throw new Exception("Region entry edge is not a yield edge");
    }

    if (region.ExitYieldEdge != null && region.ExitYieldEdge.Label != Y)
    {
      throw new Exception("Region exit edge is not a yield edge");
    }

    foreach (var edge in region.InternalEdges)
    {
      if (edge.Label == Y)
      {
        throw new Exception($"Region contains internal yield edge {edge.Id}");
      }
    }

    if (!region.Nodes.Contains(region.EntryNode))
    {
      throw new Exception("Region does not contain entry node");
    }

    if (!region.Nodes.Contains(region.ExitNode))
    {
      throw new Exception("Region does not contain exit node");
    }
  }

  public static void ValidateRegions(IEnumerable<YieldRegion> regions)
  {
    foreach (var region in regions)
    {
      ValidateRegion(region);
    }
  }


  public static string PrintRegion(YieldRegion region)
  {
    var sb = new System.Text.StringBuilder();
    var entry = region.EntryYieldEdge == null ? "ENTRY" : region.EntryYieldEdge.Id.ToString();
    var exit = region.ExitYieldEdge == null ? "EXIT" : region.ExitYieldEdge.Id.ToString();

    sb.AppendLine(
      $"EntryYield={entry}, ExitYield={exit}, " +
      $"EntryNode={region.EntryNode}, ExitNode={region.ExitNode}");

    foreach (var edge in region.InternalEdges.OrderBy(e => e.Id))
    {
      var actionName = edge.Action?.ActionDecl?.Name ?? "-";
      sb.AppendLine(
        $"  {edge.Id}: {edge.Source} --{CurrentLabel(edge)}--> {edge.Target} action={actionName}");
    }

    return sb.ToString();
  }

  public static HashSet<CivlEdge> BackwardReachableEdgesFromEdge(YieldRegion region, CivlEdge startEdge)
  {
    var result = new HashSet<CivlEdge> { startEdge };
    var worklist = new Queue<CivlNode>();
    var visitedNodes = new HashSet<CivlNode> { startEdge.Source };
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
    var worklist = new Queue<CivlNode>();
    var visitedNodes = new HashSet<CivlNode> { startEdge.Target };
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

    public HashSet<BoogieAction> MustCheckRightActions = new();
    public HashSet<BoogieAction> MustCheckLeftActions = new();
  }

  public static RegionObligations AnalyzeRegion(YieldRegion region)
  {
    var obligations = new RegionObligations
    {
      Region = region
    };

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

          if (IsCurrentlyCheckEdge(predEdge) && predEdge.Action != null) {
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

          if (IsCurrentlyCheckEdge(succEdge) && succEdge.Action != null) {
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

}