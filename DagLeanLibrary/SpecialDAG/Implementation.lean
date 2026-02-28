import DagLeanLibrary.SpecialDAG.Interface
import Std

namespace DagLeanLibrary
namespace SpecialDAG

/-- Concrete executable representation:
- `edges` contains directed edges `(u, v)`
- `nodeLabels[n] = label`
- `labelToNode[label] = n` (intended inverse map) -/
structure Graph where
  edges : List (NodeId × NodeId) := []
  nodeLabels : Std.HashMap NodeId String := ∅
  labelToNode : Std.HashMap String NodeId := ∅
  deriving Inhabited

namespace Graph

def nodes (g : Graph) : List NodeId :=
  g.nodeLabels.toList.map Prod.fst

def nodeCount (g : Graph) : Nat :=
  g.nodeLabels.size

def predecessors (g : Graph) (n : NodeId) : List NodeId :=
  (g.edges.filterMap fun (src, dst) =>
    if dst == n then some src else none).eraseDups

def successors (g : Graph) (n : NodeId) : List NodeId :=
  (g.edges.filterMap fun (src, dst) =>
    if src == n then some dst else none).eraseDups

private def closureFrom
    (next : NodeId → List NodeId)
    (fuel : Nat)
    (frontier visited : List NodeId) : List NodeId :=
  match fuel with
  | 0 => visited
  | fuel + 1 =>
      match frontier with
      | [] => visited
      | n :: rest =>
          let ns := next n
          let fresh := ns.filter (fun x => x ∉ visited)
          closureFrom next fuel (rest ++ fresh) (visited ++ fresh)

def descendantClosure (g : Graph) (n : NodeId) : List NodeId :=
  closureFrom (successors g) (nodeCount g + 1) [n] []

def ancestorClosure (g : Graph) (n : NodeId) : List NodeId :=
  closureFrom (predecessors g) (nodeCount g + 1) [n] []

def nodeLabel? (g : Graph) (n : NodeId) : Option String :=
  g.nodeLabels.get? n

def nodeOfLabel? (g : Graph) (l : String) : Option NodeId :=
  g.labelToNode.get? l

instance : Interface Graph where
  nodeCount := nodeCount
  predecessors := predecessors
  successors := successors
  ancestorClosure := ancestorClosure
  descendantClosure := descendantClosure
  nodeLabel? := nodeLabel?
  nodeOfLabel? := nodeOfLabel?

/-- Runtime checker for core invariants. Useful before full proof development. -/
def checkWellFormed (g : Graph) : Bool :=
  let everyNodeHasIncidentEdge :=
    g.nodes.all fun n =>
      !(predecessors g n).isEmpty || !(successors g n).isEmpty
  let acyclicApprox :=
    g.nodes.all fun n => n ∉ descendantClosure g n
  let noParallelEdges :=
    g.edges.eraseDups.length == g.edges.length
  let labelRoundTrip :=
    g.nodeLabels.toList.all fun (n, l) => g.labelToNode.get? l == some n
  everyNodeHasIncidentEdge && acyclicApprox && noParallelEdges && labelRoundTrip

end Graph

end SpecialDAG
end DagLeanLibrary
