import DagLeanLibrary.SpecialDAG.Builder.Interface
import DagLeanLibrary.SpecialDAG.Implementation

namespace DagLeanLibrary
namespace SpecialDAG
namespace Graph

/-- The empty graph. No nodes, no edges, no labels. -/
def empty : Graph :=
  { edges := [], nodeLabels := ∅, labelToNode := ∅ }

/-- Safely add a directed edge `src → dst` with labels `srcLabel` and `dstLabel`.

    Returns `none` if any `WellFormed` invariant would be violated:
    - `src = dst` (self-loop → cycle)
    - `src` is already a descendant of `dst` (adding the edge would create a cycle)
    - `(src, dst)` is already in the edge list (parallel edge)
    - `srcLabel` is already bound to a node other than `src` (label conflict)
    - `dstLabel` is already bound to a node other than `dst` (label conflict)
    - `src` is already labeled differently than `srcLabel` (inconsistent forward map)
    - `dst` is already labeled differently than `dstLabel` (inconsistent forward map)
    - `srcLabel = dstLabel` with `src ≠ dst` (two nodes sharing one label)

    On success, the edge and both node labels are inserted atomically into all three maps. -/
def addEdge (g : Graph) (src dst : NodeId) (srcLabel dstLabel : String) : Option Graph :=
  if src == dst then none
  else if decide (src ∈ g.descendantClosure dst) then none
  else if decide ((src, dst) ∈ g.edges) then none
  else if (g.labelToNode.get? srcLabel).isSome && !(g.labelToNode.get? srcLabel == some src) then none
  else if (g.labelToNode.get? dstLabel).isSome && !(g.labelToNode.get? dstLabel == some dst) then none
  else if (g.nodeLabels.get? src).isSome && !(g.nodeLabels.get? src == some srcLabel) then none
  else if (g.nodeLabels.get? dst).isSome && !(g.nodeLabels.get? dst == some dstLabel) then none
  else if srcLabel == dstLabel then none
  else
    let g' : Graph :=
      { edges      := g.edges ++ [(src, dst)]
      , nodeLabels := g.nodeLabels  |>.insert src srcLabel |>.insert dst dstLabel
      , labelToNode := g.labelToNode |>.insert srcLabel src |>.insert dstLabel dst }
    let sourceNodes := (g'.edges.map Prod.fst).eraseDups
    if sourceNodes.all (fun n => decide (n ∉ g'.descendantClosure n)) then some g' else none

/-- Safely delete a directed edge `src → dst`.

    Returns `none` if the edge does not exist.

    On success, this function removes the edge and then prunes any orphaned
    nodes (nodes with no incoming and no outgoing edges), including deleting
    their labels from both maps. -/
def deleteEdge (g : Graph) (src dst : NodeId) : Option Graph :=
  if !decide ((src, dst) ∈ g.edges) then none
  else
    let edges' := g.edges.erase (src, dst)
    let nodeHasIncidentEdge (n : NodeId) : Bool :=
      edges'.any (fun (u, v) => u == n || v == n)
    let nodeLabels' : Std.HashMap NodeId String :=
      g.nodeLabels.filter (fun n _ => nodeHasIncidentEdge n)
    let labelToNode' : Std.HashMap String NodeId :=
      Std.HashMap.ofList (nodeLabels'.toList.map (fun (n, lbl) => (lbl, n)))
    let g' : Graph :=
      { edges := edges'
      , nodeLabels := nodeLabels'
      , labelToNode := labelToNode' }
    let sourceNodes := (g'.edges.map Prod.fst).eraseDups
    if sourceNodes.all (fun n => decide (n ∉ g'.descendantClosure n)) then some g' else none

/-- Safely delete node `n` and all incident edges.

    Returns `none` if the node does not exist or deleting it would violate
    any `WellFormed` invariant. -/
def deleteNode (g : Graph) (n : NodeId) : Option Graph :=
  match g.nodeLabels.get? n with
  | none => none
  | some lbl =>
      let g' : Graph :=
        { edges := g.edges.filter (fun (src, dst) => src != n && dst != n)
        , nodeLabels := g.nodeLabels.erase n
        , labelToNode := g.labelToNode.erase lbl }
      if g'.checkWellFormed then some g' else none

instance : BuilderInterface Graph where
  empty := empty
  addEdge := addEdge
  deleteEdge := deleteEdge
  deleteNode := deleteNode

end Graph
end SpecialDAG
end DagLeanLibrary
