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
  else some
    { edges      := g.edges ++ [(src, dst)]
    , nodeLabels := g.nodeLabels  |>.insert src srcLabel |>.insert dst dstLabel
    , labelToNode := g.labelToNode |>.insert srcLabel src |>.insert dstLabel dst }

instance : BuilderInterface Graph where
  empty := empty
  addEdge := addEdge

end Graph
end SpecialDAG
end DagLeanLibrary
