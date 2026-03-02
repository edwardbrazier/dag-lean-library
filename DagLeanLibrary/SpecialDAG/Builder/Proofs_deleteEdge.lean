import DagLeanLibrary.SpecialDAG.Builder.Implementation

namespace DagLeanLibrary
namespace SpecialDAG
namespace Graph

/-- Any graph produced by successful `deleteEdge` from a well-formed graph
is itself well-formed. -/
theorem deleteEdge_some_wellFormed
    (g : Graph) (src dst : NodeId)
    (hWF : WellFormed Graph g)
    (g' : Graph)
    (h : deleteEdge g src dst = some g') :
    WellFormed Graph g' := by
  sorry

end Graph
end SpecialDAG
end DagLeanLibrary
