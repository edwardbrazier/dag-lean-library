import DagLeanLibrary.SpecialDAG.Builder.Implementation

namespace DagLeanLibrary
namespace SpecialDAG
namespace Graph

/-- Any graph produced by successful `deleteNode` from a well-formed graph
is itself well-formed. -/
theorem deleteNode_some_wellFormed
    (g : Graph) (n : NodeId)
    (hWF : WellFormed Graph g)
    (g' : Graph)
    (h : deleteNode g n = some g') :
    WellFormed Graph g' := by
  sorry

end Graph
end SpecialDAG
end DagLeanLibrary
