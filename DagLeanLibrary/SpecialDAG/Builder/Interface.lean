import DagLeanLibrary.SpecialDAG.Interface

namespace DagLeanLibrary
namespace SpecialDAG

/-- Interface for correct-by-construction builder operations. -/
class BuilderInterface (α : Type) [Interface α] where
  /-- The empty graph value. -/
  empty : α
  /-- Safely add an edge and any required labels, failing if invariants would be violated. -/
  addEdge : α → NodeId → NodeId → String → String → Option α

end SpecialDAG
end DagLeanLibrary
