import DagLeanLibrary.SpecialDAG.Interface

namespace DagLeanLibrary
namespace SpecialDAG

/-- Interface for correct-by-construction builder operations. -/
class BuilderInterface (α : Type) [Interface α] where
  /-- The empty graph value. -/
  empty : α
  /-- Safely add an edge and any required labels, failing if invariants would be violated. -/
  addEdge : α → NodeId → NodeId → String → String → Option α
  /-- Safely delete a directed edge, failing if the result would violate invariants. -/
  deleteEdge : α → NodeId → NodeId → Option α
  /-- Safely delete a node and its incident edges, failing if the result would violate invariants. -/
  deleteNode : α → NodeId → Option α

end SpecialDAG
end DagLeanLibrary
