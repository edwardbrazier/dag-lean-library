import DagLeanLibrary.SpecialDAG.Builder.Implementation

namespace DagLeanLibrary
namespace SpecialDAG
namespace Graph

/-- Specification: `empty` is well-formed. -/
def empty_wellFormed : Prop :=
  WellFormed Graph empty

/-- Specification: any successful `addEdge` preserves well-formedness. -/
def addEdge_some_wellFormed : Prop :=
  ∀ (g : Graph) (src dst : NodeId) (srcLabel dstLabel : String),
    WellFormed Graph g →
    ∀ (g' : Graph), addEdge g src dst srcLabel dstLabel = some g' →
      WellFormed Graph g'

/-- Specification: any successful `deleteEdge` preserves well-formedness. -/
def deleteEdge_some_wellFormed : Prop :=
  ∀ (g : Graph) (src dst : NodeId),
    WellFormed Graph g →
    ∀ (g' : Graph), deleteEdge g src dst = some g' →
      WellFormed Graph g'

/-- Specification: any successful `deleteNode` preserves well-formedness. -/
def deleteNode_some_wellFormed : Prop :=
  ∀ (g : Graph) (n : NodeId),
    WellFormed Graph g →
    ∀ (g' : Graph), deleteNode g n = some g' →
      WellFormed Graph g'

end Graph
end SpecialDAG
end DagLeanLibrary
