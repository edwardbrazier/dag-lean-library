import Std

namespace DagLeanLibrary
namespace SpecialDAG

/-- Node identifiers in the concrete implementation. -/
abbrev NodeId := Nat

/-- Abstract interface for a labeled simple DAG.

- *Labeled*: nodes carry `String` labels.
- *Simple*: there is at most one directed edge for each ordered pair `(u, v)`.
- *DAG*: graph is acyclic. -/
class Interface (α : Type) where
  /-- Number of nodes. -/
  nodeCount : α → Nat
  /-- All predecessor nodes with edges `p → n`. -/
  predecessors : α → NodeId → List NodeId
  /-- All successor nodes with edges `n → c`. -/
  successors : α → NodeId → List NodeId
  /-- Transitive closure of predecessors (all ancestors). -/
  ancestorClosure : α → NodeId → List NodeId
  /-- Transitive closure of successors (all descendants). -/
  descendantClosure : α → NodeId → List NodeId
  /-- Optional node label lookup. -/
  nodeLabel? : α → NodeId → Option String
  /-- Reverse lookup by node label. -/
  nodeOfLabel? : α → String → Option NodeId

/-- Invariants required by labeled simple DAGs. -/
structure WellFormed (α : Type) [Interface α] (g : α) : Prop where
  /-- Graph has no directed cycles. -/
  acyclic : ∀ n, n ∉ Interface.descendantClosure g n
  /-- Every node has at least one incident edge (incoming or outgoing). -/
  noIsolatedNodes :
    ∀ n, Interface.nodeLabel? g n ≠ none →
      Interface.predecessors g n ≠ [] ∨ Interface.successors g n ≠ []
  /-- Simplicity: predecessor and successor lists contain no duplicates. -/
  simpleAdjacency :
    ∀ n,
      (Interface.predecessors g n).Nodup ∧
      (Interface.successors g n).Nodup
  /-- Node labels are unique (injective reverse lookup). -/
  uniqueNodeLabels :
    ∀ l n₁ n₂,
      Interface.nodeOfLabel? g l = some n₁ →
      Interface.nodeOfLabel? g l = some n₂ →
      n₁ = n₂
  /-- Forward and reverse node label lookups agree. -/
  nodeLabelRoundTrip :
    ∀ n l,
      Interface.nodeLabel? g n = some l →
      Interface.nodeOfLabel? g l = some n

end SpecialDAG
end DagLeanLibrary
