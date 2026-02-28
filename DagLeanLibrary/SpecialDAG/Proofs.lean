import DagLeanLibrary.SpecialDAG.Implementation

namespace DagLeanLibrary
namespace SpecialDAG
namespace Graph

/-- If reverse lookup maps the same label to two nodes, those nodes are equal. -/
theorem atMostOneNodePerLabel
    (g : Graph) (l : String) (n₁ n₂ : NodeId)
    (h₁ : g.labelToNode.get? l = some n₁)
    (h₂ : g.labelToNode.get? l = some n₂) :
    n₁ = n₂ := by
  have h : some n₁ = some n₂ := h₁.symm.trans h₂
  exact Option.some.inj h

private theorem not_isEmpty_true_iff_ne_nil (xs : List α) :
    (!xs.isEmpty = true) ↔ xs ≠ [] := by
  cases xs <;> simp

/-- `checkWellFormed` unfolds to four executable checks combined with `&&`. -/
theorem checkWellFormed_eq (g : Graph) :
    g.checkWellFormed =
      ((g.nodes.all fun n =>
          !(g.predecessors n).isEmpty || !(g.successors n).isEmpty) &&
        (g.nodes.all fun n => n ∉ g.descendantClosure n) &&
        (g.edges.eraseDups.length == g.edges.length) &&
        (g.nodeLabels.toList.all fun (n, l) => g.labelToNode.get? l == some n)) := by
  rfl

theorem checkWellFormed_true_iff (g : Graph) :
    g.checkWellFormed = true ↔
      (g.nodes.all fun n =>
          !(g.predecessors n).isEmpty || !(g.successors n).isEmpty) = true ∧
      (g.nodes.all fun n => n ∉ g.descendantClosure n) = true ∧
      (g.edges.eraseDups.length == g.edges.length) = true ∧
      (g.nodeLabels.toList.all fun (n, l) => g.labelToNode.get? l == some n) = true := by
  constructor <;> intro h <;>
    simpa [Graph.checkWellFormed, Bool.and_eq_true, and_assoc, and_left_comm, and_comm] using h

/-- Soundness of the acyclicity runtime check over the listed node domain. -/
theorem checkWellFormed_true_implies_acyclicOnNodes
    (g : Graph) (h : g.checkWellFormed = true) :
    ∀ n, n ∈ g.nodes → n ∉ g.descendantClosure n := by
  have hAcyclicList : (g.nodes.all fun n => n ∉ g.descendantClosure n) = true :=
    (checkWellFormed_true_iff g).1 h |>.2.1
  intro n hn
  have hDecide : decide (n ∉ g.descendantClosure n) = true :=
    (List.all_eq_true.mp hAcyclicList) n hn
  exact (decide_eq_true_eq.mp hDecide)

/-- Soundness of the no-isolated-node runtime check over the listed node domain. -/
theorem checkWellFormed_true_implies_incidentEdgeOnNodes
    (g : Graph) (h : g.checkWellFormed = true) :
    ∀ n, n ∈ g.nodes →
      g.predecessors n ≠ [] ∨ g.successors n ≠ [] := by
  have hIncident :
      (g.nodes.all fun n => !(g.predecessors n).isEmpty || !(g.successors n).isEmpty) = true :=
    (checkWellFormed_true_iff g).1 h |>.1
  intro n hn
  have hb : (!(g.predecessors n).isEmpty || !(g.successors n).isEmpty) = true :=
    (List.all_eq_true.mp hIncident) n hn
  have hp : (!(g.predecessors n).isEmpty = true) ∨ (!(g.successors n).isEmpty = true) := by
    simpa [Bool.or_eq_true] using hb
  cases hp with
  | inl hpred =>
      left
      exact (not_isEmpty_true_iff_ne_nil _).1 hpred
  | inr hsucc =>
      right
      exact (not_isEmpty_true_iff_ne_nil _).1 hsucc

/-- Soundness of the no-parallel-edge runtime check. -/
theorem checkWellFormed_true_implies_noParallelEdges
    (g : Graph) (h : g.checkWellFormed = true) :
    g.edges.eraseDups.length = g.edges.length := by
  have hNoParallel : (g.edges.eraseDups.length == g.edges.length) = true :=
    (checkWellFormed_true_iff g).1 h |>.2.2.1
  exact LawfulBEq.eq_of_beq hNoParallel

/-- Soundness of the node label round-trip runtime check. -/
theorem checkWellFormed_true_implies_labelRoundTripOnListedPairs
    (g : Graph) (h : g.checkWellFormed = true) :
    ∀ p, p ∈ g.nodeLabels.toList → g.labelToNode.get? p.2 = some p.1 := by
  have hRoundTrip :
      (g.nodeLabels.toList.all fun (n, l) => g.labelToNode.get? l == some n) = true :=
    (checkWellFormed_true_iff g).1 h |>.2.2.2
  intro p hp
  have hb : (fun (n, l) => g.labelToNode.get? l == some n) p = true :=
    (List.all_eq_true.mp hRoundTrip) p hp
  exact LawfulBEq.eq_of_beq hb

end Graph
end SpecialDAG
end DagLeanLibrary
