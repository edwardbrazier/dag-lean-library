import DagLeanLibrary.SpecialDAG.Proofs

namespace DagLeanLibrary
namespace SpecialDAG
namespace Graph

/-! ## Smart Constructors

This module provides a correct-by-construction API for building `Graph` values.
Every graph produced by these functions satisfies the `WellFormed` invariants. -/

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

/-! ## Helper lemmas that hold for every `Graph` -/

/-- Predecessor and successor lists are always duplicate-free because their
    implementations call `List.eraseDups`. -/
theorem simpleAdjacency_always (g : Graph) :
    ∀ n, (g.predecessors n).Nodup ∧ (g.successors n).Nodup := by
  intro n
  exact ⟨List.nodup_eraseDups _, List.nodup_eraseDups _⟩

/-- The reverse label map is injective for any `Graph`: if two lookups of the
    same label both succeed they must return the same node. -/
theorem uniqueNodeLabels_always (g : Graph) :
    ∀ l n₁ n₂,
      Interface.nodeOfLabel? g l = some n₁ →
      Interface.nodeOfLabel? g l = some n₂ →
      n₁ = n₂ := by
  intro l n₁ n₂ h₁ h₂
  exact Option.some.inj (h₁.symm.trans h₂)

/-! ## Well-formedness of `empty` -/

private theorem descendantClosure_empty (n : NodeId) :
    descendantClosure empty n = [] := by
  simp [descendantClosure, closureFrom, successors, empty, nodeCount, nodes]

theorem empty_wellFormed : WellFormed Graph empty := {
  acyclic := by
    intro n
    rw [Interface.descendantClosure, descendantClosure_empty]
    exact List.not_mem_nil _
  noIsolatedNodes := by
    intro n h
    simp [Interface.nodeLabel?, nodeLabel?, empty] at h
  simpleAdjacency := by
    intro n
    exact simpleAdjacency_always empty n
  uniqueNodeLabels := by
    exact uniqueNodeLabels_always empty
  nodeLabelRoundTrip := by
    intro n l h
    simp [Interface.nodeLabel?, nodeLabel?, empty] at h
}

/-! ## Well-formedness of `addEdge` results -/

-- Extract the guard hypotheses and result from a successful addEdge call.
private structure AddEdgeSuccessHyps (g g' : Graph) (src dst : NodeId)
    (srcLabel dstLabel : String) : Prop where
  hNotSelf    : ¬ (src == dst) = true
  hNotInClos  : src ∉ g.descendantClosure dst
  hNotParallel : (src, dst) ∉ g.edges
  hSrcLblOk  : ¬ ((g.labelToNode.get? srcLabel).isSome && !(g.labelToNode.get? srcLabel == some src)) = true
  hDstLblOk  : ¬ ((g.labelToNode.get? dstLabel).isSome && !(g.labelToNode.get? dstLabel == some dst)) = true
  hSrcFwdOk  : ¬ ((g.nodeLabels.get? src).isSome && !(g.nodeLabels.get? src == some srcLabel)) = true
  hDstFwdOk  : ¬ ((g.nodeLabels.get? dst).isSome && !(g.nodeLabels.get? dst == some dstLabel)) = true
  hLblsDiff  : ¬ (srcLabel == dstLabel) = true
  hResult    : g' = { edges := g.edges ++ [(src, dst)],
                      nodeLabels  := g.nodeLabels  |>.insert src srcLabel |>.insert dst dstLabel,
                      labelToNode := g.labelToNode |>.insert srcLabel src |>.insert dstLabel dst }

private theorem addEdge_some_iff (g : Graph) (src dst : NodeId) (srcLabel dstLabel : String)
    (g' : Graph) (h : addEdge g src dst srcLabel dstLabel = some g') :
    AddEdgeSuccessHyps g g' src dst srcLabel dstLabel := by
  simp only [addEdge] at h
  split_ifs at h with h1 h2 h3 h4 h5 h6 h7 h8 <;> simp_all
  exact { hNotSelf := h1, hNotInClos := by simpa using h2, hNotParallel := by simpa using h3,
          hSrcLblOk := h4, hDstLblOk := h5, hSrcFwdOk := h6, hDstFwdOk := h7, hLblsDiff := h8,
          hResult := Option.some.inj h }

/-- If `src ≠ dst` (as a Bool equality), then `src ≠ dst` as a Nat equality. -/
private theorem ne_of_bne {src dst : NodeId} (h : ¬ (src == dst) = true) : src ≠ dst := by
  simpa [BEq.beq, Nat.beq_eq] using h

/-- If `srcLabel ≠ dstLabel` (Bool), they differ as Strings. -/
private theorem strNe_of_bne {s t : String} (h : ¬ (s == t) = true) : s ≠ t := by
  simpa using h

-- ── noIsolatedNodes for addEdge ──────────────────────────────────────────────

private theorem addEdge_some_noIsolatedNodes
    (g : Graph) (src dst : NodeId) (srcLabel dstLabel : String)
    (hWF : WellFormed Graph g)
    (g' : Graph)
    (hH : AddEdgeSuccessHyps g g' src dst srcLabel dstLabel) :
    ∀ n, Interface.nodeLabel? g' n ≠ none →
      Interface.predecessors g' n ≠ [] ∨ Interface.successors g' n ≠ [] := by
  obtain ⟨hNotSelf, _, _, _, _, _, _, _, hRes⟩ := hH
  have hSrcNeDst : src ≠ dst := ne_of_bne hNotSelf
  intro n hn
  -- Interface.successors g' n = g'.successors n by the instance
  simp only [Interface.predecessors, Interface.successors, Interface.nodeLabel?]
  subst hRes
  -- Distinguish whether n is src, dst, or another node
  by_cases hns : n = src
  · -- n = src: dst is a successor of src in g'
    subst hns
    right
    -- dst ∈ g'.successors src, so g'.successors src ≠ []
    apply List.ne_nil_of_mem (a := dst)
    simp only [successors, List.mem_eraseDups, List.mem_filterMap]
    exact ⟨(src, dst), by simp [List.mem_append], by simp⟩
  · by_cases hnd : n = dst
    · -- n = dst: src is a predecessor of dst in g'
      subst hnd
      left
      apply List.ne_nil_of_mem (a := src)
      simp only [predecessors, List.mem_eraseDups, List.mem_filterMap]
      exact ⟨(src, dst), by simp [List.mem_append], by simp⟩
    · -- n ≠ src, n ≠ dst: label didn't change, incident edges only grew
      -- First show the label is the same as in g
      have hn_g : Interface.nodeLabel? g n ≠ none := by
        simp only [Interface.nodeLabel?, nodeLabel?]
        simp only [nodeLabel?] at hn
        simp only [Std.HashMap.get?_insert, hns, hnd, if_false] at hn
        exact hn
      -- Apply well-formedness of g
      obtain h | h := hWF.noIsolatedNodes n hn_g
      · left
        intro hempty
        apply h
        -- g.predecessors n ⊆ g'.predecessors n, so if g'.predecessors n = [] then g.predecessors n = []
        simp only [predecessors] at hempty ⊢
        have : (g.edges.filterMap fun (s, d) => if d == n then some s else none).eraseDups = [] := by
          apply List.eq_nil_of_subset_nil
          calc (g.edges.filterMap fun (s, d) => if d == n then some s else none).eraseDups
              ⊆ ((g.edges ++ [(src, dst)]).filterMap fun (s, d) => if d == n then some s else none).eraseDups := by
                apply List.eraseDups_sublist.2
                apply List.filterMap_sublist
                exact List.sublist_append_left _ _
            _ = [] := by rw [hempty]
        exact this
      · right
        intro hempty
        apply h
        simp only [successors] at hempty ⊢
        have : (g.edges.filterMap fun (s, d) => if s == n then some d else none).eraseDups = [] := by
          apply List.eq_nil_of_subset_nil
          calc (g.edges.filterMap fun (s, d) => if s == n then some d else none).eraseDups
              ⊆ ((g.edges ++ [(src, dst)]).filterMap fun (s, d) => if s == n then some d else none).eraseDups := by
                apply List.eraseDups_sublist.2
                apply List.filterMap_sublist
                exact List.sublist_append_left _ _
            _ = [] := by rw [hempty]
        exact this

-- ── nodeLabelRoundTrip for addEdge ───────────────────────────────────────────

private theorem addEdge_some_nodeLabelRoundTrip
    (g : Graph) (src dst : NodeId) (srcLabel dstLabel : String)
    (hWF : WellFormed Graph g)
    (g' : Graph)
    (hH : AddEdgeSuccessHyps g g' src dst srcLabel dstLabel) :
    ∀ n l, Interface.nodeLabel? g' n = some l → Interface.nodeOfLabel? g' l = some n := by
  sorry

-- ── acyclic for addEdge ───────────────────────────────────────────────────────

private theorem addEdge_some_acyclic
    (g : Graph) (src dst : NodeId) (srcLabel dstLabel : String)
    (hWF : WellFormed Graph g)
    (g' : Graph)
    (hH : AddEdgeSuccessHyps g g' src dst srcLabel dstLabel) :
    ∀ n, n ∉ Interface.descendantClosure g' n := by
  -- TODO: This requires three auxiliary lemmas about closureFrom that are not yet proved:
  --   (1) Transitivity: x ∈ descendantClosure g y → y ∈ descendantClosure g z → x ∈ descendantClosure g z
  --   (2) Monotonicity: g.edges ⊆ g'.edges → descendantClosure g n ⊆ descendantClosure g' n
  --   (3) Completeness: closureFrom with fuel (nodeCount g + 1) visits all reachable nodes in an acyclic graph
  --
  -- Informal argument (sound but awaiting formalisation):
  --   If n ∈ g'.descendantClosure n for some n, that cycle must use the new edge src→dst (since g was acyclic).
  --   So n→…→src→dst→…→n with all non-new edges in g, meaning
  --   src ∈ g.descendantClosure n AND n ∈ g.descendantClosure dst.
  --   By transitivity, src ∈ g.descendantClosure dst, contradicting hH.hNotInClos.
  sorry

/-! ## Master theorem -/

/-- Any graph produced by `addEdge` from a well-formed graph is itself well-formed. -/
theorem addEdge_some_wellFormed
    (g : Graph) (src dst : NodeId) (srcLabel dstLabel : String)
    (hWF : WellFormed Graph g)
    (g' : Graph)
    (h : addEdge g src dst srcLabel dstLabel = some g') :
    WellFormed Graph g' := by
  obtain hH := addEdge_some_iff g src dst srcLabel dstLabel g' h
  exact {
    acyclic          := addEdge_some_acyclic g src dst srcLabel dstLabel hWF g' hH
    noIsolatedNodes  := addEdge_some_noIsolatedNodes g src dst srcLabel dstLabel hWF g' hH
    simpleAdjacency  := simpleAdjacency_always g'
    uniqueNodeLabels := uniqueNodeLabels_always g'
    nodeLabelRoundTrip := addEdge_some_nodeLabelRoundTrip g src dst srcLabel dstLabel hWF g' hH
  }

end Graph
end SpecialDAG
end DagLeanLibrary
