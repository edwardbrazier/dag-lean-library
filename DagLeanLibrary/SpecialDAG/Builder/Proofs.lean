import DagLeanLibrary.SpecialDAG.Builder.Implementation
import DagLeanLibrary.SpecialDAG.Proofs
import Std.Data.HashMap.Lemmas

namespace DagLeanLibrary
namespace SpecialDAG
namespace Graph

/-! ## Helper lemmas that hold for every `Graph` -/

private theorem mem_of_mem_eraseDups [BEq α] [LawfulBEq α] :
    ∀ (l : List α) (x : α), x ∈ l.eraseDups → x ∈ l := by
  let P : Nat → Prop := fun n => ∀ l : List α, l.length = n → ∀ x : α, x ∈ l.eraseDups → x ∈ l
  have hP : ∀ n, P n := by
    intro n
    refine Nat.strongRecOn n ?_
    intro n ih l hlen x hx
    cases l with
    | nil =>
        simp at hx
    | cons a as =>
        rw [List.eraseDups_cons] at hx
        have hx' : x = a ∨ x ∈ (as.filter (fun b => !b == a)).eraseDups := by
          simpa [List.mem_cons] using hx
        cases hx' with
        | inl hHead =>
            exact by simpa [List.mem_cons] using (Or.inl hHead : x = a ∨ x ∈ as)
        | inr htail =>
            have hfltLen : (as.filter (fun b => !b == a)).length < n := by
              have hle := List.length_filter_le (fun b => !b == a) as
              have haslt : as.length < n := by
                have : as.length < (a :: as).length := by simp
                simpa [hlen] using this
              exact Nat.lt_of_le_of_lt hle haslt
            have hxInFilter : x ∈ (as.filter (fun b => !b == a)).eraseDups := htail
            have hxInFilterList : x ∈ as.filter (fun b => !b == a) :=
              ih _ hfltLen _ rfl _ hxInFilter
            exact by
              simpa [List.mem_cons] using
                (Or.inr ((List.mem_filter.mp hxInFilterList).1) : x = a ∨ x ∈ as)
  intro l x hx
  exact hP l.length l rfl x hx

private theorem mem_eraseDups_of_mem [BEq α] [LawfulBEq α] :
    ∀ (l : List α) (x : α), x ∈ l → x ∈ l.eraseDups := by
  let P : Nat → Prop := fun n => ∀ l : List α, l.length = n → ∀ x : α, x ∈ l → x ∈ l.eraseDups
  have hP : ∀ n, P n := by
    intro n
    refine Nat.strongRecOn n ?_
    intro n ih l hlen x hx
    cases l with
    | nil =>
        cases hx
    | cons a as =>
        rw [List.eraseDups_cons]
        have hx' : x = a ∨ x ∈ as := by
          simpa [List.mem_cons] using hx
        cases hx' with
        | inl hHead =>
            simpa [hHead]
        | inr hTail =>
            by_cases hEq : x == a
            · have hxa : x = a := LawfulBEq.eq_of_beq hEq
              simpa [hxa]
            · right
              have hxInFilter : x ∈ as.filter (fun b => !b == a) := by
                exact List.mem_filter.mpr ⟨hTail, by simpa [Bool.not_eq_true] using hEq⟩
              have hfltLen : (as.filter (fun b => !b == a)).length < n := by
                have hle := List.length_filter_le (fun b => !b == a) as
                have haslt : as.length < n := by
                  have : as.length < (a :: as).length := by simp
                  simpa [hlen] using this
                exact Nat.lt_of_le_of_lt hle haslt
              exact ih _ hfltLen _ rfl _ hxInFilter
  intro l x hx
  exact hP l.length l rfl x hx

private theorem nodup_eraseDups [BEq α] [LawfulBEq α] :
    ∀ (l : List α), l.eraseDups.Nodup := by
  let P : Nat → Prop := fun n => ∀ l : List α, l.length = n → l.eraseDups.Nodup
  have hP : ∀ n, P n := by
    intro n
    refine Nat.strongRecOn n ?_
    intro n ih l hlen
    cases l with
    | nil => simp
    | cons a as =>
        rw [List.eraseDups_cons]
        refine List.nodup_cons.2 ?_
        constructor
        · intro hmem
          have hInFilter : a ∈ as.filter (fun b => !b == a) :=
            mem_of_mem_eraseDups (as.filter (fun b => !b == a)) a hmem
          have hFalse : (a == a) = false := by
            simpa using (List.mem_filter.mp hInFilter).2
          have hTrue : (a == a) = true := by
            simpa using (beq_self_eq_true a)
          exact Bool.false_ne_true (hFalse.symm.trans hTrue)
        · have hfltLen : (as.filter (fun b => !b == a)).length < n := by
            have hle := List.length_filter_le (fun b => !b == a) as
            have haslt : as.length < n := by
              have : as.length < (a :: as).length := by simp
              simpa [hlen] using this
            exact Nat.lt_of_le_of_lt hle haslt
          exact ih _ hfltLen _ rfl
  intro l
  exact hP l.length l rfl

/-- Predecessor and successor lists are always duplicate-free because their
    implementations call `List.eraseDups`. -/
theorem simpleAdjacency_always (g : Graph) :
    ∀ n, (g.predecessors n).Nodup ∧ (g.successors n).Nodup := by
  intro n
  constructor
  · simpa [predecessors] using (nodup_eraseDups ((g.edges.filterMap fun (src, dst) =>
      if dst == n then some src else none)))
  · simpa [successors] using (nodup_eraseDups ((g.edges.filterMap fun (src, dst) =>
      if src == n then some dst else none)))

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
  rfl

theorem empty_wellFormed : WellFormed Graph empty := {
  acyclic := by
    intro n
    show n ∉ empty.descendantClosure n
    simp [descendantClosure_empty]
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

/-
The helper extraction theorem and edge-preservation lemmas in this section are
adapted from `DagLeanLibrary/SpecialDAG/Solution.lean`, which was generated by
Aristotle (https://aristotle.harmonic.fun).
-/

-- Extract the guard hypotheses and result from a successful addEdge call.
private structure AddEdgeSuccessHyps (g g' : Graph) (src dst : NodeId)
    (srcLabel dstLabel : String) : Prop where
  hNotSelf    : src ≠ dst
  hNotInClos  : src ∉ g.descendantClosure dst
  hNotParallel : (src, dst) ∉ g.edges
  hSrcLblOk  : srcLabel ∈ g.labelToNode → g.labelToNode[srcLabel]? = some src
  hDstLblOk  : dstLabel ∈ g.labelToNode → g.labelToNode[dstLabel]? = some dst
  hSrcFwdOk  : src ∈ g.nodeLabels → g.nodeLabels[src]? = some srcLabel
  hDstFwdOk  : dst ∈ g.nodeLabels → g.nodeLabels[dst]? = some dstLabel
  hLblsDiff  : srcLabel ≠ dstLabel
  hResult    : g' = { edges := g.edges ++ [(src, dst)],
                      nodeLabels  := g.nodeLabels  |>.insert src srcLabel |>.insert dst dstLabel,
                      labelToNode := g.labelToNode |>.insert srcLabel src |>.insert dstLabel dst }

private theorem addEdge_some_iff (g : Graph) (src dst : NodeId) (srcLabel dstLabel : String)
    (g' : Graph) (h : addEdge g src dst srcLabel dstLabel = some g') :
    AddEdgeSuccessHyps g g' src dst srcLabel dstLabel := by
  simp [addEdge] at h
  rcases h with ⟨hNotSelf, hNotInClos, hNotParallel, hSrcLblOk, hDstLblOk,
    hSrcFwdOk, hDstFwdOk, hLblsDiff, hResult⟩
  exact {
    hNotSelf := hNotSelf
    hNotInClos := hNotInClos
    hNotParallel := hNotParallel
    hSrcLblOk := hSrcLblOk
    hDstLblOk := hDstLblOk
    hSrcFwdOk := hSrcFwdOk
    hDstFwdOk := hDstFwdOk
    hLblsDiff := hLblsDiff
    hResult := hResult.symm
  }

/-- A successful `addEdge` result keeps all existing edges and appends exactly one
    new edge `(src, dst)` at the end. -/
theorem addEdge_some_edges_shape
    (g : Graph) (src dst : NodeId) (srcLabel dstLabel : String)
    (g' : Graph)
    (h : addEdge g src dst srcLabel dstLabel = some g') :
    g'.edges = g.edges ++ [(src, dst)] := by
  exact (addEdge_some_iff g src dst srcLabel dstLabel g' h).hResult ▸ rfl

/-- Successful `addEdge` never removes old edges. -/
theorem addEdge_some_preserves_old_edges
    (g : Graph) (src dst : NodeId) (srcLabel dstLabel : String)
    (g' : Graph)
    (h : addEdge g src dst srcLabel dstLabel = some g') :
    ∀ e, e ∈ g.edges → e ∈ g'.edges := by
  intro e he
  rw [addEdge_some_edges_shape g src dst srcLabel dstLabel g' h]
  exact List.mem_append.mpr (Or.inl he)

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
  rcases hH with ⟨_, _, _, _, _, _, _, _, hResult⟩
  subst hResult
  intro n hnLbl
  by_cases hSrc : n = src
  · subst n
    right
    apply List.ne_nil_of_mem
    simpa [Interface.successors, successors] using
      (mem_eraseDups_of_mem
        ((g.edges ++ [(src, dst)]).filterMap fun (s, d) => if s == src then some d else none)
        dst
        (List.mem_filterMap.mpr ⟨(src, dst), by simp, by simp⟩))
  · by_cases hDst : n = dst
    · subst n
      left
      apply List.ne_nil_of_mem
      simpa [Interface.predecessors, predecessors] using
        (mem_eraseDups_of_mem
          ((g.edges ++ [(src, dst)]).filterMap fun (s, d) => if d == dst then some s else none)
          src
          (List.mem_filterMap.mpr ⟨(src, dst), by simp, by simp⟩))
    · have hnLblOld : Interface.nodeLabel? g n ≠ none := by
        have hGetEq :
            Interface.nodeLabel?
              ({ edges := g.edges ++ [(src, dst)]
               , nodeLabels := g.nodeLabels |>.insert src srcLabel |>.insert dst dstLabel
               , labelToNode := g.labelToNode |>.insert srcLabel src |>.insert dstLabel dst
               } : Graph)
              n = Interface.nodeLabel? g n := by
          have hSrc' : src ≠ n := by simpa [eq_comm] using hSrc
          have hDst' : dst ≠ n := by simpa [eq_comm] using hDst
          simp [Interface.nodeLabel?, nodeLabel?, Std.HashMap.getElem?_insert, hSrc', hDst']
        intro hNone
        exact hnLbl (by simpa [hGetEq] using hNone)
      have hIncidentOld := hWF.noIsolatedNodes n hnLblOld
      cases hIncidentOld with
      | inl hPredOld =>
          left
          cases hPredList : Interface.predecessors g n with
          | nil => cases hPredOld hPredList
          | cons p ps =>
              apply List.ne_nil_of_mem
              have hpOld : p ∈ Interface.predecessors g n := by simp [hPredList]
              have hpOld' : p ∈ (g.edges.filterMap fun (s, d) => if d == n then some s else none).eraseDups := by
                simpa [Interface.predecessors, predecessors] using hpOld
              have hpOldRaw : p ∈ g.edges.filterMap (fun (s, d) => if d == n then some s else none) :=
                mem_of_mem_eraseDups _ _ hpOld'
              rcases List.mem_filterMap.mp hpOldRaw with ⟨e, heMem, heVal⟩
              have hpNewRaw : p ∈
                  (g.edges ++ [(src, dst)]).filterMap (fun (s, d) => if d == n then some s else none) :=
                List.mem_filterMap.mpr ⟨e, by simp [heMem], heVal⟩
              have hpNew' : p ∈
                  ((g.edges ++ [(src, dst)]).filterMap fun (s, d) => if d == n then some s else none).eraseDups :=
                mem_eraseDups_of_mem _ _ hpNewRaw
              simpa [Interface.predecessors, predecessors] using hpNew'
      | inr hSuccOld =>
          right
          cases hSuccList : Interface.successors g n with
          | nil => cases hSuccOld hSuccList
          | cons c cs =>
              apply List.ne_nil_of_mem
              have hcOld : c ∈ Interface.successors g n := by simp [hSuccList]
              have hcOld' : c ∈ (g.edges.filterMap fun (s, d) => if s == n then some d else none).eraseDups := by
                simpa [Interface.successors, successors] using hcOld
              have hcOldRaw : c ∈ g.edges.filterMap (fun (s, d) => if s == n then some d else none) :=
                mem_of_mem_eraseDups _ _ hcOld'
              rcases List.mem_filterMap.mp hcOldRaw with ⟨e, heMem, heVal⟩
              have hcNewRaw : c ∈
                  (g.edges ++ [(src, dst)]).filterMap (fun (s, d) => if s == n then some d else none) :=
                List.mem_filterMap.mpr ⟨e, by simp [heMem], heVal⟩
              have hcNew' : c ∈
                  ((g.edges ++ [(src, dst)]).filterMap fun (s, d) => if s == n then some d else none).eraseDups :=
                mem_eraseDups_of_mem _ _ hcNewRaw
              simpa [Interface.successors, successors] using hcNew' 

-- ── nodeLabelRoundTrip for addEdge ───────────────────────────────────────────

private theorem addEdge_some_nodeLabelRoundTrip
    (g : Graph) (src dst : NodeId) (srcLabel dstLabel : String)
    (hWF : WellFormed Graph g)
    (g' : Graph)
    (hH : AddEdgeSuccessHyps g g' src dst srcLabel dstLabel) :
    ∀ n l, Interface.nodeLabel? g' n = some l → Interface.nodeOfLabel? g' l = some n := by
  -- TODO: complete HashMap insert/get? case analysis to show reverse-map consistency is preserved.
  -- Key idea:
  --   * if n = src or n = dst, both forward/reverse lookups are fixed by the two inserts;
  --   * otherwise, both lookups reduce to g and follow from hWF.nodeLabelRoundTrip.
  -- This remains the only non-acyclic “addEdge does not corrupt labels” obligation.
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
