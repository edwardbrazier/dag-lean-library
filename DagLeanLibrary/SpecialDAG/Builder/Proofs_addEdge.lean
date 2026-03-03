import DagLeanLibrary.SpecialDAG.Builder.Implementation
import DagLeanLibrary.SpecialDAG.Builder.Spec
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
            simp [hHead]
        | inr hTail =>
            by_cases hEq : x == a
            · have hxa : x = a := LawfulBEq.eq_of_beq hEq
              simp [hxa]
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
            set_option linter.unnecessarySimpa false in
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

private theorem closureFrom_nil_frontier (next : NodeId → List NodeId) (fuel : Nat) :
    closureFrom next fuel [] [] = [] := by
  cases fuel <;> simp [closureFrom]

private theorem descendantClosure_eq_nil_of_successors_eq_nil
    (g : Graph) (n : NodeId) (h : g.successors n = []) :
    g.descendantClosure n = [] := by
  unfold descendantClosure closureFrom
  simp [h, closureFrom_nil_frontier]

private theorem successors_eq_nil_of_not_mem_sources
    (g : Graph) (n : NodeId) (h : n ∉ g.edges.map Prod.fst) :
    g.successors n = [] := by
  unfold successors
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro x hx
  rcases List.mem_filterMap.mp (mem_of_mem_eraseDups _ _ hx) with ⟨e, heMem, heEq⟩
  rcases e with ⟨src, dst⟩
  have hSrc : src = n := by
    by_cases hBeq : src == n
    · exact LawfulBEq.eq_of_beq hBeq
    · simp [hBeq] at heEq
  have hIn : n ∈ g.edges.map Prod.fst := by
    exact List.mem_map.mpr ⟨(src, dst), heMem, by simp [hSrc]⟩
  exact h hIn

private theorem not_mem_descendantClosure_of_not_mem_sources
    (g : Graph) (n : NodeId) (h : n ∉ g.edges.map Prod.fst) :
    n ∉ g.descendantClosure n := by
  rw [descendantClosure_eq_nil_of_successors_eq_nil g n
      (successors_eq_nil_of_not_mem_sources g n h)]
  simp

/-! ## Well-formedness of `empty` -/

private theorem descendantClosure_empty (n : NodeId) :
    descendantClosure empty n = [] := by
  rfl

theorem empty_wellFormed_proof : empty_wellFormed := by
  unfold empty_wellFormed
  exact {
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
  hAcyclicOnSources :
    ∀ x, x ∈ (g.edges.map Prod.fst ++ [src]).eraseDups →
      x ∉ ({ edges := g.edges ++ [(src, dst)],
             nodeLabels  := g.nodeLabels  |>.insert src srcLabel |>.insert dst dstLabel,
             labelToNode := g.labelToNode |>.insert srcLabel src |>.insert dstLabel dst } : Graph).descendantClosure x
  hResult    : g' = { edges := g.edges ++ [(src, dst)],
                      nodeLabels  := g.nodeLabels  |>.insert src srcLabel |>.insert dst dstLabel,
                      labelToNode := g.labelToNode |>.insert srcLabel src |>.insert dstLabel dst }

private theorem addEdge_some_iff (g : Graph) (src dst : NodeId) (srcLabel dstLabel : String)
    (g' : Graph) (h : addEdge g src dst srcLabel dstLabel = some g') :
    AddEdgeSuccessHyps g g' src dst srcLabel dstLabel := by
  simp [addEdge] at h
  rcases h with ⟨hNotSelf, hNotInClos, hNotParallel, hSrcLblOk, hDstLblOk,
    hSrcFwdOk, hDstFwdOk, hLblsDiff, hAcyclicOnSources, hResult⟩
  exact {
    hNotSelf := hNotSelf
    hNotInClos := hNotInClos
    hNotParallel := hNotParallel
    hSrcLblOk := hSrcLblOk
    hDstLblOk := hDstLblOk
    hSrcFwdOk := hSrcFwdOk
    hDstFwdOk := hDstFwdOk
    hLblsDiff := hLblsDiff
    hAcyclicOnSources := hAcyclicOnSources
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
  rcases hH with ⟨_, _, _, _, _, _, _, _, _, hResult⟩
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
  rcases hH with ⟨hNotSelf, _, _, hSrcLblOk, hDstLblOk, _, _, hLblsDiff, _, hResult⟩
  subst hResult
  intro n l hnLbl
  by_cases hDst : n = dst
  · subst n
    have hl : dstLabel = l := by
      simpa [Interface.nodeLabel?, nodeLabel?, Std.HashMap.getElem?_insert] using hnLbl
    have hl' : l = dstLabel := hl.symm
    subst l
    have hNotEq : (srcLabel == dstLabel) = false := by
      apply Bool.eq_false_iff.2
      intro hEq
      exact hLblsDiff (LawfulBEq.eq_of_beq hEq)
    simp [Interface.nodeOfLabel?, nodeOfLabel?, hNotEq]
  · by_cases hSrc : n = src
    · subst n
      have hNotSelf' : dst ≠ src := by
        intro hEq
        exact hNotSelf hEq.symm
      have hNotSelfBeq : (dst == src) = false := by
        apply Bool.eq_false_iff.2
        intro hEq
        exact hNotSelf' (LawfulBEq.eq_of_beq hEq)
      have hnLbl' : ((g.nodeLabels.insert src srcLabel).insert dst dstLabel)[src]? = some l := by
        simpa [Interface.nodeLabel?, nodeLabel?] using hnLbl
      have hSrcLbl :
          ((g.nodeLabels.insert src srcLabel).insert dst dstLabel)[src]? = some srcLabel := by
        rw [Std.HashMap.getElem?_insert]
        simp [hNotSelfBeq]
      have hl : l = srcLabel := by
        have : some l = some srcLabel := hnLbl'.symm.trans hSrcLbl
        exact Option.some.inj this
      subst l
      have hNotEq : (dstLabel == srcLabel) = false := by
        apply Bool.eq_false_iff.2
        intro hEq
        exact hLblsDiff (LawfulBEq.eq_of_beq hEq).symm
      have hLookup : Interface.nodeOfLabel?
          ({ edges := g.edges ++ [(src, dst)]
           , nodeLabels := (g.nodeLabels.insert src srcLabel).insert dst dstLabel
           , labelToNode := (g.labelToNode.insert srcLabel src).insert dstLabel dst } : Graph)
          srcLabel
          = some src := by
        change ((g.labelToNode.insert srcLabel src).insert dstLabel dst)[srcLabel]? = some src
        rw [Std.HashMap.getElem?_insert]
        simp [hNotEq]
      simpa using hLookup
    · have hSrc' : src ≠ n := by simpa [eq_comm] using hSrc
      have hDst' : dst ≠ n := by simpa [eq_comm] using hDst
      have hOldLbl : g.nodeLabels[n]? = some l := by
        simpa [Interface.nodeLabel?, nodeLabel?, Std.HashMap.getElem?_insert, hSrc', hDst']
          using hnLbl
      have hOldRound : g.labelToNode[l]? = some n :=
        hWF.nodeLabelRoundTrip n l (by simpa [Interface.nodeLabel?, nodeLabel?] using hOldLbl)
      have hLNeSrc : l ≠ srcLabel := by
        intro hEq
        have hOldSrc : g.labelToNode[srcLabel]? = some n := by simpa [hEq] using hOldRound
        have hMemSrc : srcLabel ∈ g.labelToNode := by
          exact (Std.HashMap.mem_iff_isSome_getElem?).2 (Option.isSome_of_eq_some hOldSrc)
        have hSrcMap : g.labelToNode[srcLabel]? = some src := hSrcLblOk hMemSrc
        have : n = src := hWF.uniqueNodeLabels srcLabel n src hOldSrc hSrcMap
        exact hSrc this
      have hLNeDst : l ≠ dstLabel := by
        intro hEq
        have hOldDst : g.labelToNode[dstLabel]? = some n := by simpa [hEq] using hOldRound
        have hMemDst : dstLabel ∈ g.labelToNode := by
          exact (Std.HashMap.mem_iff_isSome_getElem?).2 (Option.isSome_of_eq_some hOldDst)
        have hDstMap : g.labelToNode[dstLabel]? = some dst := hDstLblOk hMemDst
        have : n = dst := hWF.uniqueNodeLabels dstLabel n dst hOldDst hDstMap
        exact hDst this
      have hNeDst : (dstLabel == l) = false := by
        apply Bool.eq_false_iff.2
        intro hEq
        exact hLNeDst (LawfulBEq.eq_of_beq hEq).symm
      have hNeSrc : (srcLabel == l) = false := by
        apply Bool.eq_false_iff.2
        intro hEq
        exact hLNeSrc (LawfulBEq.eq_of_beq hEq).symm
      simpa [Interface.nodeOfLabel?, nodeOfLabel?, Std.HashMap.getElem?_insert, hNeDst, hNeSrc]
        using hOldRound

-- ── acyclic for addEdge ───────────────────────────────────────────────────────

private theorem addEdge_some_acyclic
    (g : Graph) (src dst : NodeId) (srcLabel dstLabel : String)
    (_hWF : WellFormed Graph g)
    (g' : Graph)
    (hH : AddEdgeSuccessHyps g g' src dst srcLabel dstLabel) :
    ∀ n, n ∉ Interface.descendantClosure g' n := by
  rcases hH with ⟨_, _, _, _, _, _, _, _, hAcyclicOnSources, hResult⟩
  subst hResult
  intro n
  by_cases hMem : n ∈ (g.edges.map Prod.fst ++ [src]).eraseDups
  · exact hAcyclicOnSources n hMem
  · apply not_mem_descendantClosure_of_not_mem_sources
    intro hIn
    have hIn' : n ∈ g.edges.map Prod.fst ++ [src] := by
      simpa using hIn
    exact hMem (mem_eraseDups_of_mem _ _ hIn')

/-! ## Master theorem -/

/-- Any graph produced by `addEdge` from a well-formed graph is itself well-formed. -/
theorem addEdge_some_wellFormed_proof : addEdge_some_wellFormed := by
  intro g src dst srcLabel dstLabel hWF g' h
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
