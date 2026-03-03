import DagLeanLibrary.SpecialDAG.Builder.Implementation
import DagLeanLibrary.SpecialDAG.Builder.Spec
import DagLeanLibrary.SpecialDAG.Builder.Proofs_addEdge

namespace DagLeanLibrary
namespace SpecialDAG
namespace Graph

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

private theorem eraseDups_ne_nil_of_ne_nil [BEq α] :
    ∀ {xs : List α}, xs ≠ [] → xs.eraseDups ≠ [] := by
  intro xs h
  cases xs with
  | nil => contradiction
  | cons a as =>
      simp [List.eraseDups_cons]

private theorem getElem?_filter_eq_some_iff
    [BEq α] [Hashable α] [LawfulBEq α]
    (m : Std.HashMap α β) (f : α → β → Bool) (k : α) (v : β) :
    (m.filter f)[k]? = some v ↔ m[k]? = some v ∧ f k v = true := by
  rw [Std.HashMap.getElem?_filter' (m := m) (f := f) (k := k)]
  cases m[k]? <;> simp

private theorem deleteEdge_some_acyclic
    (g : Graph) (src dst : NodeId)
    (_hWF : WellFormed Graph g)
    (g' : Graph)
    (h : deleteEdge g src dst = some g') :
    ∀ n, n ∉ Interface.descendantClosure g' n := by
  intro n
  unfold deleteEdge at h
  by_cases hEdge : (!decide ((src, dst) ∈ g.edges)) = true
  · simp [hEdge] at h
  · simp [hEdge] at h
    rcases h with ⟨hAcyclicOnSources, hResult⟩
    subst hResult
    by_cases hMem : n ∈ ((g.edges.erase (src, dst)).map Prod.fst).eraseDups
    · exact hAcyclicOnSources n hMem
    · apply not_mem_descendantClosure_of_not_mem_sources
      intro hIn
      exact hMem (mem_eraseDups_of_mem _ _ hIn)

private theorem deleteEdge_some_noIsolatedNodes
    (g : Graph) (src dst : NodeId)
    (_hWF : WellFormed Graph g)
    (g' : Graph)
    (h : deleteEdge g src dst = some g') :
    ∀ n, Interface.nodeLabel? g' n ≠ none →
      Interface.predecessors g' n ≠ [] ∨ Interface.successors g' n ≠ [] := by
  intro n hn
  unfold deleteEdge at h
  by_cases hEdge : (!decide ((src, dst) ∈ g.edges)) = true
  · simp [hEdge] at h
  · simp [hEdge] at h
    rcases h with ⟨_, hResult⟩
    subst hResult
    have hKeep :
        (g.edges.erase (src, dst)).any (fun (u, v) => u == n || v == n) = true := by
      have hNodeLbl :
          (Std.HashMap.filter
            (fun n _ => (g.edges.erase (src, dst)).any (fun (u, v) => u == n || v == n))
            g.nodeLabels)[n]? ≠ none := by
        simpa [Interface.nodeLabel?, nodeLabel?] using hn
      have hFilter :
          (Std.HashMap.filter
            (fun n _ => (g.edges.erase (src, dst)).any (fun (u, v) => u == n || v == n))
            g.nodeLabels)[n]? =
          (g.nodeLabels[n]?).filter
            (fun _ => (g.edges.erase (src, dst)).any (fun (u, v) => u == n || v == n)) := by
        exact
          (Std.HashMap.getElem?_filter' (m := g.nodeLabels)
            (f := fun n _ => (g.edges.erase (src, dst)).any (fun (u, v) => u == n || v == n))
            (k := n))
      rw [hFilter] at hNodeLbl
      cases hAny : (g.edges.erase (src, dst)).any (fun (u, v) => u == n || v == n) with
      | false =>
          simp [hAny] at hNodeLbl
      | true =>
          rfl
    rcases List.any_eq_true.mp hKeep with ⟨e, heMem, heAny⟩
    rcases e with ⟨u, v⟩
    have hUV : (u == n) = true ∨ (v == n) = true := by
      simpa [Bool.or_eq_true] using heAny
    cases hUV with
    | inl hu =>
        right
        have hRawMem :
            v ∈ (g.edges.erase (src, dst)).filterMap
                  (fun (s, d) => if s == n then some d else none) := by
          exact List.mem_filterMap.mpr ⟨(u, v), heMem, by simp [hu]⟩
        have hRawNe :
            (g.edges.erase (src, dst)).filterMap
              (fun (s, d) => if s == n then some d else none) ≠ [] :=
          List.ne_nil_of_mem hRawMem
        have hSuccNe :
            ((g.edges.erase (src, dst)).filterMap
              (fun (s, d) => if s == n then some d else none)).eraseDups ≠ [] :=
          eraseDups_ne_nil_of_ne_nil hRawNe
        simpa [Interface.successors, successors] using hSuccNe
    | inr hv =>
        left
        have hRawMem :
            u ∈ (g.edges.erase (src, dst)).filterMap
                  (fun (s, d) => if d == n then some s else none) := by
          exact List.mem_filterMap.mpr ⟨(u, v), heMem, by simp [hv]⟩
        have hRawNe :
            (g.edges.erase (src, dst)).filterMap
              (fun (s, d) => if d == n then some s else none) ≠ [] :=
          List.ne_nil_of_mem hRawMem
        have hPredNe :
            ((g.edges.erase (src, dst)).filterMap
              (fun (s, d) => if d == n then some s else none)).eraseDups ≠ [] :=
          eraseDups_ne_nil_of_ne_nil hRawNe
        simpa [Interface.predecessors, predecessors] using hPredNe

private theorem deleteEdge_some_nodeLabelRoundTrip
    (g : Graph) (src dst : NodeId)
    (hWF : WellFormed Graph g)
    (g' : Graph)
    (h : deleteEdge g src dst = some g') :
    ∀ n l, Interface.nodeLabel? g' n = some l →
      Interface.nodeOfLabel? g' l = some n := by
  intro n l hnLbl
  unfold deleteEdge at h
  by_cases hEdge : (!decide ((src, dst) ∈ g.edges)) = true
  · simp [hEdge] at h
  · simp [hEdge] at h
    rcases h with ⟨_, hResult⟩
    subst hResult
    let m' : Std.HashMap NodeId String :=
      Std.HashMap.filter
        (fun n _ => (g.edges.erase (src, dst)).any (fun (u, v) => u == n || v == n))
        g.nodeLabels
    let swapped : List (String × NodeId) := m'.toList.map (fun (n, lbl) => (lbl, n))
    have hNodeLbl : m'[n]? = some l := by
      simpa [m', Interface.nodeLabel?, nodeLabel?] using hnLbl
    have hOldLbl : g.nodeLabels[n]? = some l :=
      (getElem?_filter_eq_some_iff g.nodeLabels
        (fun n _ => (g.edges.erase (src, dst)).any (fun (u, v) => u == n || v == n)) n l).1 hNodeLbl |>.1
    have hOldRound : g.labelToNode[l]? = some n :=
      hWF.nodeLabelRoundTrip n l (by simpa [Interface.nodeLabel?, nodeLabel?] using hOldLbl)
    have hMemNode : (n, l) ∈ m'.toList := by
      exact (Std.HashMap.mem_toList_iff_getElem?_eq_some).2 hNodeLbl
    have hMemSwap : (l, n) ∈ swapped := by
      refine List.mem_map.mpr ?_
      exact ⟨(n, l), hMemNode, by simp⟩
    have hPairKeys : m'.toList.Pairwise (fun a b => (a.1 == b.1) = false) := by
      exact Std.HashMap.distinct_keys_toList (m := m')
    have hPairLabels : m'.toList.Pairwise (fun a b => (a.2 == b.2) = false) := by
      refine hPairKeys.imp_of_mem ?_
      intro a b ha hb hKeyNe
      apply Bool.eq_false_iff.2
      intro hLblEq
      have haLbl : m'[a.1]? = some a.2 :=
        (Std.HashMap.mem_toList_iff_getElem?_eq_some).1 ha
      have hbLbl : m'[b.1]? = some b.2 :=
        (Std.HashMap.mem_toList_iff_getElem?_eq_some).1 hb
      have haOld : g.nodeLabels[a.1]? = some a.2 :=
        (getElem?_filter_eq_some_iff g.nodeLabels
          (fun n _ => (g.edges.erase (src, dst)).any (fun (u, v) => u == n || v == n))
          a.1 a.2).1 haLbl |>.1
      have hbOld : g.nodeLabels[b.1]? = some b.2 :=
        (getElem?_filter_eq_some_iff g.nodeLabels
          (fun n _ => (g.edges.erase (src, dst)).any (fun (u, v) => u == n || v == n))
          b.1 b.2).1 hbLbl |>.1
      have haRound : g.labelToNode[a.2]? = some a.1 :=
        hWF.nodeLabelRoundTrip a.1 a.2 (by simpa [Interface.nodeLabel?, nodeLabel?] using haOld)
      have hbRound : g.labelToNode[b.2]? = some b.1 :=
        hWF.nodeLabelRoundTrip b.1 b.2 (by simpa [Interface.nodeLabel?, nodeLabel?] using hbOld)
      have hKeyEq : a.1 = b.1 := by
        have hLblEq' : a.2 = b.2 := LawfulBEq.eq_of_beq hLblEq
        have hbRound' : g.labelToNode[a.2]? = some b.1 := by simpa [hLblEq'] using hbRound
        exact hWF.uniqueNodeLabels a.2 a.1 b.1 haRound hbRound'
      have hKeyBeqTrue : (a.1 == b.1) = true := by simp [hKeyEq]
      exact Bool.false_ne_true (hKeyNe.symm.trans hKeyBeqTrue)
    have hDistinctSwap :
        swapped.Pairwise (fun a b => (a.1 == b.1) = false) := by
      refine (List.pairwise_map (l := m'.toList)
        (f := fun p : NodeId × String => (p.2, p.1))
        (R := fun a b : String × NodeId => (a.1 == b.1) = false)).2 ?_
      simpa using hPairLabels
    have hLookup : (Std.HashMap.ofList swapped)[l]? = some n := by
      exact Std.HashMap.getElem?_ofList_of_mem (k := l) (k' := l) (k_beq := by simp)
        (distinct := hDistinctSwap) (mem := hMemSwap)
    simpa [swapped, m', Interface.nodeOfLabel?, nodeOfLabel?] using hLookup

/-- Any graph produced by successful `deleteEdge` from a well-formed graph
is itself well-formed. -/
theorem deleteEdge_some_wellFormed_proof : deleteEdge_some_wellFormed := by
  intro g src dst hWF g' h
  refine
    { acyclic := deleteEdge_some_acyclic g src dst hWF g' h
      noIsolatedNodes := deleteEdge_some_noIsolatedNodes g src dst hWF g' h
      simpleAdjacency := simpleAdjacency_always g'
      uniqueNodeLabels := uniqueNodeLabels_always g'
      nodeLabelRoundTrip := deleteEdge_some_nodeLabelRoundTrip g src dst hWF g' h }

end Graph
end SpecialDAG
end DagLeanLibrary
