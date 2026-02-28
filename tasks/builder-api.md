# Task: Correct-by-Construction Graph Builder API

## What Was Asked

Add a set of "smart constructor" functions for building `Graph` values such that any graph produced by those functions is provably well-formed (`WellFormed`), and prove that formally in Lean 4.

---

## Current State

A new file [`DagLeanLibrary/SpecialDAG/Builder.lean`](../DagLeanLibrary/SpecialDAG/Builder.lean) has been created and added to the top-level import in [`DagLeanLibrary.lean`](../DagLeanLibrary.lean). The file **does not yet compile** — it is mid-way through being fixed.

### What is in Builder.lean right now

**Smart constructors (complete and correct):**

- `Graph.empty : Graph` — the empty graph (no nodes, no edges, no labels)
- `Graph.addEdge (g : Graph) (src dst : NodeId) (srcLabel dstLabel : String) : Option Graph` — safely adds a directed edge `src → dst`, returning `none` if any `WellFormed` invariant would be violated

The `addEdge` function checks eight guards before accepting an edge:
1. `src ≠ dst` (no self-loops)
2. `src ∉ descendantClosure g dst` (no cycles)
3. `(src, dst) ∉ g.edges` (no parallel edges)
4. `srcLabel` not already bound to a different node
5. `dstLabel` not already bound to a different node
6. `src` not already labeled differently
7. `dst` not already labeled differently
8. `srcLabel ≠ dstLabel` (two distinct nodes cannot share a label)

**Theorems (partially written, not yet compiling):**

| Theorem | Status | Notes |
|---|---|---|
| `simpleAdjacency_always` | Blocked | Needs `nodup_eraseDups` which doesn't exist in Lean 4 v4.28.0 core |
| `uniqueNodeLabels_always` | Should work | Trivial from `Option.some.inj` |
| `descendantClosure_empty` | Should work | `rfl` once `closureFrom` private issue fixed |
| `empty_wellFormed` | Partially works | Interface unfold issues remain |
| `addEdge_some_noIsolatedNodes` | Partially written | Needs correct Lean 4 list API |
| `addEdge_some_nodeLabelRoundTrip` | `sorry` (planned) | Requires HashMap insert lemmas |
| `addEdge_some_acyclic` | `sorry` (planned) | Requires BFS completeness proof — significant future work |
| `addEdge_some_wellFormed` | `sorry` (planned) | Master theorem, assembles the above |

---

## Compilation Errors to Fix

The current `lake build` fails with these categories of error:

### 1. Missing standard library lemmas
Lean 4 v4.28.0 core does **not** include:
- `List.nodup_eraseDups` — needed for `simpleAdjacency_always`
- `List.mem_eraseDups` — needed for `noIsolatedNodes` proof
- `List.eraseDups_sublist` — needed for subset monotonicity argument

**Fix:** Prove these locally:
- `mem_of_mem_eraseDups : x ∈ l.eraseDups → x ∈ l` — by well-founded recursion on `l.length`, using `List.eraseDups_cons` and `List.mem_filter`
- `mem_eraseDups_of_mem : x ∈ l → x ∈ l.eraseDups` — same approach
- `nodup_eraseDups : l.eraseDups.Nodup` — from `mem_of_mem_eraseDups` + `List.mem_filter`

The `eraseDups_cons` theorem *does* exist:
```lean
theorem List.eraseDups_cons [BEq α] {a : α} {as : List α} :
    (a :: as).eraseDups = a :: (as.filter fun b => !b == a).eraseDups
```

### 2. `closureFrom` is private
`closureFrom` is declared `private` in `Implementation.lean`, so it cannot be referenced by name in `Builder.lean`. The fix is to use `rfl` for `descendantClosure_empty` (the definition reduces by computation) and `show n ∉ g.descendantClosure n` to restate the goal without needing the Interface wrapper.

### 3. `Interface.descendantClosure` rewrite issue
`Interface.descendantClosure g n` is accessed through the typeclass instance (shown as `instInterface.5 empty n` in errors). The fix is to replace `rw [Interface.descendantClosure, ...]` with `show n ∉ empty.descendantClosure n` or `simp only [Interface.descendantClosure]`.

### 4. `AddEdgeSuccessHyps` structure
The helper structure `AddEdgeSuccessHyps` was used to bundle guard hypotheses, but its proof (`addEdge_some_iff`) failed because `split_ifs` doesn't work cleanly on the Bool-guarded `if-then-else` chain. The fix is to drop this structure and use `sorry` for `addEdge_some_wellFormed` directly, or restructure the guard extraction.

### 5. `List.mem_filterMap` notation
The `⟨..., ..., ...⟩` anonymous constructor notation doesn't work for `List.Mem` (which has multiple constructors). Fix: use `List.mem_filterMap.mpr ⟨_, h1, h2⟩` instead.

---

## Plan Going Forward

### Step 1 — Prove the three missing list lemmas locally (private)
```lean
private theorem mem_of_mem_eraseDups [BEq α] [LawfulBEq α] :
    ∀ (l : List α) (x : α), x ∈ l.eraseDups → x ∈ l
-- termination_by l.length, using eraseDups_cons + mem_filter

private theorem mem_eraseDups_of_mem [BEq α] [LawfulBEq α] :
    ∀ (l : List α) (x : α), x ∈ l → x ∈ l.eraseDups
-- termination_by l.length, using eraseDups_cons + mem_filter

private theorem nodup_eraseDups [BEq α] [LawfulBEq α] :
    ∀ (l : List α), l.eraseDups.Nodup
-- induction using eraseDups_cons, mem_of_mem_eraseDups, mem_filter
```

### Step 2 — Fix `simpleAdjacency_always`
Use `nodup_eraseDups` directly.

### Step 3 — Fix `empty_wellFormed`
- Use `rfl` for `descendantClosure empty n = []`
- Use `show` to restate goals in terms of concrete functions rather than Interface methods
- The five invariants all hold vacuously for the empty graph

### Step 4 — Fix `noIsolatedNodes` proof for `addEdge`
Use `List.mem_filterMap.mpr`, `mem_eraseDups_of_mem`, and `List.ne_nil_of_mem` (which does exist).

### Step 5 — Add `sorry` for `nodeLabelRoundTrip` and `acyclic`
These are the two planned sorries. Add clear comments explaining the proof strategy and what is needed to complete them.

### Step 6 — Assemble `addEdge_some_wellFormed`
Once Steps 1–5 are done, the master theorem can be assembled.

---

## Future Work (to eliminate the sorry for acyclicity)

Proving `addEdge_some_acyclic` requires three sub-lemmas about `closureFrom`:

1. **Transitivity**: `x ∈ descendantClosure g y → y ∈ descendantClosure g z → x ∈ descendantClosure g z`
2. **Monotonicity**: Adding edges only enlarges the closure
3. **Completeness**: The fuel bound `nodeCount g + 1` is sufficient to visit all reachable nodes in an acyclic graph — this requires defining an inductive `Reachable` predicate

A suggested approach: add a new file `DagLeanLibrary/SpecialDAG/Reachability.lean` defining `Reachable` as an inductive proposition, prove completeness there, then use it in Builder.lean.

---

## Existing Proven Properties (in Proofs.lean)

For reference, what was already proved before this task began:

- `atMostOneNodePerLabel` — reverse label map is injective (any Graph)
- `checkWellFormed_eq` / `checkWellFormed_true_iff` — structure of the runtime checker
- `checkWellFormed_true_implies_acyclicOnNodes` — checker soundness for acyclicity
- `checkWellFormed_true_implies_incidentEdgeOnNodes` — checker soundness for isolated nodes
- `checkWellFormed_true_implies_noParallelEdges` — checker soundness for parallel edges
- `checkWellFormed_true_implies_labelRoundTripOnListedPairs` — checker soundness for labels
