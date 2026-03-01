# DagLeanLibrary

A Lean 4 starter library for a **labeled simple DAG**.

## What this models

This project defines an interface for directed acyclic graphs with these constraints:

- no directed cycles
- no isolated nodes (every node has at least one incident edge)
- unique node labels (`String` labels)
- simple directed edges (at most one edge per ordered pair `(u, v)`)

> Note: edges are **not** labeled in this model.

The implementation uses:

- `edges : List (NodeId × NodeId)`
- `nodeLabels : HashMap NodeId String`
- `labelToNode : HashMap String NodeId`

## File layout (clean code/proof split)

- `DagLeanLibrary/SpecialDAG/Interface.lean`: abstract operations + invariant spec
- `DagLeanLibrary/SpecialDAG/Implementation.lean`: executable data structure + functions
- `DagLeanLibrary/SpecialDAG/Proofs.lean`: proofs about implementation/checker soundness
- `DagLeanLibrary/SpecialDAG/Examples.lean`: `#guard` checks + `#eval` output for well-formedness checks
- `DagLeanLibrary/SpecialDAG/Builder/Examples.lean`: `addEdge` construction examples (successful and rejected)

## Terminology

- **predecessor** = node with an edge into a node (`p → n`)
- **successor** = node with an edge out of a node (`n → c`)
- “no node has zero edges” = **no isolated nodes**

## Existing Lean ecosystem notes

Useful related abstractions in mathlib include:

- `Mathlib.Combinatorics.SimpleGraph` (mostly undirected simple graphs)
- quiver/category-theory-oriented directed edge machinery

A custom representation is still useful here because this project needs domain-specific
operations and constraints (predecessor/successor closure, no isolates, label lookup).

## Environment setup

Use the provided setup script, which installs required tools (`elan`, Lean toolchain, `lake`),
fetches dependencies, and builds the project:

```bash
./scripts/setup-lean-env.sh
```

If the script is not executable in your environment, run:

```bash
bash ./scripts/setup-lean-env.sh
```

## Build and run

Build the project:

```bash
lake build
```

Run the executable:

```bash
lake exe dagleanlibrary
```

## Running the examples

### 1) Existing graph well-formedness examples

Execute:

```bash
lake env lean DagLeanLibrary/SpecialDAG/Examples.lean
```

This file includes `#guard` assertions and evaluates `wellFormedChecks`, reporting
which sample graphs are well formed.

### 2) Builder examples using verified `addEdge`

Execute:

```bash
lake env lean DagLeanLibrary/SpecialDAG/Builder/Examples.lean
```

This file demonstrates:

- successful graph construction via multiple valid `addEdge` calls
- unsuccessful construction attempts that are rejected (`none`) for invalid operations:
  - cycle creation
  - parallel edge insertion
  - self-loop insertion
  - conflicting label assignment

The file prints `addEdgeAttemptResults` and whether the successfully built graph is
well formed.

## Tests in Lean

Yes. You can use:

- `#guard` assertions for lightweight checks
- `#eval` for executable exploration
- theorem statements/proofs for formal guarantees

This project currently follows “tests first, proofs later”, with additional soundness
proofs showing that `checkWellFormed = true` implies the corresponding checked properties
on the executable node/list domain.
