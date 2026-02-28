# Source File Separation Policy

This project follows a strict separation of concerns for Lean source files:

- **Interface files** define signatures, classes, and API contracts.
- **Implementation files** define executable `def`/`instance` bodies.
- **Proof files** contain theorem statements and proofs.

## Rule

Do **not** mingle interface, implementation, and proofs in the same source file.

A single file should be dedicated to exactly one of these concerns.

## Recommended layout

For a feature `X`, use this structure:

- `X/Interface.lean`
- `X/Implementation.lean`
- `X/Proofs.lean`
- optional aggregator `X.lean` that only imports the three files

## Applied to Builder API

The `SpecialDAG` builder API now follows this split:

- `DagLeanLibrary/SpecialDAG/Builder/Interface.lean`
- `DagLeanLibrary/SpecialDAG/Builder/Implementation.lean`
- `DagLeanLibrary/SpecialDAG/Builder/Proofs.lean`
- `DagLeanLibrary/SpecialDAG/Builder.lean` (import-only aggregator)
