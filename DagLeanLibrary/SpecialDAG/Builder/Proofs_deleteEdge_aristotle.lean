/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 6ae4c0ad-c3c3-454a-83a2-afd3ccb92deb

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
-/

import DagLeanLibrary.SpecialDAG.Builder.Implementation


namespace DagLeanLibrary

namespace SpecialDAG

namespace Graph

/- Aristotle failed to find a proof. -/
/-- Any graph produced by successful `deleteEdge` from a well-formed graph
is itself well-formed. -/
theorem deleteEdge_some_wellFormed
    (g : Graph) (src dst : NodeId)
    (hWF : WellFormed Graph g)
    (g' : Graph)
    (h : deleteEdge g src dst = some g') :
    WellFormed Graph g' := by
  sorry

end Graph

end SpecialDAG

end DagLeanLibrary