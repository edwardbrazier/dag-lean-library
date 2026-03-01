import DagLeanLibrary.SpecialDAG.Builder.Proofs

namespace DagLeanLibrary
namespace SpecialDAG
namespace Graph

/-- A successful sequence of safe edge insertions. -/
def builtSuccessfully : Option Graph := do
  let g₁ ← addEdge empty 0 1 "Root" "Middle"
  let g₂ ← addEdge g₁ 1 2 "Middle" "Leaf"
  addEdge g₂ 0 2 "Root" "Leaf"

/-- Various `addEdge` outcomes: true = success (`some`), false = rejected (`none`). -/
def addEdgeAttemptResults : List (String × Bool) :=
  [ ("valid first edge", (addEdge empty 0 1 "A" "B").isSome)
  , ("valid chain extension", ((addEdge empty 0 1 "A" "B") >>= fun g => addEdge g 1 2 "B" "C").isSome)
  , ("reject cycle (1 -> 0 after 0 -> 1)", ((addEdge empty 0 1 "A" "B") >>= fun g => addEdge g 1 0 "B" "A").isSome)
  , ("reject parallel edge", ((addEdge empty 0 1 "A" "B") >>= fun g => addEdge g 0 1 "A" "B").isSome)
  , ("reject self-loop", (addEdge empty 7 7 "Self" "Self").isSome)
  , ("reject conflicting label assignment", ((addEdge empty 0 1 "A" "B") >>= fun g => addEdge g 2 3 "A" "D").isSome)
  ]

def builtSuccessfullyWellFormed : Option Bool :=
  builtSuccessfully.map checkWellFormed

#guard builtSuccessfully.isSome
#guard builtSuccessfullyWellFormed = some true

def main : IO Unit := do
  IO.println s!"Results from attempting to add edges: {addEdgeAttemptResults}"
  IO.println s!"Built successfully well-formed: {builtSuccessfullyWellFormed}"

end Graph
end SpecialDAG
end DagLeanLibrary

def main : IO Unit := DagLeanLibrary.SpecialDAG.Graph.main
