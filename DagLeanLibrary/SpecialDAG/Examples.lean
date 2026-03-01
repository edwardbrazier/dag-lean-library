import DagLeanLibrary.SpecialDAG.Proofs

namespace DagLeanLibrary
namespace SpecialDAG
namespace Graph

def demo : Graph :=
  { edges := [(0, 1), (1, 2), (0, 2)]
  , nodeLabels := (∅ : Std.HashMap NodeId String)
      |>.insert 0 "Root"
      |>.insert 1 "Middle"
      |>.insert 2 "Leaf"
  , labelToNode := (∅ : Std.HashMap String NodeId)
      |>.insert "Root" 0
      |>.insert "Middle" 1
      |>.insert "Leaf" 2
  }

/-- cycle: 0 → 1 → 0 -/
def cyclic : Graph :=
  { edges := [(0, 1), (1, 0)]
  , nodeLabels := (∅ : Std.HashMap NodeId String)
      |>.insert 0 "A"
      |>.insert 1 "B"
  , labelToNode := (∅ : Std.HashMap String NodeId)
      |>.insert "A" 0
      |>.insert "B" 1
  }

/-- isolated node: node 2 has no incident edge -/
def hasIsolatedNode : Graph :=
  { edges := [(0, 1)]
  , nodeLabels := (∅ : Std.HashMap NodeId String)
      |>.insert 0 "A"
      |>.insert 1 "B"
      |>.insert 2 "C"
  , labelToNode := (∅ : Std.HashMap String NodeId)
      |>.insert "A" 0
      |>.insert "B" 1
      |>.insert "C" 2
  }

/-- duplicate edge: violates simplicity -/
def hasParallelEdges : Graph :=
  { edges := [(0, 1), (0, 1)]
  , nodeLabels := (∅ : Std.HashMap NodeId String)
      |>.insert 0 "A"
      |>.insert 1 "B"
  , labelToNode := (∅ : Std.HashMap String NodeId)
      |>.insert "A" 0
      |>.insert "B" 1
  }

/-- bad reverse-map: violates label round-trip -/
def brokenLabelMap : Graph :=
  { edges := [(0, 1)]
  , nodeLabels := (∅ : Std.HashMap NodeId String)
      |>.insert 0 "A"
      |>.insert 1 "B"
  , labelToNode := (∅ : Std.HashMap String NodeId)
      |>.insert "A" 1
      |>.insert "B" 0
  }

#guard demo.nodeCount = 3
#guard demo.predecessors 2 = [1, 0]
#guard demo.successors 0 = [1, 2]
#guard demo.ancestorClosure 2 = [1, 0]
#guard demo.descendantClosure 0 = [1, 2]
#guard demo.nodeLabel? 1 = some "Middle"
#guard demo.nodeOfLabel? "Leaf" = some 2
#guard demo.checkWellFormed = true

#guard cyclic.checkWellFormed = false
#guard hasIsolatedNode.checkWellFormed = false
#guard hasParallelEdges.checkWellFormed = false
#guard brokenLabelMap.checkWellFormed = false

def wellFormedChecks : List (String × Bool) :=
  [ ("demo", demo.checkWellFormed)
  , ("cyclic", cyclic.checkWellFormed)
  , ("hasIsolatedNode", hasIsolatedNode.checkWellFormed)
  , ("hasParallelEdges", hasParallelEdges.checkWellFormed)
  , ("brokenLabelMap", brokenLabelMap.checkWellFormed)
  ]

#eval wellFormedChecks

end Graph
end SpecialDAG
end DagLeanLibrary
