import DagLeanLibrary

open DagLeanLibrary.SpecialDAG

def main : IO Unit :=
  IO.println s!"Demo node count: {Graph.demo.nodeCount}"
