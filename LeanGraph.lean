import LeanGraph.Basic

structure node where
  name : Int
  deriving Repr, DecidableEq

structure edge where
  a : node
  b : node
  deriving Repr, DecidableEq

structure graph where
  edges : List edge
  deriving Repr

def node.eqv (n1: node) (n2: node) : Bool := n1.name = n2.name

def edge.rev (e : edge) : edge where
  a := e.b
  b := e.a

def edge.eqv (e1: edge) (e2: edge) : Bool := e1 = e2 ∨ e1.rev = e2

def edge.hasNode (e: edge) (n: node) : Bool := e.a.eqv n ∨ e.b.eqv n

def graph.hasEdge (e : edge) (g : graph) : Bool :=
  match he : g.edges with
  | [] => false
  | h :: t =>
    have : t.length < g.edges.length := by
      rw [he]
      simp
    e.eqv h ∨ hasEdge e {g with edges:= t}
termination_by g.edges.length

def graph.hasNode (n: node) (g: graph) : Bool :=
  match he : g.edges with
  | [] => false
  | h :: t =>
    have : t.length < g.edges.length := by
      rw [he]
      simp
    h.hasNode n ∨ hasNode n {g with edges:= t}
  termination_by g.edges.length


def nullName : Int := 0
def nullNode : node := {name := nullName}

def testNode : node := {name:= 1}
def testNode2 : node := {name:=2}
def testNode3 : node := {name:= 3}

def edge_1 : edge := {a:= testNode, b:= testNode2}
def edge_2 : edge := {a:=testNode2, b:=testNode3}
def edge_3 : edge := {a:=testNode3, b:=testNode}

def nullGraph : graph := {edges:=[]}
def example_graph : graph := {edges:=[edge_1, edge_2]}
