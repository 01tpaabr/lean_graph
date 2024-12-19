import LeanGraph.Basic

def andFunction (a : Bool) (b : Bool) : Bool := a ∧ b
def orFunction (a : Bool) (b : Bool) : Bool := a ∨ b
def aggregEdges (el: List Edge) (el2 : List Edge) : List Edge := el ++ el2

structure node where
  name : Int

instance : Repr node where
  reprPrec ms _ := s!"Node(name: {ms.name})"

instance : ToString node where
  toString ms := s!"Node(name:{ms.name})"

structure edge where
  a : node
  b : node

instance : Repr edge where
reprPrec ms _ := s!"edge({ms.a}, {ms.b})"

instance : ToString edge where
  toString ms := s!"edge({ms.a}, {ms.b})"

structure graph where
  edges : List edge

instance : Repr graph where
  reprPrec ms _ := s!"Graph(edges: {ms.edges})"

def nodeIsEqual (n1: node) (n2: node) : Bool :=
  if n1.name = n2.name then true else false

def edgeIsEqual (e1: edge) (e2: edge) : Bool :=
  if (nodeIsEqual e1.a e2.a ∨ nodeIsEqual e1.a e2.b) ∧ (nodeIsEqual e1.b e2.a ∨ nodeIsEqual e1.b e2.b) then true else false

def edgeIsNotEqual (e1: edge) (e2:edge) : Bool := ¬(edgeIsEqual e1 e2)

def listWrapperEdgeIsEqual (e1:edge) (e2:edge) : List edge :=
  if edgeIsEqual e1 e2 then [e1] else []

-- Wrapper to handle termination problem with g.edges
def applyFunctionInDecreasingEdgeList {α : Type} {β : Type} (baseValue : β) (edges: List edge)
(composeFunction: β → β → β) (f: edge → α → β) (auxArg: α) : β :=
  match edges with
  | [] => baseValue
  | h :: t => composeFunction (f h auxArg) (applyFunctionInDecreasingEdgeList baseValue t composeFunction f auxArg)

def edgeIsUniqueInGraph (e: edge) (g: graph) : Bool :=
  applyFunctionInDecreasingEdgeList (true) (g.edges) (andFunction) (edgeIsNotEqual) (e)

def repeatedEdgesInGraph (e: edge) (g: graph) : List edge :=
  applyFunctionInDecreasingEdgeList ([]) (g.edges) (aggregEdges) (listWrapperEdgeIsEqual) (e)


def nullName : Int := 0
def nullNode : node := {name := nullName}

def testNode : node := {name:= 1}
def testNode2 : node := {name:=2}
def testNode3 : node := {name:= 3}

def edge_1 : edge := {a:= testNode, b:= testNode2}
def edge_2 : edge := {a:=testNode2, b:=testNode3}

def nullGraph : graph := {edges:=[]}
def example_graph : graph := {edges:=[edge_1, edge_2]}

#eval repeatedEdgesInGraph edge_1 example_graph
