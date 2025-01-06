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
  deriving Repr, DecidableEq

structure path where
  nodes : List node
  deriving Repr, DecidableEq

def edge.rev (e : edge) : edge where
  a := e.b
  b := e.a

def node.eqv (n1: node) (n2: node) : Bool := n1.name = n2.name

def edge.eqv (e1: edge) (e2: edge) : Bool := e1 = e2 ∨ e1.rev = e2

def edge.hasNode (e: edge) (n: node) : Bool := e.a.eqv n ∨ e.b.eqv n

def edge.listNodes (e: edge) : List node := [e.a, e.b]

theorem edgeHasAlwaysTwoNodes : ∀e : edge, (e.listNodes.length = 2) := by
  intro e; unfold edge.listNodes; simp;

def edge.otherNode (e: edge) (n: node) : node :=
  let other := (e.listNodes.filter (fun node : node => ¬(n.eqv node)));
  have : 0 < other.length := by sorry;
  other[0]

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

def graph.filterSameEdges (e: edge) (g: graph) : List edge := g.edges.filter (fun edge : edge => e.eqv edge)

def graph.ocurrencesOfEdge (e: edge) (g: graph) : Int := (g.filterSameEdges e).length

def graph.edgeIsUnique (e: edge) (g: graph) : Bool := (g.filterSameEdges e) = [e]

def graph.isProper (g: graph) : Bool := g.edges.all g.edgeIsUnique

def graph.incidentEdgesOnNode (n: node) (g: graph) : List edge := g.edges.filter (fun e : edge => e.hasNode n)

def graph.allNeighborsOfNode (n: node) (g: graph) : List node := ((g.incidentEdgesOnNode n).map (fun e : edge => e.otherNode n)).flatten

def graph.areNeighbors (n1: node) (n2: node) (g: graph) : Bool := g.edges.any (fun e : edge =>
  have possibleEdge : edge := {a:= n1, b:= n2}; e.eqv possibleEdge
)

def path.isProper (g: graph) (p: path) : Bool :=
  match he : p.nodes with
  | [] => true
  | _ :: [] => true
  | h :: h₁ :: t =>
    have : (h₁::t).length < p.nodes.length := by
      rw [he]
      simp
  g.areNeighbors h h₁ ∧ isProper g {p with nodes:=h₁::t}
  termination_by p.nodes.length



def graph.acessibleFromNode (g: graph) (n: node) : List edge :=
  let bfs (current: node) (unvisited: List edge) (result: List edge) : List edge :=
    let neighbors : List node := g.allNeighborsOfNode current;
    let currentVisitedEdges : List edge := g.incidentEdgesOnNode current;
    let newUnvisitedEdges : List edge := unvisited.removeAll currentVisitedEdges;
    let result := currentVisitedEdges ++ (newUnvisitedEdges.map (fun e : edge =>
      bfs (e.otherNode current)
    )).flatten

  -- Unfinished...


def nullName : Int := 0
def nullNode : node := {name := nullName}

def testNode : node := {name:= 1}
def testNode2 : node := {name:=2}
def testNode3 : node := {name:= 3}

def edge_1 : edge := {a:= testNode, b:= testNode2}
def edge_2 : edge := {a:=testNode2, b:=testNode3}
def edge_3 : edge := {a:=testNode3, b:=testNode}

def nullGraph : graph := {edges:=[]}
def example_graph : graph := {edges:=[edge_1, edge_2, edge_3]}
def example_path : path := {nodes:=[testNode, testNode2]}

#eval example_graph.edgeIsUnique edge_1
#eval example_path.isProper example_graph
#eval ([edge_1] ++ [edge_2])
