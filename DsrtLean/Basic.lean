import Mathlib.Data.Finset.Basic

structure Node where
  id: Nat
  deriving Repr, BEq, Hashable, Ord

inductive TransistorType where
  | nmos
  | pmos
  deriving Repr, BEq, Hashable

structure Transistor (nodes: Finset Node) where -- argument enforces that all referenced nodes are part of a given set
  source: nodes
  gate: nodes
  drain : nodes
  type: TransistorType
  deriving Repr, BEq, Hashable

structure Net where
  nodes: Finset Node
  transistors : Finset (Transistor nodes)

inductive NodeState where
  | high
  | weak_high
  | weak_low
  | unknown

structure State (nodes: Finset Node) where
  map : nodes -> NodeState
  powered : nodes -> Bool
