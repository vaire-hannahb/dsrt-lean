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

structure State (net: Net) where
  map : net.nodes -> NodeState
  powered : net.nodes -> Bool

-- define connectivity in a state

-- define CON, REV0, REV1, STAT

-- define CAP, DDC

-- show CON ∧ REV0 ∧ REV1 -> CAP

-- show CON ∧ REV0 ∧ REV1 -> DDC

-- show CAP ∧ REV0 ∧ REV1 -> CON

-- show uniqueness: if A, B and A, C both satisfy DDC and CAP, then B = C

-- define dsrt_sim(A, powered) as a function implementing the simulation algorithm

-- show if algo doesn't output error, output matches REV0, REV1, DDC, CAP
  -- deduce that therefore output matches CON, as REV0 ∧ REV1 ∧ CAP -> CON

-- show if algo outputs short-circuit, correct assignment is impossible

-- show if algo outputs REV0 or REV1 error, correct assignment is impossible
  -- relies on uniqueness given we've already generated DDC and CAP compliant assignment when we output REV0 or REV1 error

-- bonus: show algorithm is reversible
