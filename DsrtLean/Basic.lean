import Mathlib.Data.Finset.Basic

/-! # Basic Definitions

Structures and functions for the DSRT transistor semantics.
No theorems here — just the vocabulary. -/

-- Signal strength values present on nodes
inductive Value where
  | strong_low   -- 0: driven low by power rail or pMOS
  | weak_low     -- L: degraded low through nMOS
  | weak_high    -- H: degraded high through pMOS
  | strong_high  -- 1: driven high by power rail or nMOS
  deriving Repr, DecidableEq

-- Logical interpretation of a signal value
inductive LogicLevel where
  | low
  | high
  deriving Repr, DecidableEq

def logic : Value → LogicLevel
  | .strong_low  => .low
  | .weak_low    => .low
  | .weak_high   => .high
  | .strong_high => .high

/-! ## Network topology -/

structure Node where
  id : Nat
  deriving Repr, DecidableEq

inductive TransistorType where
  | nmos
  | pmos
  deriving Repr, DecidableEq

structure Transistor (nodes : Finset Node) where
  source : nodes
  gate : nodes
  drain : nodes
  type : TransistorType
  deriving Repr

structure Net where
  nodes : Finset Node
  transistors : Finset (Transistor nodes)

/-! ## Transistor functions -/

-- Whether a transistor is on given a valuation of nodes
def Transistor.isOn (T : Transistor nodes) (s : nodes → Value) : Prop :=
  match T.type with
  | .nmos => logic (s T.gate) = .high
  | .pmos => logic (s T.gate) = .low

instance (T : Transistor nodes) (s : nodes → Value) : Decidable (T.isOn s) := by
  unfold Transistor.isOn
  cases T.type <;> exact inferInstance

-- Signal value after passing through a transistor that is on
def pass : TransistorType → Value → Value
  | .nmos, .strong_low  => .strong_low
  | .nmos, .weak_low    => .weak_low
  | .nmos, .weak_high   => .weak_high
  | .nmos, .strong_high => .weak_high    -- nMOS degrades strong high
  | .pmos, .strong_low  => .weak_low     -- pMOS degrades strong low
  | .pmos, .weak_low    => .weak_low
  | .pmos, .weak_high   => .weak_high
  | .pmos, .strong_high => .strong_high

/-! ## State -/

-- A well-formed snapshot of the net at a single timestep
structure State (net : Net) where
  map : net.nodes → Value
  powered : net.nodes → Option Value
  powered_consistent : ∀ v val, powered v = some val → map v = val

/-! ## Proof outline

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
  -- relies on uniqueness given we've already generated DDC and CAP compliant
  -- assignment when we output REV0 or REV1 error

-- bonus: show algorithm is reversible
-/
