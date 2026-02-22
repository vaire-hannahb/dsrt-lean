import Mathlib.Data.Finset.Basic

/-! # Basic Definitions -/

-- Signal strength values present on nodes
inductive Value where
  | strong_low   -- 0
  | weak_low     -- L
  | weak_high    -- H
  | strong_high  -- 1
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

-- Snapshot of the net at a single timestep
structure State (net : Net) where
  val : net.nodes → Value
  powered : net.nodes → Option Value
  powered_consistent : ∀ v w, powered v = some w → val v = w

/-! ## Connectivity -/

-- The two endpoints of a transistor, ignoring which is source and which is drain
def Transistor.endpoints (T : Transistor nodes) (a b : nodes) : Prop :=
  (T.source = a ∧ T.drain = b) ∨ (T.source = b ∧ T.drain = a)

-- Two nodes are connected when you can walk between them across transistors in the net that satisfy `active`.
-- Same definition covers A-connected, B-connected, and AB-connected.
inductive Connected (net : Net) (active : Transistor net.nodes → Prop) :
    net.nodes → net.nodes → Prop where
  | refl (v : net.nodes) :
      Connected net active v v
  | step {a b c : net.nodes}
      (h : ∃ T ∈ net.transistors, active T ∧ T.endpoints a b)
      (rest : Connected net active b c) :
      Connected net active a c

/-! ## Constraints -/

-- CON(A, B): B-connected nodes have the same logical value in B.
-- TODO A isn't used here, should it be? Doing it like this so it matches the paper, for now.
def CON {net : Net} (_A B : State net) : Prop :=
  ∀ u v, Connected net (fun T => T.isOn B.val) u v →
    logic (B.val u) = logic (B.val v)

-- REV0(A, B): weak reversibility. If a transistor's gate changes logically between A and B, its endpoints must agree in A and agree in B.
-- TODO: should endpoint comparison be logical equality or exact Value equality? As far as I remember, this was supposed to be literal since we're talking about a charging over a literal transistor gate, which is dangerous, not the natural roundoff and current to zero as you turn off a transistor.
def REV0 {net : Net} (A B : State net) : Prop :=
  ∀ T ∈ net.transistors,
    logic (A.val T.gate) ≠ logic (B.val T.gate) →
      A.val T.source = A.val T.drain ∧
      B.val T.source = B.val T.drain

-- REV1(A, B): path-to-charge. If a node changes between A and B, it must be AB-connected to a node powered in A, and AB-connected to a node powered in B.
-- TODO: should the change comparison be literal or logical? Using literal for now: even a strength change (e.g. 1→H) is a physical event that needs a charge path.
def REV1 {net : Net} (A B : State net) : Prop :=
  let ab_connected := Connected net (fun T => T.isOn A.val ∨ T.isOn B.val)
  ∀ v : net.nodes, A.val v ≠ B.val v →
    (∃ p, A.powered p ≠ none ∧ ab_connected v p) ∧
    (∃ q, B.powered q ≠ none ∧ ab_connected v q)

/-! ## Proof outline

-- define STAT

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
