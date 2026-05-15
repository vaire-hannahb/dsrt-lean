import Mathlib.Data.Finset.Basic

/-! # Definitions

    Basic mathematical objects encoding the transistor semantics:
    signal values, network topology, transistor behaviour, circuit state, and connectivity.
-/

/-! ## Signal values -/

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

-- Stronger of two values within the same logical polarity: strong beats weak.
-- Behaviour on mixed-polarity inputs is a no-op (short circuit territory).
def stronger : Value → Value → Value
  | .strong_high, .weak_high   => .strong_high
  | .weak_high,   .strong_high => .strong_high
  | .strong_low,  .weak_low    => .strong_low
  | .weak_low,    .strong_low  => .strong_low
  | v,            _            => v

-- pass never changes logical polarity
theorem logic_pass (t : TransistorType) (v : Value) : logic (pass t v) = logic v := by
  cases t <;> cases v <;> rfl

-- Normalise weak values to strong: weak_high → strong_high, weak_low → strong_low.
-- Used by the CLEAN phase of the algorithm.
def strongify : Value → Value
  | .weak_high => .strong_high
  | .weak_low  => .strong_low
  | v          => v

-- strongify never changes logical polarity
theorem logic_strongify (v : Value) : logic (strongify v) = logic v := by
  cases v <;> rfl

-- strongify always produces a strong value
theorem strongify_strong (v : Value) : strongify v = .strong_low ∨ strongify v = .strong_high := by
  cases v <;> first | exact Or.inl rfl | exact Or.inr rfl

-- logic is injective when both inputs are strong values
theorem logic_injective_on_strong {v1 v2 : Value}
    (h1 : v1 = .strong_low ∨ v1 = .strong_high)
    (h2 : v2 = .strong_low ∨ v2 = .strong_high)
    (heq : logic v1 = logic v2) : v1 = v2 := by
  rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl <;> simp_all [logic]

/-! ## State -/

-- Snapshot of the net at a single timestep
@[ext]
structure State (net : Net) where
  val : net.nodes → Value
  powered : net.nodes → Option Value
  powered_consistent : ∀ v w, powered v = some w → val v = w
  -- Externally powered nodes are always driven to strong values
  powered_strong : ∀ v w, powered v = some w → w = .strong_low ∨ w = .strong_high

/-! ## Connectivity -/

-- The two endpoints of a transistor, ignoring which is source and which is drain
def Transistor.endpoints (T : Transistor nodes) (a b : nodes) : Prop :=
  (T.source = a ∧ T.drain = b) ∨ (T.source = b ∧ T.drain = a)

-- Two nodes are connected when you can walk between them across transistors satisfying `active`.
-- Same definition covers A-connected, B-connected, and AB-connected.
inductive Connected (net : Net) (active : Transistor net.nodes → Prop) :
    net.nodes → net.nodes → Prop where
  | refl (v : net.nodes) :
      Connected net active v v
  | step {a b c : net.nodes}
      (h : ∃ T ∈ net.transistors, active T ∧ T.endpoints a b)
      (rest : Connected net active b c) :
      Connected net active a c

-- S-connected: connected through transistors on in state S
def ConnectedIn {net : Net} (S : State net) :=
  Connected net (fun T => T.isOn S.val)

-- AB-connected: connected in A AND connected in B (paths need not be the same)
def ABConnected {net : Net} (A B : State net) (u v : net.nodes) : Prop :=
  ConnectedIn A u v ∧ ConnectedIn B u v

-- Connectivity is determined by node values: states that agree pointwise have identical
-- connectivity. Used in correctness proofs to transfer ABConnected between equal-valued states.
lemma connectedIn_congr {net : Net} (B B' : State net)
    (h : ∀ v, B.val v = B'.val v) {u v : net.nodes} :
    ConnectedIn B u v ↔ ConnectedIn B' u v := by
  have aux : ∀ {S S' : State net}, (∀ v, S.val v = S'.val v) →
      ∀ {u v}, ConnectedIn S u v → ConnectedIn S' u v := by
    intro S S' hSS u v hconn
    induction hconn with
    | refl v => exact Connected.refl v
    | step hstep _ ih =>
      obtain ⟨T, hT_mem, hT_on, hT_ends⟩ := hstep
      refine Connected.step ⟨T, hT_mem, ?_, hT_ends⟩ ih
      cases T.type <;> simp only [Transistor.isOn] at hT_on ⊢ <;> rwa [← hSS T.gate]
  exact ⟨aux h, aux (fun v => (h v).symm)⟩
