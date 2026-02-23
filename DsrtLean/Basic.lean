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

-- S-connected: connected through transistors on in state S
def ConnectedIn {net : Net} (S : State net) :=
  Connected net (fun T => T.isOn S.val)

-- AB-connected: connected in A AND connected in B (paths need not be the same)
def ABConnected {net : Net} (A B : State net) (u v : net.nodes) : Prop :=
  ConnectedIn A u v ∧ ConnectedIn B u v

/-! ## Constraints -/

-- CON(A, B): B-connected nodes have the same logical value in B.
-- TODO A isn't used here, should it be? Doing it like this so it matches the paper, for now.
def CON {net : Net} (_A B : State net) : Prop :=
  ∀ u v, ConnectedIn B u v → logic (B.val u) = logic (B.val v)

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
  ∀ v : net.nodes, A.val v ≠ B.val v →
    (∃ p, A.powered p ≠ none ∧ ABConnected A B v p) ∧
    (∃ q, B.powered q ≠ none ∧ ABConnected A B v q)

-- STAT(A, B): static operation. Every node in B is B-connected to a B-powered node.
-- TODO A isn't used here, should it be? Doing it like this so it matches the paper, for now.
def STAT {net : Net} (_A B : State net) : Prop :=
  ∀ v : net.nodes, ∃ p, B.powered p ≠ none ∧ ConnectedIn B v p

-- CLEAN(A, B): every node in B has a strong (non-degraded) value.
def CLEAN {net : Net} (_A B : State net) : Prop :=
  ∀ v : net.nodes, B.val v = .strong_low ∨ B.val v = .strong_high

/-! ## Derived lemmas -/

-- CAP (connected-are-powered): if v is A-connected to a B-powered node p, then logic(B(v)) = logic(B(p)).
-- Note: only logical equality, not value equality — pass degrades strength so exact equality fails.
def CAP {net : Net} (A B : State net) : Prop :=
  ∀ v p : net.nodes, ConnectedIn A v p → B.powered p ≠ none → logic (B.val v) = logic (B.val p)

-- DDC (disconnected-don't-change): if v is A-disconnected from every B-powered node, then A(v) = B(v).
def DDC {net : Net} (A B : State net) : Prop :=
  ∀ v : net.nodes,
    (∀ p : net.nodes, B.powered p ≠ none → ¬ ConnectedIn A v p) →
    A.val v = B.val v

/-! ## Proof that lemmas follow from constraints -/

-- CON ∧ REV0 implies CAP.
-- Proof: induction on the A-connection path from v to p.
--   Base case: v = p, trivial.
--   Inductive step: transistor T connects v to some intermediate node b, which is A-connected to p.
--     If T is on in B: v and b are B-connected, so CON gives logic(B(v)) = logic(B(b)).
--     If T is off in B: gate changed A→B, so REV0 gives B(T.source) = B(T.drain).
--   Chain with the IH (logic(B(b)) = logic(B(p))) in both cases.
theorem con_rev0_implies_cap {net : Net} (A B : State net)
    (hCON : CON A B) (hREV0 : REV0 A B) : CAP A B := by
  intro v p hconn
  induction hconn with
  | refl => intro _; rfl
  | step h rest ih =>
    intro hpow
    obtain ⟨T, hT_mem, hT_on_A, hT_ends⟩ := h
    by_cases hT_on_B : T.isOn B.val
    · -- T still on in B: v and the next node are B-connected, CON applies
      have hB_conn : ConnectedIn B _ _ :=
        Connected.step ⟨T, hT_mem, hT_on_B, hT_ends⟩ (Connected.refl _)
      exact (hCON _ _ hB_conn).trans (ih hpow)
    · -- T switched off A→B: gate changed logically, so REV0 gives B-value equality at endpoints
      have hgate : logic (A.val T.gate) ≠ logic (B.val T.gate) := by
        intro heq
        apply hT_on_B
        unfold Transistor.isOn at hT_on_A ⊢
        simp only [heq] at hT_on_A
        exact hT_on_A
      obtain ⟨-, hB_eq⟩ := hREV0 T hT_mem hgate
      rcases hT_ends with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact (congr_arg logic hB_eq).trans (ih hpow)
      · exact (congr_arg logic hB_eq.symm).trans (ih hpow)

-- REV1 implies DDC.
-- Proof: contrapositive. If A(v) ≠ B(v), REV1 gives a B-powered node q with ABConnected A B v q.
-- ABConnected implies A-connected, contradicting the hypothesis that v is A-disconnected from all B-powered nodes.
theorem rev1_implies_ddc {net : Net} (A B : State net)
    (hREV1 : REV1 A B) : DDC A B := by
  intro v hdisconn
  by_contra hne
  obtain ⟨-, q, hq_pow, hq_conn⟩ := hREV1 v hne
  exact hdisconn q hq_pow hq_conn.1

-- CAP ∧ REV0 ∧ REV1 implies CON, given that A itself satisfies CON.
-- The CON A A hypothesis is needed for the case where a transistor is on in both A and B
-- but neither endpoint is A-connected to a B-powered node: DDC gives B(u) = A(u) and
-- B(w) = A(w), and CON A A gives logic(A(u)) = logic(A(w)).

-- Helper: a single transistor T on in B connecting u to w gives logic(B(u)) = logic(B(w)).
private lemma step_logic_eq {net : Net} (A B : State net)
    (hCON_A : CON A A) (hCAP : CAP A B) (hREV0 : REV0 A B) (hDDC : DDC A B)
    (T : Transistor net.nodes) (hT_mem : T ∈ net.transistors) (hT_on_B : T.isOn B.val)
    {u w : net.nodes} (hT_ends : T.endpoints u w) :
    logic (B.val u) = logic (B.val w) := by
  by_cases hT_on_A : T.isOn A.val
  · -- T on in both A and B: u and w are A-connected via T
    by_cases h_pow_u : ∃ p : net.nodes, B.powered p ≠ none ∧ ConnectedIn A u p
    · -- u is A-connected to a B-powered node p; w is too via the reversed T step
      obtain ⟨p, hp_pow, hp_conn_u⟩ := h_pow_u
      have hT_ends_rev : T.endpoints w u := by unfold Transistor.endpoints at *; tauto
      have hw_conn_p := Connected.step ⟨T, hT_mem, hT_on_A, hT_ends_rev⟩ hp_conn_u
      exact (hCAP u p hp_conn_u hp_pow).trans (hCAP w p hw_conn_p hp_pow).symm
    · -- Neither u nor w is A-connected to any B-powered node
      -- (if w were, u would be too via T, contradicting h_pow_u)
      have h_disconn_u : ∀ p : net.nodes, B.powered p ≠ none → ¬ ConnectedIn A u p :=
        fun p hp hc => h_pow_u ⟨p, hp, hc⟩
      have h_disconn_w : ∀ p : net.nodes, B.powered p ≠ none → ¬ ConnectedIn A w p :=
        fun p hp hc => h_pow_u ⟨p, hp, Connected.step ⟨T, hT_mem, hT_on_A, hT_ends⟩ hc⟩
      -- DDC gives B(u) = A(u) and B(w) = A(w); CON A A closes
      rw [← hDDC u h_disconn_u, ← hDDC w h_disconn_w]
      exact hCON_A u w (Connected.step ⟨T, hT_mem, hT_on_A, hT_ends⟩ (Connected.refl w))
  · -- T off in A, on in B: gate changed, so REV0 gives B(source) = B(drain)
    have hgate : logic (A.val T.gate) ≠ logic (B.val T.gate) := by
      intro heq
      apply hT_on_A
      unfold Transistor.isOn at hT_on_B ⊢
      simp only [← heq] at hT_on_B
      exact hT_on_B
    obtain ⟨-, hB_eq⟩ := hREV0 T hT_mem hgate
    rcases hT_ends with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact congr_arg logic hB_eq
    · exact (congr_arg logic hB_eq).symm

theorem cap_rev0_rev1_implies_con {net : Net} (A B : State net)
    (hCON_A : CON A A)
    (hCAP : CAP A B)
    (hREV0 : REV0 A B)
    (hREV1 : REV1 A B) : CON A B := by
  have hDDC := rev1_implies_ddc A B hREV1
  intro u v hconn
  induction hconn with
  | refl => rfl
  | step h rest ih =>
    obtain ⟨T, hT_mem, hT_on_B, hT_ends⟩ := h
    exact (step_logic_eq A B hCON_A hCAP hREV0 hDDC T hT_mem hT_on_B hT_ends).trans ih

-- Uniqueness: if (A, B) and (A, C) both satisfy DDC, CAP, and CLEAN, and assign the same powered values, then B and C are identical on every node.
theorem uniqueness {net : Net} (A B C : State net)
    (hpow     : B.powered = C.powered)
    (hDDC_B   : DDC A B) (hCAP_B : CAP A B) (hCLEAN_B : CLEAN A B)
    (hDDC_C   : DDC A C) (hCAP_C : CAP A C) (hCLEAN_C : CLEAN A C) :
    ∀ v : net.nodes, B.val v = C.val v := by
  sorry

/-! ## Proof outline

-- define dsrt_sim(A, powered) as a function implementing the simulation algorithm

-- define dsrt_sim(A, powered) as a function implementing the simulation algorithm

-- show if algo doesn't output error, output matches REV0, REV1, DDC, CAP
  -- deduce that therefore output matches CON, as REV0 ∧ REV1 ∧ CAP -> CON

-- show if algo outputs short-circuit, correct assignment is impossible

-- show if algo outputs REV0 or REV1 error, correct assignment is impossible
  -- relies on uniqueness given we've already generated DDC and CAP compliant
  -- assignment when we output REV0 or REV1 error

-- bonus: show algorithm is reversible
-/
