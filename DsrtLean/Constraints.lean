import DsrtLean.Basic

/-! # Constraints

    The semantic constraints on valid circuit transitions:
    CON, ADB, PTC, STAT, CLEAN, and the derived predicates CAP and DDC.
    Also `ValidNextState`, the full correctness specification, and
    the uniqueness theorem showing at most one valid next state exists.
-/

/-! ## Constraint definitions -/

-- CON(A, B): B-connected nodes have the same logical value in B.
-- TODO A isn't used here; keeping it to match the paper's signature.
def CON {net : Net} (_A B : State net) : Prop :=
  ∀ u v, ConnectedIn B u v → logic (B.val u) = logic (B.val v)

-- ADB(A, B): weak reversibility. If a transistor's gate changes logically between A and B,
-- its endpoints must agree in A and agree in B.
-- TODO: should endpoint comparison be logical equality or exact Value equality?
def ADB {net : Net} (A B : State net) : Prop :=
  ∀ T ∈ net.transistors,
    logic (A.val T.gate) ≠ logic (B.val T.gate) →
      A.val T.source = A.val T.drain ∧
      B.val T.source = B.val T.drain

-- PTC(A, B): path-to-charge. If a node changes between A and B, it must be AB-connected
-- to a node powered in A, and AB-connected to a node powered in B.
-- TODO: should the change comparison be literal or logical?
def PTC {net : Net} (A B : State net) : Prop :=
  ∀ v : net.nodes, A.val v ≠ B.val v →
    (∃ p, A.powered p ≠ none ∧ ABConnected A B v p) ∧
    (∃ q, B.powered q ≠ none ∧ ABConnected A B v q)

-- STAT(A, B): static operation. Every node in B is B-connected to a B-powered node.
-- TODO A isn't used here; keeping it to match the paper's signature.
def STAT {net : Net} (_A B : State net) : Prop :=
  ∀ v : net.nodes, ∃ p, B.powered p ≠ none ∧ ConnectedIn B v p

-- CLEAN(A, B): every node in B has a strong (non-degraded) value.
def CLEAN {net : Net} (_A B : State net) : Prop :=
  ∀ v : net.nodes, B.val v = .strong_low ∨ B.val v = .strong_high

/-! ## Derived predicates -/

-- CAP (connected-are-powered): if v is A-connected to a B-powered node p,
-- then logic(B(v)) = logic(B(p)).
-- Note: only logical equality — pass degrades strength, so exact equality fails.
def CAP {net : Net} (A B : State net) : Prop :=
  ∀ v p : net.nodes, ConnectedIn A v p → B.powered p ≠ none → logic (B.val v) = logic (B.val p)

-- DDC (disconnected-don't-change): if v is A-disconnected from every B-powered node,
-- then A(v) = B(v).
def DDC {net : Net} (A B : State net) : Prop :=
  ∀ v : net.nodes,
    (∀ p : net.nodes, B.powered p ≠ none → ¬ ConnectedIn A v p) →
    A.val v = B.val v

/-! ## Full correctness specification -/

/-- A state `B` is a valid next state for `(A, powered)` if it uses the given powered assignment
    and satisfies DDC, CAP, CLEAN, ADB, and PTC. CON follows from these and is not listed. -/
def ValidNextState {net : Net} (A B : State net) (powered : net.nodes → Option Value) : Prop :=
  B.powered = powered ∧
  DDC A B ∧ CAP A B ∧ CLEAN A B ∧
  ADB A B ∧ PTC A B

def ValidNextStateStat {net : Net} (A B : State net) (powered : net.nodes → Option Value) : Prop :=
  ValidNextState A B powered ∧ STAT A B

/-! ## Implication theorems -/

-- CON ∧ ADB implies CAP.
-- Proof: induction on the A-connection path from v to p.
--   Base case: v = p, trivial.
--   Inductive step: transistor T connects v to some intermediate node b, A-connected to p.
--     If T is on in B: v and b are B-connected, so CON gives logic(B(v)) = logic(B(b)).
--     If T is off in B: gate changed A→B, so ADB gives B(T.source) = B(T.drain).
--   Chain with the IH (logic(B(b)) = logic(B(p))) in both cases.
theorem con_adb_implies_cap {net : Net} (A B : State net)
    (hCON : CON A B) (hADB : ADB A B) : CAP A B := by
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
    · -- T switched off A→B: gate changed logically, so ADB gives B-value equality at endpoints
      have hgate : logic (A.val T.gate) ≠ logic (B.val T.gate) := by
        intro heq
        apply hT_on_B
        unfold Transistor.isOn at hT_on_A ⊢
        simp only [heq] at hT_on_A
        exact hT_on_A
      obtain ⟨-, hB_eq⟩ := hADB T hT_mem hgate
      rcases hT_ends with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact (congr_arg logic hB_eq).trans (ih hpow)
      · exact (congr_arg logic hB_eq.symm).trans (ih hpow)

-- PTC implies DDC.
-- Proof: contrapositive. If A(v) ≠ B(v), PTC gives a B-powered node q with ABConnected A B v q.
-- ABConnected implies A-connected, contradicting the hypothesis.
theorem ptc_implies_ddc {net : Net} (A B : State net)
    (hPTC : PTC A B) : DDC A B := by
  intro v hdisconn
  by_contra hne
  obtain ⟨-, q, hq_pow, hq_conn⟩ := hPTC v hne
  exact hdisconn q hq_pow hq_conn.1

-- Helper: a single transistor T on in B connecting u to w gives logic(B(u)) = logic(B(w)).
private lemma step_logic_eq {net : Net} (A B : State net)
    (hCON_A : CON A A) (hCAP : CAP A B) (hADB : ADB A B) (hDDC : DDC A B)
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
    · -- Neither u nor w is A-connected to any B-powered node; DDC + CON A A close
      have h_disconn_u : ∀ p : net.nodes, B.powered p ≠ none → ¬ ConnectedIn A u p :=
        fun p hp hc => h_pow_u ⟨p, hp, hc⟩
      have h_disconn_w : ∀ p : net.nodes, B.powered p ≠ none → ¬ ConnectedIn A w p :=
        fun p hp hc => h_pow_u ⟨p, hp, Connected.step ⟨T, hT_mem, hT_on_A, hT_ends⟩ hc⟩
      rw [← hDDC u h_disconn_u, ← hDDC w h_disconn_w]
      exact hCON_A u w (Connected.step ⟨T, hT_mem, hT_on_A, hT_ends⟩ (Connected.refl w))
  · -- T off in A, on in B: gate changed, so ADB gives B(source) = B(drain)
    have hgate : logic (A.val T.gate) ≠ logic (B.val T.gate) := by
      intro heq
      apply hT_on_A
      unfold Transistor.isOn at hT_on_B ⊢
      simp only [← heq] at hT_on_B
      exact hT_on_B
    obtain ⟨-, hB_eq⟩ := hADB T hT_mem hgate
    rcases hT_ends with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact congr_arg logic hB_eq
    · exact (congr_arg logic hB_eq).symm

-- CAP ∧ ADB ∧ PTC implies CON, given that A itself satisfies CON.
theorem cap_adb_ptc_implies_con {net : Net} (A B : State net)
    (hCON_A : CON A A)
    (hCAP : CAP A B)
    (hADB : ADB A B)
    (hPTC : PTC A B) : CON A B := by
  have hDDC := ptc_implies_ddc A B hPTC
  intro u v hconn
  induction hconn with
  | refl => rfl
  | step h rest ih =>
    obtain ⟨T, hT_mem, hT_on_B, hT_ends⟩ := h
    exact (step_logic_eq A B hCON_A hCAP hADB hDDC T hT_mem hT_on_B hT_ends).trans ih

/-! ## Uniqueness -/

theorem adb_symm {net : Net} (A B : State net) (hADB : ADB A B) : ADB B A := by
  intro T hT_mem hgate
  obtain ⟨hA, hB⟩ := hADB T hT_mem (Ne.symm hgate)
  exact ⟨hB, hA⟩

theorem ptc_symm {net : Net} (A B : State net) (hPTC : PTC A B) : PTC B A := by
  intro v hchange
  have hchange' : A.val v ≠ B.val v := Ne.symm hchange
  obtain ⟨⟨p, hp, hABp⟩, ⟨q, hq, hABq⟩⟩ := hPTC v hchange'
  refine ⟨?_, ?_⟩
  · exact ⟨q, hq, by simpa [ABConnected, and_left_comm, and_assoc, and_comm] using hABq⟩
  · exact ⟨p, hp, by simpa [ABConnected, and_left_comm, and_assoc, and_comm] using hABp⟩

/-- If (A, B) and (A, C) both satisfy DDC, CAP, and CLEAN, and assign the same powered values,
    then B and C are identical on every node. -/
theorem val_uniqueness {net : Net} (A B C : State net)
    (hpow     : B.powered = C.powered)
    (hDDC_B   : DDC A B) (hCAP_B : CAP A B) (hCLEAN_B : CLEAN A B)
    (hDDC_C   : DDC A C) (hCAP_C : CAP A C) (hCLEAN_C : CLEAN A C) :
    ∀ v : net.nodes, B.val v = C.val v := by
  intro v
  by_cases h_pow : ∃ p : net.nodes, B.powered p ≠ none ∧ ConnectedIn A v p
  · -- v is A-connected to a B/C-powered node p; powered_strong gives wp is strong.
    -- CAP: logic(B(v)) = logic(wp) = logic(C(v)); CLEAN lifts to exact equality.
    obtain ⟨p, hp_pow, hp_conn⟩ := h_pow
    have hCp : C.powered p ≠ none := by rwa [← congr_fun hpow p]
    cases hpp : B.powered p with
    | none => exact absurd hpp hp_pow
    | some wp =>
      have hpp_C : C.powered p = some wp := by rwa [← congr_fun hpow p]
      have hlog : logic (B.val v) = logic (C.val v) :=
        (hCAP_B v p hp_conn hp_pow).trans
          ((congr_arg logic ((B.powered_consistent p wp hpp).trans
              (C.powered_consistent p wp hpp_C).symm)).trans
            (hCAP_C v p hp_conn hCp).symm)
      exact logic_injective_on_strong (hCLEAN_B v) (hCLEAN_C v) hlog
  · -- v is A-disconnected from all B/C-powered nodes; DDC gives B(v) = A(v) = C(v)
    have h_disconn_B : ∀ p : net.nodes, B.powered p ≠ none → ¬ ConnectedIn A v p :=
      fun p hp hc => h_pow ⟨p, hp, hc⟩
    have h_disconn_C : ∀ p : net.nodes, C.powered p ≠ none → ¬ ConnectedIn A v p := by
      intro p hp hc; exact h_disconn_B p (by rwa [hpow]) hc
    exact (hDDC_B v h_disconn_B).symm.trans (hDDC_C v h_disconn_C)

/-- Forward uniqueness:
    if `B` and `C` share a powered assignment and each satisfy `CON`, `ADB`, `PTC`, and
    `CLEAN` relative to the same prior state `A`, then `B = C`. -/
theorem uniqueness_from_con_rev {net : Net} (A B C : State net)
    (hpow    : B.powered = C.powered)
    (_hCON_A : CON A A) (hCON_B : CON B B) (hCON_C : CON C C)
    (hCLEAN_B : CLEAN A B) (hCLEAN_C : CLEAN A C)
    (hADB_B : ADB A B) (hPTC_B : PTC A B)
    (hADB_C : ADB A C) (hPTC_C : PTC A C) :
    B = C := by
  have hDDC_B : DDC A B := ptc_implies_ddc A B hPTC_B
  have hDDC_C : DDC A C := ptc_implies_ddc A C hPTC_C
  have hCAP_B : CAP A B := con_adb_implies_cap A B hCON_B hADB_B
  have hCAP_C : CAP A C := con_adb_implies_cap A C hCON_C hADB_C
  apply State.ext
  · funext v
    exact val_uniqueness A B C hpow hDDC_B hCAP_B hCLEAN_B hDDC_C hCAP_C hCLEAN_C v
  · exact hpow

/-- Reverse uniqueness (Lemma 4 in the paper):
    if `B` and `C` share a powered assignment and each satisfy `CON`, `ADB`, `PTC`, and
    `CLEAN` relative to the same successor state `A`, then `B = C`. -/
theorem reverse_uniqueness {net : Net} (A B C : State net)
    (hpow    : B.powered = C.powered)
    (hCON_A : CON A A) (hCON_B : CON B B) (hCON_C : CON C C)
    (hCLEAN_B : CLEAN A B) (hCLEAN_C : CLEAN A C)
    (hADB_B : ADB B A) (hPTC_B : PTC B A)
    (hADB_C : ADB C A) (hPTC_C : PTC C A) :
    B = C := by
  exact uniqueness_from_con_rev A B C hpow hCON_A hCON_B hCON_C hCLEAN_B hCLEAN_C
    (adb_symm B A hADB_B) (ptc_symm B A hPTC_B)
    (adb_symm C A hADB_C) (ptc_symm C A hPTC_C)

/-! ## Counterexamples to the reverse implications -/

private def ceDrainNode : Node := ⟨0⟩
private def ceGateNode : Node := ⟨1⟩
private def ceSourceNode : Node := ⟨2⟩

private def ceNodes : Finset Node := {ceDrainNode, ceGateNode, ceSourceNode}

private lemma ceDrain_mem : ceDrainNode ∈ ceNodes := by
  simp [ceNodes]

private lemma ceGate_mem : ceGateNode ∈ ceNodes := by
  simp [ceNodes]

private lemma ceSource_mem : ceSourceNode ∈ ceNodes := by
  simp [ceNodes]

private def ceDrain : ceNodes := ⟨ceDrainNode, ceDrain_mem⟩
private def ceGate : ceNodes := ⟨ceGateNode, ceGate_mem⟩
private def ceSource : ceNodes := ⟨ceSourceNode, ceSource_mem⟩

private lemma ceNodes_cases (v : ceNodes) : v = ceDrain ∨ v = ceGate ∨ v = ceSource := by
  rcases v with ⟨v, hv⟩
  change v ∈ insert ceDrainNode (insert ceGateNode ({ceSourceNode} : Finset Node)) at hv
  rw [Finset.mem_insert] at hv
  rcases hv with rfl | hv
  · exact Or.inl rfl
  · rw [Finset.mem_insert] at hv
    rcases hv with rfl | hv
    · exact Or.inr <| Or.inl rfl
    · rw [Finset.mem_singleton] at hv
      exact Or.inr <| Or.inr (by cases hv; rfl)

private def ceNet : Net where
  nodes := ceNodes
  transistors := {{
    source := ceSource
    gate := ceGate
    drain := ceDrain
    type := .nmos
  }}

private def ceTrans : Transistor ceNet.nodes := {
  source := ceSource
  gate := ceGate
  drain := ceDrain
  type := .nmos
}

private lemma ceDrain_ne_gate : ceDrain ≠ ceGate := by decide
private lemma ceDrain_ne_source : ceDrain ≠ ceSource := by decide
private lemma ceGate_ne_source : ceGate ≠ ceSource := by decide

private lemma ceTrans_mem : ceTrans ∈ ceNet.transistors := by
  change ceTrans ∈ ({{
    source := ceSource
    gate := ceGate
    drain := ceDrain
    type := .nmos
  }} : Finset (Transistor ceNet.nodes))
  exact Finset.mem_singleton.mpr rfl

private lemma ceTrans_eq_of_mem {T : Transistor ceNet.nodes} (hT_mem : T ∈ ceNet.transistors) :
    T = ceTrans := by
  change T ∈ ({{
    source := ceSource
    gate := ceGate
    drain := ceDrain
    type := .nmos
  }} : Finset (Transistor ceNet.nodes)) at hT_mem
  exact Finset.mem_singleton.mp hT_mem

private def ceVal (vd vg vs : Value) : ceNet.nodes → Value
  | v =>
      match v.1.id with
      | 0 => vd
      | 1 => vg
      | _ => vs

private def cePow (pd pg ps : Option Value) : ceNet.nodes → Option Value
  | v =>
      match v.1.id with
      | 0 => pd
      | 1 => pg
      | _ => ps

@[simp] private lemma ceVal_drain (vd vg vs : Value) :
    ceVal vd vg vs ceDrain = vd := by
  simp [ceVal, ceDrain, ceDrainNode]

@[simp] private lemma ceVal_gate (vd vg vs : Value) :
    ceVal vd vg vs ceGate = vg := by
  rfl

@[simp] private lemma ceVal_source (vd vg vs : Value) :
    ceVal vd vg vs ceSource = vs := by
  rfl

@[simp] private lemma cePow_drain (pd pg ps : Option Value) :
    cePow pd pg ps ceDrain = pd := by
  simp [cePow, ceDrain, ceDrainNode]

@[simp] private lemma cePow_gate (pd pg ps : Option Value) :
    cePow pd pg ps ceGate = pg := by
  rfl

@[simp] private lemma cePow_source (pd pg ps : Option Value) :
    cePow pd pg ps ceSource = ps := by
  rfl

private def adbA : State ceNet where
  val := ceVal .strong_low .strong_low .strong_high
  powered := cePow (.some .strong_low) (.some .strong_low) (.some .strong_high)
  powered_consistent := by
    intro v w h
    rcases ceNodes_cases v with rfl | rfl | rfl
    · simpa using Option.some.inj h
    · simpa using Option.some.inj h
    · simpa using Option.some.inj h
  powered_strong := by
    intro v w h
    rcases ceNodes_cases v with rfl | rfl | rfl
    · exact Or.inl <| by simpa using (Option.some.inj h).symm
    · exact Or.inl <| by simpa using (Option.some.inj h).symm
    · exact Or.inr <| by simpa using (Option.some.inj h).symm

private def adbB : State ceNet where
  val := ceVal .strong_low .strong_high .strong_low
  powered := cePow (.some .strong_low) (.some .strong_high) (.some .strong_low)
  powered_consistent := by
    intro v w h
    rcases ceNodes_cases v with rfl | rfl | rfl
    · simpa using Option.some.inj h
    · simpa using Option.some.inj h
    · simpa using Option.some.inj h
  powered_strong := by
    intro v w h
    rcases ceNodes_cases v with rfl | rfl | rfl
    · exact Or.inl <| by simpa using (Option.some.inj h).symm
    · exact Or.inr <| by simpa using (Option.some.inj h).symm
    · exact Or.inl <| by simpa using (Option.some.inj h).symm

private def ptcA : State ceNet where
  val := ceVal .strong_low .strong_high .strong_low
  powered := cePow (.some .strong_low) (.some .strong_high) (.some .strong_low)
  powered_consistent := by
    intro v w h
    rcases ceNodes_cases v with rfl | rfl | rfl
    · simpa using Option.some.inj h
    · simpa using Option.some.inj h
    · simpa using Option.some.inj h
  powered_strong := by
    intro v w h
    rcases ceNodes_cases v with rfl | rfl | rfl
    · exact Or.inl <| by simpa using (Option.some.inj h).symm
    · exact Or.inr <| by simpa using (Option.some.inj h).symm
    · exact Or.inl <| by simpa using (Option.some.inj h).symm

private def ptcB : State ceNet where
  val := ceVal .strong_high .strong_low .strong_high
  powered := cePow none (.some .strong_low) (.some .strong_high)
  powered_consistent := by
    intro v w h
    rcases ceNodes_cases v with rfl | rfl | rfl
    · simp at h
    · simpa using Option.some.inj h
    · simpa using Option.some.inj h
  powered_strong := by
    intro v w h
    rcases ceNodes_cases v with rfl | rfl | rfl
    · simp at h
    · exact Or.inl <| by simpa using (Option.some.inj h).symm
    · exact Or.inr <| by simpa using (Option.some.inj h).symm

private lemma ceTrans_off_adbA : ¬ ceTrans.isOn adbA.val := by
  native_decide

private lemma ceTrans_on_adbB : ceTrans.isOn adbB.val := by
  native_decide

private lemma ceTrans_on_ptcA : ceTrans.isOn ptcA.val := by
  native_decide

private lemma ceTrans_off_ptcB : ¬ ceTrans.isOn ptcB.val := by
  native_decide

private lemma connected_eq_of_ceTrans_off {S : State ceNet} (hoff : ¬ ceTrans.isOn S.val)
    {u v : ceNet.nodes} (hconn : ConnectedIn S u v) : u = v := by
  induction hconn with
  | refl _ => rfl
  | step h _ _ =>
      obtain ⟨T, hT_mem, hT_on, _⟩ := h
      have hT : T = ceTrans := ceTrans_eq_of_mem hT_mem
      subst hT
      exact False.elim (hoff hT_on)

private lemma con_adbB : CON adbB adbB := by
  intro u v hconn
  induction hconn with
  | refl _ => rfl
  | @step a b c h rest ih =>
      obtain ⟨T, hT_mem, hT_on, hT_ends⟩ := h
      have hT : T = ceTrans := ceTrans_eq_of_mem hT_mem
      subst hT
      have hab : logic (adbB.val a) = logic (adbB.val b) := by
        rcases hT_ends with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> subst h1 <;> subst h2 <;> native_decide
      exact hab.trans ih

private lemma ddc_adb : DDC adbA adbB := by
  intro v hdisconn
  exact False.elim <| hdisconn v (by rcases ceNodes_cases v with rfl | rfl | rfl <;> simp [adbB]) (Connected.refl _)

private lemma cap_adb : CAP adbA adbB := by
  intro v p hconn hpow
  cases hconn with
  | refl _ => rfl
  | step h _ =>
      obtain ⟨T, hT_mem, hT_on, _⟩ := h
      have hT : T = ceTrans := ceTrans_eq_of_mem hT_mem
      subst hT
      exact False.elim (ceTrans_off_adbA hT_on)

private lemma not_adb_adb : ¬ ADB adbA adbB := by
  intro hADB
  have hgate : logic (adbA.val ceTrans.gate) ≠ logic (adbB.val ceTrans.gate) := by
    simp [adbA, adbB, ceTrans, logic]
  obtain ⟨hAeq, _⟩ := hADB ceTrans ceTrans_mem hgate
  simp [adbA, ceTrans] at hAeq

private lemma con_ptcB : CON ptcB ptcB := by
  intro u v hconn
  have hEq : u = v := connected_eq_of_ceTrans_off ceTrans_off_ptcB hconn
  subst hEq
  rfl

private lemma adb_ptc : ADB ptcA ptcB := by
  intro T hT_mem hgate
  have hT : T = ceTrans := ceTrans_eq_of_mem hT_mem
  subst hT
  refine ⟨?_, ?_⟩ <;> simp [ptcA, ptcB, ceTrans]

private lemma cap_ptc : CAP ptcA ptcB :=
  con_adb_implies_cap ptcA ptcB con_ptcB adb_ptc

private lemma ddc_ptc : DDC ptcA ptcB := by
  intro v hdisconn
  rcases ceNodes_cases v with rfl | rfl | rfl
  · exact False.elim <| hdisconn ceSource (by simp [ptcB]) <|
      Connected.step ⟨ceTrans, ceTrans_mem, ceTrans_on_ptcA, Or.inr ⟨rfl, rfl⟩⟩ (Connected.refl _)
  · exact False.elim <| hdisconn ceGate (by simp [ptcB]) (Connected.refl _)
  · exact False.elim <| hdisconn ceSource (by simp [ptcB]) (Connected.refl _)

private lemma not_ptc_ptc : ¬ PTC ptcA ptcB := by
  intro hPTC
  have hchg : ptcA.val ceDrain ≠ ptcB.val ceDrain := by
    simp [ptcA, ptcB]
  obtain ⟨_, ⟨q, hqpow, hAB⟩⟩ := hPTC ceDrain hchg
  rcases ceNodes_cases q with rfl | rfl | rfl
  · exact hqpow rfl
  · have : ConnectedIn ptcB ceDrain ceGate := hAB.2
    have hEq : ceDrain = ceGate := connected_eq_of_ceTrans_off ceTrans_off_ptcB this
    exact ceDrain_ne_gate hEq
  · have : ConnectedIn ptcB ceDrain ceSource := hAB.2
    have hEq : ceDrain = ceSource := connected_eq_of_ceTrans_off ceTrans_off_ptcB this
    exact ceDrain_ne_source hEq

/-- There exist compliant states satisfying `CON`, `DDC`, and `CAP` but violating `ADB`. -/
theorem exists_con_ddc_cap_not_adb :
    ∃ (net : Net) (A B : State net),
      CON B B ∧ DDC A B ∧ CAP A B ∧ ¬ ADB A B := by
  refine ⟨ceNet, adbA, adbB, con_adbB, ddc_adb, cap_adb, not_adb_adb⟩

/-- There exist compliant states satisfying `CON`, `DDC`, and `CAP` but violating `PTC`. -/
theorem exists_con_ddc_cap_not_ptc :
    ∃ (net : Net) (A B : State net),
      CON B B ∧ DDC A B ∧ CAP A B ∧ ¬ PTC A B := by
  refine ⟨ceNet, ptcA, ptcB, con_ptcB, ddc_ptc, cap_ptc, not_ptc_ptc⟩
