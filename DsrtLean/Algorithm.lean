import DsrtLean.Constraints

/-! # Algorithm

    The relational simulation step: `SimStepRelation` is the headline of this module.
    It characterises the output of the DSRT simulation algorithm as a relation on
    initial states and powered assignments, with each constructor corresponding to
    one outcome of the pseudocode.

    Supporting definitions built up in order:
    - `Drives`: flood-fill value propagation from powered seeds
    - `ShortCircuit`: conflicting drives reaching the same node
    - `ValidFloodFill`: postcondition of phases 1–3 (flood fill + DDC + CLEAN)
    - `SimResult`: the simulation result type
    - `SimStepRelation`: the headline
-/

/-! ## Flood-fill value propagation -/

-- `Drives net A powered v w` holds when, seeding from `powered` and stepping through
-- transistors on in A, value w can be driven onto node v.
-- The `pass T.type w` in the step case mirrors `drive ← pass(T, B(near))` in the pseudocode.
inductive Drives (net : Net) (A : State net) (powered : net.nodes → Option Value) :
    net.nodes → Value → Prop where
  | direct {v w} :
      powered v = some w →
      Drives net A powered v w
  | step {near far : net.nodes} (T : Transistor net.nodes) (w : Value) :
      T ∈ net.transistors →
      T.isOn A.val →
      T.endpoints near far →
      Drives net A powered near w →
      Drives net A powered far (pass T.type w)

/-! ## Short circuit -/

-- Combined source lemma: a driven value traces back to a single powered node that is
-- both the origin of the logical polarity AND A-connected to the driven node.
-- The powered source is guaranteed to be a strong value (by the State invariant).
private lemma drives_src {net : Net} {A : State net} {powered : net.nodes → Option Value}
    (hstrong : ∀ v w, powered v = some w → w = .strong_low ∨ w = .strong_high)
    {v : net.nodes} {w : Value} (h : Drives net A powered v w) :
    ∃ (p : net.nodes) (wp : Value),
      powered p = some wp ∧ logic w = logic wp ∧ ConnectedIn A v p ∧
      (wp = .strong_low ∨ wp = .strong_high) := by
  induction h with
  | direct hpow =>
    exact ⟨_, _, hpow, rfl, Connected.refl _, hstrong _ _ hpow⟩
  | step T _ hT_mem hT_on hT_ends _ ih =>
    obtain ⟨p, wp, hpow, hlog, hconn, hwp⟩ := ih
    refine ⟨p, wp, hpow, by rw [logic_pass]; exact hlog,
            Connected.step ⟨T, hT_mem, hT_on, ?_⟩ hconn, hwp⟩
    rcases hT_ends with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inr ⟨h1, h2⟩
    · exact Or.inl ⟨h1, h2⟩

-- Node-local short circuit witness: opposite-polarity drives reach the same node v.
def ShortCircuitAt {net : Net} (A : State net) (powered : net.nodes → Option Value)
    (v : net.nodes) : Prop :=
  ∃ (w₁ w₂ : Value),
    Drives net A powered v w₁ ∧
    Drives net A powered v w₂ ∧
    logic w₁ ≠ logic w₂

-- A short circuit occurs when some node has a node-local witness.
-- Depends only on A and the powered assignment — B need not be constructed.
def ShortCircuit {net : Net} (A : State net) (powered : net.nodes → Option Value) : Prop :=
  ∃ v : net.nodes, ShortCircuitAt A powered v

-- A short circuit makes CAP unsatisfiable: two A-connected B-powered nodes would need
-- different logical values in B, but CAP forces them to agree via the common node v.
theorem shortCircuit_no_cap {net : Net} (A B : State net) (powered : net.nodes → Option Value)
    (hpow : B.powered = powered) (hSC : ShortCircuit A powered) : ¬ CAP A B := by
  obtain ⟨v, w₁, w₂, hd1, hd2, hne⟩ := hSC
  obtain ⟨p1, wp1, hpp1, hl1, hconn1, _⟩ :=
    drives_src (fun v w h => B.powered_strong v w (hpow ▸ h)) hd1
  obtain ⟨p2, wp2, hpp2, hl2, hconn2, _⟩ :=
    drives_src (fun v w h => B.powered_strong v w (hpow ▸ h)) hd2
  intro hCAP
  have hBp1 : B.powered p1 ≠ none := by simp [hpow, hpp1]
  have hBp2 : B.powered p2 ≠ none := by simp [hpow, hpp2]
  have hBval_p1 : B.val p1 = wp1 := B.powered_consistent p1 wp1 (hpow ▸ hpp1)
  have hBval_p2 : B.val p2 = wp2 := B.powered_consistent p2 wp2 (hpow ▸ hpp2)
  have heq : logic wp1 = logic wp2 := by
    rw [← hBval_p1, ← hBval_p2]
    exact (hCAP v p1 hconn1 hBp1).symm.trans (hCAP v p2 hconn2 hBp2)
  exact hne (hl1.trans (heq.trans hl2.symm))

-- A short circuit means no valid next state can exist, regardless of reversibility checks.
theorem shortCircuit_no_validNextState {net : Net} (A : State net)
    (powered : net.nodes → Option Value) (hSC : ShortCircuit A powered) :
    ¬ ∃ B : State net, ValidNextState A B powered := by
  intro ⟨B, hB⟩
  exact shortCircuit_no_cap A B powered hB.1 hSC hB.2.2.1

/-! ## Flood-fill postcondition -/

/-- ValidFloodFillPreClean: postcondition of phases 1–2 (flood fill + handle unknowns).
    DDC and CAP hold; CLEAN not yet enforced — weak values may be present. -/
def ValidFloodFillPreClean {net : Net} (A B : State net) (powered : net.nodes → Option Value) : Prop :=
  B.powered = powered ∧ DDC A B ∧ CAP A B

/-- ValidFloodFill: B satisfies the powered assignment, DDC, CAP, and CLEAN.
    This is the postcondition of phases 1–3 of the algorithm (flood fill, DDC fill, CLEAN),
    and the precondition for the ADB and PTC checks in phases 4 and 5.
    Strictly weaker than ValidNextState: reversibility is not yet checked. -/
def ValidFloodFill {net : Net} (A B : State net) (powered : net.nodes → Option Value) : Prop :=
  B.powered = powered ∧
  DDC A B ∧ CAP A B ∧ CLEAN A B


-- ValidFloodFill is exactly the non-reversibility prefix of ValidNextState.
theorem validNextState_implies_validFloodFill {net : Net} (A B : State net)
    (powered : net.nodes → Option Value) (h : ValidNextState A B powered) :
    ValidFloodFill A B powered :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩

-- Supplying ADB and PTC on top of ValidFloodFill recovers ValidNextState.
theorem validFloodFill_rev0_rev1 {net : Net} (A B : State net)
    (powered : net.nodes → Option Value)
    (hVF : ValidFloodFill A B powered) (hR0 : ADB A B) (hR1 : PTC A B) :
    ValidNextState A B powered :=
  ⟨hVF.1, hVF.2.1, hVF.2.2.1, hVF.2.2.2, hR0, hR1⟩

/-! ## Simulation result type -/

/-- The result of a single simulation timestep.
  - `ok B`: successful transition to state `B`
  - `shortCircuit v`: opposite-polarity drives conflict at node `v`
  - `rev0Error T`: transistor `T` switches while its endpoints disagree (weak reversibility violated)
  - `rev1Error v`: node `v` changes value without an AB-connected charge path (path-to-charge violated)
-/
inductive SimResult (net : Net) where
  | ok           : State net → SimResult net
  | shortCircuit : net.nodes → SimResult net
  | staticError  : net.nodes → SimResult net
  | rev0Error    : Transistor net.nodes → SimResult net
  | rev1Error    : net.nodes → SimResult net

/-! ## Simulation step relation -/

/-- SimStepRelation: the relational characterisation of the simulation algorithm's output.
    `requireStatic` selects whether the optional STAT check is enforced.
    Each constructor corresponds to one pseudocode phase outcome, in the same order as the
    pseudocode.

    - `shortCircuit`: flood fill detects conflicting drives (phase 1 fails)
    - `rev0Error`:    flood fill succeeded; ADB check fails (phase 4 fails)
    - `rev1Error`:    ADB passed; PTC check fails (phase 5 fails)
    - `ok`:           all phases passed

    Correctness theorems (soundness, per-error impossibility, completeness, uniqueness)
    are in `Correctness.lean`. -/
inductive SimStepRelation {net : Net} (requireStatic : Bool)
    (A : State net) (powered : net.nodes → Option Value) :
    SimResult net → Prop where
  /-- Phase 1 (flood fill) failed: conflicting drives detected.
      The payload `v` is the conflicted node itself. -/
  | shortCircuit {v : net.nodes} :
      ShortCircuitAt A powered v →
      SimStepRelation requireStatic A powered (.shortCircuit v)
  /-- Phases 1–3 succeeded; phase 2 (STAT check) failed.
      v is not B-connected to any B-powered node. Only fires when static operation is enforced.
      Precondition is ValidFloodFill (phases 1–3 complete, including CLEAN). -/
  | staticError {B : State net} {v : net.nodes} :
      requireStatic = true →
      ¬ ShortCircuit A powered →
      ValidFloodFill A B powered →
      (∀ p, B.powered p ≠ none → ¬ ConnectedIn B v p) →
      SimStepRelation requireStatic A powered (.staticError v)
  /-- Phases 1–3 succeeded; phase 4 (ADB check) failed.
      T witnesses the violation: the conditions are exactly ¬ (T's contribution to ADB A B). -/
  | rev0Error {B : State net} {T : Transistor net.nodes} :
      ¬ ShortCircuit A powered →
      ValidFloodFill A B powered →
      T ∈ net.transistors →
      logic (A.val T.gate) ≠ logic (B.val T.gate) →
      (A.val T.source ≠ A.val T.drain ∨ B.val T.source ≠ B.val T.drain) →
      SimStepRelation requireStatic A powered (.rev0Error T)
  /-- Phases 1–4 succeeded; phase 5 (PTC check) failed.
      v witnesses the violation: A.val v ≠ B.val v and v lacks an AB-connected charge path.
      The two disjuncts correspond to the two halves of the PTC conjunction. -/
  | rev1Error {B : State net} {v : net.nodes} :
      ¬ ShortCircuit A powered →
      ValidFloodFill A B powered →
      ADB A B →
      A.val v ≠ B.val v →
      ((∀ p, A.powered p ≠ none → ¬ ABConnected A B v p) ∨
       (∀ q, B.powered q ≠ none → ¬ ABConnected A B v q)) →
      SimStepRelation requireStatic A powered (.rev1Error v)
  /-- All phases succeeded. -/
  | ok {B : State net} :
      ¬ ShortCircuit A powered →
      ValidFloodFill A B powered →
      ADB A B →
      PTC A B →
      (requireStatic = false ∨ STAT A B) →
      SimStepRelation requireStatic A powered (.ok B)

-- Under ValidFloodFill, the next state is determined uniquely by A and the powered assignment.
-- Used in the per-error impossibility proofs in Correctness.lean.
theorem validFloodFill_uniqueness {net : Net} (A B C : State net)
    (powered : net.nodes → Option Value)
    (hB : ValidFloodFill A B powered) (hC : ValidFloodFill A C powered) :
    ∀ v, B.val v = C.val v :=
  val_uniqueness A B C (hB.1.trans hC.1.symm)
    hB.2.1 hB.2.2.1 hB.2.2.2 hC.2.1 hC.2.2.1 hC.2.2.2
