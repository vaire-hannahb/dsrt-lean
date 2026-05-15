import DsrtLean.Algorithm

/-! # Correctness

    Soundness, per-error impossibility, completeness, and uniqueness for `SimStepRelation`.
-/

-- Soundness: the ok constructor directly gives a valid next state.
theorem simStepRelation_ok_sound {net : Net} (A B : State net)
    (powered : net.nodes → Option Value) (requireStatic : Bool)
    (h : SimStepRelation requireStatic A powered (.ok B)) : ValidNextState A B powered := by
  cases h with
  | ok _ hVF hR0 hR1 _ => exact validFloodFill_rev0_rev1 A B powered hVF hR0 hR1

-- CON is preserved: if A satisfies CON A A, the ok output satisfies CON A B.
theorem simStepRelation_ok_con {net : Net} (A B : State net)
    (powered : net.nodes → Option Value) (requireStatic : Bool)
    (hA : CON A A) (h : SimStepRelation requireStatic A powered (.ok B)) : CON A B := by
  cases h with
  | ok _ hVF hR0 hR1 _ =>
    exact cap_rev0_rev1_implies_con A B hA hVF.2.2.1 hR0 hR1

-- A short circuit means no valid next state exists.
theorem simStepRelation_shortCircuit_no_valid {net : Net} (A : State net)
    (powered : net.nodes → Option Value) (requireStatic : Bool) (v : net.nodes)
    (h : SimStepRelation requireStatic A powered (.shortCircuit v)) :
    ¬ ∃ B : State net, ValidNextState A B powered := by
  cases h with
  | shortCircuit hSC =>
    exact shortCircuit_no_validNextState A powered ⟨v, hSC⟩

-- A rev0Error means no valid next state exists.
-- The unique ValidFloodFill state already fails ADB, so no candidate can satisfy ValidNextState.
theorem simStepRelation_rev0Error_no_valid {net : Net} (A : State net)
    (powered : net.nodes → Option Value) (requireStatic : Bool) (T : Transistor net.nodes)
    (h : SimStepRelation requireStatic A powered (.rev0Error T)) :
    ¬ ∃ B : State net, ValidNextState A B powered := by
  cases h with
  | rev0Error _ hVF hT_mem hgate hends =>
    intro ⟨B', hB'⟩
    have hVF' := validNextState_implies_validFloodFill A B' powered hB'
    have huniq := validFloodFill_uniqueness A _ B' powered hVF hVF'
    obtain ⟨-, -, -, -, hADB, -⟩ := hB'
    have hgate' : logic (A.val T.gate) ≠ logic (B'.val T.gate) :=
      fun heq => hgate (heq.trans (congr_arg logic (huniq T.gate)).symm)
    obtain ⟨h1, h2⟩ := hADB T hT_mem hgate'
    rcases hends with hA | hBe
    · exact hA h1
    · exact hBe ((huniq T.source).trans (h2.trans (huniq T.drain).symm))

-- A rev1Error means no valid next state exists.
-- The unique ValidFloodFill state already fails PTC, so no candidate can satisfy ValidNextState.
theorem simStepRelation_rev1Error_no_valid {net : Net} (A : State net)
    (powered : net.nodes → Option Value) (requireStatic : Bool) (v : net.nodes)
    (h : SimStepRelation requireStatic A powered (.rev1Error v)) :
    ¬ ∃ B : State net, ValidNextState A B powered := by
  cases h with
  | rev1Error _ hVF _ hchange hdisconn =>
    intro ⟨B', hB'⟩
    have hVF' := validNextState_implies_validFloodFill A B' powered hB'
    have huniq := validFloodFill_uniqueness A _ B' powered hVF hVF'
    obtain ⟨-, -, -, -, -, hPTC⟩ := hB'
    have hchange' : A.val v ≠ B'.val v :=
      fun heq => hchange (heq.trans (huniq v).symm)
    obtain ⟨hA_conn, hB_conn⟩ := hPTC v hchange'
    rcases hdisconn with hA_disconn | hB_disconn
    · obtain ⟨p, hAp, hABconn'⟩ := hA_conn
      exact hA_disconn p hAp ⟨hABconn'.1, (connectedIn_congr _ _ huniq).mpr hABconn'.2⟩
    · obtain ⟨q, hBq, hABconn'⟩ := hB_conn
      have hpow_q : powered q ≠ none := by rw [← hVF'.1]; exact hBq
      exact hB_disconn q (by rw [hVF.1]; exact hpow_q)
        ⟨hABconn'.1, (connectedIn_congr _ _ huniq).mpr hABconn'.2⟩

-- A staticError means no ValidNextStateStat (valid next state satisfying STAT) can exist.
theorem simStepRelation_staticError_no_valid_stat {net : Net} (A : State net)
    (powered : net.nodes → Option Value) (requireStatic : Bool) (v : net.nodes)
    (h : SimStepRelation requireStatic A powered (.staticError v)) :
    ¬ ∃ B' : State net, ValidNextStateStat A B' powered := by
  cases h with
  | staticError _ _ hVF hfail =>
    intro ⟨B', hB'⟩
    have hVF' := validNextState_implies_validFloodFill A B' powered hB'.1
    have huniq := validFloodFill_uniqueness A _ B' powered hVF hVF'
    obtain ⟨p, hp_pow, hp_conn⟩ := hB'.2 v
    exact hfail p (by rwa [hVF.1, ← hVF'.1]) ((connectedIn_congr _ _ huniq).mpr hp_conn)

/-- Completeness: if a valid next state exists, the relation produces ok.
    The converse is `simStepRelation_ok_sound`. -/
theorem simStepRelation_complete {net : Net} (A : State net) (powered : net.nodes → Option Value)
    (requireStatic : Bool) (hStatic : requireStatic = false)
    (h : ∃ B : State net, ValidNextState A B powered) :
    ∃ B : State net, SimStepRelation requireStatic A powered (.ok B) := by
  obtain ⟨B, hB⟩ := h
  exact ⟨B, .ok
    (fun hSC => shortCircuit_no_validNextState A powered hSC ⟨B, hB⟩)
    (validNextState_implies_validFloodFill A B powered hB)
    hB.2.2.2.2.1
    hB.2.2.2.2.2
    (Or.inl hStatic)⟩

/-- Uniqueness: any two valid next states are pointwise identical. -/
theorem uniqueness {net : Net} (A B C : State net) (powered : net.nodes → Option Value)
    (hB : ValidNextState A B powered) (hC : ValidNextState A C powered) :
    ∀ v, B.val v = C.val v := by
  obtain ⟨hpowB, hDDC_B, hCAP_B, hCLEAN_B, -, -⟩ := hB
  obtain ⟨hpowC, hDDC_C, hCAP_C, hCLEAN_C, -, -⟩ := hC
  exact val_uniqueness A B C (hpowB.trans hpowC.symm) hDDC_B hCAP_B hCLEAN_B hDDC_C hCAP_C hCLEAN_C
