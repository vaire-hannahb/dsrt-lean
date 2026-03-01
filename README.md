# dsrt-lean

Lean formalization for the Discrete Semantics of Reversible Transistor Networks (DSRT) semantics and correctness results.

## Build

This is a **library-only** project (no executable target).

```bash
lake build
```

## What is in this repo

### Lean modules

- `DsrtLean/Basic.lean`
  - Core semantic objects: values, logic projection, transistor on/off, pass behavior, state, connectivity.
- `DsrtLean/Constraints.lean`
  - Constraint predicates (`CON`, `REV0`, `REV1`, `STAT`, `CLEAN`, `CAP`, `DDC`) and key implication/uniqueness theorems.
- `DsrtLean/Algorithm.lean`
  - Relational algorithm model (`Drives`, `ShortCircuit`, `ValidFloodFill`, `SimResult`, `SimStepRelation`).
- `DsrtLean/Correctness.lean`
  - Headline public correctness theorems (soundness/completeness/error-impossibility/uniqueness style results).
- `DsrtLean.lean`
  - Root import file for the full library.

### Paper/design markdown files

- `hugh_transistor_semantics.md`
  - Main semantics and algorithm write-up.
- `Extended Hugh's Transistor Semantics.md`
  - Extended write-up including optional-constraint framing.
- `design_notes.md`, `optional_constraints_plan*.md`, `phase3_loose_ends.md`
  - Working notes/planning docs (not normative spec).

## Scope choices in this Lean artifact

### REV2 (strict reversibility)

`REV2` is treated as optional in the paper discussion and is **not included** in the current Lean proof target.  
Rationale: `REV2` trivially implies `REV0`, and the relations proved in this artifact require `REV0` (not `REV2`) together with the other core constraints. So adding `REV2` would be a strict strengthening, not needed for the results formalized here.

### CLEAN

The algorithm-level optional switch for CLEAN is:
- fail on weak outputs, or
- normalize weak outputs to strong (`H -> 1`, `L -> 0`).

Either way, successful execution yields a clean (strong-only) final state.  
For theorem statements, we therefore make `CLEAN` mandatory in `ValidNextState`, so proofs are stated over the canonical post-step state class.

## Headline results proved

### Core correctness (relation-level)

- **Soundness of `ok`**: if `SimStepRelation A powered (.ok B)` then `ValidNextState A B powered`.
  - Lean: `simStepRelation_ok_sound` (`DsrtLean/Correctness.lean`).
- **Completeness toward `ok`**: if some valid next state exists, the relation yields an `ok` outcome.
  - Lean: `simStepRelation_complete`.
- **Error impossibility results**: each error constructor corresponds to impossibility of a compliant next state (or statically compliant next state for `staticError`).
  - Lean: `simStepRelation_shortCircuit_no_valid`,
    `simStepRelation_rev0Error_no_valid`,
    `simStepRelation_rev1Error_no_valid`,
    `simStepRelation_staticError_no_valid_stat`.

### Uniqueness

- **Uniqueness of valid next-state values** is proved directly from constraints (`DDC`, `CAP`, `CLEAN`, powered agreement), without requiring an executable simulator implementation.
  - Lean: `val_uniqueness` (`DsrtLean/Constraints.lean`) and exported endpoint `uniqueness` (`DsrtLean/Correctness.lean`).

### Other results

- `CON ∧ REV0 -> CAP`: `con_rev0_implies_cap`.
- `REV1 -> DDC`: `rev1_implies_ddc`.
- `(CAP ∧ REV0 ∧ REV1, plus CON on A) -> CON on B`: `cap_rev0_rev1_implies_con`.
- Short-circuit implies CAP impossibility and no valid next state:
  - `shortCircuit_no_cap`, `shortCircuit_no_validNextState` (`DsrtLean/Algorithm.lean`).
