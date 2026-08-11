/-
Dependency guard for the proof-system core (issue #18, step 6 of the migration plan).

Certifies that the proof calculus and its soundness are parameterized by a raw permitted
sentence set and CANNOT reach any legacy fragment structure — the boundary established by
the consumer audit (interface contract §8). `ConsistencyBridge` legitimately reaches
`BarwiseFragment` and is deliberately NOT imported here.

Roots: `Derivable`, `AConsistent`, `Derivable.sound`, `AConsistent.of_has_model`.
Forbidden in their cones: `FiniteCompactFragment`, `AdmissibleFragmentCore`,
`BarwiseFragment`.

POSITIVE sanity checks certify that theorem proof bodies are genuinely traversed (a
forbidden-root failure test alone cannot show this): `Derivable.sound`'s cone must contain
`realize_openBounds` (the semantic roundtrip its quantifier cases use), and
`AConsistent.of_has_model`'s cone must contain `Derivable.sound`.

Run with: lake env lean scripts/check_proof_system_boundary.lean
-/
import InfinitaryLogic.Admissible.Barwise.Soundness

open Lean

/-- `value?` returns `none` for THEOREMS (it only exposes `def` bodies); match `.thmInfo`
explicitly, otherwise theorem proof bodies are silently skipped and a forbidden structure
hidden in a proof would be MISSED. Same trap as documented in
`check_truth_lemma_cone.lean`. -/
def declValue? (ci : ConstantInfo) : Option Expr :=
  match ci with
  | .defnInfo v => some v.value
  | .thmInfo v => some v.value
  | .opaqueInfo v => some v.value
  | _ => none

/-- Transitive constants of a declaration, following the TYPE (so an inductive's signature
is covered), the VALUE via `declValue?` (so theorem proof bodies are covered), and an
inductive's constructors. -/
partial def deps (env : Environment) (n : Name) : NameSet := go n {} where
  go (n : Name) (acc : NameSet) : NameSet :=
    if acc.contains n then acc else
      let acc := acc.insert n
      match env.find? n with
      | some ci =>
        let cs := ci.type.getUsedConstants ++
          ((declValue? ci).map (·.getUsedConstants)).getD #[]
        let cs := match ci with
          | .inductInfo ii => cs ++ ii.ctors.toArray
          | _ => cs
        cs.foldl (fun a d => go d a) acc
      | none => acc

def guardedRoots : List Name :=
  [`FirstOrder.Language.Derivable,
   `FirstOrder.Language.AConsistent,
   `FirstOrder.Language.Derivable.sound,
   `FirstOrder.Language.AConsistent.of_has_model]

def forbiddenSub : List String :=
  ["FiniteCompactFragment", "AdmissibleFragmentCore", "BarwiseFragment"]

run_cmd do
  let env ← getEnv
  for root in guardedRoots do
    unless (env.find? root).isSome do throwError "root {root} not found"
    let d := deps env root
    let hits := d.toList.filter fun c => forbiddenSub.any fun s =>
      (c.toString.splitOn s).length ≠ 1
    unless hits.isEmpty do
      throwError "[FORBIDDEN] {root} reaches legacy fragment structures: {hits}"
  -- Positive checks: theorem bodies are genuinely traversed.
  let dSound := deps env `FirstOrder.Language.Derivable.sound
  unless dSound.contains `FirstOrder.Language.realize_openBounds do
    throwError
      "[MISSING] Derivable.sound's cone lacks realize_openBounds — theorem bodies not traversed?"
  let dModel := deps env `FirstOrder.Language.AConsistent.of_has_model
  unless dModel.contains `FirstOrder.Language.Derivable.sound do
    throwError
      "[MISSING] AConsistent.of_has_model's cone lacks Derivable.sound — theorem bodies not traversed?"
  logInfo "Proof-system boundary: OK (theorem bodies traversed; no legacy fragment structure in any cone)"
