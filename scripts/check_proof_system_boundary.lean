/-
Dependency guard for the proof-system core (issue #18, step 6 of the migration plan).

Certifies that the proof calculus and its soundness are parameterized by a raw permitted
sentence set and CANNOT reach any legacy fragment structure — the boundary established by
the consumer audit (interface contract §8). `ConsistencyBridge` legitimately reaches
`BarwiseFragment` and is deliberately NOT imported here.

Roots: `Derivable`, `AConsistent`, `Derivable.sound`, `AConsistent.of_has_model`.
Forbidden in their cones: `FiniteCompactFragment`, `AdmissibleFragmentCore`,
`BarwiseFragment`.

Run with: lake env lean scripts/check_proof_system_boundary.lean
-/
import InfinitaryLogic.Admissible.Barwise.Soundness

open Lean

/-- Transitive constants of a declaration, following both the TYPE (so an inductive's
signature and constructors are covered) and the value. -/
partial def deps (env : Environment) (n : Name) : NameSet := go n {} where
  go (n : Name) (acc : NameSet) : NameSet :=
    if acc.contains n then acc else
      let acc := acc.insert n
      match env.find? n with
      | some ci =>
        let cs := ci.type.getUsedConstants ++
          ((ci.value?.map (·.getUsedConstants)).getD #[])
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
  logInfo "Proof-system boundary: OK (Derivable/AConsistent/soundness reach no legacy fragment structure)"
