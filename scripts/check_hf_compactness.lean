/-
Dependency guard for the honest HF fragment (issue #18).

Certifies PROOF ARCHITECTURE, which `#print axioms` cannot: that HF compactness is *derived* from
Mathlib's first-order compactness rather than projected from a stored field, and that the honest HF
objects are not built on the quarantined legacy structures.

1. REQUIRED — `finitaryFragment_compact`'s cone must contain
   `Theory.isSatisfiable_iff_isFinitelySatisfiable`.
2. FORBIDDEN — no honest HF declaration may reach `FiniteCompactFragment` (whose `compact` field is
   the projected principle), `AdmissibleFragmentCore` (whose upward closure HF cannot satisfy), or
   `CodedIn` (the Nadel oracle).

Run with: lake env lean scripts/check_hf_compactness.lean
-/
import InfinitaryLogic.Admissible.AmbientHF

open Lean

partial def deps (env : Environment) (n : Name) : NameSet := go n {} where
  go (n : Name) (acc : NameSet) : NameSet :=
    if acc.contains n then acc else
      let acc := acc.insert n
      match env.find? n with
      | some (.thmInfo ti) => ti.value.getUsedConstants.foldl (fun a d => go d a) acc
      | some ci => match ci.value? with
        | some v => v.getUsedConstants.foldl (fun a d => go d a) acc
        | none => acc
      | none => acc

def guardedRoots : List Name :=
  [`FirstOrder.Language.finitaryFragment_compact,
   `FirstOrder.Language.hfFragment,
   `FirstOrder.Language.hfAdmissibleFragment,
   `FirstOrder.Language.hfAmbient_compact]

def forbiddenSub : List String :=
  ["FiniteCompactFragment", "AdmissibleFragmentCore", "CodedIn", "BarwiseFragment"]

run_cmd do
  let env ← getEnv
  for root in guardedRoots do
    unless (env.find? root).isSome do throwError "root {root} not found"
    let d := deps env root
    let hits := d.toList.filter fun c => forbiddenSub.any fun s =>
      (c.toString.splitOn s).length ≠ 1
    unless hits.isEmpty do
      throwError "[FORBIDDEN] {root} reaches legacy admissible structures: {hits}"
  let dc := deps env `FirstOrder.Language.finitaryFragment_compact
  unless dc.contains `FirstOrder.Language.Theory.isSatisfiable_iff_isFinitelySatisfiable do
    throwError "[MISSING] finitaryFragment_compact does not use Mathlib compactness"
  logInfo "HF guard: OK (Mathlib compactness consumed; no legacy admissible structures in cone)"
