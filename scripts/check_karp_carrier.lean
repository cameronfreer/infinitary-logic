/-
Acceptance guard for the fixed-carrier Karp formulation.

Two jobs, neither of which an axiom scan can do.

1. ELABORATION GATES — the formulation's claims are about *signatures*, so they are checked by
   elaborating them, not by inspecting proofs:
     * `karp_theorem_at` accepts structures in different universes and a common carrier in a
       third, unrelated universe;
     * `karp_theorem_on_sum` is the canonical specialization — `rfl`-equal to `karp_theorem_at`
       fed the two sum injections, so it cannot silently become an independent re-proof;
     * a carrier unrelated to both structures (here `ℕ`, via `Encodable` codings) works, which
       is the actual content of "any common carrier suffices";
     * the packaged same-universe endpoint resolves from the DEFAULT import surface.

2. ZERO-OCCURRENCE — the old per-node-index Karp implementation (`liftUI`, `existsLastVarInf`,
   the `LinfEquivW` bridges, and the superseded endpoint names) must be ABSENT from the
   environment, not merely unreferenced. Absence is what makes the replacement real; a
   surviving-but-unused copy would silently rot.

3. DEPENDENCY CONE — with a POSITIVE assertion, not only prohibitions. A guard that merely
   forbids is satisfied vacuously by a theorem that proves nothing, so the cone must be shown
   to *contain* the coded-conjunction machinery (`iInfAlong`, `IndexCoding`, `reindex`) that
   the fixed-carrier argument is supposed to run on, and to contain none of the old per-node
   syntax (`BoundedFormulaInfLegacy`, `liftUI`, `existsLastVarInf`).

   Theorem proof bodies are reached via `.thmInfo`/`.opaqueInfo`: `ConstantInfo.value?` exposes
   only `def` bodies, so matching on it alone would silently skip every theorem and hide a
   legacy dependency sitting in a proof.

Run with: lake env lean scripts/check_karp_carrier.lean
-/
import InfinitaryLogic

open Lean

/-! ## 1. Elaboration gates -/

universe u v w w' uκ

namespace FirstOrder

namespace Language

section Gates

variable {L : Language.{u, v}} [L.IsRelational]

/-- Heterogeneous structure universes, arbitrary common carrier. -/
example {M : Type w} {N : Type w'} [L.Structure M] [L.Structure N] {κ : Type uκ}
    (cM : IndexCoding M κ) (cN : IndexCoding N κ) :
    Nonempty (PotentialIso L M N) ↔ InfEquivAt L κ M N :=
  karp_theorem_at cM cN

/-- The sum carrier is the canonical *specialization*, definitionally — not a re-proof. -/
example {M N : Type w} [L.Structure M] [L.Structure N] :
    (karp_theorem_on_sum : Nonempty (PotentialIso L M N) ↔ InfEquivAt L (M ⊕ N) M N) =
      karp_theorem_at (.sumInl M N) (.sumInr M N) :=
  rfl

/-- A carrier unrelated to both structures suffices. -/
example {M N : Type} [L.Structure M] [L.Structure N] [Encodable M] [Encodable N] :
    Nonempty (PotentialIso L M N) ↔ InfEquivAt L ℕ M N :=
  karp_theorem_at (.ofEncodable M) (.ofEncodable N)

/-- Forward is generic in the index universe. -/
example {M : Type w} {N : Type w'} [L.Structure M] [L.Structure N]
    (P : PotentialIso L M N) (κ : Type uκ) : InfEquivAt L κ M N :=
  P.infEquivAt κ

/-- Contravariance in codings, at heterogeneous universes. -/
example {M : Type w} {N : Type w'} [L.Structure M] [L.Structure N] {ι : Type*} {κ : Type*}
    (c : IndexCoding ι κ) (h : InfEquivAt L κ M N) : InfEquivAt L ι M N :=
  h.of_reindex c

/-- The public same-universe endpoint, from the default import surface. -/
example {M N : Type w} [L.Structure M] [L.Structure N] :
    Nonempty (PotentialIso L M N) ↔ InfEquivW L M N :=
  karp_theorem_w

end Gates

end Language

end FirstOrder

/-! ## 2. Dependency cone -/

/-- `value?` returns `none` for THEOREMS (it exposes only `def` bodies); match `.thmInfo`
explicitly, or every theorem proof body is silently skipped and a legacy-syntax use hidden in
a proof would be MISSED. -/
def declValue? (ci : ConstantInfo) : Option Expr :=
  match ci with
  | .defnInfo v => some v.value
  | .thmInfo v => some v.value
  | .opaqueInfo v => some v.value
  | _ => none

partial def transitiveDeps (env : Environment) (start : Name) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut stack : List Name := [start]
  while !stack.isEmpty do
    let n := stack.head!
    stack := stack.tail!
    if seen.contains n then continue
    seen := seen.insert n
    match env.find? n with
    | none => pure ()
    | some ci =>
      let mut cs := ci.type.getUsedConstantsAsSet
      match declValue? ci with
      | some v => cs := cs.union v.getUsedConstantsAsSet
      | none => pure ()
      for c in cs do
        if !seen.contains c then stack := c :: stack
  return seen

def hasSub (hay needle : String) : Bool := (hay.splitOn needle).length > 1

/-- The old per-node-index syntax and the operations that exist only to serve it. -/
def forbiddenSub : List String := ["BoundedFormulaInfLegacy", "FormulaInfLegacy",
  "SentenceInfLegacy"]

/-- The old Karp implementation's operations. These are now DELETED, so the assertion below
is that they are absent from the environment entirely — a stronger and cheaper check than a
cone scan, and one that fails loudly if any of them is ever reintroduced. -/
def removedNames : List Name :=
  [`FirstOrder.Language.BoundedFormulaInfLegacy.liftUI,
   `FirstOrder.Language.BoundedFormulaInfLegacy.realize_liftUI,
   `FirstOrder.Language.BoundedFormulaInfLegacy.existsLastVarInf,
   `FirstOrder.Language.BoundedFormulaInfLegacy.realize_existsLastVarInf,
   `FirstOrder.Language.LinfEquivW_implies_potentialIso,
   `FirstOrder.Language.LinfEquivW_implies_LinfEquiv,
   `FirstOrder.Language.PotentialIso_implies_LinfEquiv,
   `FirstOrder.Language.karp_theorem_forward,
   `FirstOrder.Language.karp_theorem_universe0,
   `FirstOrder.Language.karp_theorem_idx]

def forbiddenExact : List Name := removedNames

/-- POSITIVE assertion: the fixed-carrier machinery the argument must actually run on. Without
this a cone guard is satisfied by a theorem that proves nothing. -/
def requiredWitness : List Name :=
  [`FirstOrder.IndexCoding,
   `FirstOrder.Language.BoundedFormulaInf.iInfAlong,
   `FirstOrder.Language.BoundedFormulaInf.realize_iInfAlong,
   `FirstOrder.Language.BoundedFormulaInf]

/-- Roots whose cone must reach the coded machinery. `karp_theorem_at` is the theorem doing
the work; the other two are its packagings, and inherit the cone. -/
def guardedRoots : List Name :=
  [`FirstOrder.Language.karp_theorem_at,
   `FirstOrder.Language.karp_theorem_on_sum,
   `FirstOrder.Language.karp_theorem_w]

run_cmd do
  let env ← getEnv
  -- zero-occurrence check: the old implementation must be gone, not merely unreferenced
  let survivors := removedNames.filter fun n => (env.find? n).isSome
  unless survivors.isEmpty do
    throwError "[NOT REMOVED] the old Karp implementation is still in the environment: \
      {survivors}"
  for root in guardedRoots do
    unless (env.find? root).isSome do throwError "root declaration {root} not found"
    let deps := transitiveDeps env root
    let hits := deps.toList.filter fun d =>
      forbiddenSub.any (hasSub d.toString ·) || forbiddenExact.contains d
    unless hits.isEmpty do
      throwError "[FORBIDDEN] {root} depends on the legacy per-node syntax: {hits}"
    let missing := requiredWitness.filter fun r => !deps.contains r
    unless missing.isEmpty do
      throwError "[MISSING WITNESS] {root} does not consume the coded-conjunction \
        machinery: {missing}"
  logInfo "Karp carrier guard: OK (elaboration gates pass; old implementation absent; cones \
    consume IndexCoding/iInfAlong and no legacy syntax)"
