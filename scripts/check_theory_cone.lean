/-
Dependency-cone guard for the #19A theory layer (migration stage 5.2).

Companion to `check_family_cone.lean`, one layer up. Certifies that the theory API —
`TheoryPresentation`, `decodeTheory`, `AFinite`, `AFinitelySatisfiable`, adequacy — depends only on
the family view plus membership and sentence decoding, and never on definition codes, `Sigma1`, KP,
or any numbering.

The shortcut this exists to prevent is specific: defining the production `AFinite` as
`AmbientPresentation.AFinite` would type-check, pass every test, and silently make the entire
theory interface depend on the Σ layer that not one theory-side proof uses.

1. FORBIDDEN — no declaration in the cone of a theory root may be the ambient presentation, its
   definability declarations, KP, the numbering layer, or the legacy bundling presentation.

2. REQUIRED — the cone MUST contain `TheoryPresentation`, so a root cannot pass by depending on
   nothing.

3. STALENESS — every forbidden name must still exist. A renamed-away forbidden name is silently
   useless, and this list demonstrably went stale within one commit of being written.

CAVEAT: structure-field projections compile to `Expr.proj` and are NOT cone-visible, so
`AmbientPresentation.IsDefinitionCode` and `.enumerates` cannot be detected directly. The enclosing
structure `AmbientPresentation` is forbidden instead — nothing can use a projection without its
structure appearing in the type. Genuine `def`s (`AmbientPresentation.Sigma1`, `.theoryOf`) are
listed individually and are detected directly.

`hfAmbient`-based results are deliberately NOT roots: they are HF *instances* over an ambient
presentation, so they legitimately mention the Σ layer. The boundary guarded is the generic theory
interface.

Run with: lake env lean scripts/check_theory_cone.lean
-/
import InfinitaryLogic.Admissible

open Lean

/-- `value?` returns `none` for THEOREMS (it only exposes `def` bodies); match `.thmInfo`
explicitly, otherwise theorem proof bodies are silently skipped. -/
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

/-- Forbidden: the definability layer, KP, the numbering layer, and the legacy bundle. -/
def forbiddenExact : List Name :=
  [-- the definability layer
   `FirstOrder.Language.AmbientPresentation,
   `FirstOrder.Language.AmbientPresentation.Sigma1,
   `FirstOrder.Language.AmbientPresentation.theoryOf,
   `FirstOrder.Language.AmbientPresentation.WithKP,
   -- the coding and numbering layers
   `FirstOrder.Language.FinitaryCoding,
   `FirstOrder.Language.FinitaryNumbering,
   `FirstOrder.Language.ComputablyEquivalent,
   `FirstOrder.Language.AreComputablyEquivalent,
   `FirstOrder.Language.CE,
   `FirstOrder.Language.hfAmbient,
   -- KP / Ackermann membership
   `Nat.AckMem,
   `Nat.ackPair,
   `Nat.ackUnion,
   -- the legacy bundling signature and its external predicates
   `FirstOrder.Language.AdmissiblePresentation,
   `FirstOrder.Language.AdmissiblePresentation.AFinite,
   `FirstOrder.Language.AdmissiblePresentation.ACEnumerable,
   `FirstOrder.Language.AdmissiblePresentation.CompactFor]

/-- Positive witness: the theory view must genuinely be consumed. -/
def requiredWitness : List Name := [`FirstOrder.Language.TheoryPresentation]

/-- The generic theory-layer interface. -/
def guardedRoots : List Name :=
  [`FirstOrder.Language.TheoryPresentation,
   `FirstOrder.Language.TheoryPresentation.IsTheoryCode,
   `FirstOrder.Language.TheoryPresentation.members,
   `FirstOrder.Language.TheoryPresentation.decodeTheory,
   `FirstOrder.Language.TheoryPresentation.AFinite,
   `FirstOrder.Language.TheoryPresentation.AFinitelySatisfiable,
   `FirstOrder.Language.TheoryPresentation.sentenceRange,
   `FirstOrder.Language.TheoryPresentation.AdequateFor,
   `FirstOrder.Language.TheoryPresentation.decodeTheory_subset,
   `FirstOrder.Language.TheoryPresentation.AFinite.subset_of_adequate,
   `FirstOrder.Language.TheoryPresentation.AFinite.unique,
   `FirstOrder.Language.TheoryPresentation.mem_decodeTheory]

run_cmd do
  let env ← getEnv
  for f in forbiddenExact do
    unless (env.find? f).isSome do
      throwError "[STALE GUARD] forbidden declaration {f} no longer exists — update this list"
  for root in guardedRoots do
    unless (env.find? root).isSome do throwError "root declaration {root} not found"
    let deps := transitiveDeps env root
    let hits := deps.toList.filter fun d => forbiddenExact.contains d
    unless hits.isEmpty do
      throwError "[FORBIDDEN] {root} reaches outside the theory layer: {hits}"
    let missing := requiredWitness.filter fun r => !deps.contains r
    unless missing.isEmpty do
      throwError "[MISSING WITNESS] {root} does not consume the theory view: {missing}"
  logInfo "theory-layer cone guard: OK (theory API depends only on TheoryPresentation)"
