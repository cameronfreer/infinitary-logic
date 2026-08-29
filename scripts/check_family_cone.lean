/-
Dependency-cone guard for the #19A family layer (migration stage 5.1).

Certifies the SYNTAX BOUNDARY, which no build success can: `CodedFamily`, `codedIInf` and
`codedISup` must depend only on the family view `FamilyPresentation`, never on theory decoding,
`Sigma1`, definition codes, KP, or any numbering.

Today that also holds by imports — `Admissible/Family.lean` is imported *by* the files defining
those things, so it cannot see them. This guard exists because that import direction is easy to
reverse by accident: adding one `import` to `Family.lean`, or re-parameterizing `CodedFamily` by a
richer structure, would silently re-bundle the layers and every build would still pass.

1. FORBIDDEN — no declaration in the cone of the family-layer roots may be the bundling
   presentation (`AdmissiblePresentation`), the ambient presentation or any of its theory /
   Σ-definition / KP declarations, the numbering layer, or the c.e. predicate.

2. REQUIRED — the cone MUST contain `FamilyPresentation`, so a root cannot pass by having been
   rewritten to depend on nothing at all.

CAVEAT, stated because it bounds what this proves: structure-field projections compile to
`Expr.proj` and are NOT cone-visible, so `AdmissiblePresentation.Sigma1` — a projection — cannot be
detected directly. That is why the enclosing STRUCTURES are forbidden by name: any use of a
projection requires its structure in the type, and the structure is cone-visible. Declarations that
are genuine `def`s (`AmbientPresentation.Sigma1`, `.decodeTheory`, `.theoryOf`, `.AFinite`) are
listed individually and are detected directly.

`hfAdmissibleFragment` and the other HF syntax consumers ARE roots, as of stage 5.4's preparation:
they are stated over `hfFamily`, the family-layer HF presentation, so they no longer reach
`hfPresentation`. They were excluded while they went through `hfPresentation.toFamilyPresentation`.

Still excluded, and legitimately: HF's THEORY-side results (`hf_compactFor`, `hf_aFinite_iff`,
`hf_compact_of_aFinite`), which are stated over the legacy presentation until stage 5.4 retires it.
`hf_compactFor` is the current witness that this guard discriminates — adding it as a root makes
the guard report `AdmissiblePresentation`.

Run with: lake env lean scripts/check_family_cone.lean
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

/-- Forbidden exact declarations: the bundling presentation, the theory / Σ / KP layers, and the
numbering layer.

Every name here is checked to EXIST before the cone test runs.  A forbidden name that has been
renamed away is silently useless — the guard would keep reporting OK while protecting nothing.
That is not hypothetical: this list went stale within one commit, when the theory layer moved from
`AmbientPresentation` to `TheoryPresentation` and the bare `AFinite` became
`AdmissiblePresentation.AFinite`. -/
def forbiddenExact : List Name :=
  [-- the bundling signature the syntax layer must no longer reach
   `FirstOrder.Language.AdmissiblePresentation,
   -- the theory layer
   `FirstOrder.Language.TheoryPresentation,
   `FirstOrder.Language.TheoryPresentation.IsTheoryCode,
   `FirstOrder.Language.TheoryPresentation.decodeTheory,
   `FirstOrder.Language.TheoryPresentation.members,
   `FirstOrder.Language.TheoryPresentation.AFinite,
   `FirstOrder.Language.TheoryPresentation.AFinitelySatisfiable,
   `FirstOrder.Language.TheoryPresentation.sentenceRange,
   `FirstOrder.Language.TheoryPresentation.AdequateFor,
   -- the ambient presentation and its definability layer
   `FirstOrder.Language.AmbientPresentation,
   `FirstOrder.Language.AmbientPresentation.WithKP,
   `FirstOrder.Language.AmbientPresentation.theoryOf,
   `FirstOrder.Language.AmbientPresentation.Sigma1,
   `FirstOrder.Language.AmbientPresentation.ACEnumerable,
   `FirstOrder.Language.AmbientPresentation.CompactFor,
   -- the legacy external theory predicates
   `FirstOrder.Language.AdmissiblePresentation.AFinite,
   `FirstOrder.Language.AdmissiblePresentation.ACEnumerable,
   `FirstOrder.Language.AdmissiblePresentation.AFinitelySatisfiable,
   `FirstOrder.Language.AdmissiblePresentation.CompactFor,
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
   `Nat.ackUnion]

/-- Positive witness: the family view must genuinely be consumed. -/
def requiredWitness : List Name := [`FirstOrder.Language.FamilyPresentation]

/-- The generic family-layer interface. -/
def guardedRoots : List Name :=
  [`FirstOrder.Language.CodedFamily,
   `FirstOrder.Language.CodedFamily.ext,
   `FirstOrder.Language.CodedFamily.infinitary,
   `FirstOrder.Language.codedIInf,
   `FirstOrder.Language.codedISup,
   `FirstOrder.Language.realize_codedIInf,
   `FirstOrder.Language.realize_codedISup,
   `FirstOrder.Language.codedIInf_uses_presentation_encoding,
   `FirstOrder.Language.codedIInf_eq_of_code_eq,
   `FirstOrder.Language.codedISup_eq_of_code_eq,
   `FirstOrder.Language.AdmissibleFragment,
   -- HF's SYNTAX consumers, now stated over `hfFamily` rather than a full presentation.
   -- These were excluded while they went through `hfPresentation.toFamilyPresentation`; that
   -- they are roots at all is the content of migration stage 5.4's preparation.
   `FirstOrder.Language.hfFamily,
   `FirstOrder.Language.isEmpty_codedFamily_hf,
   `FirstOrder.Language.hf_coded_closure_vacuous,
   `FirstOrder.Language.hfAdmissibleFragment]

run_cmd do
  let env ← getEnv
  -- a forbidden name that no longer exists protects nothing; fail loudly rather than pass
  for f in forbiddenExact do
    unless (env.find? f).isSome do
      throwError "[STALE GUARD] forbidden declaration {f} no longer exists — update this list"
  for root in guardedRoots do
    unless (env.find? root).isSome do throwError "root declaration {root} not found"
    let deps := transitiveDeps env root
    let hits := deps.toList.filter fun d => forbiddenExact.contains d
    unless hits.isEmpty do
      throwError "[FORBIDDEN] {root} reaches outside the family layer: {hits}"
    let missing := requiredWitness.filter fun r => !deps.contains r
    unless missing.isEmpty do
      throwError "[MISSING WITNESS] {root} does not consume the family view: {missing}"
  logInfo "family-layer cone guard: OK (syntax depends only on FamilyPresentation)"
