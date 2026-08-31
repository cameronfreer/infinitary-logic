/-
Dependency-cone guard for the #19A family layer (migration stage 5.1).

Certifies the SYNTAX BOUNDARY, which no build success can: `CodedFamily`, `codedIInf` and
`codedISup` must depend only on the family view `FamilyPresentation`, never on theory decoding,
`Sigma1`, definition codes, KP, or any numbering.

Today that also holds by imports — `Admissible/Family.lean` is imported *by* the files defining
those things, so it cannot see them. This guard exists because that import direction is easy to
reverse by accident: adding one `import` to `Family.lean`, or re-parameterizing `CodedFamily` by a
richer structure, would silently re-bundle the layers and every build would still pass.

1. FORBIDDEN — no declaration in the cone of the family-layer roots may be the theory layer, the
   ambient presentation or any of its Σ-definition / KP declarations, the numbering layer, or the
   c.e. predicate.

2. REQUIRED — the cone MUST contain `FamilyPresentation`, so a root cannot pass by having been
   rewritten to depend on nothing at all.

CAVEAT, stated because it bounds what this proves: structure-field projections compile to
`Expr.proj` and are NOT cone-visible, so `AmbientPresentation.enumerates` — a projection — cannot
be detected directly. That is why the enclosing STRUCTURES are forbidden by name: any use of a
projection requires its structure in the type, and the structure is cone-visible. Declarations that
are genuine `def`s (`AmbientPresentation.Sigma1`, `TheoryPresentation.decodeTheory`, `.AFinite`)
are listed individually and are detected directly.

`hfAdmissibleFragment` and the other HF syntax consumers ARE roots: they are stated over
`hfFamily`, the family-layer HF presentation.

Still excluded, and legitimately: HF's THEORY-side results (`hfAmbient_compact`,
`hfAmbient_aFinite_iff`), which live at the ambient layer by construction. `hfAmbient_compact` is
the witness that this guard discriminates — adding it as a root makes the guard report
`hfAmbient`, `AmbientPresentation` and the theory layer.

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

/-- Transitive constant cone.  `followThm := false` skips THEOREM bodies while still following
types and `def` bodies; running the cone both ways is what proves a dependency is reachable *only*
through proof bodies, which inspecting direct constants cannot show. -/
partial def depsWith (env : Environment) (followThm : Bool) (start : Name) : NameSet := Id.run do
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
      let follow := match ci with | .thmInfo _ => followThm | _ => true
      if follow then
        match declValue? ci with
        | some v => cs := cs.union v.getUsedConstantsAsSet
        | none => pure ()
      for c in cs do
        if !seen.contains c then stack := c :: stack
  return seen

/-- The real cone: theorem bodies included. -/
def transitiveDeps (env : Environment) (start : Name) : NameSet := depsWith env true start

/-- Forbidden exact declarations: the bundling presentation, the theory / Σ / KP layers, and the
numbering layer.

Every name here is checked to EXIST before the cone test runs.  A forbidden name that has been
renamed away is silently useless — the guard would keep reporting OK while protecting nothing.
That is not hypothetical: this list went stale twice — when the theory layer moved from
`AmbientPresentation` to `TheoryPresentation`, and again when the legacy presentation was deleted
outright. Both times the existence check is what forced the update. -/
def forbiddenExact : List Name :=
  [   -- the theory layer
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
  -- NEGATIVE CONTROL for the `.thmInfo` path.
  --
  -- Every root above would still pass with theorem-body traversal completely broken, because each
  -- forbidden name they could plausibly touch also occurs in a TYPE. This control certifies the
  -- traversal MECHANISM instead, on a probe whose dependency is reachable only through proof
  -- bodies: `hfAmbient_compact`'s proof calls `finitaryFragment_compact`, whose own proof calls
  -- `foTheory`. Neither name occurs in any type along the way.
  --
  -- The claim is established by running the cone TWICE, not by inspecting direct constants:
  --
  --   * `depsWith false` (types and `def` bodies, no theorem bodies) must NOT reach `foTheory`;
  --   * `depsWith true`  (the real traversal)                        must reach it.
  --
  -- Two further assertions keep it honest. `foTheory` must be absent from the probe's own value,
  -- so the full traversal is exercising TRANSITIVITY -- here two theorem bodies deep -- rather
  -- than a one-hop lookup; and `finitaryFragment_compact` must be present there while absent from
  -- the type, so the probe is genuinely proof-only. All four are re-verified every run, so the
  -- control cannot rot into a tautology as the surrounding API moves.
  let probe := `FirstOrder.Language.hfAmbient_compact
  let witness := `FirstOrder.Language.finitaryFragment_compact
  let leaked := `FirstOrder.Language.foTheory
  let some pci := env.find? probe | throwError "negative control: {probe} not found"
  let some pval := declValue? pci
    | throwError "negative control: no value for {probe}; declValue? is not matching .thmInfo"
  if pci.type.getUsedConstants.contains witness then
    throwError "negative control is no longer proof-only: {witness} now occurs in {probe}'s type"
  unless pval.getUsedConstants.contains witness do
    throwError "negative control: {witness} absent from {probe}'s value"
  if pval.getUsedConstants.contains leaked then
    throwError "negative control no longer exercises transitivity: {leaked} occurs directly in \
      {probe}'s value"
  if (depsWith env false probe).contains leaked then
    throwError "negative control is no longer proof-only: {leaked} is reachable from {probe} \
      without traversing any theorem body"
  unless (depsWith env true probe).contains leaked do
    throwError "negative control FAILED: theorem-body traversal is broken \
      ({leaked} is reachable from {probe} only through a proof body)"

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
