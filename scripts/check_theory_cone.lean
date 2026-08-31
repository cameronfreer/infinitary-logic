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

/-- Forbidden: the definability layer, KP, the numbering layer, and the legacy bundle. -/
def forbiddenExact : List Name :=
  [-- the definability layer
   `FirstOrder.Language.AmbientPresentation,
   `FirstOrder.Language.AmbientPresentation.Sigma1,
   `FirstOrder.Language.AmbientPresentation.ACEnumerable,
   `FirstOrder.Language.AmbientPresentation.CompactFor,
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
