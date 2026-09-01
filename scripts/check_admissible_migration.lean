/-
Guard: the #19A migration is COMPLETE and its result is genuinely ASSEMBLED (stage 5.6).

Two kinds of coverage, because neither can see what the other checks.

1. ABSENCE — the legacy bundling cluster deleted in stage 5.4 must be gone from the environment.

   A deleted name needs an ABSENCE assertion, not a forbidden-list entry in a cone guard: those
   lists carry a `[STALE GUARD]` existence check that *rejects* names which no longer exist, so
   listing a deleted name there fails the guard rather than protecting anything. The two tools are
   for opposite situations — forbidden-list for "exists, must not be reachable", absence for "must
   not exist at all".

   MECHANISM CONTROL. Absence assertions are the easiest kind of check to make vacuous: were
   `env.find?` to return `none` for everything, all fourteen would pass and the guard would certify
   nothing. Every run therefore first requires a set of names that MUST resolve. If the lookup
   mechanism breaks, the control fails before any absence claim is made.

2. ASSEMBLY — the honest route must actually be wired, which no absence check can see. Deleting the
   legacy cluster and leaving the replacement disconnected would pass part 1 completely.

   * `hfAmbient_compactFor` must expose `AmbientPresentation.CompactFor` in its TYPE (so HF inhabits
     the real interface, not a look-alike) and must reach `hfAmbient_compact` in its cone (so the
     interface is inhabited by the honest Mathlib-compactness route, not by a restatement);
   * `AmbientPresentation.compactFor_of_adequate` must reach `AmbientPresentation.subset_of_adequate`
     in its cone — that is the containment derivation, the whole reason the caller never supplies
     `T ⊆ P` by hand.

Run *after* `lake build`, so the oleans it resolves against are current.

Run with: lake env lean scripts/check_admissible_migration.lean
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

/-- Transitive constant cone, theorem bodies included. -/
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

/-- The legacy cluster deleted in stage 5.4. None of these may exist. -/
def mustBeAbsent : List Name :=
  [-- the bundling presentation and its namespaced predicates
   `FirstOrder.Language.AdmissiblePresentation,
   `FirstOrder.Language.AdmissiblePresentation.AFinite,
   `FirstOrder.Language.AdmissiblePresentation.ACEnumerable,
   `FirstOrder.Language.AdmissiblePresentation.AFinitelySatisfiable,
   `FirstOrder.Language.AdmissiblePresentation.CompactFor,
   `FirstOrder.Language.AdmissiblePresentation.Sigma1,
   -- the legacy theory-decoding law, replaced by the code subtype
   `FirstOrder.Language.DecodesTheory,
   `FirstOrder.Language.decodes_theory_unique,
   -- the legacy HF instance and everything stated against it
   `FirstOrder.Language.hfPresentation,
   `FirstOrder.Language.hf_aFinite_iff,
   `FirstOrder.Language.hf_aFinitelySatisfiable_iff,
   `FirstOrder.Language.hfPresentation_sigma1_eq_top,
   `FirstOrder.Language.hf_compact_of_aFinite,
   `FirstOrder.Language.hf_compactFor]

/-- Names that MUST resolve, so a broken lookup cannot make the absence list vacuous. -/
def mechanismControl : List Name :=
  [`FirstOrder.Language.FamilyPresentation,
   `FirstOrder.Language.TheoryPresentation,
   `FirstOrder.Language.AmbientPresentation]

run_cmd do
  let env ← getEnv

  -- MECHANISM CONTROL, before any absence claim.
  for n in mechanismControl do
    unless (env.find? n).isSome do
      throwError "[BROKEN CONTROL] {n} does not resolve, so absence assertions below would pass \
        vacuously — fix the lookup before trusting this guard"

  -- 1. ABSENCE.
  for n in mustBeAbsent do
    if (env.find? n).isSome then
      throwError "[NOT DELETED] {n} still exists; stage 5.4 removed it and nothing should \
        reintroduce it"

  -- 2. ASSEMBLY.
  let compactFor := `FirstOrder.Language.hfAmbient_compactFor
  let honest := `FirstOrder.Language.AmbientPresentation.CompactFor
  let route := `FirstOrder.Language.hfAmbient_compact
  let some cci := env.find? compactFor | throwError "assembly: {compactFor} not found"
  unless cci.type.getUsedConstants.contains honest do
    throwError "[NOT ASSEMBLED] {compactFor} does not mention {honest} in its type: HF no longer \
      inhabits the honest compactness interface"
  -- proof-only: `hfAmbient_compact` must be reached through the BODY, not read off the type.
  -- Without this the cone assertion would pass trivially if the route were ever hoisted into the
  -- statement, certifying nothing about how the interface is actually inhabited.
  if cci.type.getUsedConstants.contains route then
    throwError "[WEAKENED CHECK] {route} now occurs in {compactFor}'s type, so the cone assertion \
      below no longer tests that the interface is inhabited through a proof"
  unless (transitiveDeps env compactFor).contains route do
    throwError "[NOT ASSEMBLED] {compactFor} does not reach {route}: the interface is inhabited by \
      something other than the honest compactness route"

  let derived := `FirstOrder.Language.AmbientPresentation.compactFor_of_adequate
  let containment := `FirstOrder.Language.AmbientPresentation.subset_of_adequate
  let some dci := env.find? derived | throwError "assembly: {derived} not found"
  if dci.type.getUsedConstants.contains containment then
    throwError "[WEAKENED CHECK] {containment} now occurs in {derived}'s type, so the cone \
      assertion below no longer tests that containment is derived in the proof"
  unless (transitiveDeps env derived).contains containment do
    throwError "[NOT ASSEMBLED] {derived} does not reach {containment}: containment is no longer \
      derived from adequacy, so the caller must be supplying it by hand"

  logInfo s!"admissible migration guard: OK ({mustBeAbsent.length} legacy declarations absent; \
    HF inhabits the honest interface and containment is derived)"
