/-
Dependency-cone guard for the issue #8 forward truth lemma (commit 5b).

Certifies LOGICAL STRENGTH, which `#print axioms` cannot: the maximal-consistency
truth lemma and the forward Henkin truth lemma are BOTH axiom-clean
(`[propext, Classical.choice, Quot.sound]`), so an axiom scan cannot tell whether
`truth_both` earns its conclusion from Henkin closure or from smuggled completeness.
This guard inspects the transitive proof-term cone instead:

1. FORBIDDEN — no declaration in the cone of `truth_both` / `truth_pos` / `truth_neg` /
   `exists_model_of_henkinComplete` may be a maximal-consistency lemma
   (`…MaximalConsistent…` namespace, catches `not_mem_iff`/`decide`/etc.), the
   maximal-consistency biconditional `truthLemma`, or the maximal→HenkinComplete bridge
   `henkinComplete_univ_of_maximal`.

2. REQUIRED — the cone MUST contain the intended Henkin interface: the `HenkinComplete`
   structure and the commit-5a atomic API. (Structure-field projections such as
   `HenkinComplete.all_inst` compile to `Expr.proj` and are NOT cone-visible; their
   consumption is verified by proof read, not here.)

Run with: lake env lean scripts/check_truth_lemma_cone.lean
-/
import InfinitaryLogic.Methods.Interpolation.QuotientTruthLemma

open Lean

/-- `value?` returns `none` for THEOREMS (it only exposes `def` bodies); match `.thmInfo`
explicitly, otherwise theorem proof bodies are silently skipped and a maximality use hidden
in a proof would be MISSED. -/
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

/-- Forbidden namespace substrings (precise: maximal-consistency namespace only; NOT generic
`decide`/`Classical.decEq`, which arise from harmless finite-coordinate syntax). -/
def forbiddenSub : List String := ["MaximalConsistent"]

/-- Forbidden exact declarations. -/
def forbiddenExact : List Name :=
  [`FirstOrder.Language.truthLemma, `FirstOrder.Language.henkinComplete_univ_of_maximal]

/-- Positive witnesses: the Henkin interface the truth lemma must genuinely consume. -/
def requiredWitness : List Name :=
  [`FirstOrder.Language.HenkinComplete,
   `FirstOrder.Language.qmk_eq_of_mem, `FirstOrder.Language.qmk_ne_of_neg_mem,
   `FirstOrder.Language.relMap_of_mem, `FirstOrder.Language.not_relMap_of_neg_mem]

def guardedRoots : List Name :=
  [`FirstOrder.Language.truth_both, `FirstOrder.Language.truth_pos,
   `FirstOrder.Language.truth_neg, `FirstOrder.Language.exists_model_of_henkinComplete]

run_cmd do
  let env ← getEnv
  for root in guardedRoots do
    unless (env.find? root).isSome do throwError "root declaration {root} not found"
    let deps := transitiveDeps env root
    let hits := deps.toList.filter fun d =>
      forbiddenSub.any (hasSub d.toString ·) || forbiddenExact.contains d
    unless hits.isEmpty do
      throwError "[FORBIDDEN] {root} depends on maximal-consistency declarations: {hits}"
    let missing := requiredWitness.filter fun r => !deps.contains r
    unless missing.isEmpty do
      throwError "[MISSING WITNESS] {root} does not consume the Henkin interface: {missing}"
  logInfo "truth-lemma cone guard: OK (no maximal consistency; Henkin interface consumed)"
