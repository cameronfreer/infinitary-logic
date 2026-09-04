/-
Dependency-cone guard for the relational kernel adapter and the source-fragment adapter
(issue #19B).

`HenkinClosed.exists_countable_model_of_aconsistent` and
`Fragment.exists_countable_model_of_aconsistent_withConstants` must earn their models from the
fair enumeration and the forward quotient truth lemma, never from a maximal-consistent
construction, and must not touch the legacy fragment structures. The source-fragment root must
additionally consume the constants-expanded universe, the basis, and the reduct transport.

1. FORBIDDEN — no declaration in the cone may be a maximal-consistency lemma
   (`…MaximalConsistent…`), the maximal-consistency biconditional `truthLemma`, the
   maximal→HenkinComplete bridge, or any of `FullBarwiseFragment`, `BarwiseFragment`,
   `FiniteCompactFragment`, `AdmissibleFragmentCore`.
2. REQUIRED — the endpoint's cone MUST contain `HenkinComplete`, `AConsistent`, `Derivable`,
   `exists_henkinComplete` and `truth_both`; the family constructor's cone MUST contain
   `ConsistencyPropertyEqOn`, `AConsistent` and `Derivable`. A root cannot pass by depending
   on nothing.
3. STALENESS — every exactly-named forbidden declaration must still exist.
4. PROOF-ONLY — `truth_both` and `exists_henkinComplete` (and, for the source-fragment root,
   `realize_mapLanguage`) must be absent from each endpoint's TYPE, so their presence in the cone
   certifies theorem-body traversal.

Theorem bodies are traversed (`.thmInfo` matched explicitly), as in the other cone guards.

Run with: lake env lean scripts/check_henkin_closed_cone.lean
-/
import InfinitaryLogic.Admissible.Barwise.HenkinClosed
import InfinitaryLogic.Admissible.Barwise.HenkinClosure
import InfinitaryLogic.Admissible.Barwise.SourceFragment
import InfinitaryLogic.Admissible.Barwise.ConsistencyBridge
import InfinitaryLogic.Methods.Henkin.Construction

open Lean

def declValue? (ci : ConstantInfo) : Option Expr :=
  match ci with
  | .defnInfo v => some v.value
  | .thmInfo v => some v.value
  | .opaqueInfo v => some v.value
  | _ => none

/-- Transitive dependencies through types and bodies.  With `skipProofs := true`, theorem
bodies are not followed (definition bodies and all types still are), which is the traversal a
proof-only witness must be absent from. -/
partial def transitiveDepsWith (env : Environment) (skipProofs : Bool) (start : Name) :
    NameSet := Id.run do
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
      let followBody := match ci with
        | .thmInfo _ => !skipProofs
        | _ => true
      if followBody then
        match declValue? ci with
        | some v => cs := cs.union v.getUsedConstantsAsSet
        | none => pure ()
      for c in cs do
        if !seen.contains c then stack := c :: stack
  return seen

def transitiveDeps (env : Environment) (start : Name) : NameSet :=
  transitiveDepsWith env false start

/-- Forbidden by exact name (existence-checked). -/
def forbiddenExact : List Name :=
  [`FirstOrder.Language.truthLemma,
   `FirstOrder.Language.ConsistencyProperty.MaximalConsistent,
   `FirstOrder.Language.ConsistencyProperty.exists_maximal,
   `FirstOrder.Language.FullBarwiseFragment,
   `FirstOrder.Language.BarwiseFragment,
   `FirstOrder.Language.FiniteCompactFragment,
   `FirstOrder.Language.AdmissibleFragmentCore]

/-- Forbidden by substring (catches the whole maximal-consistency namespace). -/
def forbiddenSub : List String :=
  ["MaximalConsistent", "FullBarwiseFragment", "BarwiseFragment", "FiniteCompactFragment",
   "AdmissibleFragmentCore", "henkinComplete_univ_of_maximal"]

/-- Per-root required witnesses: the endpoint must run the fair enumeration and the forward
truth lemma; the family constructor must consume the kernel's structure and the proof system. -/
def guardedRoots : List (Name × List Name) :=
  [(`FirstOrder.Language.HenkinClosed.exists_countable_model_of_aconsistent,
    [`FirstOrder.Language.HenkinComplete, `FirstOrder.Language.AConsistent,
     `FirstOrder.Language.Derivable, `FirstOrder.Language.exists_henkinComplete,
     `FirstOrder.Language.truth_both]),
   (`FirstOrder.Language.HenkinClosed.consistencyPropertyEqOn,
    [`FirstOrder.Language.ConsistencyPropertyEqOn, `FirstOrder.Language.AConsistent,
     `FirstOrder.Language.Derivable]),
   -- The source-fragment adapter: constants-expanded universe, Henkin closure, fair enumeration,
   -- forward truth lemma, and reduct transport must all be consumed.
   (`FirstOrder.Language.Fragment.exists_countable_model_of_aconsistent_withConstants,
    [`FirstOrder.Language.Fragment.withNatConstantsSentences,
     `FirstOrder.Language.Fragment.HenkinBasis,
     `FirstOrder.Language.HenkinClosed, `FirstOrder.Language.AConsistent,
     `FirstOrder.Language.exists_henkinComplete, `FirstOrder.Language.truth_both,
     `FirstOrder.Language.BoundedFormulaω.realize_mapLanguage]),
   -- The minimal-closure family constructor: the kernel's structure and the proof system.
   (`FirstOrder.Language.HenkinClosedMin.consistencyPropertyEqOn,
    [`FirstOrder.Language.ConsistencyPropertyEqOn, `FirstOrder.Language.AConsistent,
     `FirstOrder.Language.Derivable]),
   -- The closure endpoint: the closure operator, the generic negation closure, the basis it
   -- supplies, and the whole source-fragment route below it.
   (`FirstOrder.Language.Fragment.exists_countable_model_of_aconsistent_henkinClosure,
    [`FirstOrder.Language.Fragment.henkinClosure, `FirstOrder.Language.Fragment.negationClosure,
     `FirstOrder.Language.Fragment.henkinBasisSeed, `FirstOrder.Language.Fragment.HenkinBasis,
     `FirstOrder.Language.Fragment.withNatConstantsSentences,
     `FirstOrder.Language.HenkinClosed, `FirstOrder.Language.HenkinClosedMin,
     `FirstOrder.Language.AConsistent, `FirstOrder.Language.exists_henkinComplete,
     `FirstOrder.Language.truth_both,
     `FirstOrder.Language.BoundedFormulaω.realize_mapLanguage])]

def requiredWitness : List Name := (guardedRoots.map Prod.snd).flatten

run_cmd do
  let env ← getEnv
  for f in forbiddenExact do
    unless (env.find? f).isSome do
      throwError "[STALE GUARD] forbidden declaration {f} no longer exists — update this list"
  for w in requiredWitness do
    unless (env.find? w).isSome do throwError "required witness {w} not found"
  -- Theorem-body traversal is certified, not assumed, by two traversals: a proof-only witness
  -- must be ABSENT from the cone that skips theorem bodies (types and definition bodies are
  -- still followed, so a witness reachable through a definition does not qualify) and PRESENT
  -- in the cone that follows them.  Absence from the endpoint's type alone is insufficient.
  let proofOnly : List (Name × List Name) :=
    [(`FirstOrder.Language.HenkinClosed.exists_countable_model_of_aconsistent,
      [`FirstOrder.Language.truth_both, `FirstOrder.Language.exists_henkinComplete]),
     (`FirstOrder.Language.Fragment.exists_countable_model_of_aconsistent_withConstants,
      [`FirstOrder.Language.truth_both, `FirstOrder.Language.exists_henkinComplete,
       `FirstOrder.Language.BoundedFormulaω.realize_mapLanguage]),
     (`FirstOrder.Language.Fragment.exists_countable_model_of_aconsistent_henkinClosure,
      [`FirstOrder.Language.truth_both, `FirstOrder.Language.exists_henkinComplete,
       `FirstOrder.Language.BoundedFormulaω.realize_mapLanguage])]
  for (endpoint, ws) in proofOnly do
    unless (env.find? endpoint).isSome do throwError "endpoint {endpoint} not found"
    let noProofs := transitiveDepsWith env true endpoint
    let withProofs := transitiveDepsWith env false endpoint
    for w in ws do
      if noProofs.contains w then
        throwError "[WEAKENED CHECK] {w} is reachable from {endpoint} without traversing any \
          theorem body; requiring it below would no longer certify proof traversal"
      unless withProofs.contains w do
        throwError "[MISSING WITNESS] {endpoint} does not consume {w} in its proof"
  for (root, witnesses) in guardedRoots do
    unless (env.find? root).isSome do throwError "root declaration {root} not found"
    let deps := transitiveDeps env root
    let hits := deps.toList.filter fun d =>
      forbiddenExact.contains d || forbiddenSub.any fun s => (d.toString.splitOn s).length ≠ 1
    unless hits.isEmpty do
      throwError "[FORBIDDEN] {root} reaches maximality or legacy fragment machinery: {hits}"
    let missing := witnesses.filter fun r => !deps.contains r
    unless missing.isEmpty do
      throwError "[MISSING WITNESS] {root} does not consume the kernel: {missing}"
  logInfo "HenkinClosed cone guard: OK (fair-enumeration kernel and reduct transport consumed; \
    no maximality, no legacy fragment structures)"
