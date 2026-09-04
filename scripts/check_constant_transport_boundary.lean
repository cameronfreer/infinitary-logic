/-
Boundary guard for the syntactic consistency transport (issue #19).

`Language.IsRelational` empties every function arity, including arity zero, so a relational
language has no closed term. The relational kernel adapters (`HenkinClosed.lean`,
`SourceFragment.lean`) require `[L.IsRelational]`; the syntactic transport
(`ConstantTransport.lean`) requires a closed base term `t₀ : L.Term Empty`. A declaration
assuming both is vacuous — it would type-check and prove anything by explosion — so this guard:

1. requires the boundary lemma `isEmpty_term_empty_of_isRelational` to exist;
2. REJECTS any declaration in the three modules whose TYPE mentions both `IsRelational` and
   `Term`, the signature shape of such a vacuous composite — except the boundary lemma itself,
   which refutes the combination rather than assuming it;
3. NEGATIVE CONTROL: certifies the mechanism by checking that a synthetic declaration with that
   shape, declared in this file, IS detected.

Run with: lake env lean scripts/check_constant_transport_boundary.lean
-/
import InfinitaryLogic.Admissible.Barwise.ConstantTransport

open Lean FirstOrder Language

/-- Negative control: exactly the vacuous shape the guard must catch. -/
theorem vacuousShapeControl {L : Language.{0, 0}} [L.IsRelational] (t₀ : L.Term Empty) : False :=
  (isEmpty_term_empty_of_isRelational).false t₀

def mentionsBoth (env : Environment) (n : Name) : Bool :=
  match env.find? n with
  | none => false
  | some ci =>
    let cs := ci.type.getUsedConstantsAsSet
    cs.contains `FirstOrder.Language.IsRelational && cs.contains `FirstOrder.Language.Term

/-- The one legitimate declaration of that shape: the boundary lemma itself, which *refutes*
the combination rather than assuming it. -/
def allowed : List Name := [`FirstOrder.Language.isEmpty_term_empty_of_isRelational]

def guardedModules : List Name :=
  [`InfinitaryLogic.Admissible.Barwise.ConstantTransport,
   `InfinitaryLogic.Admissible.Barwise.SourceFragment,
   `InfinitaryLogic.Admissible.Barwise.HenkinClosed]

run_cmd do
  let env ← getEnv
  unless (env.find? `FirstOrder.Language.isEmpty_term_empty_of_isRelational).isSome do
    throwError "boundary lemma isEmpty_term_empty_of_isRelational not found"
  -- negative control: the mechanism must see the vacuous shape
  unless mentionsBoth env `vacuousShapeControl do
    throwError "negative control FAILED: the guard cannot detect the vacuous shape"
  -- the guarded modules must contain no declaration of that shape
  let mut hits : List Name := []
  for (n, _) in env.constants.map₁.toList do
    match env.getModuleFor? n with
    | some m =>
      if guardedModules.contains m && !n.isInternal && !allowed.contains n &&
          mentionsBoth env n then
        hits := n :: hits
    | none => pure ()
  unless hits.isEmpty do
    throwError "[VACUOUS COMPOSITE] declarations assuming both a relational language and a closed \
      term: {hits}"
  logInfo "constant-transport boundary guard: OK (no declaration assumes both IsRelational and a \
    closed term; the syntactic transport and the relational kernel stay uncomposed)"
