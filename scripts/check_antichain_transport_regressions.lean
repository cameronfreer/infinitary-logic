/-
Regression guard for antichain transport across a measurable embedding and its Morleyization
specialization.

Required shapes: the empty class transports (both sides thin); an isomorphism-respecting
homeomorphic identity transports trivially; the Morleyization specialization admits the empty
family and an arbitrary class, not assumed Borel, in its statement (the check is the absence of
the hypothesis, not a concrete non-Borel example).  Headline declarations on standard
axioms.

Run with: lake env lean scripts/check_antichain_transport_regressions.lean
-/
import InfinitaryLogic.Descriptive.MorleyizationThin

open Lean FirstOrder Language MeasureTheory

/-- The identity is a measurable embedding respecting any relation: transport is the identity. -/
theorem identity_regression {X : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X]
    [BorelSpace X] (r : Setoid X) (A : Set X) :
    IsThinOn r (id '' A) ↔ IsThinOn r A :=
  isThinOn_image_iff MeasurableEmbedding.id (fun _ _ => Iff.rfl) A

/-- The empty class is thin on both sides. -/
theorem empty_class_regression {X Y : Type*} [TopologicalSpace X] [PolishSpace X]
    [MeasurableSpace X] [BorelSpace X] [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y]
    [BorelSpace Y] {r : Setoid X} {r' : Setoid Y} {g : X → Y} (hg : MeasurableEmbedding g)
    (hrel : ∀ x y, r'.r (g x) (g y) ↔ r.r x y) :
    IsThinOn r' (g '' ∅) := by
  rw [isThinOn_image_iff hg hrel]
  rintro ⟨P, -, ⟨x, hx⟩, hsub, -⟩
  exact hsub hx

/-- The Morleyization specialization with the empty family, on an arbitrary class: no Borelness
hypothesis appears in the statement. -/
theorem empty_family_regression {L : Language.{0, 0}} [L.IsRelational]
    [Countable (Σ l, L.Relations l)] (C : Set (StructureSpace L)) :
    IsThinOn (structureIsoSetoid (L.morleyize ∅)) (morleyCode ∅ '' C) ↔
      IsThinOn (structureIsoSetoid L) C :=
  isThinOn_morleyCode_image_iff C

def headline : List Name :=
  [`hasCantorAntichainOn_image_iff, `isThinOn_image_iff,
   `FirstOrder.Language.hasCantorAntichainOn_morleyCode_image_iff,
   `FirstOrder.Language.isThinOn_morleyCode_image_iff,
   `identity_regression, `empty_class_regression, `empty_family_regression]

def standardAxioms : List Name := [`propext, `Classical.choice, `Quot.sound]

run_cmd do
  let env ← getEnv
  for n in headline do
    unless (env.find? n).isSome do throwError "headline declaration {n} not found"
    let axs ← Elab.Command.liftCoreM (collectAxioms n)
    let bad := axs.toList.filter fun a => !standardAxioms.contains a
    unless bad.isEmpty do throwError "[NONSTANDARD AXIOMS] {n} uses {bad}"
  logInfo "antichain-transport guard: OK (identity, empty class, empty family on an arbitrary \
    class; headline declarations on standard axioms)"
