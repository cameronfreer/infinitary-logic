/-
Regression guard for observable constancy (`Descriptive/CountableSplits.lean`,
`Descriptive/ObservableConstancy.lean`).

Checked: the **constant-off-countable corollary** on Cantor space with **both choices of countable
side** (a map with a singleton true side and one with a singleton false side) and a **constant
map**; a **genuine countable-exception** regression (the exceptional set of the predicates `x = xs i`
must contain every `xs i`); **simultaneous constancy** of a repeated sentence family on a `Bool` presentation; and the
**Borel-observation theorem** as a conditional API composition on a `Language.{0, 1}` signature
with nullary symbols and a presentation type carrying **no measurable structure**; and the same theorem
with a **`Type 1` parameter space** (the Borel model-class subtype of a sentence of that signature,
standard Borel and with measurable inclusion by the library) and a **`Type y` target**, again with no
measurable structure on the presentation type and no consumer-defined bridge, as conditional API
composition.  Headline
declarations use only the standard axioms.

Run with: lake env lean scripts/check_observable_constancy_regressions.lean
-/
import InfinitaryLogic.Descriptive.ObservableConstancy

open Lean FirstOrder Language

universe y

/-- Cantor space is uncountable (diagonal argument). -/
theorem not_countable_cantor : ¬ Countable (ℕ → Bool) := fun _ => by
  obtain ⟨g, hg⟩ := exists_surjective_nat (ℕ → Bool)
  obtain ⟨n, hn⟩ := hg fun k => !(g k k)
  have := congrFun hn n
  simp at this

open Classical in
/-- **Both choices of countable side**, and a constant map. -/
theorem corollary_regression (x₀ : ℕ → Bool) :
    (∃ x₁, ({x | decide (x = x₀) ≠ decide (x₁ = x₀)} : Set (ℕ → Bool)).Countable) ∧
    (∃ x₁, ({x | decide (x ≠ x₀) ≠ decide (x₁ ≠ x₀)} : Set (ℕ → Bool)).Countable) ∧
    (∃ _x₁ : ℕ → Bool, ({_x | (true : Bool) ≠ true} : Set (ℕ → Bool)).Countable) :=
  ⟨constant_off_countable_of_splits not_countable_cantor (fun x => decide (x = x₀))
      (fun _ : Unit => fun b => b = true) (fun y z h => by cases y <;> cases z <;> simp_all)
      (fun _ => Or.inl (by simp)),
    constant_off_countable_of_splits not_countable_cantor (fun x => decide (x ≠ x₀))
      (fun _ : Unit => fun b => b = true) (fun y z h => by cases y <;> cases z <;> simp_all)
      (fun _ => Or.inr (by simp)),
    constant_off_countable_of_splits not_countable_cantor (fun _ => true)
      (fun _ : Unit => fun b => b = true) (fun y z h => by cases y <;> cases z <;> simp_all)
      (fun _ => Or.inr (by simp))⟩

/-- **Genuine countable exceptions**: for the predicates `x = xs i` (`i : ℕ`), every `xs i` lies
in the exceptional set.  (If some `xs i` were outside it, constancy would force every point outside
it to equal `xs i`, so the complement would be a subsingleton and Cantor space countable.) -/
theorem exception_regression (xs : ℕ → (ℕ → Bool)) :
    ∃ E : Set (ℕ → Bool), E.Countable ∧ (∀ x ∉ E, ∀ y ∉ E, ∀ i, x = xs i ↔ y = xs i) ∧
      ∀ i, xs i ∈ E := by
  obtain ⟨E, hE, hconst⟩ := exists_countable_exceptions_of_splits (fun i x => x = xs i)
    (fun i => Or.inl (by simp))
  refine ⟨E, hE, hconst, fun i => ?_⟩
  by_contra hi
  apply not_countable_cantor
  apply Set.countable_univ_iff.mp
  refine (hE.union (Set.countable_singleton (xs i))).mono fun y _ => ?_
  by_cases hy : y ∈ E
  · exact Or.inl hy
  · exact Or.inr ((hconst y hy (xs i) hi i).mpr rfl)

/-- A `Type 1` relational signature with a symbol at every arity, including arity `0`. -/
def bigLang : Language.{0, 1} where
  Functions _ := Empty
  Relations n := ULift.{1} (Fin (n + 1))

instance : bigLang.IsRelational := fun _ => inferInstanceAs (IsEmpty Empty)

instance : Countable (Σ n, bigLang.Relations n) :=
  inferInstanceAs (Countable (Σ n, ULift.{1} (Fin (n + 1))))

/-- **Simultaneous constancy** of a repeated family on a `Bool` presentation. -/
theorem simultaneous_regression (c : StructureSpace bigLang) (φ : bigLang.Sentenceω) :
    ∃ E : Set Bool, E.Countable ∧ ∀ q ∉ E, ∀ q' ∉ E, ∀ n : ℕ,
      (fun (θ : bigLang.Sentenceω) (_ : Bool) => c ∈ ModelsOf θ) ((fun _ => φ) n) q ↔
      (fun (θ : bigLang.Sentenceω) (_ : Bool) => c ∈ ModelsOf θ) ((fun _ => φ) n) q' :=
  sentences_constant_off_countable (fun θ (_ : Bool) => c ∈ ModelsOf θ)
    (fun _ => Or.inl (Set.to_countable _)) (fun _ => φ)

/-- **Conditional API composition** of the Borel-observation theorem: `Q` carries no measurable
structure, measurability sits on the composite, and the family, presentation, truth, and split
hypotheses are explicit. -/
theorem observation_regression {X : Type} [MeasurableSpace X] [StandardBorelSpace X]
    (codes : X → StructureSpace bigLang) (hcodes : Measurable codes)
    {Q : Type} (classOf : X → Q) (honto : Function.Surjective classOf)
    (hiso : ∀ x y, (structureIsoSetoid bigLang).r (codes x) (codes y) → classOf x = classOf y)
    (hQ : ¬ Countable Q) (truth : bigLang.Sentenceω → Q → Prop)
    (htruth : ∀ φ x, truth φ (classOf x) ↔ codes x ∈ ModelsOf φ)
    (hsplit : ∀ φ, ({q | truth φ q} : Set Q).Countable ∨ ({q | ¬ truth φ q} : Set Q).Countable)
    (f : Q → Bool) (hf : Measurable (f ∘ classOf)) :
    ∃ q₀, ({q | f q ≠ f q₀} : Set Q).Countable :=
  constant_off_countable_of_borel_observation codes hcodes classOf honto hiso hQ truth htruth
    hsplit f hf

/-- **Higher-universe parameter and target spaces**, conditional API composition: the parameter space
is the Borel model-class subtype `↥(ModelsOf φ)` of a sentence of the `Language.{0, 1}` signature (in
`Type 1`), with its standard-Borel instance and the measurability of the inclusion supplied by the
library, the target `Y : Type y` with its own measurable and countably separated assumptions, and a
presentation type `Q` with no measurable-space instance.  No consumer-defined shrinking bridge; the
split, uncountability, and presentation hypotheses remain hypotheses. -/
theorem higher_universe_observation_regression {Y : Type y} [MeasurableSpace Y]
    [MeasurableSpace.CountablySeparated Y] (φ : bigLang.Sentenceω)
    {Q : Type} (classOf : ↥(ModelsOf φ) → Q) (honto : Function.Surjective classOf)
    (hiso : ∀ x y : ↥(ModelsOf φ), (structureIsoSetoid bigLang).r x.1 y.1 → classOf x = classOf y)
    (hQ : ¬ Countable Q) (truth : bigLang.Sentenceω → Q → Prop)
    (htruth : ∀ ψ (x : ↥(ModelsOf φ)), truth ψ (classOf x) ↔ x.1 ∈ ModelsOf ψ)
    (hsplit : ∀ ψ, ({q | truth ψ q} : Set Q).Countable ∨ ({q | ¬ truth ψ q} : Set Q).Countable)
    (f : Q → Y) (hf : Measurable (f ∘ classOf)) :
    ∃ q₀, ({q | f q ≠ f q₀} : Set Q).Countable :=
  constant_off_countable_of_borel_observation (Subtype.val : ↥(ModelsOf φ) → StructureSpace bigLang)
    measurable_subtype_coe classOf honto hiso hQ truth htruth hsplit f hf

/-! ### Axiom hygiene -/

def headline : List Name :=
  [`constant_off_countable_of_splits,
   `FirstOrder.Language.sentences_constant_off_countable,
   `FirstOrder.Language.constant_off_countable_of_borel_observation,
   `not_countable_cantor, `corollary_regression, `exception_regression, `simultaneous_regression,
   `observation_regression, `higher_universe_observation_regression]

def standardAxioms : List Name := [`propext, `Classical.choice, `Quot.sound]

run_cmd do
  let env ← getEnv
  for n in headline do
    unless (env.find? n).isSome do throwError "headline declaration {n} not found"
    let axs ← Elab.Command.liftCoreM (collectAxioms n)
    let bad := axs.toList.filter fun a => !standardAxioms.contains a
    unless bad.isEmpty do throwError "[NONSTANDARD AXIOMS] {n} uses {bad}"
  logInfo "observable-constancy regression guard: OK (both countable sides and a constant map on \
    Cantor space, genuine countable exceptions, simultaneous constancy of a repeated family, conditional Borel-observation \
    composition on Language.{0, 1} at parameter space Type and at the Type 1 model-class subtype \
    with a Type y target, no measurable structure on the presentation; headline \
    declarations on standard axioms)"
