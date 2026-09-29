/-
Regression guard for Gδ subsets of Polish spaces and Gδ sets of coded models
(`Descriptive/GDeltaPolish.lean`, `Descriptive/ModelsOfGDelta.lean`).

Generic theorem: the **whole space**, the **empty subset**, an **empty ambient space**, a Gδ set with
**empty subtype**, recovery of the **open and closed cases**, and the instance on the **subspace
topology**; the standard-Borel corollary.  Coded models: the Polish corollary on the subspace
topology as conditional API composition; the **closure lemmas** for finite, countable, and
encodable-indexed conjunctions applied; and the **counterexample** that the Gδ hypothesis is
not automatic, formalized on the set of codes (the codes with finite `P`-extension in the
one-unary-relation language are countable and dense in a perfect Polish space, hence not Gδ by
Baire category; their identification with the model set of the finitely-many-`P` sentence is stated
in prose).  Headline declarations use only the standard axioms.

Run with: lake env lean scripts/check_gdelta_polish_regressions.lean
-/
import InfinitaryLogic.Descriptive.ModelsOfGDelta
import Mathlib.Topology.Baire.CompleteMetrizable

open Lean FirstOrder Language Set Topology TopologicalSpace Filter

/-! ### The generic theorem -/

/-- **Whole space, empty subset, empty ambient space, empty subtype.** -/
theorem generic_edge_regression {α : Type} [TopologicalSpace α] [PolishSpace α] :
    PolishSpace (Set.univ : Set α) ∧ PolishSpace (∅ : Set α) ∧
    (∀ [IsEmpty α] {s : Set α}, IsGδ s → PolishSpace s) ∧
    (∀ {s : Set α}, IsGδ s → IsEmpty s → PolishSpace s) :=
  ⟨IsGδ.univ.polishSpace, IsGδ.empty.polishSpace,
    fun {_} {s} (hs : IsGδ s) => hs.polishSpace, fun hs _ => hs.polishSpace⟩

/-- **The open and closed cases are recovered.** -/
theorem generic_recovery_regression {α : Type} [TopologicalSpace α] [PolishSpace α] {s : Set α} :
    (IsOpen s → PolishSpace s) ∧ (IsClosed s → PolishSpace s) :=
  ⟨fun hs => hs.isGδ.polishSpace, fun hs => hs.isGδ.polishSpace⟩

/-- **The instance is on the subspace topology**, and the standard-Borel corollary. -/
theorem generic_subspace_regression {α : Type} [TopologicalSpace α] [PolishSpace α]
    [MeasurableSpace α] [BorelSpace α] {s : Set α} (hs : IsGδ s) :
    @PolishSpace s instTopologicalSpaceSubtype ∧ StandardBorelSpace s :=
  ⟨hs.polishSpace, hs.standardBorelSpace⟩

/-! ### Coded models -/

variable {L : Language.{0, 0}} [L.IsRelational] [Countable (Σ l, L.Relations l)]

/-- **The Polish corollary on the subspace topology** (conditional API composition). -/
theorem models_subspace_regression {φ : L.Sentenceω} (h : IsGδ (ModelsOf φ)) :
    @PolishSpace ↥(ModelsOf φ) instTopologicalSpaceSubtype :=
  polishSpace_modelsOf_of_isGδ h

omit [Countable (Σ l, L.Relations l)] in
/-- **Closure lemmas applied**: finite, countable, and encodable-indexed conjunctions. -/
theorem closure_regression {φ ψ : L.Sentenceω} (hφ : IsGδ (ModelsOf φ)) (hψ : IsGδ (ModelsOf ψ))
    {φs : ℕ → L.Sentenceω} (hφs : ∀ n, IsGδ (ModelsOf (φs n)))
    {ψs : Bool → L.Sentenceω} (hψs : ∀ b, IsGδ (ModelsOf (ψs b))) :
    IsGδ (ModelsOf (φ ⊓ ψ)) ∧ IsGδ (ModelsOf (BoundedFormulaω.iInf φs)) ∧
    IsGδ (ModelsOf (BoundedFormulaω.einf ψs)) ∧
    ModelsOf (φ ⊓ ψ) = ModelsOf φ ∩ ModelsOf ψ :=
  ⟨modelsOf_inf_isGδ hφ hψ, modelsOf_iInf_isGδ hφs, modelsOf_einf_isGδ hψs, modelsOf_inf φ ψ⟩

/-! ### The Gδ hypothesis is not automatic

In the language of one unary relation `P`, the sentence "only finitely many elements satisfy `P`"
has as coded models exactly the codes whose set of `P`-true elements is finite.  That set is
countable (it injects into the finite subsets of `ℕ`) and dense in the code space (every basic open
set constrains finitely many queries, and can be extended by `false`), and the code space is a
perfect Polish space (flipping an unconstrained query stays in any basic open set).  A countable
set in a perfect Polish space is meagre; a dense Gδ set is comeagre; both cannot hold in a
nonempty Baire space.  Hence that model set is not Gδ, and `polishSpace_modelsOf_of_isGδ` does not
apply to it.  The theorems above are stated conditionally for exactly this reason.

Formalized below on the set of codes: `finiteCodes`, the codes whose `P`-extension is finite, is not
Gδ (`finiteCodes_not_isGδ`).  That set is the coded model set of the sentence "only finitely many
elements satisfy `P`" (a countable disjunction over `N` of "at most `N` elements satisfy `P`"); the
identification with `ModelsOf` of that sentence is stated here in prose, not formalized. -/


/-- The language with no function symbols and exactly one unary relation symbol. -/
def unaryLang : FirstOrder.Language.{0,0} where
  Functions _ := Empty
  Relations l := { _u : Unit // l = 1 }

instance : unaryLang.IsRelational := fun _ ↦ inferInstanceAs (IsEmpty Empty)

instance : Countable (Σ l, unaryLang.Relations l) :=
  inferInstanceAs (Countable (Σ l : ℕ, { _u : Unit // l = 1 }))

/-- The unique (unary) relation symbol. -/
def unaryP : unaryLang.Relations 1 := ⟨(), rfl⟩

/-- The query "does `P` hold of `n`?". -/
def qry (n : ℕ) : RelQueryOn unaryLang ℕ := ⟨⟨1, unaryP⟩, fun _ ↦ n⟩

/-- Codes whose unary predicate has finite extension. -/
def finiteCodes : Set (StructureSpace unaryLang) :=
  {c | {n : ℕ | c ⟨⟨1, unaryP⟩, fun _ ↦ n⟩ = true}.Finite}

/-- Every query has arity one. -/
lemma arity_eq (x : RelQueryOn unaryLang ℕ) : x.1.1 = 1 :=
  (x.1.2 : { _u : Unit // x.1.1 = 1 }).2

/-- The unique tuple entry of a query. -/
def val (x : RelQueryOn unaryLang ℕ) : ℕ := x.2 ⟨0, by rw [arity_eq x]; exact Nat.one_pos⟩

@[simp] lemma val_qry (n : ℕ) : val (qry n) = n := rfl

/-- Every query is `qry n` for `n` its unique tuple entry. -/
lemma query_eq (x : RelQueryOn unaryLang ℕ) : x = qry (val x) := by
  rcases x with ⟨⟨l, ⟨u, hl⟩⟩, t⟩
  subst hl
  cases u
  unfold qry unaryP val
  congr
  funext i
  rw [Subsingleton.elim i ⟨0, Nat.one_pos⟩]

noncomputable instance : DecidableEq (RelQueryOn unaryLang ℕ) := Classical.decEq _

instance : Nonempty (StructureSpace unaryLang) := ⟨fun _ ↦ false⟩

/-- `finiteCodes` is countable. -/
lemma finiteCodes_countable : finiteCodes.Countable := by
  let f : StructureSpace unaryLang → Set ℕ := fun c ↦ {n | c (qry n) = true}
  have hmaps : MapsTo f finiteCodes {t | t.Finite ∧ t ⊆ univ} :=
    fun c hc ↦ ⟨hc, subset_univ _⟩
  have hinj : InjOn f finiteCodes := by
    intro c _ d _ h
    funext x
    rw [query_eq x]
    have := congrArg (fun s : Set ℕ ↦ val x ∈ s) h
    simp only [f, mem_ofPred_eq, eq_iff_iff] at this
    cases hc : c (qry (val x)) <;> cases hd : d (qry (val x)) <;> simp_all
  exact hmaps.countable_of_injOn hinj (countable_ofPred_finite_subset countable_univ)

/-- `finiteCodes` is dense. -/
lemma finiteCodes_dense : Dense finiteCodes := by
  intro c
  let tr : ℕ → StructureSpace unaryLang := fun N x ↦ if val x < N then c x else false
  have hmem : ∀ N, tr N ∈ finiteCodes := by
    intro N
    refine (Set.finite_lt_nat N).subset ?_
    intro n hn
    simp only [mem_ofPred_eq, tr] at hn ⊢
    split_ifs at hn with h
    exact h
  have ht : Tendsto tr atTop (𝓝 c) := by
    apply tendsto_pi_nhds.2
    intro x
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop (val x)] with N hN
    simp [tr, hN]
  exact mem_closure_of_tendsto ht (Eventually.of_forall hmem)

/-- Flip the value of a code at `qry n`. -/
noncomputable def flipAt (x : StructureSpace unaryLang) (n : ℕ) : StructureSpace unaryLang :=
  Function.update x (qry n) (!x (qry n))

lemma flipAt_ne (x : StructureSpace unaryLang) (n : ℕ) : flipAt x n ≠ x := by
  intro h
  have h1 : flipAt x n (qry n) = !x (qry n) := Function.update_self _ _ _
  have h2 := h1.symm.trans (congrFun h (qry n))
  cases x (qry n) <;> simp at h2

lemma tendsto_flipAt (x : StructureSpace unaryLang) : Tendsto (flipAt x) atTop (𝓝 x) := by
  apply tendsto_pi_nhds.2
  intro y
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_gt_atTop (val y)] with n hn
  have hne : y ≠ qry n := by
    intro h
    rw [h, val_qry] at hn
    exact lt_irrefl n hn
  exact (Function.update_of_ne hne _ _).symm

/-- Singletons are nowhere dense in the code space (no isolated points). -/
lemma isNowhereDense_singleton (x : StructureSpace unaryLang) :
    IsNowhereDense ({x} : Set (StructureSpace unaryLang)) := by
  rw [isClosed_singleton.isNowhereDense_iff, eq_empty_iff_forall_notMem]
  intro y hy
  have hyx : y ∈ ({x} : Set (StructureSpace unaryLang)) := interior_subset hy
  rw [mem_singleton_iff] at hyx
  subst hyx
  have hnhds : ({y} : Set (StructureSpace unaryLang)) ∈ 𝓝 y := mem_interior_iff_mem_nhds.1 hy
  obtain ⟨n, hn⟩ := ((tendsto_flipAt y).eventually hnhds).exists
  exact flipAt_ne y n hn

/-- `finiteCodes` is meagre, being a countable union of nowhere dense singletons. -/
lemma finiteCodes_isMeagre : IsMeagre finiteCodes := by
  refine (isMeagre_biUnion finiteCodes_countable
    (fun x _ ↦ (isNowhereDense_singleton x).isMeagre)).mono ?_
  intro x hx
  exact mem_biUnion hx rfl

/-- The set of codes with finite unary predicate is not Gδ. -/
theorem finiteCodes_not_isGδ : ¬ IsGδ finiteCodes := fun h ↦
  not_isMeagre_of_isGδ_of_dense h finiteCodes_dense finiteCodes_isMeagre


/-! ### Axiom hygiene -/

def headline : List Name :=
  [`IsGδ.polishSpace, `IsGδ.standardBorelSpace,
   `FirstOrder.Language.polishSpace_modelsOf_of_isGδ, `FirstOrder.Language.modelsOf_inf,
   `FirstOrder.Language.modelsOf_inf_isGδ, `FirstOrder.Language.modelsOf_iInf,
   `FirstOrder.Language.modelsOf_iInf_isGδ, `FirstOrder.Language.modelsOf_einf,
   `FirstOrder.Language.modelsOf_einf_isGδ,
   `generic_edge_regression, `generic_recovery_regression, `generic_subspace_regression,
   `models_subspace_regression, `closure_regression, `finiteCodes_not_isGδ]

def standardAxioms : List Name := [`propext, `Classical.choice, `Quot.sound]

run_cmd do
  let env ← getEnv
  for n in headline do
    unless (env.find? n).isSome do throwError "headline declaration {n} not found"
    let axs ← Elab.Command.liftCoreM (collectAxioms n)
    let bad := axs.toList.filter fun a => !standardAxioms.contains a
    unless bad.isEmpty do throwError "[NONSTANDARD AXIOMS] {n} uses {bad}"
  logInfo "gdelta-polish regression guard: OK (whole space, empty subset, empty ambient space, \
    empty subtype, open and closed cases recovered, subspace topology and standard Borel; coded \
    models: subspace corollary, closure under finite, countable, and encodable conjunctions; \
    non-Gδ counterexample formalized on the code set; headline declarations on standard axioms)"
