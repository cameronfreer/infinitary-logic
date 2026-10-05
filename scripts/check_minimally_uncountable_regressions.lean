/-
Regression guard for minimally uncountable classes and sentence cuts
(`InfinitaryLogic/Descriptive/MinimallyUncountable.lean`), for the level-`α` Scott sentence
(`scottSentenceAt` and `realize_scottSentenceAt_iff_BFEquiv` in
`InfinitaryLogic/Scott/Formula.lean`), and for four small additions beside existing
declarations: `mem_modelsOf_iff_realize` (`Descriptive/SatisfactionBorel.lean`, implicit `L`),
`modelsOf_not` and `modelsOf_inf_not` (`Descriptive/ModelsOfGDelta.lean`) and
`BFScattered.mono` (`Descriptive/BFScattered.lean`).

Every public declaration of the module and every addition is *applied*, not only listed for its
axioms.

* **Generic applications.**  The rank definitions and their lemmas (`BoundedRankOn`,
  `UnboundedRankOn`, `unboundedRankOn_iff_not_boundedRankOn`, `BoundedRankOn.mono`,
  `boundedRankOn_empty`, `boundedRankOn_sUnion`, `BoundedRankOn.union`) for an arbitrary
  `Language.{u, v}` with neither a relational nor a countability instance; the sentence-cut
  layer (`modelsOf_inf_not`, `modelsOf_not`, `mem_modelsOf_iff_realize` with `L` implicit,
  `BFScattered.mono`, `MinimallyUncountableOn`, `Sentenceω.MinimallyUncountable`,
  `Sentenceω.minimallyUncountable_iff_inf`) for an arbitrary relational language with no
  countability; the back-and-forth classes (`modelsOf_scottSentenceAt`,
  `MinimallyUncountableOn.countable_bfClass_or_compl`, `exists_bfClass_compl_of_sentence_cuts`,
  `MinimallyUncountableOn.exists_bfClass_compl_countable`) and the concentration equivalence
  (`MinimallyUncountableOn.concentratedAtBFLevels`,
  `ConcentratedAtBFLevels.minimallyUncountableOn`, `bfScattered_and_minimallyUncountableOn_iff`,
  `minimallyUncountableOn_iff`) for countably many relation symbols.  The engine is applied
  with the smallness "`ρ` bounded" for an arbitrary `ρ`, with no isolating rank in scope.
* **The Scott sentence at a level.**  `realize_scottSentenceAt_iff_BFEquiv` for an arbitrary
  `Language.{u, v}` with no relational instance, carriers in independent universes `w`, `w'`
  and the level in a third universe `x`.  The explicit universe lists are pinned: the
  declarations' `levelParams` are exactly `[uL, vL, wM, uO]` and `[uL, vL, wM, wN, uO]`, and the
  statement shapes are pinned by explicit instantiation at distinct universes
  (`scottSentenceAt.{1, 2, 3, 4}`, `realize_scottSentenceAt_iff_BFEquiv.{1, 2, 3, 5, 4}`).
  The bridge `(scottSentence M).toSentenceω = scottSentenceAt M (stabilizationOrdinal M)` holds
  by `rfl` (this guard imports `Scott.Sentence`, through `Descriptive.ScatteredCounting`; the
  module does not).
* **Necessity of `α < ω₁`.**  `scottFormula` is `⊤` at `ω₁` (`scottFormula_omega_one`), so in
  the language with one nullary relation symbol, the structure on `Unit` where it fails
  satisfies `scottSentenceAt` at `ω₁` of the structure on `Unit` where it holds, yet the two are
  not back-and-forth equivalent even at level `0`: the iff fails at `α = ω₁`.
* **Sentence cuts, not arbitrary invariant subsets (decision 9).**
  `exists_rankSplit_of_unboundedRankOn`: a class on which `ρ < ω₁` is unbounded has a cut by a
  set of rank values with both sides unbounded.  For an isomorphism-invariant `ρ` that cut is
  isomorphism invariant, so the variant of minimality over arbitrary invariant subsets is
  unsatisfiable (`not_minimal_over_invariant_subsets`).
* **Empty class.**  It is bounded, not unbounded, and not minimally uncountable.
* **Signature checks.**  The types of all public declarations of the module are inspected: an
  instance `Countable (Σ l, _)` occurs in exactly the back-and-forth and concentration
  statements (`[COUNTABILITY DRIFT]`), every public declaration is classified, and no type
  mentions `IsIsolatingRank` (`[RANK DRIFT]`).  `scottSentenceAt` and
  `realize_scottSentenceAt_iff_BFEquiv` mention neither `IsRelational` nor `StructureSpace`;
  `mem_modelsOf_iff_realize` takes `L` implicitly; each addition is declared in its module
  (`[PLACEMENT]`).
* **Exact import closures.**  The `InfinitaryLogic` closure of `Descriptive.MinimallyUncountable`
  is exactly `allowedClosure` (33 modules: the closures of `Descriptive.BFConcentration` (27),
  `Scott.Formula` (8), `Descriptive.ModelsOfGDelta` (10) and `Lomega1omega.Theory` (4), plus the
  module), and it is checked to be that union.  It contains no module with prefix `Karp`,
  `ModelTheory`, `Methods`, `Admissible`, `Conditional`, `ScottProcess` or `WIP`, none of
  `Descriptive.ScatteredCounting`, `Scott.Sentence`, `Scott.RefinementCount`,
  `Scott.IsolatingLevel`, and no module whose name contains `LopezEscobar` or `SmallVocabulary`
  (`[BROAD CONE]`).  The closures of `Scott.Formula` (8), `Descriptive.SatisfactionBorel` (8),
  `Descriptive.ModelsOfGDelta` (10) and `Descriptive.BFScattered` (25) are pinned exactly, so
  the additions there added no import.
* **Standard axioms** for every declaration of the module (enumerated from the environment), the
  additions, and every declaration of this guard.  The OK line is printed only after the
  closure and axiom checks.

Run with: lake env lean scripts/check_minimally_uncountable_regressions.lean
-/
import InfinitaryLogic.Descriptive.MinimallyUncountable
-- for the `rfl` bridge to `scottSentence`, the rank-split regression, and so that the modules
-- of the boundary exist in the environment (the module itself imports none of them)
import InfinitaryLogic.Descriptive.ScatteredCounting

open Lean FirstOrder FirstOrder.Language Set MeasureTheory Cardinal

universe u v w w' x

noncomputable section

namespace MinimallyUncountableRegressions

/-! ### Generic applications -/

/-- **The rank layer for an arbitrary language**, with neither a relational nor a countability
instance. -/
theorem generic_rank_regression {L : Language.{u, v}} (ρ : StructureSpace L → Ordinal.{0})
    {J K : Set (StructureSpace L)} {S : Set (Set (StructureSpace L))} (hS : S.Countable)
    (hSb : ∀ s ∈ S, BoundedRankOn ρ s) (hJ : BoundedRankOn ρ J) (hK : BoundedRankOn ρ K)
    (hJK : J ⊆ K) :
    (UnboundedRankOn ρ K ↔ ¬ BoundedRankOn ρ K) ∧ BoundedRankOn ρ J ∧ BoundedRankOn ρ ∅ ∧
      BoundedRankOn ρ (⋃₀ S) ∧ BoundedRankOn ρ (J ∪ K) ∧
      (BoundedRankOn ρ K ↔ ∃ β < Ordinal.omega 1, ∀ c ∈ K, ρ c < β) ∧
      (UnboundedRankOn ρ K ↔ ∀ β < Ordinal.omega 1, ∃ c ∈ K, β ≤ ρ c) :=
  ⟨unboundedRankOn_iff_not_boundedRankOn, hK.mono hJK, boundedRankOn_empty,
    boundedRankOn_sUnion hS hSb, hJ.union hK, Iff.rfl, Iff.rfl⟩

/-- **The sentence-cut layer for an arbitrary relational language**, no countability:
`mem_modelsOf_iff_realize` is applied with `L` implicit. -/
theorem generic_cut_regression {L : Language.{u, v}} [L.IsRelational] (Θ θ : L.Sentenceω)
    (c : StructureSpace L) {J K : Set (StructureSpace L)} (hK : BFScattered K) (hJK : J ⊆ K) :
    ModelsOf (Θ ⊓ θ.not) = ModelsOf Θ \ ModelsOf θ ∧ ModelsOf θ.not = (ModelsOf θ)ᶜ ∧
      (c ∈ ModelsOf θ ↔ @Sentenceω.Realize L θ ℕ c.toStructure) ∧ BFScattered J ∧
      (Θ.MinimallyUncountable ↔ MinimallyUncountableOn (ModelsOf Θ)) ∧
      (MinimallyUncountableOn K ↔ ¬ (Quotient.mk (structureIsoSetoid L) '' K).Countable ∧
        ∀ θ : L.Sentenceω, (Quotient.mk (structureIsoSetoid L) '' (K ∩ ModelsOf θ)).Countable ∨
          (Quotient.mk (structureIsoSetoid L) '' (K \ ModelsOf θ)).Countable) ∧
      (Θ.MinimallyUncountable ↔ ¬ (Quotient.mk (structureIsoSetoid L) '' ModelsOf Θ).Countable ∧
        ∀ θ : L.Sentenceω, (Quotient.mk (structureIsoSetoid L) '' ModelsOf (Θ ⊓ θ)).Countable ∨
          (Quotient.mk (structureIsoSetoid L) '' ModelsOf (Θ ⊓ θ.not)).Countable) :=
  ⟨modelsOf_inf_not Θ θ, modelsOf_not θ, mem_modelsOf_iff_realize c θ, hK.mono hJK, Iff.rfl,
    Iff.rfl, Sentenceω.minimallyUncountable_iff_inf Θ⟩

/-- **The back-and-forth classes**, for countably many relation symbols: the code form of the
Scott sentence, the cut by a class, the generic engine with the smallness "`ρ` bounded" for an
arbitrary `ρ` (no isolating rank in scope), and the countable form. -/
theorem bfClass_regression {L : Language.{u, v}} [L.IsRelational]
    [Countable (Σ l, L.Relations l)] {K : Set (StructureSpace L)} (h : MinimallyUncountableOn K)
    (ρ : StructureSpace L → Ordinal.{0}) (hρK : ¬ BoundedRankOn ρ K)
    (hρcut : ∀ θ : L.Sentenceω, BoundedRankOn ρ (K ∩ ModelsOf θ) ∨
      BoundedRankOn ρ (K \ ModelsOf θ))
    (c : StructureSpace L) {α : Ordinal.{0}} (hα : α < Ordinal.omega 1)
    (hKα : Countable (Quotient ((codeBFEquivSetoid L α).comap
      (Subtype.val : K → StructureSpace L)))) :
    ModelsOf (@scottSentenceAt L _ ℕ c.toStructure _ α) = {d | CodeBFEquiv α c d} ∧
      ((Quotient.mk (structureIsoSetoid L) '' (K ∩ {d | CodeBFEquiv α c d})).Countable ∨
        (Quotient.mk (structureIsoSetoid L) '' (K \ {d | CodeBFEquiv α c d})).Countable) ∧
      (∃ a ∈ K, ¬ BoundedRankOn ρ (K ∩ {d | CodeBFEquiv α a d}) ∧
        BoundedRankOn ρ (K \ {d | CodeBFEquiv α a d})) ∧
      ∃ a ∈ K,
        ¬ (Quotient.mk (structureIsoSetoid L) '' (K ∩ {d | CodeBFEquiv α a d})).Countable ∧
          (Quotient.mk (structureIsoSetoid L) '' (K \ {d | CodeBFEquiv α a d})).Countable :=
  ⟨modelsOf_scottSentenceAt c hα, h.countable_bfClass_or_compl c hα,
    exists_bfClass_compl_of_sentence_cuts (BoundedRankOn ρ) (fun _ _ hJK h ↦ h.mono hJK)
      (fun _ hS h ↦ boundedRankOn_sUnion hS h) hρK hρcut hα hKα,
    h.exists_bfClass_compl_countable hα hKα⟩

/-- **The concentration equivalence**, for countably many relation symbols: both directions,
the hypothesis-free form for an analytic class and the form for a scattered analytic class. -/
theorem concentration_regression {L : Language.{u, v}} [L.IsRelational]
    [Countable (Σ l, L.Relations l)] {K : Set (StructureSpace L)} (hKa : AnalyticSet K) :
    (MinimallyUncountableOn K → BFScattered K → ConcentratedAtBFLevels K) ∧
      (ConcentratedAtBFLevels K → ¬ (Quotient.mk (structureIsoSetoid L) '' K).Countable →
        MinimallyUncountableOn K) ∧
      (BFScattered K ∧ MinimallyUncountableOn K ↔
        ConcentratedAtBFLevels K ∧ ¬ (Quotient.mk (structureIsoSetoid L) '' K).Countable) ∧
      (BFScattered K → (MinimallyUncountableOn K ↔
        ConcentratedAtBFLevels K ∧ ¬ (Quotient.mk (structureIsoSetoid L) '' K).Countable)) :=
  ⟨fun h hK ↦ h.concentratedAtBFLevels hK, fun hC hunc ↦ hC.minimallyUncountableOn hKa hunc,
    bfScattered_and_minimallyUncountableOn_iff hKa, minimallyUncountableOn_iff hKa⟩

/-! ### The Scott sentence at a level -/

/-- **The characterization for an arbitrary language**, with no relational instance, carriers
in independent universes and the level in a third universe. -/
theorem generic_scottSentenceAt_regression {L : Language.{u, v}}
    [Countable (Σ l, L.Relations l)] (M : Type w) [L.Structure M] [Countable M] (N : Type w')
    [L.Structure N] {α : Ordinal.{x}} (hα : α < Ordinal.omega 1) :
    (scottSentenceAt (L := L) M α).Realize N ↔
      BFEquiv (L := L) α 0 (Fin.elim0 : Fin 0 → M) (Fin.elim0 : Fin 0 → N) :=
  realize_scottSentenceAt_iff_BFEquiv M N hα

/-- The explicit universe order of `scottSentenceAt`: function symbols, relation symbols, the
carrier, the level; every position distinct. -/
example {L₁ : Language.{1, 2}} [Countable (Σ l, L₁.Relations l)] (A : Type 3) [L₁.Structure A]
    [Countable A] (α : Ordinal.{4}) : L₁.Sentenceω :=
  scottSentenceAt.{1, 2, 3, 4} A α

/-- The explicit universe order of `realize_scottSentenceAt_iff_BFEquiv`: function symbols,
relation symbols, the two carriers, the level; every position distinct. -/
example {L₁ : Language.{1, 2}} [Countable (Σ l, L₁.Relations l)] (A : Type 3) [L₁.Structure A]
    [Countable A] (B : Type 5) [L₁.Structure B] {α : Ordinal.{4}} (hα : α < Ordinal.omega 1) :
    (scottSentenceAt (L := L₁) A α).Realize B ↔
      BFEquiv (L := L₁) α 0 (Fin.elim0 : Fin 0 → A) (Fin.elim0 : Fin 0 → B) :=
  realize_scottSentenceAt_iff_BFEquiv.{1, 2, 3, 5, 4} A B hα

/-- **The bridge to `scottSentence`**, by `rfl`: the Scott sentence is the level-`α` sentence
at the stabilization ordinal. -/
theorem scottSentence_bridge_regression {L : Language.{u, v}} [L.IsRelational]
    [Countable (Σ l, L.Relations l)] (M : Type w) [L.Structure M] [Countable M] :
    (scottSentence (L := L) M).toSentenceω =
      scottSentenceAt (L := L) M (stabilizationOrdinal (L := L) M) :=
  rfl

/-! ### Necessity of `α < ω₁` -/

/-- **`scottFormula` is `⊤` at `ω₁`** (the limit case of its recursion returns `⊤` at limits
`≥ ω₁`). -/
theorem scottFormula_omega_one {L : Language.{u, v}} [L.IsRelational]
    [Countable (Σ l, L.Relations l)] {M : Type w} [L.Structure M] [Countable M] {n : ℕ}
    (a : Fin n → M) : scottFormula (L := L) a (Ordinal.omega.{0} 1) = ⊤ := by
  unfold scottFormula
  rw [Ordinal.limitRecOn_limit _ _ _ _ (Cardinal.isSuccLimit_omega 1)]
  simp

/-- One nullary relation symbol, nothing else. -/
def nullLang : Language.{0, 0} where
  Functions _ := Empty
  Relations l := { _u : Unit // l = 0 }

instance : nullLang.IsRelational := fun _ ↦ inferInstanceAs (IsEmpty Empty)

instance : Subsingleton (Σ l, nullLang.Relations l) :=
  ⟨by rintro ⟨_, ⟨⟨⟩, rfl⟩⟩ ⟨_, ⟨⟨⟩, rfl⟩⟩; rfl⟩

instance : Countable (Σ l, nullLang.Relations l) := Finite.to_countable

/-- The nullary symbol. -/
def nullP : nullLang.Relations 0 := ⟨(), rfl⟩

/-- The structure on `Unit` in which the nullary symbol holds. -/
@[instance_reducible] def trueStr : nullLang.Structure Unit where
  funMap f := Empty.elim f
  RelMap _ _ := True

/-- The structure on `Unit` in which the nullary symbol fails. -/
@[instance_reducible] def falseStr : nullLang.Structure Unit where
  funMap f := Empty.elim f
  RelMap _ _ := False

/-- The level-`ω₁` Scott sentence of the true structure. -/
def psiTrue : nullLang.Sentenceω :=
  @scottSentenceAt nullLang _ Unit trueStr _ (Ordinal.omega.{0} 1)

/-- Back-and-forth equivalence at `ω₁` of the true and the false structure. -/
def bfTrueFalse : Prop :=
  @BFEquiv nullLang Unit trueStr Unit falseStr (Ordinal.omega.{0} 1) 0 Fin.elim0 Fin.elim0

/-- **The characterization fails at `ω₁`**: the false structure satisfies the level-`ω₁`
Scott sentence of the true structure (it is `⊤`), but the two are not back-and-forth
equivalent at `ω₁` (not even at level `0`). -/
theorem omega_one_necessity :
    @Sentenceω.Realize nullLang psiTrue Unit falseStr ∧ ¬ bfTrueFalse ∧
      ¬ (@Sentenceω.Realize nullLang psiTrue Unit falseStr ↔ bfTrueFalse) := by
  have hreal : @Sentenceω.Realize nullLang psiTrue Unit falseStr := by
    rw [psiTrue, scottSentenceAt, @Formulaω.realize_toSentenceω nullLang Unit falseStr,
      @scottFormula_omega_one nullLang _ _ Unit trueStr _ 0 Fin.elim0]
    exact (@Formulaω.realize_top nullLang Unit falseStr _ _).mpr trivial
  have hnot : ¬ bfTrueFalse := fun h ↦ by
    have h0 := (@BFEquiv.zero nullLang Unit trueStr Unit falseStr 0 Fin.elim0 Fin.elim0).mp
      (@BFEquiv.monotone nullLang Unit trueStr Unit falseStr 0 _ _ (Ordinal.omega_pos 1).le _ _ h)
    exact (h0 (.rel nullP Fin.elim0)).mp trivial
  exact ⟨hreal, hnot, fun h ↦ hnot (h.mp hreal)⟩

/-! ### Sentence cuts, not arbitrary invariant subsets -/

/-- **Decision 9 as a theorem**: an unbounded class with values below `ω₁` has a cut by a set of
rank values with both sides unbounded. -/
theorem exists_rankSplit_of_unboundedRankOn {L : Language.{u, v}}
    {ρ : StructureSpace L → Ordinal.{0}} {K : Set (StructureSpace L)}
    (hlt : ∀ c ∈ K, ρ c < Ordinal.omega 1) (hK : UnboundedRankOn ρ K) :
    ∃ E : Set Ordinal.{0}, UnboundedRankOn ρ (K ∩ ρ ⁻¹' E) ∧
      UnboundedRankOn ρ (K \ ρ ⁻¹' E) := by
  set R := ρ '' K
  -- an uncountable set of realized values is cofinal below `ω₁`
  have hcof : ∀ T ⊆ R, ¬ T.Countable → ∀ β < Ordinal.omega 1, ∃ x ∈ T, β ≤ x := by
    intro T _ hT β hβ
    by_contra hne
    push Not at hne
    exact hT ((InfinitaryLogic.setCountable_Iio_of_lt_omega1 β hβ).mono fun x hx ↦ hne x hx)
  -- the realized values are uncountable
  have hR : ¬ R.Countable := by
    intro hc
    have := hc.to_subtype
    obtain ⟨c, hc, hle⟩ := hK _ (InfinitaryLogic.iSup_add_one_lt_omega1 (fun r : R ↦ r.1)
      fun ⟨_, c, hc, rfl⟩ ↦ hlt c hc)
    exact (Order.lt_add_one_iff.mpr le_rfl).not_ge <| hle.trans' <|
      le_ciSup (f := fun r : R ↦ r.1 + 1) Ordinal.bddAbove_of_small ⟨ρ c, c, hc, rfl⟩
  -- split `R` into two uncountable halves
  have hinf : ℵ₀ ≤ #R := by
    by_contra h
    exact hR (Set.countable_coe_iff.mp (Cardinal.mk_le_aleph0_iff.mp (not_le.mp h).le))
  obtain ⟨e⟩ : Nonempty (R ⊕ R ≃ R) := Cardinal.eq.mp (by
    rw [Cardinal.mk_sum, Cardinal.lift_id, Cardinal.add_eq_self hinf])
  have hunc : ∀ f : R → R, Function.Injective f → ¬ (range fun x ↦ (f x).1).Countable := by
    intro f hf hc
    have := hc.to_subtype
    exact hR (Set.countable_coe_iff.mp (Function.Injective.countable
      (f := fun x : R ↦ (⟨(f x).1, x, rfl⟩ : range fun x ↦ (f x).1))
      fun x y hxy ↦ hf (Subtype.ext (by simpa using congrArg Subtype.val hxy))))
  have hsub : ∀ f : R → R, (range fun x ↦ (f x).1) ⊆ R := by
    rintro f _ ⟨x, rfl⟩; exact (f x).2
  refine ⟨range fun x ↦ (e (Sum.inl x)).1, fun β hβ ↦ ?_, fun β hβ ↦ ?_⟩
  · obtain ⟨_, ⟨x, rfl⟩, hle⟩ :=
      hcof _ (hsub _) (hunc _ (e.injective.comp Sum.inl_injective)) β hβ
    obtain ⟨c, hc, hρc⟩ := (e (Sum.inl x)).2
    exact ⟨c, ⟨hc, x, hρc.symm⟩, hρc ▸ hle⟩
  · obtain ⟨_, ⟨x, rfl⟩, hle⟩ :=
      hcof _ (hsub _) (hunc _ (e.injective.comp Sum.inr_injective)) β hβ
    obtain ⟨c, hc, hρc⟩ := (e (Sum.inr x)).2
    refine ⟨c, ⟨hc, ?_⟩, hρc ▸ hle⟩
    rintro ⟨y, hy⟩
    exact Sum.inl_ne_inr (e.injective (Subtype.ext (hy.trans hρc)))

/-- **Minimality over arbitrary invariant subsets is unsatisfiable**: for an isomorphism-invariant
`ρ` with values below `ω₁` on an unbounded class, some isomorphism-invariant subset cuts the
class into two unbounded sides.  Hence `MinimallyUnboundedOn` ranges over sentence cuts. -/
theorem not_minimal_over_invariant_subsets {L : Language.{u, v}} [L.IsRelational]
    {ρ : StructureSpace L → Ordinal.{0}} {K : Set (StructureSpace L)}
    (hinv : ∀ ⦃c d : StructureSpace L⦄, (structureIsoSetoid L).r c d → ρ c = ρ d)
    (hlt : ∀ c ∈ K, ρ c < Ordinal.omega 1) (hK : UnboundedRankOn ρ K) :
    ¬ ∀ E : Set (StructureSpace L),
      (∀ ⦃c d : StructureSpace L⦄, (structureIsoSetoid L).r c d → (c ∈ E ↔ d ∈ E)) →
        BoundedRankOn ρ (K ∩ E) ∨ BoundedRankOn ρ (K \ E) := fun h ↦ by
  obtain ⟨E, h₁, h₂⟩ := exists_rankSplit_of_unboundedRankOn hlt hK
  rcases h (ρ ⁻¹' E) (fun c d hcd ↦ by simp only [mem_preimage, hinv hcd]) with hb | hb
  · exact unboundedRankOn_iff_not_boundedRankOn.mp h₁ hb
  · exact unboundedRankOn_iff_not_boundedRankOn.mp h₂ hb

/-- **The empty class** is bounded, not unbounded, and not minimally uncountable. -/
theorem empty_regression {L : Language.{u, v}} [L.IsRelational]
    (ρ : StructureSpace L → Ordinal.{0}) :
    BoundedRankOn ρ ∅ ∧ ¬ UnboundedRankOn ρ ∅ ∧
      ¬ MinimallyUncountableOn (∅ : Set (StructureSpace L)) :=
  ⟨boundedRankOn_empty, unboundedRankOn_iff_not_boundedRankOn.not.mpr (not_not.mpr
    boundedRankOn_empty), fun h ↦ h.1 (by simp)⟩

end MinimallyUncountableRegressions

end

/-! ### Signature checks -/

open MinimallyUncountableRegressions

/-- Prefix a list of names with `FirstOrder.Language`. -/
def fol (l : List Name) : List Name := l.map (`FirstOrder.Language ++ ·)

/-- The module under test. -/
def targetModule : Name := `InfinitaryLogic.Descriptive.MinimallyUncountable

/-- The public declarations of the module whose types must not assume countably many relation
symbols. -/
def countabilityFree : List Name :=
  fol [`BoundedRankOn, `UnboundedRankOn, `unboundedRankOn_iff_not_boundedRankOn,
    `BoundedRankOn.mono, `boundedRankOn_empty, `boundedRankOn_sUnion, `BoundedRankOn.union,
    `MinimallyUncountableOn, `Sentenceω.MinimallyUncountable,
    `Sentenceω.minimallyUncountable_iff_inf]

/-- The public declarations of the module whose types assume countably many relation symbols:
those that cut by a back-and-forth class (through `scottSentenceAt`) and those that use the
Borel step of `ConcentratedAtBFLevels.countable_isoClasses_or`. -/
def countabilityUsing : List Name :=
  fol [`modelsOf_scottSentenceAt, `MinimallyUncountableOn.countable_bfClass_or_compl,
    `exists_bfClass_compl_of_sentence_cuts, `MinimallyUncountableOn.exists_bfClass_compl_countable,
    `MinimallyUncountableOn.concentratedAtBFLevels, `ConcentratedAtBFLevels.minimallyUncountableOn,
    `bfScattered_and_minimallyUncountableOn_iff, `minimallyUncountableOn_iff]

/-- The additions outside the module, with their modules. -/
def additions : List (Name × Name) :=
  [(`FirstOrder.Language.scottSentenceAt, `InfinitaryLogic.Scott.Formula),
   (`FirstOrder.Language.realize_scottSentenceAt_iff_BFEquiv, `InfinitaryLogic.Scott.Formula),
   (`FirstOrder.Language.mem_modelsOf_iff_realize, `InfinitaryLogic.Descriptive.SatisfactionBorel),
   (`FirstOrder.Language.modelsOf_not, `InfinitaryLogic.Descriptive.ModelsOfGDelta),
   (`FirstOrder.Language.modelsOf_inf_not, `InfinitaryLogic.Descriptive.ModelsOfGDelta),
   (`FirstOrder.Language.BFScattered.mono, `InfinitaryLogic.Descriptive.BFScattered)]

run_cmd do
  let env ← getEnv
  let isCountableSigma (e : Expr) : Bool :=
    e.isAppOfArity ``Countable 1 && e.appArg!.isAppOf ``Sigma
  let typeOf (n : Name) : Elab.Command.CommandElabM Expr := do
    let some ci := env.find? n | throwError "declaration {n} not found"
    return ci.type
  for n in countabilityFree do
    if ((← typeOf n).find? isCountableSigma).isSome then
      throwError "[COUNTABILITY DRIFT] the type of {n} assumes countably many symbols"
  for n in countabilityUsing do
    unless ((← typeOf n).find? isCountableSigma).isSome do
      throwError "[COUNTABILITY DRIFT] the type of {n} no longer assumes countably many \
        symbols; update the guard and the module docstring"
  -- every public declaration of the module is classified; none mentions an isolating rank
  let some idx := env.getModuleIdx? targetModule | throwError "module {targetModule} not found"
  let pub := (env.header.moduleData[idx.toNat]!).constNames.toList.filter fun n ↦
    !n.isInternalDetail && !(n.getString!.endsWith "congr_simp") && !isPrivateName n
  let classified := countabilityFree ++ countabilityUsing
  let unclassified := pub.filter fun n ↦ !classified.contains n
  let absent := classified.filter fun n ↦ !pub.contains n
  unless unclassified.isEmpty && absent.isEmpty do
    throwError "[COUNTABILITY DRIFT] the public declarations of {targetModule} changed \
      (unclassified {unclassified}, not declared there {absent}); classify them"
  for n in pub do
    if ((← typeOf n).find? (·.isConstOf ``FirstOrder.Language.IsIsolatingRank)).isSome then
      throwError "[RANK DRIFT] the type of {n} mentions IsIsolatingRank"
  -- the rank definitions need no relational instance
  for n in fol [`BoundedRankOn, `UnboundedRankOn, `boundedRankOn_sUnion] do
    if ((← typeOf n).find? (·.isAppOf ``FirstOrder.Language.IsRelational)).isSome then
      throwError "[SIGNATURE DRIFT] the type of {n} assumes a relational language"
  -- the additions: placement, and the Scott sentence needs no relational instance or codes
  for (n, m) in additions do
    let some sidx := env.getModuleIdxFor? n | throwError "no module for {n}"
    unless env.header.moduleNames[sidx.toNat]! == m do
      throwError "[PLACEMENT] {n} is not declared in {m}"
  for n in fol [`scottSentenceAt, `realize_scottSentenceAt_iff_BFEquiv] do
    if ((← typeOf n).find? fun e ↦ e.isAppOf ``FirstOrder.Language.IsRelational ||
        e.isConstOf ``FirstOrder.Language.StructureSpace).isSome then
      throwError "[SIGNATURE DRIFT] the type of {n} mentions IsRelational or StructureSpace"
  -- explicit universe lists, pinned by name and position
  let some ss := env.find? `FirstOrder.Language.scottSentenceAt | throwError "no scottSentenceAt"
  unless ss.levelParams == [`uL, `vL, `wM, `uO] do
    throwError "[UNIVERSE DRIFT] scottSentenceAt has universes {ss.levelParams}"
  let some rs := env.find? `FirstOrder.Language.realize_scottSentenceAt_iff_BFEquiv
    | throwError "no realize_scottSentenceAt_iff_BFEquiv"
  unless rs.levelParams == [`uL, `vL, `wM, `wN, `uO] do
    throwError "[UNIVERSE DRIFT] realize_scottSentenceAt_iff_BFEquiv has universes \
      {rs.levelParams}"
  -- `mem_modelsOf_iff_realize` takes `L` implicitly
  let .forallE _ _ _ bi := (← typeOf `FirstOrder.Language.mem_modelsOf_iff_realize)
    | throwError "mem_modelsOf_iff_realize is not a Π-type"
  unless bi == .implicit do
    throwError "[SIGNATURE DRIFT] mem_modelsOf_iff_realize does not take L implicitly"

/-! ### Exact import closures and axiom hygiene -/

/-- The modules transitively imported by `m` (including `m`), read from the environment
header. -/
partial def importClosure (env : Environment) (m : Name) : NameSet :=
  go [m] {}
where
  go : List Name → NameSet → NameSet
    | [], seen => seen
    | m :: rest, seen =>
      if seen.contains m then go rest seen
      else
        let deps := match env.getModuleIdx? m with
          | some idx => (env.header.moduleData[idx.toNat]!).imports.toList.map (·.module)
          | none => []
        go (deps ++ rest) (seen.insert m)

/-- The `InfinitaryLogic` modules of a closure. -/
def ilClosure (env : Environment) (m : Name) : List Name :=
  (importClosure env m).toList.filter fun n ↦ (`InfinitaryLogic).isPrefixOf n

/-- Module prefixes the closure of the module may not reach (the hard boundary). -/
def forbiddenPrefixes : List Name :=
  [`InfinitaryLogic.Karp, `InfinitaryLogic.ModelTheory, `InfinitaryLogic.Methods,
   `InfinitaryLogic.Admissible, `InfinitaryLogic.Conditional, `InfinitaryLogic.ScottProcess,
   `InfinitaryLogic.WIP, `InfinitaryLogic.Descriptive.ScatteredCounting,
   `InfinitaryLogic.Scott.Sentence, `InfinitaryLogic.Scott.RefinementCount,
   `InfinitaryLogic.Scott.IsolatingLevel]

/-- Substrings no module of the closure may contain. -/
def forbiddenSubstrings : List String := ["LopezEscobar", "SmallVocabulary"]

/-- The exact `InfinitaryLogic` import closure of `Descriptive.MinimallyUncountable`. -/
def allowedClosure : List Name :=
  [`InfinitaryLogic.Util, `InfinitaryLogic.OrdinalUtil, `InfinitaryLogic.Topology.Perfect,
   `InfinitaryLogic.Lomega1omega.Syntax, `InfinitaryLogic.Lomega1omega.Semantics,
   `InfinitaryLogic.Lomega1omega.Operations, `InfinitaryLogic.Lomega1omega.OpenBoundsSemantics,
   `InfinitaryLogic.Lomega1omega.Theory,
   `InfinitaryLogic.Scott.AtomicDiagram, `InfinitaryLogic.Scott.BackAndForth,
   `InfinitaryLogic.Scott.Formula, `InfinitaryLogic.Scott.BFEquivRelabel,
   `InfinitaryLogic.Descriptive.StructureSpace, `InfinitaryLogic.Descriptive.Topology,
   `InfinitaryLogic.Descriptive.Measurable, `InfinitaryLogic.Descriptive.Polish,
   `InfinitaryLogic.Descriptive.GDeltaPolish, `InfinitaryLogic.Descriptive.ModelsOfGDelta,
   `InfinitaryLogic.Descriptive.SatisfactionBorel, `InfinitaryLogic.Descriptive.SatisfactionBorelOn,
   `InfinitaryLogic.Descriptive.ModelClassStandardBorel,
   `InfinitaryLogic.Descriptive.PerfectAntichain, `InfinitaryLogic.Descriptive.CantorAntichain,
   `InfinitaryLogic.Descriptive.StructureIsoSetoid, `InfinitaryLogic.Descriptive.BFEquivBorel,
   `InfinitaryLogic.Descriptive.KleeneBrouwer, `InfinitaryLogic.Descriptive.BFTree,
   `InfinitaryLogic.Descriptive.AnalyticTreeBoundedness,
   `InfinitaryLogic.Descriptive.AnalyticClosure, `InfinitaryLogic.Descriptive.BFSeparation,
   `InfinitaryLogic.Descriptive.BFScattered, `InfinitaryLogic.Descriptive.BFConcentration,
   `InfinitaryLogic.Descriptive.MinimallyUncountable]

/-- The exact `InfinitaryLogic` import closure of `Scott.Formula`, unchanged by
`scottSentenceAt`. -/
def formulaClosure : List Name :=
  [`InfinitaryLogic.Util, `InfinitaryLogic.Lomega1omega.Syntax,
   `InfinitaryLogic.Lomega1omega.Semantics, `InfinitaryLogic.Lomega1omega.Operations,
   `InfinitaryLogic.Lomega1omega.OpenBoundsSemantics, `InfinitaryLogic.Scott.AtomicDiagram,
   `InfinitaryLogic.Scott.BackAndForth, `InfinitaryLogic.Scott.Formula]

/-- The exact `InfinitaryLogic` import closure of `Descriptive.SatisfactionBorel`, unchanged by
`mem_modelsOf_iff_realize`. -/
def satisfactionBorelClosure : List Name :=
  [`InfinitaryLogic.Lomega1omega.Syntax, `InfinitaryLogic.Lomega1omega.Semantics,
   `InfinitaryLogic.Descriptive.StructureSpace, `InfinitaryLogic.Descriptive.Topology,
   `InfinitaryLogic.Descriptive.Measurable, `InfinitaryLogic.Descriptive.Polish,
   `InfinitaryLogic.Descriptive.SatisfactionBorelOn, `InfinitaryLogic.Descriptive.SatisfactionBorel]

/-- The exact `InfinitaryLogic` import closure of `Descriptive.ModelsOfGDelta`, unchanged by
`modelsOf_not` and `modelsOf_inf_not`. -/
def modelsOfGDeltaClosure : List Name :=
  satisfactionBorelClosure ++
    [`InfinitaryLogic.Descriptive.GDeltaPolish, `InfinitaryLogic.Descriptive.ModelsOfGDelta]

/-- The guard's own declarations whose axioms are audited. -/
def guardDecls : List Name :=
  [`generic_rank_regression, `generic_cut_regression, `bfClass_regression,
   `concentration_regression, `generic_scottSentenceAt_regression,
   `scottSentence_bridge_regression, `scottFormula_omega_one, `nullLang, `nullP, `trueStr,
   `falseStr, `psiTrue, `bfTrueFalse, `omega_one_necessity, `exists_rankSplit_of_unboundedRankOn,
   `not_minimal_over_invariant_subsets, `empty_regression].map
    (`MinimallyUncountableRegressions ++ ·)

/-- The standard axioms. -/
def standardAxioms : List Name := [`propext, `Classical.choice, `Quot.sound]

/-- Exact comparison of a computed closure with a pinned list. -/
def checkExact (what : Name) (actual expected : List Name) : Elab.Command.CommandElabM Unit := do
  let extra := actual.filter fun m ↦ !expected.contains m
  let missing := expected.filter fun m ↦ !actual.contains m
  unless extra.isEmpty && missing.isEmpty do
    throwError "[CLOSURE DRIFT] the InfinitaryLogic closure of {what} is {actual}; update the \
      pinned list deliberately (extra {extra}, missing {missing})"

-- the closure checks and the axiom audit run in one command, then the OK line
run_cmd do
  let env ← getEnv
  let some idx := env.getModuleIdx? targetModule
    | throwError "module {targetModule} is not in the environment"
  -- the module's closure: forbidden-free, exact, and the predicted union
  let ilModules := ilClosure env targetModule
  let hits := ilModules.filter fun m ↦ forbiddenPrefixes.any (·.isPrefixOf m) ||
    forbiddenSubstrings.any fun s ↦ (m.toString.splitOn s).length ≠ 1
  unless hits.isEmpty do
    throwError "[BROAD CONE] the closure of {targetModule} reaches {hits}"
  -- the named forbidden modules exist, so the boundary check is not vacuous
  for m in forbiddenPrefixes.drop 7 ++ [`InfinitaryLogic.Karp.PotentialIso] do
    unless (env.getModuleIdx? m).isSome do
      throwError "[VACUOUS] forbidden module {m} is not in the environment"
  checkExact targetModule ilModules allowedClosure
  unless ilModules.length == 33 do
    throwError "[CLOSURE DRIFT] expected 33 InfinitaryLogic modules, found {ilModules.length}"
  let parts := [`InfinitaryLogic.Descriptive.BFConcentration, `InfinitaryLogic.Scott.Formula,
    `InfinitaryLogic.Descriptive.ModelsOfGDelta, `InfinitaryLogic.Lomega1omega.Theory]
  let sizes := parts.map fun p ↦ (ilClosure env p).length
  unless sizes == [27, 8, 10, 4] do
    throwError "[CLOSURE DRIFT] the closures of {parts} have sizes {sizes}, not [27, 8, 10, 4]"
  let union := (parts.foldl (fun s p ↦ s ++ .ofList (ilClosure env p)) ({} : NameSet)).insert
    targetModule
  checkExact targetModule ilModules union.toList
  -- the modules of the additions: closures unchanged
  checkExact `InfinitaryLogic.Scott.Formula (ilClosure env `InfinitaryLogic.Scott.Formula)
    formulaClosure
  checkExact `InfinitaryLogic.Descriptive.SatisfactionBorel
    (ilClosure env `InfinitaryLogic.Descriptive.SatisfactionBorel) satisfactionBorelClosure
  checkExact `InfinitaryLogic.Descriptive.ModelsOfGDelta
    (ilClosure env `InfinitaryLogic.Descriptive.ModelsOfGDelta) modelsOfGDeltaClosure
  let bfs := (ilClosure env `InfinitaryLogic.Descriptive.BFScattered).length
  unless bfs == 25 do
    throwError "[CLOSURE DRIFT] the closure of Descriptive.BFScattered has {bfs} modules, not 25"
  -- axioms: every declaration of the module, the additions and the guard's declarations
  let enumerated := (env.header.moduleData[idx.toNat]!).constNames.toList
  let audited := enumerated ++ additions.map (·.1) ++ guardDecls
  for n in audited do
    unless (env.find? n).isSome do throwError "declaration {n} not found"
    let axs ← Elab.Command.liftCoreM (collectAxioms n)
    let bad := axs.toList.filter fun a ↦ !standardAxioms.contains a
    unless bad.isEmpty do throwError "[NONSTANDARD AXIOMS] {n} uses {bad}"
  logInfo m!"minimally uncountable regression guard: OK (applied: the rank layer for an \
    arbitrary Language.\{u, v} with no relational or countability instance; the sentence-cut \
    layer, mem_modelsOf_iff_realize with L implicit, modelsOf_not, modelsOf_inf_not and \
    BFScattered.mono with no \
    countability; the back-and-forth classes, the generic engine with an arbitrary rank and no \
    isolating rank, and the concentration equivalence with countably many symbols; \
    realize_scottSentenceAt_iff_BFEquiv with no relational instance and independent carrier \
    and level universes; explicit universe lists pinned by name and by instantiation; the rfl \
    bridge to scottSentence; necessity of α < ω₁: scottFormula is ⊤ at ω₁ and the iff fails \
    there for one nullary symbol; decision 9: a rank-value cut with both sides unbounded, so \
    minimality over arbitrary invariant subsets is unsatisfiable; the empty class; \
    Countable (Σ l, _) in exactly {countabilityUsing.length} declarations, every public \
    declaration classified, none mentioning IsIsolatingRank; the additions placed in their \
    modules; exact import closure ({ilModules.length} modules, the union of BFConcentration, \
    Scott.Formula, ModelsOfGDelta and Lomega1omega.Theory plus the module) with no Karp, \
    ModelTheory, Methods, Admissible, Conditional, ScottProcess, WIP, ScatteredCounting, \
    Scott.Sentence, RefinementCount, IsolatingLevel, LopezEscobar or SmallVocabulary module; \
    Scott.Formula ({formulaClosure.length}), SatisfactionBorel \
    ({satisfactionBorelClosure.length}), ModelsOfGDelta ({modelsOfGDeltaClosure.length}) and \
    BFScattered ({bfs}) closures unchanged; standard axioms for {audited.length} declarations)"
