/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Admissible.Barwise.HenkinClosed
import InfinitaryLogic.Admissible.HF

/-!
# The source-fragment adapter: from an honest fragment to a Henkin-closed universe

Syntactic model existence for a theory inside an honest `Fragment` of a relational language,
through the constants-expanded universe of that fragment (issue #19B, step 3).

## The constants-expanded universe

`Fragment.withNatConstantsSentences F` is the set of sentences of `L[[ℕ]]` obtained by taking a
member `⟨n, φ⟩` of `F` at **any** arity, mapping it into the constants expansion, and closing its
`n` bound variables by constants.  Every arity contributes: that is what makes universal-instance
closure follow from `Fragment.all_mem` (the body of a universal is a member at arity `n + 1`, and
appending the chosen constant to the parameter tuple is the instance —
`instConst_closeBy_all_remainder`).  No substitution field is added to any fragment structure.

## The basis

`Fragment` deliberately omits what the kernel's atomic and negation fields need;
`Fragment.HenkinBasis` supplies exactly that: falsum, closure under negation at every arity, one
equality template
at arity two, and one relation template per symbol.  Closing the templates by constants produces
every `constEq` and every `relInst`.  The adapter consumes only `Fragment` and `HenkinBasis`; the
coded-family closure of `AdmissibleFragment` never enters.

## The theorem

`Fragment.exists_countable_model_of_aconsistent_withConstants`: for a countable fragment with a
basis, a theory `T ⊆ F.sentenceSlice` that is consistent **in the expanded universe** has a
countable model of `T` itself, as an `L`-structure, obtained by forgetting the constants.  The
hypothesis is consistency in `withNatConstantsSentences F`, and the theorem is named for it.
Transporting base-language consistency into the expanded universe is a separate question,
recorded as a deferred design branch in `docs/admissible-interface-contract.md` §8.
-/

namespace FirstOrder.Language

open FirstOrder Structure

variable {L : Language.{0, 0}}

namespace Fragment

/-! ## Sentence slice and the constants-expanded universe -/

/-- The sentences of a fragment: its members at arity zero. -/
def sentenceSlice (F : Fragment L) : Set L.Sentenceω :=
  {φ | (⟨0, φ⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ F}

theorem mem_sentenceSlice {F : Fragment L} {φ : L.Sentenceω} :
    φ ∈ F.sentenceSlice ↔ (⟨0, φ⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ F :=
  Iff.rfl

/-- The constants-expanded universe: every member of `F`, at every arity, mapped into `L[[ℕ]]`
and closed by constants. -/
def withNatConstantsSentences (F : Fragment L) : Set L[[ℕ]].Sentenceω :=
  {σ | ∃ (n : ℕ) (φ : L.BoundedFormulaω Empty n) (a : Fin n → ℕ),
    (⟨n, φ⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ F ∧
      σ = closeBy (φ.mapLanguage (L.lhomWithConstants ℕ)) a}

theorem closeBy_mapLanguage_mem {F : Fragment L} {n : ℕ} {φ : L.BoundedFormulaω Empty n}
    (h : (⟨n, φ⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ F) (a : Fin n → ℕ) :
    closeBy (φ.mapLanguage (L.lhomWithConstants ℕ)) a ∈ F.withNatConstantsSentences :=
  ⟨n, φ, a, h, rfl⟩

/-- Theory inclusion: a sentence of the fragment, mapped into the expansion, lies in the
universe. -/
theorem mapLanguage_mem_withNatConstantsSentences {F : Fragment L} {φ : L.Sentenceω}
    (h : φ ∈ F.sentenceSlice) :
    φ.mapLanguage (L.lhomWithConstants ℕ) ∈ F.withNatConstantsSentences := by
  rw [← closeBy_zero (φ.mapLanguage (L.lhomWithConstants ℕ)) Fin.elim0]
  exact closeBy_mapLanguage_mem h Fin.elim0

theorem mapLanguage_image_subset {F : Fragment L} {T : Set L.Sentenceω}
    (hT : T ⊆ F.sentenceSlice) :
    BoundedFormulaω.mapLanguage (L.lhomWithConstants ℕ) '' T ⊆ F.withNatConstantsSentences := by
  rintro _ ⟨φ, hφ, rfl⟩
  exact mapLanguage_mem_withNatConstantsSentences (hT hφ)

/-- Countability: countably many members, each with countably many parameter tuples. -/
theorem withNatConstantsSentences_countable {F : Fragment L} (hF : F.toSet.Countable) :
    F.withNatConstantsSentences.Countable := by
  have : F.withNatConstantsSentences =
      ⋃ p ∈ F.toSet,
        Set.range (fun a : Fin p.1 → ℕ => closeBy (p.2.mapLanguage (L.lhomWithConstants ℕ)) a) := by
    ext σ
    simp only [withNatConstantsSentences, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_range]
    constructor
    · rintro ⟨n, φ, a, hφ, rfl⟩
      exact ⟨⟨n, φ⟩, hφ, a, rfl⟩
    · rintro ⟨⟨n, φ⟩, hφ, a, rfl⟩
      exact ⟨n, φ, a, hφ, rfl⟩
  rw [this]
  exact hF.biUnion fun _ _ => Set.countable_range _

/-! ## The basis -/

/-- The equality template `x₀ = x₁` at arity two. -/
def equalTemplate (L : Language.{0, 0}) : L.BoundedFormulaω Empty 2 :=
  BoundedFormulaω.equal (Term.var (Sum.inr 0)) (Term.var (Sum.inr 1))

/-- The relation template `R(x₀, …, x_{l-1})` at arity `l`. -/
def relTemplate {l : ℕ} (R : L.Relations l) : L.BoundedFormulaω Empty l :=
  BoundedFormulaω.rel R fun i => Term.var (Sum.inr i)

/-- **The Henkin basis** of a fragment: what `Fragment` omits and the kernel's atomic and negation
fields need.  Separate from `AdmissibleFragment`; no fragment structure gains a field. -/
structure HenkinBasis (F : Fragment L) : Prop where
  falsum_mem : (⟨0, BoundedFormulaω.falsum⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ F
  not_mem : ∀ {n : ℕ} {φ : L.BoundedFormulaω Empty n},
    (⟨n, φ⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ F → ⟨n, φ.not⟩ ∈ F
  equalTemplate_mem : (⟨2, equalTemplate L⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ F
  relTemplate_mem : ∀ {l : ℕ} (R : L.Relations l),
    (⟨l, relTemplate R⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ F

/-- The finitary fragment has a basis. -/
theorem henkinBasis_hfFragment : HenkinBasis (hfFragment L) where
  falsum_mem := BoundedFormulaω.isFirstOrder_falsum
  not_mem h := BoundedFormulaω.isFirstOrder_imp_iff.mpr ⟨h, BoundedFormulaω.isFirstOrder_falsum⟩
  equalTemplate_mem := BoundedFormulaω.isFirstOrder_equal _ _
  relTemplate_mem R := BoundedFormulaω.isFirstOrder_rel R _

/-- The full fragment has a basis. -/
theorem henkinBasis_top : HenkinBasis (Fragment.top : Fragment L) where
  falsum_mem := Set.mem_univ _
  not_mem _ := Set.mem_univ _
  equalTemplate_mem := Set.mem_univ _
  relTemplate_mem _ := Set.mem_univ _

/-! ## Closing the templates gives the atoms -/

theorem closeBy_equalTemplate (a b : ℕ) :
    closeBy ((equalTemplate L).mapLanguage (L.lhomWithConstants ℕ)) ![a, b] = constEq a b := by
  show BoundedFormulaω.equal _ _ = BoundedFormulaω.equal _ _
  congr 1
  · show (constTerm (![a, b] 0)).relabel Sum.inl = constTermS a
    exact constTerm_relabel_inl a
  · show (constTerm (![a, b] 1)).relabel Sum.inl = constTermS b
    exact constTerm_relabel_inl b

theorem closeBy_relTemplate {l : ℕ} (R : L.Relations l) (g : Fin l → ℕ) :
    closeBy ((relTemplate R).mapLanguage (L.lhomWithConstants ℕ)) g = relInst R g := by
  show BoundedFormulaω.rel _ _ = BoundedFormulaω.rel _ _
  congr 1
  funext i
  show (constTerm (g i)).relabel Sum.inl = constTermS (g i)
  exact constTerm_relabel_inl (g i)

/-! ## Decomposing a member of the universe by its head constructor -/

section Decompose

variable {F : Fragment L}

private abbrev ML (φ : L.BoundedFormulaω Empty n) : L[[ℕ]].BoundedFormulaω Empty n :=
  φ.mapLanguage (L.lhomWithConstants ℕ)

private theorem eq_imp_decomp {n : ℕ} {θ : L.BoundedFormulaω Empty n} {a : Fin n → ℕ}
    {φ' ψ' : L[[ℕ]].Sentenceω} (h : closeBy (ML θ) a = φ'.imp ψ') :
    ∃ θ₁ θ₂ : L.BoundedFormulaω Empty n, θ = θ₁.imp θ₂ ∧
      closeBy (ML θ₁) a = φ' ∧ closeBy (ML θ₂) a = ψ' := by
  cases θ with
  | imp θ₁ θ₂ =>
    injection h with _ h₁ h₂
    exact ⟨θ₁, θ₂, rfl, h₁, h₂⟩
  | falsum => cases h
  | equal _ _ => cases h
  | rel _ _ => cases h
  | all _ => cases h
  | iSup _ => cases h
  | iInf _ => cases h

private theorem eq_iInf_decomp {n : ℕ} {θ : L.BoundedFormulaω Empty n} {a : Fin n → ℕ}
    {φs : ℕ → L[[ℕ]].Sentenceω} (h : closeBy (ML θ) a = BoundedFormulaω.iInf φs) :
    ∃ θs : ℕ → L.BoundedFormulaω Empty n, θ = BoundedFormulaω.iInf θs ∧
      ∀ k, closeBy (ML (θs k)) a = φs k := by
  cases θ with
  | iInf θs =>
    injection h with _ h'
    exact ⟨θs, rfl, fun k => congrFun h' k⟩
  | falsum => cases h
  | equal _ _ => cases h
  | rel _ _ => cases h
  | imp _ _ => cases h
  | all _ => cases h
  | iSup _ => cases h

private theorem eq_iSup_decomp {n : ℕ} {θ : L.BoundedFormulaω Empty n} {a : Fin n → ℕ}
    {φs : ℕ → L[[ℕ]].Sentenceω} (h : closeBy (ML θ) a = BoundedFormulaω.iSup φs) :
    ∃ θs : ℕ → L.BoundedFormulaω Empty n, θ = BoundedFormulaω.iSup θs ∧
      ∀ k, closeBy (ML (θs k)) a = φs k := by
  cases θ with
  | iSup θs =>
    injection h with _ h'
    exact ⟨θs, rfl, fun k => congrFun h' k⟩
  | falsum => cases h
  | equal _ _ => cases h
  | rel _ _ => cases h
  | imp _ _ => cases h
  | all _ => cases h
  | iInf _ => cases h

private theorem eq_all_decomp {n : ℕ} {θ : L.BoundedFormulaω Empty n} {a : Fin n → ℕ}
    {ψ : L[[ℕ]].BoundedFormulaω Empty 1} (h : closeBy (ML θ) a = ψ.all) :
    ∃ θ₀ : L.BoundedFormulaω Empty (n + 1), θ = θ₀.all ∧
      (((ML θ₀).openBounds).relabel insertLastBound).subst (fun i => constTerm (a i)) = ψ := by
  cases θ with
  | all θ₀ =>
    rw [show ML θ₀.all = (ML θ₀).all from rfl, closeBy_all] at h
    injection h with _ h'
    exact ⟨θ₀, rfl, h'⟩
  | falsum => cases h
  | equal _ _ => cases h
  | rel _ _ => cases h
  | imp _ _ => cases h
  | iSup _ => cases h
  | iInf _ => cases h

end Decompose

/-! ## The universe is Henkin-closed -/

/-- **The constants-expanded universe of a fragment with a basis is Henkin-closed.**  Connective
components come from the fragment's component closure, negation and the atoms from the basis, and
universal instances from `Fragment.all_mem` through `instConst_closeBy_all_remainder`. -/
theorem henkinClosed_withNatConstantsSentences {F : Fragment L} (hB : F.HenkinBasis) :
    HenkinClosed F.withNatConstantsSentences where
  falsum_mem := ⟨0, BoundedFormulaω.falsum, Fin.elim0, hB.falsum_mem, rfl⟩
  not_mem := by
    rintro _ ⟨n, θ, a, hθ, rfl⟩
    exact ⟨n, θ.not, a, hB.not_mem hθ, by rw [BoundedFormulaω.mapLanguage_not, closeBy_not]⟩
  imp_left := by
    rintro φ' ψ' ⟨n, θ, a, hθ, h⟩
    obtain ⟨θ₁, θ₂, rfl, h₁, -⟩ := eq_imp_decomp h.symm
    exact ⟨n, θ₁, a, F.imp_left_mem hθ, h₁.symm⟩
  imp_right := by
    rintro φ' ψ' ⟨n, θ, a, hθ, h⟩
    obtain ⟨θ₁, θ₂, rfl, -, h₂⟩ := eq_imp_decomp h.symm
    exact ⟨n, θ₂, a, F.imp_right_mem hθ, h₂.symm⟩
  iInf_comp := by
    rintro φs ⟨n, θ, a, hθ, h⟩ k
    obtain ⟨θs, rfl, hk⟩ := eq_iInf_decomp h.symm
    exact ⟨n, θs k, a, F.iInf_mem hθ k, (hk k).symm⟩
  iSup_comp := by
    rintro φs ⟨n, θ, a, hθ, h⟩ k
    obtain ⟨θs, rfl, hk⟩ := eq_iSup_decomp h.symm
    exact ⟨n, θs k, a, F.iSup_mem hθ k, (hk k).symm⟩
  all_inst := by
    rintro ψ ⟨n, θ, a, hθ, h⟩ c
    obtain ⟨θ₀, rfl, hψ⟩ := eq_all_decomp h.symm
    refine ⟨n + 1, θ₀, Fin.snoc a c, F.all_mem hθ, ?_⟩
    rw [← hψ, instConst_closeBy_all_remainder]
  constEq_mem a b :=
    ⟨2, equalTemplate L, ![a, b], hB.equalTemplate_mem, (closeBy_equalTemplate a b).symm⟩
  relInst_mem l R g := ⟨l, relTemplate R, g, hB.relTemplate_mem R, (closeBy_relTemplate R g).symm⟩

/-! ## Assembly -/

/-- Forgetting the constants: an `L[[ℕ]]`-model of the mapped theory is, as its `L`-reduct, a model
of the theory.  A three-line argument from `realize_mapLanguage`, kept local so that no Marker-stage
module is imported. -/
theorem model_reduct_of_model_mapLanguage_image (T : L.Theoryω) {N : Type} [L[[ℕ]].Structure N]
    (h : Theoryω.Model (BoundedFormulaω.mapLanguage (L.lhomWithConstants ℕ) '' T) N) :
    letI : L.Structure N := (L.lhomWithConstants ℕ).reduct N
    Theoryω.Model T N := by
  let : L.Structure N := (L.lhomWithConstants ℕ).reduct N
  have : (L.lhomWithConstants ℕ).IsExpansionOn N := LHom.isExpansionOn_reduct _ _
  intro τ hτ
  exact (BoundedFormulaω.realize_mapLanguage (L.lhomWithConstants ℕ) τ _ _).mp
    (h _ (Set.mem_image_of_mem _ hτ))

/-- **Syntactic model existence over a source fragment (relational core).**  A theory inside a
countable fragment with a basis that is consistent in the fragment's constants-expanded universe
has a countable model, as an `L`-structure.  No countability of `T`; the consistency hypothesis is
in the expanded universe, and the theorem is named for it. -/
theorem exists_countable_model_of_aconsistent_withConstants [L.IsRelational]
    [Countable (Σ l, L.Relations l)] {F : Fragment L} (hF : F.toSet.Countable)
    (hB : F.HenkinBasis) {T : L.Theoryω} (hT : T ⊆ F.sentenceSlice)
    (hcons : AConsistent F.withNatConstantsSentences
      (BoundedFormulaω.mapLanguage (L.lhomWithConstants ℕ) '' T)) :
    ∃ (M : Type) (_ : L.Structure M) (_ : Nonempty M) (_ : Countable M), Theoryω.Model T M := by
  obtain ⟨M, instM, hne, hcount, hmodel⟩ :=
    (henkinClosed_withNatConstantsSentences hB).exists_countable_model_of_aconsistent
      (withNatConstantsSentences_countable hF) (mapLanguage_image_subset hT) hcons
  exact ⟨M, (L.lhomWithConstants ℕ).reduct M, hne, hcount,
    model_reduct_of_model_mapLanguage_image T hmodel⟩

end Fragment

end FirstOrder.Language
