/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Admissible.Barwise.ProofSystem
import InfinitaryLogic.Methods.ConstantInstances
import InfinitaryLogic.Admissible.Barwise.SourceFragment

/-!
# Constant elimination and the syntactic consistency transport

The syntactic half of the constants question for the source-fragment adapter (issue #19).

## Constant elimination

`elimConstsTerm t₀` and `elimConsts t₀` replace every constant `c_k` of `L[[ℕ]]` by one fixed
closed base term `t₀`, structurally; variables and binders are untouched.  Elimination retracts
`mapLanguage` (`elimConsts_mapLanguage`) and commutes with `relabel`, `castLE`, `openBounds` and
`subst`, so the closing operations of `Methods/ConstantInstances.lean` are respected:
`elimConsts_closeBy` sends a constant-closed member of a fragment to the corresponding
term-closed member.

## The derivation homomorphism

`Derivable.map_elimConsts`: a derivation over the expansion maps to a derivation over the base,
with every rule mapping to itself.  The ω-rule obtains its base instances from the premises at the
`onTerm` images of the base closed terms, and `imp_intro` is unaffected because no quantifier
prefix is introduced — the substitution translation, not the universal-prefix translation.
`AConsistent.of_elimConsts` is the contrapositive; `Derivable.mono_perm` and `AConsistent.anti_perm`
record that permission sets enter only as side conditions.

## The transport

`Fragment.closedInstances F` is the base-side counterpart of `Fragment.withNatConstantsSentences`:
every member, at every arity, closed by base terms.  It contains the sentence slice, and
`aconsistent_withConstants_of_closedInstances` transports consistency over it into consistency in
the constants expansion, for any closed base term `t₀`.

## What this module does not do

It has no semantic composition with the relational kernel.  `Language.IsRelational` empties every
function arity including zero, so a relational language has no closed term
(`isEmpty_term_empty_of_isRelational`), and the relational adapters of `HenkinClosed.lean` and
`SourceFragment.lean` require `[L.IsRelational]`.  A theorem assuming both would hold by explosion.
The arbitrary-language semantic endpoint is pending the relationalization transport; the guard
`scripts/check_constant_transport_boundary.lean` rejects any declaration in these modules whose
type mentions both a relational-language instance and a closed base term.
-/

namespace FirstOrder.Language

open FirstOrder Structure

variable {L : Language.{0, 0}} (t₀ : L.Term Empty)

/-- The image of a symbol application: a base symbol keeps its (translated) arguments, a
constant becomes `t₀`. -/
def elimConstsFunc {α : Type} {n : ℕ} (f : L[[ℕ]].Functions n) (args : Fin n → L.Term α) :
    L.Term α :=
  match f with
  | Sum.inl g => .func g args
  | Sum.inr _ => t₀.relabel Empty.elim

/-- Replace every constant by `t₀`. -/
def elimConstsTerm {α : Type} : L[[ℕ]].Term α → L.Term α
  | .var x => .var x
  | .func f ts => elimConstsFunc t₀ f fun i => elimConstsTerm (ts i)

theorem elimConstsTerm_var {α : Type} (x : α) :
    elimConstsTerm t₀ (.var x : L[[ℕ]].Term α) = .var x := rfl

theorem elimConstsTerm_func_inl {α : Type} {n : ℕ} (g : L.Functions n)
    (ts : Fin n → L[[ℕ]].Term α) :
    elimConstsTerm t₀ (.func (Sum.inl g : L[[ℕ]].Functions n) ts)
      = .func g fun i => elimConstsTerm t₀ (ts i) := rfl

theorem elimConstsTerm_onTerm {α : Type} (t : L.Term α) :
    elimConstsTerm t₀ ((L.lhomWithConstants ℕ).onTerm t) = t := by
  induction t with
  | var x => rfl
  | func g ts ih =>
    show elimConstsTerm t₀ (.func (Sum.inl g) fun i => (L.lhomWithConstants ℕ).onTerm (ts i)) = _
    rw [elimConstsTerm_func_inl]
    congr 1; funext i; exact ih i

theorem elimConstsTerm_constTerm (k : ℕ) :
    elimConstsTerm t₀ (constTerm (L' := L) (J := ℕ) k) = t₀.relabel Empty.elim := rfl

/-! ## Formulas -/

/-- Replace every constant by `t₀` throughout a bounded formula: structural, variables and
binders untouched. -/
def elimConsts {α : Type} : ∀ {n : ℕ}, L[[ℕ]].BoundedFormulaω α n → L.BoundedFormulaω α n
  | _, .falsum => .falsum
  | _, .equal t₁ t₂ => .equal (elimConstsTerm t₀ t₁) (elimConstsTerm t₀ t₂)
  | _, .rel R ts =>
    match R with
    | Sum.inl R' => .rel R' fun i => elimConstsTerm t₀ (ts i)
    | Sum.inr r => isEmptyElim r
  | _, .imp φ ψ => (elimConsts φ).imp (elimConsts ψ)
  | _, .all φ => (elimConsts φ).all
  | _, .iSup φs => .iSup fun i => elimConsts (φs i)
  | _, .iInf φs => .iInf fun i => elimConsts (φs i)

theorem elimConsts_imp {α : Type} {n : ℕ} (φ ψ : L[[ℕ]].BoundedFormulaω α n) :
    elimConsts t₀ (φ.imp ψ) = (elimConsts t₀ φ).imp (elimConsts t₀ ψ) := rfl

theorem elimConsts_not {α : Type} {n : ℕ} (φ : L[[ℕ]].BoundedFormulaω α n) :
    elimConsts t₀ φ.not = (elimConsts t₀ φ).not := rfl

theorem elimConsts_falsum {α : Type} {n : ℕ} :
    elimConsts t₀ (.falsum : L[[ℕ]].BoundedFormulaω α n) = .falsum := rfl

theorem elimConsts_iInf {α : Type} {n : ℕ} (φs : ℕ → L[[ℕ]].BoundedFormulaω α n) :
    elimConsts t₀ (.iInf φs) = .iInf fun i => elimConsts t₀ (φs i) := rfl

theorem elimConsts_iSup {α : Type} {n : ℕ} (φs : ℕ → L[[ℕ]].BoundedFormulaω α n) :
    elimConsts t₀ (.iSup φs) = .iSup fun i => elimConsts t₀ (φs i) := rfl

theorem elimConsts_all {α : Type} {n : ℕ} (φ : L[[ℕ]].BoundedFormulaω α (n + 1)) :
    elimConsts t₀ φ.all = (elimConsts t₀ φ).all := rfl

/-- Base formulas mapped into the expansion come back unchanged. -/
theorem elimConsts_mapLanguage {α : Type} : ∀ {n : ℕ} (φ : L.BoundedFormulaω α n),
    elimConsts t₀ (φ.mapLanguage (L.lhomWithConstants ℕ)) = φ
  | _, .falsum => rfl
  | _, .equal t₁ t₂ => by
    simp only [BoundedFormulaω.mapLanguage, elimConsts, elimConstsTerm_onTerm]
  | _, .rel R ts => by
    show elimConsts t₀ (.rel (Sum.inl R) fun i => (L.lhomWithConstants ℕ).onTerm (ts i)) = _
    simp only [elimConsts, elimConstsTerm_onTerm]
  | _, .imp φ ψ => by
    simp only [BoundedFormulaω.mapLanguage, elimConsts, elimConsts_mapLanguage φ,
      elimConsts_mapLanguage ψ]
  | _, .all φ => by
    simp only [BoundedFormulaω.mapLanguage, elimConsts, elimConsts_mapLanguage φ]
  | _, .iSup φs => by
    simp only [BoundedFormulaω.mapLanguage, elimConsts]
    congr 1; funext i; exact elimConsts_mapLanguage (φs i)
  | _, .iInf φs => by
    simp only [BoundedFormulaω.mapLanguage, elimConsts]
    congr 1; funext i; exact elimConsts_mapLanguage (φs i)

/-! ## Commutation with `openBounds` and `subst` -/

theorem elimConstsTerm_relabel {α β : Type} (f : α → β) (t : L[[ℕ]].Term α) :
    elimConstsTerm t₀ (t.relabel f) = (elimConstsTerm t₀ t).relabel f := by
  induction t with
  | var x => rfl
  | func F ts ih =>
    rcases F with g | c
    · show elimConstsTerm t₀ (.func (Sum.inl g) fun i => (ts i).relabel f) = _
      rw [elimConstsTerm_func_inl]
      show _ = (Term.func g fun i => elimConstsTerm t₀ (ts i)).relabel f
      simp only [Term.relabel]
      congr 1; funext i; exact ih i
    · show t₀.relabel Empty.elim = (t₀.relabel Empty.elim).relabel f
      rw [Term.relabel_relabel]
      congr 1; funext e; exact e.elim

theorem elimConstsTerm_subst {α β : Type} (t : L[[ℕ]].Term α) (tf : α → L[[ℕ]].Term β) :
    elimConstsTerm t₀ (t.subst tf)
      = (elimConstsTerm t₀ t).subst fun a => elimConstsTerm t₀ (tf a) := by
  induction t with
  | var x => rfl
  | func F ts ih =>
    rcases F with g | c
    · show elimConstsTerm t₀ (.func (Sum.inl g) fun i => (ts i).subst tf) = _
      rw [elimConstsTerm_func_inl]
      show _ = (Term.func g fun i => elimConstsTerm t₀ (ts i)).subst _
      simp only [Term.subst]
      congr 1; funext i; exact ih i
    · show t₀.relabel Empty.elim = (t₀.relabel Empty.elim).subst _
      rw [Term.subst_relabel]
      exact (Term.subst_empty_eq_relabel' t₀ _ _)
where
  Term.subst_empty_eq_relabel' : ∀ (t : L.Term Empty) {β : Type} (f : Empty → L.Term β)
      (g : Empty → β), t.relabel g = t.subst f
    | .var e, _, _, _ => e.elim
    | .func F ts, _, f, g => by
      simp only [Term.relabel, Term.subst]
      congr 1; funext i; exact Term.subst_empty_eq_relabel' (ts i) f g

theorem elimConsts_castLE {α : Type} : ∀ {m n : ℕ} (h : m ≤ n) (φ : L[[ℕ]].BoundedFormulaω α m),
    elimConsts t₀ (φ.castLE h) = (elimConsts t₀ φ).castLE h
  | _, _, _, .falsum => rfl
  | _, _, _, .equal t₁ t₂ => by
    simp only [BoundedFormulaω.castLE, elimConsts, elimConstsTerm_relabel]
  | _, _, _, .rel R ts => by
    rcases R with R' | r
    · show elimConsts t₀ (.rel (Sum.inl R') fun i => (ts i).relabel _) = _
      simp only [elimConsts, elimConstsTerm_relabel]
      rfl
    · exact isEmptyElim r
  | _, _, h, .imp φ ψ => by
    simp only [BoundedFormulaω.castLE, elimConsts, elimConsts_castLE h φ, elimConsts_castLE h ψ]
  | _, _, h, .all φ => by
    simp only [BoundedFormulaω.castLE, elimConsts, elimConsts_castLE _ φ]
  | _, _, h, .iSup φs => by
    simp only [BoundedFormulaω.castLE, elimConsts]
    congr 1; funext i; exact elimConsts_castLE h (φs i)
  | _, _, h, .iInf φs => by
    simp only [BoundedFormulaω.castLE, elimConsts]
    congr 1; funext i; exact elimConsts_castLE h (φs i)

theorem elimConsts_relabel {α β : Type} {n : ℕ} (g : α → β ⊕ Fin n) :
    ∀ {k : ℕ} (φ : L[[ℕ]].BoundedFormulaω α k),
    elimConsts t₀ (φ.relabel g) = (elimConsts t₀ φ).relabel g
  | _, .falsum => rfl
  | _, .equal t₁ t₂ => by
    simp only [BoundedFormulaω.relabel, elimConsts, elimConstsTerm_relabel]
  | _, .rel R ts => by
    rcases R with R' | r
    · show elimConsts t₀ (.rel (Sum.inl R') fun i => (ts i).relabel _) = _
      simp only [elimConsts, elimConstsTerm_relabel]
      rfl
    · exact isEmptyElim r
  | _, .imp φ ψ => by
    simp only [BoundedFormulaω.relabel, elimConsts, elimConsts_relabel g φ, elimConsts_relabel g ψ]
  | _, .all φ => by
    simp only [BoundedFormulaω.relabel, elimConsts, elimConsts_castLE, elimConsts_relabel g φ]
  | _, .iSup φs => by
    simp only [BoundedFormulaω.relabel, elimConsts]
    congr 1; funext i; exact elimConsts_relabel g (φs i)
  | _, .iInf φs => by
    simp only [BoundedFormulaω.relabel, elimConsts]
    congr 1; funext i; exact elimConsts_relabel g (φs i)

theorem elimConsts_openBounds : ∀ {n : ℕ} (φ : L[[ℕ]].BoundedFormulaω Empty n),
    elimConsts t₀ φ.openBounds = (elimConsts t₀ φ).openBounds
  | _, .falsum => rfl
  | _, .equal t₁ t₂ => by
    simp only [BoundedFormulaω.openBounds, elimConsts, elimConstsTerm_relabel]
  | _, .rel R ts => by
    rcases R with R' | r
    · show elimConsts t₀ (.rel (Sum.inl R') fun i => (ts i).relabel _) = _
      simp only [elimConsts, elimConstsTerm_relabel]
      rfl
    · exact isEmptyElim r
  | _, .imp φ ψ => by
    simp only [BoundedFormulaω.openBounds, elimConsts, elimConsts_openBounds φ,
      elimConsts_openBounds ψ]
  | _, .all φ => by
    simp only [BoundedFormulaω.openBounds, elimConsts, elimConsts_relabel, elimConsts_openBounds φ]
  | _, .iSup φs => by
    simp only [BoundedFormulaω.openBounds, elimConsts]
    congr 1; funext i; exact elimConsts_openBounds (φs i)
  | _, .iInf φs => by
    simp only [BoundedFormulaω.openBounds, elimConsts]
    congr 1; funext i; exact elimConsts_openBounds (φs i)

/-- The bound-variable-aware substitution map of `BoundedFormulaω.subst` commutes with
constant elimination, pointwise. -/
theorem elimConsts_substAux {α β : Type} {n : ℕ} (tf : α → L[[ℕ]].Term β) :
    (fun x : α ⊕ Fin n => elimConstsTerm t₀
        (Sum.elim (Term.relabel Sum.inl ∘ tf) (Term.var ∘ Sum.inr) x))
      = Sum.elim (Term.relabel Sum.inl ∘ fun a => elimConstsTerm t₀ (tf a))
          (Term.var ∘ Sum.inr) := by
  funext x
  rcases x with a | i
  · simp only [Sum.elim_inl, Function.comp_apply, elimConstsTerm_relabel]
  · rfl

theorem elimConsts_subst {α β : Type} : ∀ {n : ℕ} (φ : L[[ℕ]].BoundedFormulaω α n)
    (tf : α → L[[ℕ]].Term β),
    elimConsts t₀ (φ.subst tf) = (elimConsts t₀ φ).subst fun a => elimConstsTerm t₀ (tf a)
  | _, .falsum, _ => rfl
  | _, .equal t₁ t₂, tf => by
    simp only [BoundedFormulaω.subst, elimConsts, elimConstsTerm_subst, elimConsts_substAux]
  | _, .rel R ts, tf => by
    rcases R with R' | r
    · show elimConsts t₀ (.rel (Sum.inl R') fun i => (ts i).subst _) = _
      simp only [elimConsts, elimConstsTerm_subst, elimConsts_substAux]
      rfl
    · exact isEmptyElim r
  | _, .imp φ ψ, tf => by
    simp only [BoundedFormulaω.subst, elimConsts, elimConsts_subst φ, elimConsts_subst ψ]
  | _, .all φ, tf => by
    simp only [BoundedFormulaω.subst, elimConsts, elimConsts_subst φ]
  | _, .iSup φs, tf => by
    simp only [BoundedFormulaω.subst, elimConsts]
    congr 1; funext i; exact elimConsts_subst (φs i) tf
  | _, .iInf φs, tf => by
    simp only [BoundedFormulaω.subst, elimConsts]
    congr 1; funext i; exact elimConsts_subst (φs i) tf

/-! ## The derivation homomorphism -/

/-- The image of a sentence set. -/
abbrev elimConstsSet (P : Set L[[ℕ]].Sentenceω) : Set L.Sentenceω := elimConsts t₀ '' P

/-- **Derivations transport along constant elimination.**  Every rule maps to itself; the ω-rule
needs instances at every closed base term, obtained from the premise at that term's image in the
expansion. -/
theorem Derivable.map_elimConsts {P T : Set L[[ℕ]].Sentenceω} {φ : L[[ℕ]].Sentenceω}
    (hd : Derivable P T φ) :
    Derivable (elimConstsSet t₀ P) (elimConstsSet t₀ T) (elimConsts t₀ φ) := by
  induction hd with
  | assumption hT hP => exact .assumption ⟨_, hT, rfl⟩ ⟨_, hP, rfl⟩
  | weaken hsub _ ih => exact .weaken (Set.image_mono hsub) ih
  | falsum_elim _ hP ih => exact .falsum_elim ih ⟨_, hP, rfl⟩
  | imp_intro hP _ ih =>
    rw [elimConsts_imp]
    refine .imp_intro ⟨_, hP, rfl⟩ ?_
    simpa only [elimConstsSet, Set.image_union, Set.image_singleton] using ih
  | imp_elim _ _ ih₁ ih₂ => exact .imp_elim ih₁ ih₂
  | not_not_elim _ ih => exact .not_not_elim ih
  | iInf_intro _ hP ih => exact .iInf_intro ih ⟨_, hP, rfl⟩
  | iInf_elim k _ ih => exact .iInf_elim k ih
  | iSup_intro k _ hP ih => exact .iSup_intro k ih ⟨_, hP, rfl⟩
  | iSup_elim _ _ ih₁ ih₂ =>
    refine .iSup_elim ih₁ fun k => ?_
    simpa only [elimConstsSet, Set.image_union, Set.image_singleton] using ih₂ k
  | all_intro ψ _ hP ih =>
    rw [elimConsts_all]
    refine .all_intro (elimConsts t₀ ψ) (fun s => ?_) ⟨_, hP, rfl⟩
    have := ih ((L.lhomWithConstants ℕ).onTerm s)
    rwa [elimConsts_subst, elimConsts_openBounds, elimConstsTerm_onTerm] at this
  | all_elim ψ t _ ih =>
    have := Derivable.all_elim (elimConsts t₀ ψ) (elimConstsTerm t₀ t) ih
    rwa [elimConsts_subst, elimConsts_openBounds]
  | eq_refl t hP =>
    exact Derivable.eq_refl (elimConstsTerm t₀ t) ⟨_, hP, rfl⟩
  | eq_subst t₁ t₂ ψ _ _ hP ih₁ ih₂ =>
    have h := Derivable.eq_subst (elimConstsTerm t₀ t₁) (elimConstsTerm t₀ t₂) (elimConsts t₀ ψ)
      (by simpa only [elimConsts, elimConstsTerm_relabel] using ih₁)
      (by simpa only [elimConsts_subst] using ih₂)
      (by rw [← elimConsts_subst]; exact Set.mem_image_of_mem _ hP)
    simpa only [elimConsts_subst] using h
  | em ψ hP =>
    exact Derivable.em (elimConsts t₀ ψ) ⟨_, hP, rfl⟩

/-- **Consistency transports back**: consistency of the images gives consistency in the
expansion. -/
theorem AConsistent.of_elimConsts {P T : Set L[[ℕ]].Sentenceω}
    (h : AConsistent (elimConstsSet t₀ P) (elimConstsSet t₀ T)) : AConsistent P T :=
  fun hd => h (by simpa only [elimConsts_falsum] using hd.map_elimConsts t₀)

/-! ## The base-side closed-instance universe and the transport theorem -/

/-- Close a bounded formula by closed base terms: the base analogue of `closeBy`. -/
def closeByTerms {n : ℕ} (φ : L.BoundedFormulaω Empty n) (τ : Fin n → L.Term Empty) :
    L.Sentenceω :=
  (φ.openBounds).subst τ

/-- The closed-instance universe of a fragment: every member, at every arity, closed by base
terms. -/
def Fragment.closedInstances (F : Fragment L) : Set L.Sentenceω :=
  {σ | ∃ (n : ℕ) (φ : L.BoundedFormulaω Empty n) (τ : Fin n → L.Term Empty),
    (⟨n, φ⟩ : Σ n, L.BoundedFormulaω Empty n) ∈ F ∧ σ = closeByTerms φ τ}

theorem Fragment.sentenceSlice_subset_closedInstances (F : Fragment L) :
    F.sentenceSlice ⊆ F.closedInstances :=
  fun φ hφ => ⟨0, φ, Fin.elim0, hφ, (openBounds_subst_elim0 φ Fin.elim0).symm⟩

/-- Eliminating the constants from a constant-closed member gives a term-closed member. -/
theorem elimConsts_closeBy {n : ℕ} (φ : L.BoundedFormulaω Empty n) (a : Fin n → ℕ) :
    elimConsts t₀ (closeBy (φ.mapLanguage (L.lhomWithConstants ℕ)) a)
      = closeByTerms φ fun _ => t₀.relabel Empty.elim := by
  unfold closeBy closeByTerms
  rw [elimConsts_subst, elimConsts_openBounds, elimConsts_mapLanguage]
  rfl

theorem elimConsts_image_withNatConstantsSentences_subset (F : Fragment L) :
    elimConstsSet t₀ F.withNatConstantsSentences ⊆ F.closedInstances := by
  rintro _ ⟨σ, ⟨n, φ, a, hφ, rfl⟩, rfl⟩
  exact ⟨n, φ, fun _ => t₀.relabel Empty.elim, hφ, elimConsts_closeBy t₀ φ a⟩

theorem elimConsts_image_mapLanguage (T : Set L.Sentenceω) :
    elimConstsSet t₀ (BoundedFormulaω.mapLanguage (L.lhomWithConstants ℕ) '' T) = T := by
  ext φ
  constructor
  · rintro ⟨_, ⟨ψ, hψ, rfl⟩, rfl⟩
    rw [elimConsts_mapLanguage]; exact hψ
  · intro hφ
    exact ⟨_, ⟨φ, hφ, rfl⟩, elimConsts_mapLanguage t₀ φ⟩

/-- Permission sets only appear as side conditions, so derivability is monotone in them. -/
theorem Derivable.mono_perm {P P' T : Set L.Sentenceω} {φ : L.Sentenceω} (hP : P ⊆ P')
    (hd : Derivable P T φ) : Derivable P' T φ := by
  induction hd with
  | assumption hT h => exact .assumption hT (hP h)
  | weaken hsub _ ih => exact .weaken hsub ih
  | falsum_elim _ h ih => exact .falsum_elim ih (hP h)
  | imp_intro h _ ih => exact .imp_intro (hP h) ih
  | imp_elim _ _ ih₁ ih₂ => exact .imp_elim ih₁ ih₂
  | not_not_elim _ ih => exact .not_not_elim ih
  | iInf_intro _ h ih => exact .iInf_intro ih (hP h)
  | iInf_elim k _ ih => exact .iInf_elim k ih
  | iSup_intro k _ h ih => exact .iSup_intro k ih (hP h)
  | iSup_elim _ _ ih₁ ih₂ => exact .iSup_elim ih₁ ih₂
  | all_intro ψ _ h ih => exact .all_intro ψ ih (hP h)
  | all_elim ψ t _ ih => exact .all_elim ψ t ih
  | eq_refl t h => exact .eq_refl t (hP h)
  | eq_subst t₁ t₂ ψ _ _ h ih₁ ih₂ => exact .eq_subst t₁ t₂ ψ ih₁ ih₂ (hP h)
  | em ψ h => exact .em ψ (hP h)

theorem AConsistent.anti_perm {P P' T : Set L.Sentenceω} (hP : P ⊆ P')
    (h : AConsistent P' T) : AConsistent P T :=
  fun hd => h (hd.mono_perm hP)

/-- **The transport**: consistency over the closed-instance universe gives consistency in the
constants expansion, for any closed base term `t₀`. -/
theorem aconsistent_withConstants_of_closedInstances (t₀ : L.Term Empty) (F : Fragment L)
    {T₀ : Set L.Sentenceω}
    (h : AConsistent F.closedInstances T₀) :
    AConsistent F.withNatConstantsSentences
      (BoundedFormulaω.mapLanguage (L.lhomWithConstants ℕ) '' T₀) := by
  refine AConsistent.of_elimConsts t₀ ?_
  rw [elimConsts_image_mapLanguage]
  exact h.anti_perm (elimConsts_image_withNatConstantsSentences_subset t₀ F)

/-! ## The boundary with the relational kernel

`Language.IsRelational` empties every function arity, including arity zero, so a relational
language has **no** closed term.  The transport above therefore has no composition with the
relational kernel adapters of `HenkinClosed.lean` and `SourceFragment.lean`, which require
`[L.IsRelational]`: a theorem assuming both would be vacuous.  The arbitrary-language semantic
endpoint is pending the relationalization transport, and
`scripts/check_constant_transport_boundary.lean` rejects any declaration whose type mentions
both. -/

/-- A relational language has no closed term. -/
theorem isEmpty_term_empty_of_isRelational [L.IsRelational] : IsEmpty (L.Term Empty) :=
  ⟨fun t => match t with
    | .var e => e.elim
    | .func f _ => (‹L.IsRelational› _).false f⟩

end FirstOrder.Language

