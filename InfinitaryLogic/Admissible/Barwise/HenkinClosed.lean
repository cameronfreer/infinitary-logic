/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Admissible.Barwise.ProofSystem
import InfinitaryLogic.Methods.Henkin.CountableCompletion.FairEnumeration
import InfinitaryLogic.Methods.Henkin.CountableCompletion.QuotientTruthLemma

/-!
# Proof-theoretic consistency over a Henkin-closed sentence set

The relational kernel adapter for syntactic Barwise completeness (issue #19B).

`HenkinClosed P` names the memberships a sentence set `P ⊆ L[[ℕ]].Sentenceω` must have for the
family of `P`-bounded `P`-consistent sets to be a consistency property in the countable-completion
kernel's sense.  `HenkinClosed.consistencyPropertyEqOn` inhabits `ConsistencyPropertyEqOn P` from
that family using only the rules of `Derivable`; `exists_countable_model_of_aconsistent` then runs
the fair enumeration and the quotient term model.

## Why this engine

The kernel's `ConsistencyPropertyEqOn` has **no** `extension` and **no** `chain_closure` field.
Both would be needed by a Zorn-style maximal-consistent construction, and chain closure is
*false* for `AConsistent`: with ℕ constants, the sets `{¬⋀ₖ U(cₖ)} ∪ {U(cₖ) | k ≤ n}` are each
consistent and form a chain whose union derives `⊥` by the ω-rule.
`scripts/check_chain_closure_counterexample.lean` keeps that fact executable.  The fair
enumeration adds one closure target at a time and never claims the union is in the family, so it
needs neither field.

## Substitution

The one-hole templates for equality symmetry, transitivity and relation congruence are closed
terms substituted into a `Fin 1`-formula; `Derivable.eq_subst` already takes the target's
membership `φ.subst t₂ ∈ P` as a premise, and `HenkinClosed` supplies it for closed atoms.  No
general substitution closure is imposed on `P`.

## Scope

Relational base `L`, `Language.{0, 0}`, auxiliary constants present in the model.  Forgetting the
constants, the source-fragment adapter (`L_A(C)` in `L[[ℕ]]`), and arbitrary languages are
separate steps.
-/

namespace FirstOrder.Language

open FirstOrder Structure

variable {L : Language.{0, 0}}

/-- **Henkin closure** of a sentence set over `L[[ℕ]]`: exactly the memberships the
proof-theoretic consistency family needs to discharge the kernel's fields. -/
structure HenkinClosed (P : Set L[[ℕ]].Sentenceω) : Prop where
  falsum_mem : (BoundedFormulaω.falsum : L[[ℕ]].Sentenceω) ∈ P
  not_mem : ∀ φ : L[[ℕ]].Sentenceω, φ ∈ P → φ.not ∈ P
  imp_left : ∀ φ ψ : L[[ℕ]].Sentenceω, φ.imp ψ ∈ P → φ ∈ P
  imp_right : ∀ φ ψ : L[[ℕ]].Sentenceω, φ.imp ψ ∈ P → ψ ∈ P
  iInf_comp : ∀ φs : ℕ → L[[ℕ]].Sentenceω, BoundedFormulaω.iInf φs ∈ P → ∀ k, φs k ∈ P
  iSup_comp : ∀ φs : ℕ → L[[ℕ]].Sentenceω, BoundedFormulaω.iSup φs ∈ P → ∀ k, φs k ∈ P
  all_inst : ∀ φ : L[[ℕ]].BoundedFormulaω Empty 1, φ.all ∈ P → ∀ c : ℕ, instConst c φ ∈ P
  constEq_mem : ∀ a b : ℕ, constEq (L := L) a b ∈ P
  relInst_mem : ∀ (l : ℕ) (R : L.Relations l) (g : Fin l → ℕ), relInst R g ∈ P

namespace HenkinClosed

variable {P : Set L[[ℕ]].Sentenceω}

/-- The proof-theoretic family: `P`-bounded `P`-consistent sets. -/
def aconsistentSets (P : Set L[[ℕ]].Sentenceω) : Set (Set L[[ℕ]].Sentenceω) :=
  {S | S ⊆ P ∧ AConsistent P S}

theorem union_singleton_subset {S : Set L[[ℕ]].Sentenceω} (hS : S ⊆ P)
    {φ : L[[ℕ]].Sentenceω} (hφ : φ ∈ P) : S ∪ {φ} ⊆ P := by
  intro τ hτ
  rcases hτ with hτ | hτ
  · exact hS hτ
  · rw [Set.mem_singleton_iff.mp hτ]; exact hφ

private theorem derivable_falsum_of_not_mem {S : Set L[[ℕ]].Sentenceω}
    {φ : L[[ℕ]].Sentenceω} (hSφ : S ∪ {φ} ⊆ P)
    (h : S ∪ {φ} ∉ aconsistentSets P) : Derivable P (S ∪ {φ}) .falsum := by
  by_contra hd
  exact h ⟨hSφ, hd⟩

/-- `¬φ ∈ P` gives `φ ∈ P`, since `φ.not = φ.imp ⊥`. -/
theorem mem_of_not_mem (hP : HenkinClosed P) {φ : L[[ℕ]].Sentenceω} (h : φ.not ∈ P) : φ ∈ P :=
  hP.imp_left φ _ h

/-- The one-hole relation template `R(g with x at coordinate i)` and its two instances. -/
private theorem relInst_update_derivable (hP : HenkinClosed P) {S : Set L[[ℕ]].Sentenceω}
    (hS : S ⊆ P)
    {l : ℕ} (R : L.Relations l) (g : Fin l → ℕ) (i : Fin l) (b : ℕ)
    (hrel : relInst R g ∈ S) (heq : constEq (g i) b ∈ S) :
    Derivable P S (relInst R (Function.update g i b)) := by
  let φ : L[[ℕ]].Formulaω (Fin 1) :=
    BoundedFormulaω.rel (Sum.inl R) fun j =>
      if j = i then Term.var (Sum.inl (0 : Fin 1))
      else (constTerm (g j)).relabel (Sum.inl ∘ Empty.elim)
  have hφ_subst : ∀ s : L[[ℕ]].Term Empty, φ.subst (fun _ => s)
      = BoundedFormulaω.rel (Sum.inl R) fun j =>
          if j = i then s.relabel (Sum.inl : Empty → Empty ⊕ Fin 0)
          else (constTerm (g j)).relabel (Sum.inl : Empty → Empty ⊕ Fin 0) := by
    intro s
    show BoundedFormulaω.rel (Sum.inl R) (fun j =>
        ((if j = i then Term.var (Sum.inl (0 : Fin 1))
          else (constTerm (g j)).relabel (Sum.inl ∘ Empty.elim)).subst
            (Sum.elim (Term.relabel Sum.inl ∘ fun _ => s) (Term.var ∘ Sum.inr)))) = _
    congr 1
    funext j
    split
    · simp [Term.subst, Sum.elim_inl, Function.comp_apply]
    · exact term_subst_empty_aux (constTerm (g j)) s
  have hinst : ∀ e : ℕ, BoundedFormulaω.rel (Sum.inl R) (fun j =>
      if j = i then (constTerm e).relabel (Sum.inl : Empty → Empty ⊕ Fin 0)
      else (constTerm (g j)).relabel (Sum.inl : Empty → Empty ⊕ Fin 0))
      = relInst R (Function.update g i e) := by
    intro e
    simp only [relInst]
    congr 1
    funext j
    by_cases hj : j = i
    · subst hj; rw [ite_eq_left rfl, Function.update_self, constTerm_relabel_inl]
    · rw [ite_eq_right hj, Function.update_of_ne hj, constTerm_relabel_inl]
  have hφ_ai : φ.subst (fun _ => constTerm (g i)) = relInst R g := by
    rw [hφ_subst, hinst, Function.update_eq_self_iff.mpr rfl]
  have hφ_b : φ.subst (fun _ => constTerm b) = relInst R (Function.update g i b) := by
    rw [hφ_subst, hinst]
  have heq' : Derivable P S (BoundedFormulaω.equal
      ((constTerm (g i)).relabel (Sum.inl : Empty → Empty ⊕ Fin 0))
      ((constTerm b).relabel (Sum.inl : Empty → Empty ⊕ Fin 0))) := by
    rw [constTerm_relabel_inl, constTerm_relabel_inl]
    exact .assumption heq (hS heq)
  have hd := Derivable.eq_subst (constTerm (g i)) (constTerm b) φ heq'
    (by rw [hφ_ai]; exact .assumption hrel (hS hrel))
    (by rw [hφ_b]; exact hP.relInst_mem l R _)
  rwa [hφ_b] at hd

/-- The one-hole equality template `x = c_a` (symmetry) — instances `c_a = c_a` and
`c_b = c_a`. -/
private theorem constEq_symm_derivable (hP : HenkinClosed P) {S : Set L[[ℕ]].Sentenceω} (hS : S ⊆ P)
    (a b : ℕ) (h : constEq a b ∈ S) : Derivable P S (constEq b a) := by
  let φ : L[[ℕ]].Formulaω (Fin 1) :=
    BoundedFormulaω.equal (Term.var (Sum.inl (0 : Fin 1)))
      ((constTerm a).relabel (Sum.inl ∘ Empty.elim))
  have hφ_subst : ∀ s : L[[ℕ]].Term Empty, φ.subst (fun _ => s) = BoundedFormulaω.equal
      (s.relabel (Sum.inl : Empty → Empty ⊕ Fin 0)) (constTermS a) := by
    intro s
    show BoundedFormulaω.equal
      ((Term.var (Sum.inl (0 : Fin 1)) : L[[ℕ]].Term (Fin 1 ⊕ Fin 0)).subst
        (Sum.elim (Term.relabel Sum.inl ∘ fun _ => s) (Term.var ∘ Sum.inr)))
      (((constTerm a).relabel (Sum.inl ∘ Empty.elim)).subst
        (Sum.elim (Term.relabel Sum.inl ∘ fun _ => s) (Term.var ∘ Sum.inr))) = _
    rw [term_subst_empty_aux (constTerm a) s, constTerm_relabel_inl]
    rfl
  have h1 : φ.subst (fun _ => constTerm a) = constEq a a := by
    rw [hφ_subst, constTerm_relabel_inl]; rfl
  have h2 : φ.subst (fun _ => constTerm b) = constEq b a := by
    rw [hφ_subst, constTerm_relabel_inl]; rfl
  have heq' : Derivable P S (BoundedFormulaω.equal
      ((constTerm a).relabel (Sum.inl : Empty → Empty ⊕ Fin 0))
      ((constTerm b).relabel (Sum.inl : Empty → Empty ⊕ Fin 0))) := by
    rw [constTerm_relabel_inl, constTerm_relabel_inl]
    exact .assumption h (hS h)
  have hd := Derivable.eq_subst (constTerm a) (constTerm b) φ heq'
    (by rw [h1]; exact .eq_refl (constTermS a) (hP.constEq_mem a a))
    (by rw [h2]; exact hP.constEq_mem b a)
  rwa [h2] at hd

/-- The one-hole equality template `c_a = x` (transitivity) — instances `c_a = c_b`, `c_a = c_d`. -/
private theorem constEq_trans_derivable (hP : HenkinClosed P) {S : Set L[[ℕ]].Sentenceω}
    (hS : S ⊆ P)
    (a b d : ℕ) (h₁ : constEq a b ∈ S) (h₂ : constEq b d ∈ S) :
    Derivable P S (constEq a d) := by
  let φ : L[[ℕ]].Formulaω (Fin 1) :=
    BoundedFormulaω.equal ((constTerm a).relabel (Sum.inl ∘ Empty.elim))
      (Term.var (Sum.inl (0 : Fin 1)))
  have hφ_subst : ∀ s : L[[ℕ]].Term Empty, φ.subst (fun _ => s) = BoundedFormulaω.equal
      (constTermS a) (s.relabel (Sum.inl : Empty → Empty ⊕ Fin 0)) := by
    intro s
    show BoundedFormulaω.equal
      (((constTerm a).relabel (Sum.inl ∘ Empty.elim)).subst
        (Sum.elim (Term.relabel Sum.inl ∘ fun _ => s) (Term.var ∘ Sum.inr)))
      ((Term.var (Sum.inl (0 : Fin 1)) : L[[ℕ]].Term (Fin 1 ⊕ Fin 0)).subst
        (Sum.elim (Term.relabel Sum.inl ∘ fun _ => s) (Term.var ∘ Sum.inr))) = _
    rw [term_subst_empty_aux (constTerm a) s, constTerm_relabel_inl]
    rfl
  have h1 : φ.subst (fun _ => constTerm b) = constEq a b := by
    rw [hφ_subst, constTerm_relabel_inl]; rfl
  have h2 : φ.subst (fun _ => constTerm d) = constEq a d := by
    rw [hφ_subst, constTerm_relabel_inl]; rfl
  have heq' : Derivable P S (BoundedFormulaω.equal
      ((constTerm b).relabel (Sum.inl : Empty → Empty ⊕ Fin 0))
      ((constTerm d).relabel (Sum.inl : Empty → Empty ⊕ Fin 0))) := by
    rw [constTerm_relabel_inl, constTerm_relabel_inl]
    exact .assumption h₂ (hS h₂)
  have hd := Derivable.eq_subst (constTerm b) (constTerm d) φ heq'
    (by rw [h1]; exact .assumption h₁ (hS h₁))
    (by rw [h2]; exact hP.constEq_mem a d)
  rwa [h2] at hd

/-- **The proof-theoretic consistency property over a Henkin-closed `P`.**  No `extension`,
no `chain_closure`: the kernel does not ask for them. -/
def consistencyPropertyEqOn (hP : HenkinClosed P) [L.IsRelational] :
    ConsistencyPropertyEqOn P where
  sets := aconsistentSets P
  subset_U := fun _ hS => hS.1
  C0_no_falsum := fun _ ⟨hS, hc⟩ hf => hc (.assumption hf (hS hf))
  C0_no_contradiction := fun _ ⟨hS, hc⟩ φ ⟨hφ, hφn⟩ =>
    hc (.neg_elim (.assumption hφ (hS hφ)) (.assumption hφn (hS hφn)))
  C1_imp := by
    intro S ⟨hS, hc⟩ φ ψ himp
    have hφP := hP.imp_left φ ψ (hS himp)
    have hψP := hP.imp_right φ ψ (hS himp)
    by_contra h; push Not at h
    have hinc₁ := derivable_falsum_of_not_mem (union_singleton_subset hS (hP.not_mem φ hφP)) h.1
    have hinc₂ := derivable_falsum_of_not_mem (union_singleton_subset hS hψP) h.2
    have hφ_deriv := Derivable.not_not_elim (.neg_intro (hP.not_mem φ hφP) hinc₁)
    have hψn := Derivable.neg_intro hψP hinc₂
    exact hc (.neg_elim (.imp_elim (.assumption himp (hS himp)) hφ_deriv) hψn)
  C1_neg_imp := by
    intro S ⟨hS, hc⟩ φ ψ hnimp
    have himpP := hP.mem_of_not_mem (hS hnimp)
    have hφP := hP.imp_left φ ψ himpP
    have hψP := hP.imp_right φ ψ himpP
    constructor
    · refine ⟨union_singleton_subset hS hφP, ?_⟩
      intro hd
      have hnφ := Derivable.neg_intro hφP hd
      have himp := Derivable.imp_intro_from_neg hnφ hφP hψP
      exact hc (.neg_elim himp (.assumption hnimp (hS hnimp)))
    · refine ⟨union_singleton_subset hS (hP.not_mem ψ hψP), ?_⟩
      intro hd
      have hψ := Derivable.not_not_elim (.neg_intro (hP.not_mem ψ hψP) hd)
      have himp := Derivable.imp_intro hφP (.weaken Set.subset_union_left hψ)
      exact hc (.neg_elim himp (.assumption hnimp (hS hnimp)))
  C2_not_not := by
    intro S ⟨hS, hc⟩ φ hnn
    have hφP := hP.mem_of_not_mem (hP.mem_of_not_mem (hS hnn))
    refine ⟨union_singleton_subset hS hφP, ?_⟩
    intro hd
    have h_neg := Derivable.neg_intro hφP hd
    exact hc (.neg_elim (.not_not_elim (.assumption hnn (hS hnn))) h_neg)
  C3_iInf := by
    intro S ⟨hS, hc⟩ φs hinf k
    have hkP := hP.iInf_comp φs (hS hinf) k
    refine ⟨union_singleton_subset hS hkP, ?_⟩
    intro hd
    have h_neg := Derivable.neg_intro hkP hd
    exact hc (.neg_elim (.iInf_elim k (.assumption hinf (hS hinf))) h_neg)
  C3_neg_iInf := by
    intro S ⟨hS, hc⟩ φs hninf
    have hinfP := hP.mem_of_not_mem (hS hninf)
    by_contra h; push Not at h
    have hall : ∀ k, Derivable P S (φs k) := by
      intro k
      have hkP := hP.iInf_comp φs hinfP k
      have := derivable_falsum_of_not_mem
        (union_singleton_subset hS (hP.not_mem _ hkP)) (h k)
      exact .not_not_elim (.neg_intro (hP.not_mem _ hkP) this)
    exact hc (.neg_elim (.iInf_intro hall hinfP) (.assumption hninf (hS hninf)))
  C4_iSup := by
    intro S ⟨hS, hc⟩ φs hsup
    by_contra h; push Not at h
    have hnegs : ∀ k, Derivable P S (φs k).not := by
      intro k
      have hkP := hP.iSup_comp φs (hS hsup) k
      have := derivable_falsum_of_not_mem (union_singleton_subset hS hkP) (h k)
      exact .neg_intro hkP this
    apply hc
    apply Derivable.iSup_elim (.assumption hsup (hS hsup))
    intro k
    exact .neg_elim
      (.assumption (Set.mem_union_right S rfl) (hP.iSup_comp φs (hS hsup) k))
      (.weaken Set.subset_union_left (hnegs k))
  C4_neg_iSup := by
    intro S ⟨hS, hc⟩ φs hnsup k
    have hsupP := hP.mem_of_not_mem (hS hnsup)
    have hkP := hP.iSup_comp φs hsupP k
    refine ⟨union_singleton_subset hS (hP.not_mem _ hkP), ?_⟩
    intro hd
    have hφk := Derivable.not_not_elim (.neg_intro (hP.not_mem _ hkP) hd)
    exact hc (.neg_elim (.iSup_intro (k := k) hφk hsupP) (.assumption hnsup (hS hnsup)))
  eq_refl := by
    intro S ⟨hS, hc⟩ c
    refine ⟨union_singleton_subset hS (hP.constEq_mem c c), ?_⟩
    intro hd
    exact hc (Derivable.derivable_collapses_extension
      (.eq_refl (constTermS c) (hP.constEq_mem c c)) (hP.constEq_mem c c) hd)
  eq_symm := by
    intro S ⟨hS, hc⟩ a b h
    refine ⟨union_singleton_subset hS (hP.constEq_mem b a), ?_⟩
    intro hd
    exact hc (Derivable.derivable_collapses_extension
      (hP.constEq_symm_derivable hS a b h) (hP.constEq_mem b a) hd)
  eq_trans := by
    intro S ⟨hS, hc⟩ a b d h₁ h₂
    refine ⟨union_singleton_subset hS (hP.constEq_mem a d), ?_⟩
    intro hd
    exact hc (Derivable.derivable_collapses_extension
      (hP.constEq_trans_derivable hS a b d h₁ h₂) (hP.constEq_mem a d) hd)
  rel_congr := by
    intro S ⟨hS, hc⟩ l R g i b h₁ h₂
    refine ⟨union_singleton_subset hS (hP.relInst_mem l R _), ?_⟩
    intro hd
    exact hc (Derivable.derivable_collapses_extension
      (hP.relInst_update_derivable hS R g i b h₁ h₂) (hP.relInst_mem l R _) hd)
  all_inst := by
    intro S ⟨hS, hc⟩ φ hall c
    have hcP := hP.all_inst φ (hS hall) c
    refine ⟨union_singleton_subset hS hcP, ?_⟩
    intro hd
    exact hc (Derivable.derivable_collapses_extension
      (.all_elim φ (constTerm c) (.assumption hall (hS hall))) hcP hd)
  neg_all_witness := by
    intro S ⟨hS, hc⟩ φ hnall
    have hallP := hP.mem_of_not_mem (hS hnall)
    by_contra h; push Not at h
    -- every constant instance is derivable ...
    have hconst : ∀ c : ℕ, Derivable P S (instConst c φ) := by
      intro c
      have hcP := hP.all_inst φ hallP c
      have := derivable_falsum_of_not_mem
        (union_singleton_subset hS (hP.not_mem _ hcP)) (h c)
      exact .not_not_elim (.neg_intro (hP.not_mem _ hcP) this)
    -- ... and over a relational base every closed term is a constant.
    have hderiv : ∀ t : L[[ℕ]].Term Empty, Derivable P S (φ.openBounds.subst (fun _ => t)) := by
      intro t
      obtain ⟨c, rfl⟩ := exists_eq_constTerm t
      exact hconst c
    exact hc (.neg_elim (.all_intro φ hderiv hallP) (.assumption hnall (hS hnall)))

/-- **Syntactic model existence over the relational core (countable `P`).**  A `P`-consistent
`T ⊆ P` has a countable `L[[ℕ]]`-model.  No chain closure and no extension hypothesis: the fair
enumeration never needs them.

This is the kernel adapter, stated explicitly over a relational base with the auxiliary constants
still present.  It is not yet the Barwise theorem over an arbitrary language. -/
theorem exists_countable_model_of_aconsistent (hP : HenkinClosed P) [L.IsRelational]
    [Countable (Σ l, L.Relations l)] (hPc : P.Countable) {T : Set L[[ℕ]].Sentenceω}
    (hT : T ⊆ P) (hcons : AConsistent P T) :
    ∃ (M : Type) (_ : L[[ℕ]].Structure M) (_ : Nonempty M) (_ : Countable M),
      Theoryω.Model T M := by
  have : Countable P := hPc.to_subtype
  obtain ⟨Sstar, hTS, -, hsc⟩ :=
    exists_henkinComplete (P := hP.consistencyPropertyEqOn) ⟨T, hT, hcons⟩
  have hsurj : Function.Surjective (fun c : ℕ => qmk hsc (constTerm c)) := fun x => by
    obtain ⟨c, hc⟩ := qmk_surjective hsc x
    exact ⟨c, hc.symm⟩
  exact ⟨QModel hsc, qModelStructure hsc, ⟨qmk hsc (constTerm 0)⟩, hsurj.countable,
    fun φ hφ => (truth_both hsc φ).1 (hTS hφ)⟩

end HenkinClosed

end FirstOrder.Language
