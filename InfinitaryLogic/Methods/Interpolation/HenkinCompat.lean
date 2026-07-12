/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Methods.Interpolation.ConsistencyPropertyEqOn
import InfinitaryLogic.Methods.Henkin.Construction

/-!
# Compatibility: maximal consistent sets are Henkin-complete (issue #8 tranche 2, commit 2b)

The bridge from the pre-existing Henkin API: a maximal consistent set `S` of a
`ConsistencyPropertyEq` over `L[[ℕ]]` (relational base) satisfies `HenkinComplete Set.univ S`.
The completion is stated on `Set.univ`, not an arbitrary generated `U` — a maximal set decides
the *full* syntax, so its natural universe is everything.

This file lives downstream of both APIs (`ConsistencyPropertyEqOn` and `Henkin.Construction`)
precisely so that `Construction.lean` never needs to know about the interpolation interface —
no import cycle is possible through an innocent reuse refactor.

The `C0`–`C4` and quantifier fields reuse the public `MaximalConsistent.*_mem` lemmas; the
atomic equality fields reuse the public `termEquiv`/`termEquiv_equivalence`; the atomic relation
congruence is re-derived here from `C6_eq_subst` (the analogous `Construction` lemma is private).
The negated-universal witness lands a *constant* witness via the relational collapse
`exists_eq_constTerm`.
-/

namespace FirstOrder.Language

open FirstOrder Structure

variable {L : Language.{0, 0}}

/-- `constTerm c` relabelled into a sentence's term context is `constTermS c`. -/
theorem constTerm_relabel_eq (c : ℕ) :
    (constTerm (L' := L) (J := ℕ) c).relabel (Sum.inl : Empty → Empty ⊕ Fin 0)
      = constTermS c := by
  simp only [constTerm, constTermS, Term.relabel]
  congr 1
  funext i
  exact i.elim0

/-- Substituting a closed term into a variable-free term (in the `Fin 1` free context) reduces
to the plain relabel — a local copy of the analogous private lemma in `Construction`. -/
private theorem term_subst_empty_aux (t t' : L[[ℕ]].Term Empty) :
    (t.relabel (Sum.inl ∘ Empty.elim : Empty → Fin 1 ⊕ Fin 0)).subst
      (Sum.elim (Term.relabel Sum.inl ∘ fun (_ : Fin 1) => t') (Term.var ∘ Sum.inr)) =
    t.relabel (Sum.inl : Empty → Empty ⊕ Fin 0) := by
  induction t with
  | var e => exact Empty.elim e
  | func f ts ih =>
    simp only [Term.relabel, Term.subst]
    congr 1
    funext i
    exact ih i

variable {C : ConsistencyPropertyEq L[[ℕ]]} {S : Set L[[ℕ]].Sentenceω}
  (hmax : C.toConsistencyProperty.MaximalConsistent S)

/-- `constEq c d ∈ S` is exactly the term-model equivalence of the two constants. -/
theorem constEq_mem_iff_termEquiv (c d : ℕ) :
    constEq c d ∈ S ↔ termEquiv C S hmax (constTerm c) (constTerm d) := by
  unfold termEquiv constEq
  rw [constTerm_relabel_eq, constTerm_relabel_eq]

include hmax in
/-- The atomic relation congruence, re-derived from `C6_eq_subst`. -/
theorem rel_congr_of_maximal {l : ℕ} (R : L.Relations l) (g : Fin l → ℕ) (i : Fin l) (b : ℕ)
    (hrel : relInst R g ∈ S) (heq : constEq (g i) b ∈ S) :
    relInst R (Function.update g i b) ∈ S := by
  -- φ(x) = R(g with x at coordinate i), in the `Fin 1` free context.
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
  -- The relation-instance / relabel bridge.
  have hinst : ∀ e : ℕ, BoundedFormulaω.rel (Sum.inl R) (fun j =>
      if j = i then (constTerm e).relabel (Sum.inl : Empty → Empty ⊕ Fin 0)
      else (constTerm (g j)).relabel (Sum.inl : Empty → Empty ⊕ Fin 0))
      = relInst R (Function.update g i e) := by
    intro e
    simp only [relInst]
    congr 1
    funext j
    by_cases hj : j = i
    · subst hj; rw [if_pos rfl, Function.update_self, constTerm_relabel_eq]
    · rw [if_neg hj, Function.update_of_ne hj, constTerm_relabel_eq]
  -- φ(c_{g i}) = R(g) ∈ S.
  have hφ_ai : φ.subst (fun _ => constTerm (g i)) ∈ S := by
    rw [hφ_subst, hinst, Function.update_eq_self_iff.mpr rfl]; exact hrel
  -- The C6 premise, in the required relabel form.
  have heq' : BoundedFormulaω.equal
      ((constTerm (g i)).relabel (Sum.inl : Empty → Empty ⊕ Fin 0))
      ((constTerm b).relabel (Sum.inl : Empty → Empty ⊕ Fin 0)) ∈ S := by
    rw [constTerm_relabel_eq, constTerm_relabel_eq]; exact heq
  have hc6 := C.C6_eq_subst S hmax.consistent (constTerm (g i)) (constTerm b) φ heq' hφ_ai
  rw [hφ_subst, hinst] at hc6
  exact hmax.mem_of_union_consistent hc6

include hmax in
/-- **Compatibility bridge**: a maximal consistent set of a relational `ConsistencyPropertyEq`
over `L[[ℕ]]` is Henkin-complete for the full syntax. -/
theorem henkinComplete_univ_of_maximal [L.IsRelational] :
    HenkinComplete (L := L) Set.univ S where
  subset_U := Set.subset_univ _
  no_falsum := C.toConsistencyProperty.C0_no_falsum S hmax.consistent
  no_contradiction := C.toConsistencyProperty.C0_no_contradiction S hmax.consistent
  imp _ _ h := hmax.imp_mem h
  neg_imp _ _ h := hmax.neg_imp_mem h
  not_not _ h := hmax.not_not_mem h
  iInf _ h k := hmax.iInf_mem h k
  neg_iInf _ h := hmax.neg_iInf_mem h
  iSup _ h := hmax.iSup_mem h
  neg_iSup _ h k := hmax.neg_iSup_mem h k
  eq_refl c := (constEq_mem_iff_termEquiv hmax c c).mpr ((termEquiv_equivalence C S hmax).refl _)
  eq_symm a b h := (constEq_mem_iff_termEquiv hmax b a).mpr
    ((termEquiv_equivalence C S hmax).symm ((constEq_mem_iff_termEquiv hmax a b).mp h))
  eq_trans a b d h₁ h₂ := (constEq_mem_iff_termEquiv hmax a d).mpr
    ((termEquiv_equivalence C S hmax).trans ((constEq_mem_iff_termEquiv hmax a b).mp h₁)
      ((constEq_mem_iff_termEquiv hmax b d).mp h₂))
  rel_congr _ R g i b hrel heq := rel_congr_of_maximal hmax R g i b hrel heq
  all_inst φ h c := ConsistencyPropertyEq.MaximalConsistent.all_bound_mem hmax h (constTerm c)
  neg_all_witness φ h := by
    obtain ⟨t, ht⟩ := ConsistencyPropertyEq.MaximalConsistent.neg_all_bound_mem hmax h
    obtain ⟨c, rfl⟩ := exists_eq_constTerm t
    exact ⟨c, ht⟩

end FirstOrder.Language
