/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Conditional.SilverAntichain
import InfinitaryLogic.ModelTheory.MorleyCounting
import Architect

/-!
# Morley counting, with a witness in the second alternative

`morley_counting` says the number of isomorphism classes of countable models is `≤ ℵ₁` or exactly
`2^{ℵ₀}`.  Its second alternative is a bare cardinal equation: it asserts that continuum-many
classes exist without exhibiting them, and it cannot do better, because its
`SilverBurgessDichotomy` hypothesis carries only cardinal information.

Here the proved Silver route is used directly instead, through `silver_core_polish`, and the
second alternative becomes a **perfect set** of pairwise non-isomorphic models.  That is strictly
more information: continuum-many classes follows from a perfect antichain
(`HasPerfectSetOfPairwiseNonisomorphicNatModels.continuum_le`), so the cardinal form is recovered
as `morley_counting_or_perfect_cardinal` below, while the converse fails — a cardinal equation
gives no set.

## Two tiers, one pipeline

Countable models come in tiers: carrier `ℕ`, and carrier `Fin n` for each `n`.  The finite tier is
not a formality.  An infinite language can have continuum-many `Fin n`-models and no `ℕ`-models at
all, so a statement offering only an `ℕ`-tier perfect set would be false; hence the third
alternative.

Both tiers run through `silver_countable_or_cantorAntichain`, which handles the fact that the
model class is a *Borel* subset of the structure space and so is not Polish as a subtype.  They
differ only in which relation Silver is applied to:

* at `ℕ`, Silver sees back-and-forth equivalence at a level `α < ω₁` — the relation the Scott
  stratification makes Borel — and the antichain is transferred to isomorphism, which refines it;
* at `Fin n`, isomorphism is itself Borel (a finite union of permutation graphs), so Silver is
  applied to it directly.

`morley_counting` itself is left untouched: it remains the statement parameterized by the
dichotomy, and nothing here is a replacement for it.
-/

open Cardinal

universe u v

namespace FirstOrder.Language

variable {L : Language.{u, v}} [L.IsRelational] [Countable (Σ l, L.Relations l)]

/-! ### The two tiers -/

/-- **Morley counting for `ℕ`-coded models, with a witness.**  Either at most `ℵ₁` isomorphism
classes, or a perfect set of pairwise non-isomorphic models.

The case split is on the conclusion itself rather than on a cardinal: if no perfect set exists,
then no level of the stratification can produce a Cantor antichain, so every level has a countable
quotient and the Scott-height bound applies. -/
@[blueprint "thm:morley-counting-coded-or-perfect"
  (title := /-- Morley counting for $\mathbb{N}$-models, with a witness -/)
  (statement := /-- For any $\Lomegaone$ sentence $\varphi$, either the $\mathbb{N}$-coded
    isomorphism classes number at most $\aleph_1$, or the model class carries a perfect set of
    pairwise non-isomorphic models. -/)
  (proof := /-- If there is no perfect set, then Silver applied to back-and-forth equivalence at
    each level $\alpha < \omegaone$ must return a countable quotient, since a Cantor antichain
    there would transfer to isomorphism and yield a perfect set.  The Scott-height stratification
    then bounds the isomorphism classes by $\aleph_1$. -/)
  (uses := ["thm:cantor-to-perfect", "def:iso-setoid"])]
theorem morley_counting_coded_or_perfect (φ : L.Sentenceω) :
    #(Quotient (isoSetoid φ)) ≤ Cardinal.aleph 1 ∨
      φ.HasPerfectSetOfPairwiseNonisomorphicNatModels := by
  by_cases hperf : φ.HasPerfectSetOfPairwiseNonisomorphicNatModels
  · exact Or.inr hperf
  refine Or.inl (mk_isoSetoid_quotient_le_aleph_one φ fun α hα => ?_)
  rcases silver_countable_or_cantorAntichain (modelsOf_measurableSet φ) (structureIsoSetoid L)
      (bfEquivSetoid φ α) (fun _ _ h => isoSetoid_refines_bfEquivSetoid φ α h)
      (bfEquivSetoid_measurableSet φ α hα) with hcount | hcantor
  · have := hcount
    exact Cardinal.mk_le_aleph0
  · exact absurd (Sentenceω.hasPerfectSet_of_ambient_cantorAntichain hcantor) hperf

/-- **Finite-carrier counting, with a witness.**  Either countably many isomorphism classes among
the `Fin n`-models, or a perfect set of pairwise non-isomorphic ones.

Unlike the `ℕ` tier this needs no stratification: isomorphism of `Fin n`-structures is the orbit
relation of a finite group, hence Borel outright, so Silver applies to it directly and the
relation-refinement step is the identity. -/
@[blueprint "thm:counting-fin-models-or-perfect"
  (title := /-- Finite-carrier counting, with a witness -/)
  (statement := /-- For each $n$, either the isomorphism classes of $\operatorname{Fin} n$-models
    of $\varphi$ are countable, or that model class carries a perfect set of pairwise
    non-isomorphic models. -/)
  (proof := /-- Isomorphism on $\operatorname{Fin} n$-structures is a finite union of graphs of
    continuous permutation actions, hence Borel, so Silver applies to it directly on a clopenable
    refinement; the resulting Cantor antichain returns to the ambient space. -/)
  (uses := ["thm:finite-carrier-iso-borel", "thm:cantor-to-perfect"])]
theorem counting_fin_models_countable_or_perfect (φ : L.Sentenceω) (n : ℕ) :
    #(Quotient (isoSetoidOn φ n)) ≤ ℵ₀ ∨
      φ.HasPerfectSetOfPairwiseNonisomorphicFinModels n := by
  rcases silver_countable_or_cantorAntichain (modelsOfOn_measurableSet φ)
      (structureIsoSetoidOn L n) (isoSetoidOn φ n) (fun _ _ h => h)
      (isoSetoidOn_measurableSet φ n) with hcount | hcantor
  · have := hcount
    exact Or.inl Cardinal.mk_le_aleph0
  · exact Or.inr (Sentenceω.hasPerfectSetFin_of_ambient_cantorAntichain hcantor)

/-! ### The tiered theorem -/

/-- **Morley's counting theorem, with a witness in the second alternative.**

Either at most `ℵ₁` isomorphism classes of countable models, or a perfect set of pairwise
non-isomorphic models at one of the two tiers.

The `ℕ`-tier and `Fin n`-tier alternatives are kept separate because they are genuinely different
statements about different spaces, and because neither implies the other: a sentence may have a
perfect set of finite models and no infinite models whatsoever. -/
@[blueprint "thm:morley-counting-or-perfect"
  (title := /-- Morley counting or a perfect set -/)
  (statement := /-- For any $\Lomegaone$ sentence $\varphi$, either the isomorphism classes of
    countable models number at most $\aleph_1$, or $\varphi$ has a perfect set of pairwise
    non-isomorphic $\mathbb{N}$-models, or it has one of pairwise non-isomorphic
    $\operatorname{Fin} n$-models for some $n$. -/)
  (proof := /-- Combine the two per-tier witnessed dichotomies.  If neither tier yields a perfect
    set, the $\mathbb{N}$ tier contributes at most $\aleph_1$ classes and the countably many
    finite tiers contribute at most $\aleph_0 \cdot \aleph_0 = \aleph_0$ between them. -/)
  (uses := ["thm:morley-counting-coded-or-perfect", "thm:counting-fin-models-or-perfect"])]
theorem morley_counting_or_perfect (φ : L.Sentenceω) :
    #(AllCodedIsoClasses φ) ≤ Cardinal.aleph 1 ∨
      φ.HasPerfectSetOfPairwiseNonisomorphicNatModels ∨
      ∃ n, φ.HasPerfectSetOfPairwiseNonisomorphicFinModels n := by
  rcases morley_counting_coded_or_perfect φ with hN | hN
  swap
  · exact Or.inr (Or.inl hN)
  by_cases hFin : ∃ n, φ.HasPerfectSetOfPairwiseNonisomorphicFinModels n
  · exact Or.inr (Or.inr hFin)
  push Not at hFin
  have hfin : ∀ n, #(Quotient (isoSetoidOn φ n)) ≤ ℵ₀ := fun n =>
    (counting_fin_models_countable_or_perfect φ n).resolve_right (hFin n)
  refine Or.inl ?_
  show #(Quotient (isoSetoid φ) ⊕ Σ n, Quotient (isoSetoidOn φ n)) ≤ Cardinal.aleph 1
  rw [Cardinal.mk_sum, Cardinal.lift_id, Cardinal.lift_id]
  refine Cardinal.add_le_of_le (Cardinal.aleph0_le_aleph 1) hN ?_
  calc #(Σ n, Quotient (isoSetoidOn φ n))
      ≤ ℵ₀ * ℵ₀ := mk_sigma_isoSetoidOn_le φ _ hfin
    _ = ℵ₀ := Cardinal.aleph0_mul_aleph0
    _ ≤ Cardinal.aleph 1 := Cardinal.aleph0_le_aleph 1

/-! ### The cardinal form as a corollary

Recovering `morley_counting`'s conclusion from the witnessed one, which is the sense in which the
perfect alternatives carry more information rather than merely restating it.  The upper bound
`≤ 2^{ℵ₀}` is not part of the witnessed statement and is supplied here: every tier's quotient is a
quotient of a `Bool`-valued function space on a countable index. -/

/-- Each tier has at most continuum-many isomorphism classes. -/
private theorem mk_quotient_tiers_le_continuum (φ : L.Sentenceω) :
    #(Quotient (isoSetoid φ)) ≤ Cardinal.continuum ∧
      ∀ n, #(Quotient (isoSetoidOn φ n)) ≤ Cardinal.continuum := by
  refine ⟨?_, fun n => ?_⟩
  · exact Cardinal.mk_quotient_le.trans
      ((Cardinal.mk_subtype_le _).trans mk_structureSpaceOn_le_continuum)
  · exact Cardinal.mk_quotient_le.trans
      ((Cardinal.mk_subtype_le _).trans mk_structureSpaceOn_le_continuum)

/-- **The cardinal alternative, as a corollary of the witnessed one.**

This is `morley_counting`'s conclusion, obtained without assuming the Silver–Burgess dichotomy:
either alternative's perfect set forces continuum-many classes, and the ambient space supplies the
matching upper bound. -/
theorem morley_counting_or_perfect_cardinal (φ : L.Sentenceω) :
    #(AllCodedIsoClasses φ) ≤ Cardinal.aleph 1 ∨
      #(AllCodedIsoClasses φ) = Cardinal.continuum := by
  obtain ⟨hNle, hFinle⟩ := mk_quotient_tiers_le_continuum φ
  -- the upper bound holds in every branch, so it is established once
  have hupper : #(AllCodedIsoClasses φ) ≤ Cardinal.continuum := by
    show #(Quotient (isoSetoid φ) ⊕ Σ n, Quotient (isoSetoidOn φ n)) ≤ Cardinal.continuum
    rw [Cardinal.mk_sum, Cardinal.lift_id, Cardinal.lift_id]
    refine Cardinal.add_le_of_le Cardinal.aleph0_le_continuum hNle ?_
    calc #(Σ n, Quotient (isoSetoidOn φ n))
        ≤ ℵ₀ * Cardinal.continuum := mk_sigma_isoSetoidOn_le φ _ hFinle
      _ = Cardinal.continuum := Cardinal.aleph0_mul_eq Cardinal.aleph0_le_continuum
  -- a perfect set at either tier gives the matching lower bound, through that tier's summand
  have hlower : ∀ {c : Cardinal.{v}}, Cardinal.continuum ≤ c →
      c ≤ #(AllCodedIsoClasses φ) → #(AllCodedIsoClasses φ) = Cardinal.continuum :=
    fun hc hle => le_antisymm hupper (hc.trans hle)
  rcases morley_counting_or_perfect φ with h | h | ⟨n, h⟩
  · exact Or.inl h
  · refine Or.inr (hlower h.continuum_le ?_)
    show #(Quotient (isoSetoid φ)) ≤ #(Quotient (isoSetoid φ) ⊕ Σ n, Quotient (isoSetoidOn φ n))
    rw [Cardinal.mk_sum, Cardinal.lift_id, Cardinal.lift_id]
    exact le_self_add
  · refine Or.inr (hlower h.continuum_le ?_)
    show #(Quotient (isoSetoidOn φ n)) ≤
      #(Quotient (isoSetoid φ) ⊕ Σ m, Quotient (isoSetoidOn φ m))
    rw [Cardinal.mk_sum, Cardinal.lift_id, Cardinal.lift_id]
    exact le_add_self.trans' ⟨⟨fun x => ⟨n, x⟩, fun a b h => eq_of_heq (Sigma.mk.inj h).2⟩⟩

end FirstOrder.Language
