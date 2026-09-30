/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.FiniteSupportClosure
import Mathlib.Data.Set.Countable
import Mathlib.Data.Finset.Card
import Mathlib.SetTheory.Cardinal.Aleph
import Mathlib.SetTheory.Cardinal.Arithmetic

/-!
# Cardinal bounds from two-generator finite hulls

For a closure operator `c` on the finite subsets of `M` and its finite-character extension
`setClosure c`:

* `mk_setClosure_eq`: closing an infinite set does not change its cardinality (no generation
  hypothesis; the closure is a union of finite hulls over the finite subsets).
* Under **whole-hull two-generation**, `hgen : ∀ S, ∃ T ⊆ S, T.card ≤ 2 ∧ c T = c S` (the hull of
  every finite input is the hull of at most two of its points):
  `countable_of_isClosed_ne_univ` (every proper closed subset is countable),
  `eq_univ_of_isClosed_uncountable`, `mk_le_aleph_one` (the carrier has cardinality at most
  `ℵ₁`, in any universe), and `surjective_of_isClosed_range` (an embedding of an uncountable type
  whose range is closed is surjective; closedness of the range is an explicit hypothesis).

The hypothesis concerns the **whole** hull of each finite input, not two-element witnesses for
individual memberships: the identity closure has pair witnesses for every membership on carriers
of any size, so the weaker form implies no bound (see the regression guard).  No anti-exchange,
singleton-closedness, nonemptiness, or model-theoretic assumption is used.
-/

set_option autoImplicit false

namespace InfinitaryLogic.FiniteSupportClosure

variable {M : Type*} (c : ClosureOperator (Finset M))

/-- Two exclusions in a triple force the third point into the remaining pair's hull. -/
theorem mem_pair_of_two_exclusions [DecidableEq M]
    (hgen : ∀ S, ∃ T ⊆ S, T.card ≤ 2 ∧ c T = c S)
    {a b s : M} (ha : a ∉ c {b, s}) (hb : b ∉ c {a, s}) : s ∈ c {a, b} := by
  obtain ⟨T, hT, hcard, he⟩ := hgen {a, b, s}
  have haT : a ∈ T := by
    by_contra h
    apply ha
    have hsub : T ⊆ {b, s} := by
      intro x hx
      have := hT hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at this ⊢
      rcases this with rfl | hx
      · exact (h hx).elim
      · exact hx
    apply c.monotone hsub
    rw [he]
    exact c.le_closure _ (by simp)
  have hbT : b ∈ T := by
    by_contra h
    apply hb
    have hsub : T ⊆ {a, s} := by
      intro x hx
      have := hT hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at this ⊢
      rcases this with rfl | rfl | rfl
      · exact Or.inl rfl
      · exact (h hx).elim
      · exact Or.inr rfl
    apply c.monotone hsub
    rw [he]
    exact c.le_closure _ (by simp)
  have hab : a ≠ b := by
    rintro rfl
    exact ha (c.le_closure _ (by simp))
  have hpair : ({a, b} : Finset M) = T :=
    Finset.eq_of_subset_of_card_le
      (Finset.insert_subset haT (Finset.singleton_subset_iff.mpr hbT))
      (by simpa [Finset.card_pair hab] using hcard)
  rw [hpair, he]
  exact c.le_closure _ (by simp)

/-- Every proper closed subset is countable.  The contradiction puts a countably infinite set
inside one finite two-point hull. -/
theorem countable_of_isClosed_ne_univ
    (hgen : ∀ S, ∃ T ⊆ S, T.card ≤ 2 ∧ c T = c S)
    {A : Set M} (hclosed : (setClosure c).IsClosed A) (hne : A ≠ Set.univ) :
    A.Countable := by
  classical
  by_contra hunc
  obtain ⟨b, hb⟩ := (Set.ne_univ_iff_exists_notMem A).mp hne
  have hAinf : A.Infinite := fun hfin => hunc hfin.countable
  obtain ⟨S, hSA, hSc, hSi⟩ := hAinf.exists_subset_countable_infinite
  let U : Set M := ⋃ s ∈ S, (↑(c {b, s}) : Set M)
  have hUc : U.Countable := hSc.biUnion fun s _ => (c {b, s}).countable_toSet
  have hnot : ¬ A ⊆ U := fun h => hunc (hUc.mono h)
  obtain ⟨a, haA, haU⟩ := Set.not_subset.mp hnot
  apply hSi
  apply (c {a, b}).finite_toSet.subset
  intro s hs
  apply mem_pair_of_two_exclusions c hgen
  · intro ha
    exact haU (Set.mem_iUnion₂.mpr ⟨s, hs, ha⟩)
  · intro hb'
    apply hb
    exact (setClosure_closed_iff c A).mp hclosed {a, s}
      (by simpa only [Finset.coe_insert, Finset.coe_singleton,
        Set.insert_subset_iff, Set.singleton_subset_iff] using And.intro haA (hSA hs)) hb'

/-- A closed uncountable subset is the entire carrier. -/
theorem eq_univ_of_isClosed_uncountable
    (hgen : ∀ S, ∃ T ⊆ S, T.card ≤ 2 ∧ c T = c S)
    {A : Set M} (hclosed : (setClosure c).IsClosed A) (hunc : ¬ A.Countable) :
    A = Set.univ := by
  by_contra hne
  exact hunc (countable_of_isClosed_ne_univ c hgen hclosed hne)

open Cardinal in
/-- A locally finite closure does not increase the cardinality of an infinite set.  This needs no
generation hypothesis. -/
theorem mk_setClosure_eq {A : Set M} (hA : A.Infinite) :
    #(setClosure c A) = #A := by
  classical
  have : Infinite A := hA.to_subtype
  have he : setClosure c A =
      ⋃ S : Finset A, (↑(c (S.map (Function.Embedding.subtype _))) : Set M) := by
    ext x
    constructor
    · rintro ⟨S, hS, hx⟩
      apply Set.mem_iUnion.mpr
      refine ⟨S.subtype (· ∈ A), ?_⟩
      simpa only [Finset.subtype_map_of_mem (fun y hy => hS hy), Finset.mem_coe] using hx
    · intro hx
      obtain ⟨S, hx⟩ := Set.mem_iUnion.mp hx
      exact ⟨_, S.map_subtype_subset, hx⟩
  apply le_antisymm
  · rw [he]
    calc
      _ ≤ #(Finset A) * ⨆ S : Finset A,
          #(↑(c (S.map (Function.Embedding.subtype _))) : Set M) := mk_iUnion_le _
      _ ≤ #A * #A := by
        rw [mk_finset_of_infinite]
        apply mul_le_mul_right
        apply ciSup_le'
        intro S
        exact mk_le_aleph0.trans (aleph0_le_mk A)
      _ = #A := mul_eq_self (aleph0_le_mk A)
  · exact mk_le_mk_of_subset ((setClosure c).le_closure A)

open Cardinal in
/-- Whole-hull two-generation bounds the entire carrier by the first uncountable cardinal, in any
universe. -/
theorem mk_le_aleph_one
    (hgen : ∀ S, ∃ T ⊆ S, T.card ≤ 2 ∧ c T = c S) : #M ≤ ℵ₁ := by
  classical
  by_contra h
  have hlarge : ℵ₁ < #M := lt_of_not_ge h
  obtain ⟨A, hA⟩ := le_mk_iff_exists_set.mp hlarge.le
  have hunc : ¬ A.Countable := by
    intro hcount
    have := le_aleph0_iff_set_countable.mpr hcount
    rw [hA] at this
    exact aleph0_lt_aleph_one.not_ge this
  have hinf : A.Infinite := fun hfin => hunc hfin.countable
  have hcard := mk_setClosure_eq c hinf
  have hproper : setClosure c A ≠ Set.univ := by
    intro he
    rw [he, mk_univ, hA] at hcard
    exact hlarge.ne hcard.symm
  have hcount := countable_of_isClosed_ne_univ c hgen
    ((setClosure c).isClosed_closure A) hproper
  exact hunc (hcount.mono ((setClosure c).le_closure A))

/-- Uncountable embeddings with closed range are surjective.  Closedness is an explicit
hypothesis, not a consequence of injectivity alone. -/
theorem surjective_of_isClosed_range {N : Type*} [Uncountable N]
    (hgen : ∀ S, ∃ T ⊆ S, T.card ≤ 2 ∧ c T = c S)
    (e : N ↪ M) (hclosed : (setClosure c).IsClosed (Set.range e)) :
    Function.Surjective e := by
  apply Set.range_eq_univ.mp
  apply eq_univ_of_isClosed_uncountable c hgen hclosed
  intro hcount
  have : Countable (Set.range e) := hcount.to_subtype
  have hinj : Function.Injective (fun x : N => (⟨e x, x, rfl⟩ : Set.range e)) :=
    fun x y h => e.injective (congrArg Subtype.val h)
  exact not_countable hinj.countable

end InfinitaryLogic.FiniteSupportClosure
