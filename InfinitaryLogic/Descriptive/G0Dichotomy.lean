/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# Towards the classical `G₀`-dichotomy: independence and positivity machinery

Foundations for the proof of `GSGraphHomHypothesis` (the KST/Miller `G₀`-dichotomy core;
see `InfinitaryLogic/Conditional/SilverCategoryRoute.lean` and
`docs/silver-phase2-route.md`). This file provides the two pillars of the classical
(forcing-free, effective-DST-free) proof:

* **The separation core** (`exists_measurableSet_relIndependent_superset`): for an analytic
  relation `G` on a Polish space, every analytic `G`-independent set is contained in a
  *Borel* `G`-independent set. This is the Kechris–Solecki–Todorcevic lemma, proved here by
  an ω-recursion of Lusin separations (`AnalyticSet.measurablySeparable`): build a
  decreasing sequence of Borel sets `C n ⊇ A`, each separated from the `G`-neighborhood of
  the previous one; the intersection is Borel and independent.

* **The positivity machinery** (`SmallFam`): a family `Φ` of finite assignments `ι → α` is
  *small* if countably many Borel `G`-independent sets capture a value of every member —
  Miller's ideal `I_n` on partial homomorphisms. Smallness is monotone and countably
  additive (`SmallFam.iUnion_of_forall`), giving the pigeonhole
  (`exists_not_smallFam_inter`) used to refine positive families by vertex-value and
  witness-prefix constraints. For the graph `¬r` of a Borel equivalence relation with
  uncountably many classes, the full family is not small (`not_smallFam_univ`): every
  `¬r`-independent set lies in a single class, so a countable capture family would make the
  quotient countable.

The remaining steps of the dichotomy (the combination lemma transferring positivity from
level `n` to level `n + 1`, and the fusion extracting the continuous homomorphism) build on
these; see the 2C-b plan in `docs/silver-phase2-route.md`.
-/

open Set Function MeasureTheory

/-! ### Independent sets and neighborhoods -/

section Independence

variable {α : Type*}

/-- A set is independent for a relation `G` (a set of pairs) if it contains no `G`-edge. -/
def RelIndependent (G : Set (α × α)) (A : Set α) : Prop :=
  ∀ ⦃a⦄, a ∈ A → ∀ ⦃b⦄, b ∈ A → (a, b) ∉ G

theorem RelIndependent.mono {G : Set (α × α)} {A B : Set α} (hBA : B ⊆ A)
    (hA : RelIndependent G A) : RelIndependent G B :=
  fun _ ha _ hb => hA (hBA ha) (hBA hb)

/-- The set of points `G`-adjacent (in either orientation) to some point of `C`. -/
def relNbhd (G : Set (α × α)) (C : Set α) : Set α :=
  {x | ∃ y ∈ C, (x, y) ∈ G ∨ (y, x) ∈ G}

theorem relNbhd_mono {G : Set (α × α)} {C D : Set α} (h : C ⊆ D) :
    relNbhd G C ⊆ relNbhd G D :=
  fun _ ⟨y, hy, he⟩ => ⟨y, h hy, he⟩

theorem RelIndependent.disjoint_relNbhd {G : Set (α × α)} {A : Set α}
    (hA : RelIndependent G A) : Disjoint A (relNbhd G A) := by
  rw [Set.disjoint_left]
  rintro x hxA ⟨y, hyA, he | he⟩
  · exact hA hxA hyA he
  · exact hA hyA hxA he

end Independence

section Separation

variable {α : Type*} [TopologicalSpace α] [PolishSpace α]

theorem analyticSet_relNbhd {G : Set (α × α)} (hG : AnalyticSet G)
    {C : Set α} (hC : AnalyticSet C) : AnalyticSet (relNbhd G C) := by
  have hswap : AnalyticSet (Prod.swap ⁻¹' G : Set (α × α)) :=
    hG.preimage continuous_swap
  have hunion : AnalyticSet (G ∪ Prod.swap ⁻¹' G) := by
    rw [Set.union_eq_iUnion]
    exact AnalyticSet.iUnion fun b => by cases b <;> simpa
  have hsnd : AnalyticSet (Prod.snd ⁻¹' C : Set (α × α)) :=
    hC.preimage continuous_snd
  have hinter : AnalyticSet ((G ∪ Prod.swap ⁻¹' G) ∩ Prod.snd ⁻¹' C) := by
    rw [Set.inter_eq_iInter]
    exact AnalyticSet.iInter fun b => by cases b <;> simpa
  have himg := hinter.image_of_continuous continuous_fst
  convert himg using 1
  ext x
  constructor
  · rintro ⟨y, hyC, he⟩
    exact ⟨(x, y), ⟨by simpa using he, hyC⟩, rfl⟩
  · rintro ⟨⟨x', y⟩, ⟨he, hyC⟩, rfl⟩
    exact ⟨y, hyC, by simpa using he⟩

variable [MeasurableSpace α] [BorelSpace α]

/-- **The KST independent-superset lemma**: every analytic independent set for an analytic
relation on a Polish space is contained in a Borel independent set. Proved by an
ω-recursion of Lusin separations. -/
theorem exists_measurableSet_relIndependent_superset
    {G : Set (α × α)} (hG : AnalyticSet G)
    {A : Set α} (hA : AnalyticSet A) (hAind : RelIndependent G A) :
    ∃ B : Set α, MeasurableSet B ∧ A ⊆ B ∧ RelIndependent G B := by
  classical
  -- Stages: Borel supersets of A disjoint from the G-neighborhood of A
  let T := {C : Set α // MeasurableSet C ∧ A ⊆ C ∧ Disjoint C (relNbhd G A)}
  -- The initial stage, separating A from its own neighborhood
  have h0 : ∃ C : Set α, MeasurableSet C ∧ A ⊆ C ∧ Disjoint C (relNbhd G A) := by
    obtain ⟨u, hAu, hdis, hum⟩ :=
      hA.measurablySeparable (analyticSet_relNbhd hG hA) hAind.disjoint_relNbhd
    exact ⟨u, hum, hAu, hdis.symm⟩
  -- The refinement step, separating A from the neighborhood of the current stage
  have hstep : ∀ t : T, ∃ t' : T, t'.1 ⊆ t.1 ∧ Disjoint t'.1 (relNbhd G t.1) := by
    rintro ⟨C, hCm, hAC, hCd⟩
    have hdisj : Disjoint A (relNbhd G C) := by
      rw [Set.disjoint_left]
      rintro x hxA ⟨y, hyC, he⟩
      have hy : y ∈ relNbhd G A := ⟨x, hxA, he.symm⟩
      exact Set.disjoint_left.mp hCd hyC hy
    obtain ⟨u, hAu, hdis, hum⟩ :=
      hA.measurablySeparable (analyticSet_relNbhd hG hCm.analyticSet) hdisj
    exact ⟨⟨u ∩ C, hum.inter hCm, subset_inter hAu hAC,
      hCd.mono_left inter_subset_right⟩, inter_subset_right,
      hdis.symm.mono_left inter_subset_left⟩
  -- The tower of stages
  let seq : ℕ → T := fun n => Nat.rec ⟨_, h0.choose_spec⟩ (fun _ t => (hstep t).choose) n
  have hseq : ∀ n, (seq (n + 1)).1 ⊆ (seq n).1 ∧
      Disjoint (seq (n + 1)).1 (relNbhd G (seq n).1) :=
    fun n => (hstep (seq n)).choose_spec
  refine ⟨⋂ n, (seq n).1, MeasurableSet.iInter fun n => (seq n).2.1,
    subset_iInter fun n => (seq n).2.2.1, ?_⟩
  -- Independence of the intersection
  rintro a ha b hb hab
  have haB : a ∈ (seq 0).1 := mem_iInter.mp ha 0
  have hbB : b ∈ (seq 1).1 := mem_iInter.mp hb 1
  have hbn : b ∈ relNbhd G (seq 0).1 := ⟨a, haB, Or.inr hab⟩
  exact Set.disjoint_left.mp (hseq 0).2 hbB hbn

end Separation

/-! ### The smallness ideal on families of finite assignments -/

section Smallness

variable {α : Type*} [MeasurableSpace α]

/-- A family `Φ` of assignments `ι → α` is **small** for `G` if countably many Borel
`G`-independent sets capture a value of every member of `Φ`. This is Miller's ideal `I_n`
on the spaces of partial homomorphisms. -/
def SmallFam (G : Set (α × α)) {ι : Type*} (Φ : Set (ι → α)) : Prop :=
  ∃ C : ℕ → Set α, (∀ k, MeasurableSet (C k) ∧ RelIndependent G (C k)) ∧
    ∀ φ ∈ Φ, ∃ i : ι, ∃ k : ℕ, φ i ∈ C k

theorem SmallFam.mono {G : Set (α × α)} {ι : Type*} {Φ Ψ : Set (ι → α)}
    (hΨΦ : Ψ ⊆ Φ) (h : SmallFam G Φ) : SmallFam G Ψ := by
  obtain ⟨C, hC, hcap⟩ := h
  exact ⟨C, hC, fun φ hφ => hcap φ (hΨΦ hφ)⟩

theorem SmallFam.empty {G : Set (α × α)} {ι : Type*} :
    SmallFam G (∅ : Set (ι → α)) :=
  ⟨fun _ => ∅, fun _ => ⟨MeasurableSet.empty, fun _ h => h.elim⟩, fun _ h => h.elim⟩

/-- Smallness is countably additive. -/
theorem SmallFam.iUnion_of_forall {G : Set (α × α)} {ι : Type*} {Ψ : ℕ → Set (ι → α)}
    (h : ∀ n, SmallFam G (Ψ n)) : SmallFam G (⋃ n, Ψ n) := by
  choose C hC hcap using h
  refine ⟨fun k => C (Nat.unpair k).1 (Nat.unpair k).2, fun k => hC _ _, ?_⟩
  rintro φ hφ
  obtain ⟨n, hn⟩ := mem_iUnion.mp hφ
  obtain ⟨i, k, hik⟩ := hcap n φ hn
  exact ⟨i, Nat.pair n k, by simpa [Nat.unpair_pair] using hik⟩

/-- **Positivity pigeonhole**: a non-small family covered by countably many pieces has a
non-small piece. Used to refine positive families by vertex-value and witness-prefix
constraints. -/
theorem exists_not_smallFam_inter {G : Set (α × α)} {ι : Type*} {Φ : Set (ι → α)}
    (hΦ : ¬ SmallFam G Φ) {Ψ : ℕ → Set (ι → α)} (hcov : Φ ⊆ ⋃ n, Ψ n) :
    ∃ n, ¬ SmallFam G (Φ ∩ Ψ n) := by
  by_contra h
  push_neg at h
  apply hΦ
  have hΦeq : Φ = ⋃ n, Φ ∩ Ψ n := by
    ext φ
    simp only [mem_iUnion, mem_inter_iff]
    exact ⟨fun hφ => by obtain ⟨n, hn⟩ := mem_iUnion.mp (hcov hφ); exact ⟨n, hφ, hn⟩,
      fun ⟨n, hφ, _⟩ => hφ⟩
  rw [hΦeq]
  exact SmallFam.iUnion_of_forall h

/-- Non-small families are nonempty. -/
theorem nonempty_of_not_smallFam {G : Set (α × α)} {ι : Type*} {Φ : Set (ι → α)}
    (hΦ : ¬ SmallFam G Φ) : Φ.Nonempty := by
  by_contra h
  rw [Set.not_nonempty_iff_eq_empty] at h
  exact hΦ (h ▸ SmallFam.empty)

/-! ### The seed: positivity of the full family for `¬r` -/

omit [MeasurableSpace α] in
/-- For the complement graph of an equivalence relation, independent sets lie in a single
class. -/
theorem rel_of_relIndependent_compl (r : Setoid α) {C : Set α}
    (hC : RelIndependent {p : α × α | ¬ r.r p.1 p.2} C) :
    ∀ ⦃a⦄, a ∈ C → ∀ ⦃b⦄, b ∈ C → r.r a b := by
  intro a ha b hb
  by_contra h
  exact hC ha hb h

/-- **The seed**: if a Borel equivalence relation has uncountably many classes, then the
full family of assignments is not small for the complement graph — a countable capture
family of independent (hence single-class) Borel sets would make the quotient countable. -/
theorem not_smallFam_univ {ι : Type*} [Nonempty ι] (r : Setoid α)
    (hunc : ¬ Countable (Quotient r)) :
    ¬ SmallFam {p : α × α | ¬ r.r p.1 p.2} (univ : Set (ι → α)) := by
  rintro ⟨C, hC, hcap⟩
  apply hunc
  -- every point lies in some C k
  have hcov : ∀ x : α, ∃ k, x ∈ C k := by
    intro x
    obtain ⟨_, k, hk⟩ := hcap (fun _ => x) (mem_univ _)
    exact ⟨k, hk⟩
  haveI : Nonempty α := by
    by_contra hne
    rw [not_nonempty_iff] at hne
    haveI : IsEmpty (Quotient r) := ⟨fun q => q.exists_rep.elim fun x _ => hne.false x⟩
    exact hunc inferInstance
  classical
  set f : ℕ → Quotient r := fun k =>
    if h : (C k).Nonempty then Quotient.mk r h.choose
    else Quotient.mk r Classical.ofNonempty
  have hsurj : Surjective f := by
    intro q
    obtain ⟨x, rfl⟩ := Quotient.exists_rep q
    obtain ⟨k, hk⟩ := hcov x
    refine ⟨k, ?_⟩
    have hne : (C k).Nonempty := ⟨x, hk⟩
    simp only [f, dif_pos hne]
    exact Quotient.sound (rel_of_relIndependent_compl r (hC k).2 hne.choose_spec hk)
  exact hsurj.countable

end Smallness
