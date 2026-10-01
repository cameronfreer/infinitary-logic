/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import InfinitaryLogic.Descriptive.KleeneBrouwer

/-!
# Boundedness for analytic families of well-founded trees

An analytic family of well-founded trees on `ℕ`, whose node sets are closed, has heights bounded
by a single countable ordinal.  The proof is descriptive and self-contained: a continuous
parametrization by Baire space, one countable witness tree that dominates every tree of the
family, and the countability of the height of a well-founded tree.  It uses only the definition
of analytic sets, convergence in Baire space and the regularity of `ℵ₁`; no boundedness theorem
for well-orders is involved.

## Main declarations

* `KleeneBrouwer.analytic_tree_rank_bounded`: for an analytic `A ⊆ X` and `T : X → tree ℕ` with
  every node set `{x | s ∈ T x}` closed and `T x` well-founded on `A`, some `β < ω₁` strictly
  bounds `treeHeight (T x)` for every `x ∈ A`.

The helpers it consumes live with their subjects: `InfinitaryLogic.rank_le_rank_of_relHom`
(`OrdinalUtil`), and `hasInfiniteBranch_iff_exists_seq`, `treeHeight_le_of_relHom` and
`treeHeight_lt_omega1` (`KleeneBrouwer`).

## The witness tree

Write `A` as the range of a continuous `f : (ℕ → ℕ) → X` (the empty case is immediate).  A node
of the witness tree `W` is a list of `Nat.pair` codes of pairs `(s i, u i)` such that some `y`
extending `u` has `s ∈ T (f y)`; it is prefix-closed because the trees `T (f y)` are.

* `W` is well-founded.  Take a branch, with first coordinates `x` and second coordinates `y`,
  and for each stage `n` a witness `yₙ` extending `y|n` with `x|n ∈ T (f yₙ)`.  Fix a length `k`.
  For every stage `n ≥ k`, prefix closure of `T (f yₙ)` puts `yₙ` in the fixed set
  `{z | x|k ∈ T (f z)}`, which is closed as the preimage of a closed node set under `f`.  Since
  `yₙ → y` in Baire space, the limit `y` lies in that set: `x|k ∈ T (f y)` for every `k`, an
  infinite branch of `T (f y)`, although `f y ∈ A`.
* For `y : ℕ → ℕ`, the map `s ↦ (s, y|s.length)` is a homomorphism of strict extension from
  `T (f y)` to `W`, so `treeHeight (T (f y)) ≤ treeHeight W`; it need not be injective, and no
  injectivity is used.  As `W` is a well-founded tree on `ℕ`, `treeHeight W < ω₁`, and
  `β = treeHeight W + 1` works.

## Interpretation choices

* **Closed node sets.**  The hypothesis is that each `{x | s ∈ T x}` is closed, not necessarily
  clopen, so the assignment `x ↦ T x` need not be continuous.  Closedness is what the limit step
  uses, pulled back along the parametrization.  Measurable node sets on a Polish space are not
  treated here.
* **The explicit limit step.**  Membership of the limit is obtained from witnesses at all
  sufficiently long stages lying in one fixed closed set (`IsClosed.mem_of_tendsto`), not from a
  compactness or König argument.
* **Rank convention.**  `treeHeight T = ⨆ x, succ (rank x)` for the rank of strict extension, so
  the empty tree has height `0` and the root-only tree height `1`; the bound is strict.
* **Universes.**  Heights and the bound live in `Ordinal.{0}`; the parameter space `X` is in any
  universe.
* **Namespace.**  The theorem is stated in `KleeneBrouwer`, the namespace of `treeHeight`,
  `extBelow` and `HasInfiniteBranch`, which it is about.

## References

* A. S. Kechris, *Classical Descriptive Set Theory*, Graduate Texts in Mathematics 156,
  Springer, 1995, §31.A: Theorem 31.2 (the Boundedness Theorem for WF: an analytic set of
  well-founded trees on `ℕ` has ranks bounded below `ω₁`), derived there from Theorem 31.1
  (analytic well-founded relations have countable rank), whose proof (due to Kunen) maps into a
  countable well-founded tree of attempts.  The statement here parametrizes the trees over an
  arbitrary topological space with closed node sets; Kechris's `ρ(T)` is `treeHeight T`.
* R. Chen, *A topological proof of the boundedness theorem for Σ¹₁ well-founded relations*, note,
  rynchn.github.io/math/treebound.pdf: a direct proof through inverse limits of Polish spaces.
  The construction here is the witness tree above, not the argument of that note.
-/

namespace KleeneBrouwer

open Descriptive MeasureTheory Filter Topology Set

variable {X : Type*}

/-! ## Coded pairs -/

/-- The first coordinates of a list of `Nat.pair` codes. -/
private def fstList (l : List ℕ) : List ℕ := l.map fun n ↦ n.unpair.1

/-- The second coordinates of `l` form an initial segment of `y`. -/
private def SndAgrees (l : List ℕ) (y : ℕ → ℕ) : Prop :=
  ∀ i (h : i < l.length), l[i].unpair.2 = y i

/-- Pair a list with the initial segment of `y` of the same length. -/
private def pairList (s : List ℕ) (y : ℕ → ℕ) : List ℕ := s.mapIdx fun i a ↦ Nat.pair a (y i)

private theorem fstList_pairList (s : List ℕ) (y : ℕ → ℕ) : fstList (pairList s y) = s :=
  List.ext_getElem (by simp [fstList, pairList]) fun i _ _ ↦ by simp [fstList, pairList]

private theorem sndAgrees_pairList (s : List ℕ) (y : ℕ → ℕ) : SndAgrees (pairList s y) y :=
  fun i _ ↦ by simp [pairList]

/-- Pairing with a fixed sequence preserves proper prefixes. -/
private theorem properPrefix_pairList {s t : List ℕ} (y : ℕ → ℕ) (h : ProperPrefix s t) :
    ProperPrefix (pairList s y) (pairList t y) := by
  obtain ⟨⟨r, rfl⟩, hne⟩ := h
  refine ⟨by simp only [pairList, List.mapIdx_append]; exact List.prefix_append _ _,
    fun heq ↦ hne ?_⟩
  have hlen := congrArg List.length heq
  simp only [pairList, List.length_mapIdx, List.length_append] at hlen
  have hr : r = [] := List.eq_nil_of_length_eq_zero (by omega)
  simp [hr]

/-! ## The witness tree -/

/-- The nodes of the witness tree: codes of pairs `(s, u)` such that some `y` extending `u` has
`s ∈ T (f y)`. -/
private def witnessNodes (f : (ℕ → ℕ) → X) (T : X → tree ℕ) : Set (List ℕ) :=
  {l | ∃ y, SndAgrees l y ∧ fstList l ∈ T (f y)}

private theorem witnessNodes_prefix {f : (ℕ → ℕ) → X} {T : X → tree ℕ} ⦃l : List ℕ⦄ ⦃a : ℕ⦄
    (h : l ++ [a] ∈ witnessNodes f T) : l ∈ witnessNodes f T := by
  obtain ⟨y, hy, hmem⟩ := h
  refine ⟨y, fun i hi ↦ ?_, Tree.mem_of_prefix ?_ hmem⟩
  · have := hy i (by simp; omega)
    rwa [List.getElem_append_left hi] at this
  · simp [fstList]

/-- The witness tree ("tree of attempts") of `T` along `f`. -/
private def witnessTree (f : (ℕ → ℕ) → X) (T : X → tree ℕ) : tree ℕ :=
  ⟨witnessNodes f T, fun _ _ h ↦ witnessNodes_prefix h⟩

private theorem mem_witnessTree {f : (ℕ → ℕ) → X} {T : X → tree ℕ} {l : List ℕ} :
    l ∈ witnessTree f T ↔ ∃ y, SndAgrees l y ∧ fstList l ∈ T (f y) := Iff.rfl

/-- **The witness tree is well-founded**: a branch would converge, through closed node sets, to an
infinite branch of a tree of the family. -/
private theorem wellFounded_witnessTree [TopologicalSpace X] {f : (ℕ → ℕ) → X}
    (hf : Continuous f) (T : X → tree ℕ) (hT : ∀ s : List ℕ, IsClosed {x | s ∈ T x})
    (hwf : ∀ x ∈ range f, WellFounded (extBelow (T x))) :
    WellFounded (extBelow (witnessTree f T)) := by
  rw [wellFounded_extBelow_iff_not_hasInfiniteBranch, hasInfiniteBranch_iff_exists_seq]
  rintro ⟨z, hz⟩
  -- the branch splits into first coordinates `x` and second coordinates `y`
  set x : ℕ → ℕ := fun i ↦ (z i).unpair.1 with hx
  set y : ℕ → ℕ := fun i ↦ (z i).unpair.2
  -- a witness `w n` at every stage `n`
  choose w hw hmem using fun n ↦ mem_witnessTree.mp (hz n)
  have hfst : ∀ n, fstList (List.ofFn fun i : Fin n ↦ z i) = List.ofFn fun i : Fin n ↦ x i :=
    fun n ↦ by simp [fstList, hx, List.map_ofFn, Function.comp_def]
  have hagree : ∀ n i, i < n → w n i = y i := fun n i hi ↦ by
    have := hw n i (by simpa using hi)
    simp only [List.getElem_ofFn] at this
    exact this.symm
  -- the witnesses converge to `y` in Baire space
  have htend : Tendsto w atTop (𝓝 y) :=
    tendsto_pi_nhds.mpr fun i ↦ tendsto_atTop_of_eventually_const (i₀ := i + 1)
      fun n hn ↦ hagree n i (by omega)
  -- the limit step: fix `k`; every stage `n ≥ k` puts `w n` in one closed set
  have hbranch : ∀ k, (List.ofFn fun i : Fin k ↦ x i) ∈ T (f y) := by
    intro k
    have hclosed : IsClosed {v : ℕ → ℕ | (List.ofFn fun i : Fin k ↦ x i) ∈ T (f v)} :=
      (hT _).preimage hf
    refine hclosed.mem_of_tendsto htend (eventually_atTop.mpr ⟨k, fun n hn ↦ ?_⟩)
    have hn : (List.ofFn fun i : Fin n ↦ x i) ∈ T (f (w n)) := hfst n ▸ hmem n
    have htake : (List.ofFn fun i : Fin n ↦ x i).take k = List.ofFn fun i : Fin k ↦ x i :=
      List.ext_getElem (by simp; omega) fun i _ _ ↦ by simp
    exact htake ▸ Tree.mem_of_prefix (List.take_prefix _ _) hn
  exact (wellFounded_extBelow_iff_not_hasInfiniteBranch _).mp (hwf (f y) (mem_range_self y))
    ((hasInfiniteBranch_iff_exists_seq _).mpr ⟨x, hbranch⟩)

/-- The tree of the parameter `f y` maps into the witness tree, pairing each node with the
matching initial segment of `y`. -/
private def witnessHom (f : (ℕ → ℕ) → X) (T : X → tree ℕ) (y : ℕ → ℕ) :
    extBelow (T (f y)) →r extBelow (witnessTree f T) where
  toFun s := ⟨pairList s y, mem_witnessTree.mpr
    ⟨y, sndAgrees_pairList _ y, by rw [fstList_pairList]; exact s.2⟩⟩
  map_rel' h := properPrefix_pairList y h

/-! ## Boundedness -/

/-- **Boundedness for analytic families of well-founded trees.**  If `A` is analytic, every node
set `{x | s ∈ T x}` is closed, and `T x` is well-founded for `x ∈ A`, then one countable ordinal
strictly bounds the heights of all the trees `T x` with `x ∈ A`. -/
theorem analytic_tree_rank_bounded [TopologicalSpace X] {A : Set X} (hA : AnalyticSet A)
    (T : X → tree ℕ) (hT : ∀ s : List ℕ, IsClosed {x | s ∈ T x})
    (hwf : ∀ x ∈ A, WellFounded (extBelow (T x))) :
    ∃ β : Ordinal.{0}, β < Ordinal.omega 1 ∧
      ∀ x (hx : x ∈ A), @treeHeight (T x) (hwf x hx) < β := by
  rw [AnalyticSet] at hA
  rcases hA with rfl | ⟨f, hf, rfl⟩
  · exact ⟨0, Ordinal.omega_pos 1, fun _ hx ↦ hx.elim⟩
  have : WellFounded (extBelow (witnessTree f T)) := wellFounded_witnessTree hf T hT hwf
  refine ⟨treeHeight (witnessTree f T) + 1, ?_, ?_⟩
  · rw [← Order.succ_eq_add_one]
    exact (Cardinal.isSuccLimit_omega 1).succ_lt (treeHeight_lt_omega1 _)
  · rintro _ ⟨y, rfl⟩
    have := hwf (f y) (mem_range_self y)
    exact (treeHeight_le_of_relHom (witnessHom f T y)).trans_lt (lt_add_one _)

end KleeneBrouwer
