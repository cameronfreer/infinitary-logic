/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.SetTheory.Ordinal.Arithmetic
import InfinitaryLogic.Scott.AtomicDiagram

/-!
# The free array of a relational vocabulary

The array `Ψ^n_α` of Larson, *Scott processes* (Beyond First Order Model Theory, vol. I),
Definition 2.1 with the syntax stripped, together with the extension sets `E` of Definition
2.4, the vertical projections `V` of Definition 2.6, the horizontal projections `H` of
Definition 2.11, their commutation (Proposition 2.15), and Remarks 2.8, 2.13 and 2.14(2).
No formulas are built: an element of `Ψ^n_{α+1}` *is* the pair `(φ', E)` of Definition
2.1(2), and an element of `Ψ^n_λ` at a limit `λ` *is* the family of its conjuncts.

## Main declarations

* `AtomicData`: level-`0` data, a column family `Ψ0 n` with functorial restriction along
  injections `Fin m ↪ Fin n`; `relAtomic L` is the instance for a relational language `L`,
  built on the relation instances `AtomicIdx.rel` of `Scott/AtomicDiagram.lean`.
* `Ψ A α n`: the column `n` of row `α` (`α : Ordinal.{0}`, `n : ℕ`).
* `H j`, `V h`, `E`: the horizontal projection along `j : Fin m ↪ Fin n`, the vertical
  projection to a lower row, and the extension set of a successor-row element.
* `zeroEquiv`, `succEquiv`, `limEquiv`: the unfoldings of rows `0`, `α + 1` and `λ`;
  `mkSucc φ' E hE` builds the successor-row element `(φ', E)`, and `Ψ.ext_succ`, `Ψ.ext_limit`
  are the extensionality principles of successor and limit rows.
* `V_H_comm` (Proposition 2.15), `V_comp` (Remark 2.8), `H_id` (Remark 2.13),
  `H_comp` (Remark 2.14(2)), `E_H` (Definition 2.11(3)), `H_limit_entry` (Definition 2.11(4)),
  and the fullness statements `exists_succ_of_V_E`, `exists_limit_of_thread`.

## Interpretation choices

* **Abstract level `0`.** Row `0` is a parameter (`AtomicData`) rather than the set of
  complete atomic types; `relAtomic L` recovers Definition 2.1(1) for a relational `L`,
  storing one truth value per relation instance `AtomicIdx.rel R f` on `Fin n` (equalities
  are fixed by distinctness of the variables and are not stored), and restricting along
  `AtomicIdx.pushforward`.  Larson's standing assumption of a `0`-ary relation (Remark 2.3) is
  not imposed.
* **Universes and the row index.** Rows are indexed by `Ordinal.{0}`, and the columns live in
  `Type (w + 1)`: a limit-row column is a type of threads, which quantifies over
  `Ordinal.{0} : Type 1`, so no column can live in `Type 0`.  The level-`0` data is therefore
  stated in `Type (w + 1)`, and `relAtomic` lifts its truth assignments with `ULift`.  The rank
  invariants `orbitRank` and `internalScottRank` of `Scott/OrbitRank.lean` take values in
  `Ordinal.{w}` for `M : Type w`; the intended bridge between them and the rows here is
  `Ordinal.lift`, for countable (or otherwise small) structures.  The index universe is not
  generalized.
* **Indexing by `(α, n)`.** Columns are separate types `Ψ A α n` rather than subsets of one
  set `Ψ_α` of formulas; Larson's `Φ ∩ Ψ^n_α` becomes a family of sets indexed by `n`, and
  `Ψ_α = ⋃ n, Ψ^n_α` (Definition 2.1(4)) is not formed.
* **Entry-wise limit coherence.** A limit-row element is a thread `(ψ_β)_{β<λ}` satisfying
  Definition 2.1(3)(a) at successors and (3)(b) at limits, each stated entry-wise through
  the projection record rather than as an equation between conjunctions.
* **Projection above `α`.** The projection record of row `α` is defined at every ordinal;
  at or above `α` it returns the element itself (`Level.proj_of_le`).  Only `β ≤ α` is used
  by `V`.
* **Nonemptiness of `E(H φ j)`.** Definition 2.11(3) requires the new extension set to be
  nonempty; this is witnessed by the extension of `j` sending the last coordinate to the
  last coordinate (`extLast`).

## Encoding

The recursion on `α` returns a `Level α`: a column family `Ψ`, the horizontal maps `H`, and a
*projection record* `proj`. `proj n x β` records the vertical projection of `x` to row `β`
as a dependent pair `⟨row β as a package, value⟩`, where a package is a column family together
with its horizontal maps. Because the target of `proj` is a single fixed type, the limit step
can state the coherence conditions (a) and (b) for an arbitrary family of lower levels, with no
casts between the lower rows. The global `V` then reads off the value, after a single transport
along the proven identification of the recorded package with row `β`.  The lemmas computing
the projection record, and the transport lemmas, are private: the downstream interface is `V`,
`E`, `H` and their laws, with `V_eq_iff` characterizing `V` through the record.

## References

* Paul B. Larson, *Scott processes*, in *Beyond First Order Model Theory*, vol. I
  (J. Iovino, ed.), CRC Press, 2017, ch. 2.  Numbering follows the book; it agrees with the
  2016 preprint for §§2–4.
-/

open Order

universe w

noncomputable section

namespace InfinitaryLogic.ScottProcess.FreeArray

/-! ### Level 0 -/

/-- Level-`0` data: a column family with horizontal restriction (Definition 2.11(2)),
functorial along composition of injections. -/
structure AtomicData where
  /-- The column `Ψ^n_0`. -/
  Ψ0 : ℕ → Type (w + 1)
  /-- Horizontal restriction `H^n_0(·, j)` along `j : Fin m ↪ Fin n`. -/
  H0 : ∀ n m : ℕ, (Fin m ↪ Fin n) → Ψ0 n → Ψ0 m
  /-- Restriction along the identity is the identity. -/
  H0_id : ∀ n (x : Ψ0 n), H0 n n (Function.Embedding.refl _) x = x
  /-- Restriction is functorial. -/
  H0_comp : ∀ n m l (j : Fin m ↪ Fin n) (k : Fin l ↪ Fin m) (x : Ψ0 n),
    H0 m l k (H0 n m j x) = H0 n l (k.trans j) x

/-! ### Packages and levels -/

/-- A package: a column family together with its horizontal maps. -/
abbrev Pkg : Type (w + 2) :=
  Σ T : ℕ → Type (w + 1), ∀ n m : ℕ, (Fin m ↪ Fin n) → T n → T m

/-- A row `α` of the array, together with the projection record to all rows. -/
structure Level (α : Ordinal.{0}) where
  /-- The columns `Ψ^n_α`. -/
  Ψ : ℕ → Type (w + 1)
  /-- The horizontal maps `H^n_α(·, j)`. -/
  H : ∀ n m : ℕ, (Fin m ↪ Fin n) → Ψ n → Ψ m
  /-- The projection record: row `β` (as a package) and the projection of `x` to it. -/
  proj : ∀ n, Ψ n → Ordinal.{0} → Σ p : Pkg.{w}, p.1 n
  /-- At or above row `α` the record is `x` itself. -/
  proj_of_le : ∀ n x β, α ≤ β → proj n x β = ⟨⟨Ψ, H⟩, x⟩
  /-- The record commutes with the horizontal maps. -/
  proj_H : ∀ n m (j : Fin m ↪ Fin n) x β,
    proj m (H n m j x) β = ⟨(proj n x β).1, (proj n x β).1.2 n m j (proj n x β).2⟩

namespace Level

/-- The package of a level. -/
abbrev pkg {α : Ordinal.{0}} (L : Level.{w} α) : Pkg.{w} := ⟨L.Ψ, L.H⟩

end Level

/-- The zero row. -/
def zeroLevel (A : AtomicData.{w}) : Level.{w} 0 where
  Ψ := A.Ψ0
  H := A.H0
  proj _ x _ := ⟨⟨A.Ψ0, A.H0⟩, x⟩
  proj_of_le _ _ _ _ := rfl
  proj_H _ _ _ _ _ := rfl

/-! ### The successor step -/

/-- The admissible extensions of `j : Fin m ↪ Fin n` (Definition 2.11(3)): injections
`Fin (m+1) ↪ Fin (n+1)` agreeing with `j` on `Fin m` and sending the new coordinate `m` to
any coordinate of `Fin (n+1)` outside the range of `j` (the new coordinate `n`, or a
forgotten old one). -/
def extSet {n m : ℕ} (j : Fin m ↪ Fin n) : Set (Fin (m + 1) ↪ Fin (n + 1)) :=
  {j' | (∀ i : Fin m, j' i.castSucc = (j i).castSucc) ∧
    ∀ i : Fin m, j' (Fin.last m) ≠ (j i).castSucc}

/-- The extension of `j` sending the new coordinate `m` to `y`, a coordinate outside the
range of `j`. -/
def extTo {n m : ℕ} (j : Fin m ↪ Fin n) (y : Fin (n + 1)) (hy : ∀ i, y ≠ (j i).castSucc) :
    Fin (m + 1) ↪ Fin (n + 1) :=
  ⟨Fin.snoc (α := fun _ ↦ Fin (n + 1)) (fun i ↦ (j i).castSucc) y,
    Fin.snoc_injective_iff.2
      ⟨Fin.castSuccEmb.injective.comp j.injective, by rintro ⟨i, hi⟩; exact hy i hi.symm⟩⟩

/-- `extTo j y` is `Fin.snoc` of `j` (followed by `Fin.castSucc`) and `y`. -/
theorem coe_extTo {n m : ℕ} (j : Fin m ↪ Fin n) (y : Fin (n + 1))
    (hy : ∀ i, y ≠ (j i).castSucc) :
    ⇑(extTo j y hy) = Fin.snoc (α := fun _ ↦ Fin (n + 1)) (fun i ↦ (j i).castSucc) y :=
  rfl

/-- `extTo j y` agrees with `j` on the old coordinates. -/
@[simp] theorem extTo_castSucc {n m : ℕ} (j : Fin m ↪ Fin n) (y : Fin (n + 1))
    (hy : ∀ i, y ≠ (j i).castSucc) (i : Fin m) :
    extTo j y hy i.castSucc = (j i).castSucc := by
  rw [coe_extTo, Fin.snoc_castSucc]

/-- `extTo j y` sends the new coordinate to `y`. -/
@[simp] theorem extTo_last {n m : ℕ} (j : Fin m ↪ Fin n) (y : Fin (n + 1))
    (hy : ∀ i, y ≠ (j i).castSucc) : extTo j y hy (Fin.last m) = y := by
  rw [coe_extTo, Fin.snoc_last]

/-- `extTo j y` is an admissible extension of `j`. -/
theorem extTo_mem {n m : ℕ} (j : Fin m ↪ Fin n) (y : Fin (n + 1))
    (hy : ∀ i, y ≠ (j i).castSucc) : extTo j y hy ∈ extSet j :=
  ⟨fun i ↦ extTo_castSucc j y hy i, fun i ↦ by rw [extTo_last]; exact hy i⟩

/-- The extension sending the new coordinate to the new coordinate. -/
def extLast {n m : ℕ} (j : Fin m ↪ Fin n) : Fin (m + 1) ↪ Fin (n + 1) :=
  extTo j (Fin.last n) fun i ↦ (Fin.castSucc_ne_last (j i)).symm

/-- `extLast j` agrees with `j` on the old coordinates. -/
@[simp] theorem extLast_castSucc {n m : ℕ} (j : Fin m ↪ Fin n) (i : Fin m) :
    extLast j i.castSucc = (j i).castSucc :=
  extTo_castSucc _ _ _ i

/-- `extLast j` sends the new coordinate to the new coordinate. -/
@[simp] theorem extLast_last {n m : ℕ} (j : Fin m ↪ Fin n) :
    extLast j (Fin.last m) = Fin.last n :=
  extTo_last _ _ _

/-- `extLast j` is an admissible extension of `j`. -/
theorem extLast_mem {n m : ℕ} (j : Fin m ↪ Fin n) : extLast j ∈ extSet j :=
  extTo_mem _ _ _

/-- The admissible extensions of the identity: only the identity. -/
@[simp] theorem extSet_refl (n : ℕ) :
    extSet (Function.Embedding.refl (Fin n)) = {Function.Embedding.refl (Fin (n + 1))} := by
  ext j'
  rw [Set.mem_singleton_iff]
  constructor
  · intro hj'
    refine Function.Embedding.ext fun a ↦ ?_
    induction a using Fin.lastCases with
    | last =>
      rcases Fin.eq_castSucc_or_eq_last (j' (Fin.last n)) with ⟨i, hi⟩ | hi
      · exact absurd hi (hj'.2 i)
      · exact hi
    | cast a => exact hj'.1 a
  · rintro rfl
    exact ⟨fun _ ↦ rfl, fun i ↦ (Fin.castSucc_ne_last i).symm⟩

/-- Composites of admissible extensions are admissible extensions of the composite. -/
theorem trans_mem_extSet {n m l : ℕ} {j : Fin m ↪ Fin n} {k : Fin l ↪ Fin m}
    {j' : Fin (m + 1) ↪ Fin (n + 1)} {k' : Fin (l + 1) ↪ Fin (m + 1)}
    (hj' : j' ∈ extSet j) (hk' : k' ∈ extSet k) : k'.trans j' ∈ extSet (k.trans j) := by
  refine ⟨fun x ↦ ?_, fun x ↦ ?_⟩
  · simp only [Function.Embedding.trans_apply, hk'.1 x, hj'.1 (k x)]
  · simp only [Function.Embedding.trans_apply]
    rcases Fin.eq_castSucc_or_eq_last (k' (Fin.last l)) with ⟨y, hy⟩ | hy
    · rw [hy, hj'.1 y]
      intro h
      rw [Fin.castSucc_inj] at h
      exact hk'.2 x (hy.trans (congrArg Fin.castSucc (j.injective h)))
    · rw [hy]
      exact hj'.2 (k x)

/-- Every admissible extension of a composite factors through admissible extensions. -/
theorem exists_trans_of_mem_extSet {n m l : ℕ} {j : Fin m ↪ Fin n} {k : Fin l ↪ Fin m}
    {i : Fin (l + 1) ↪ Fin (n + 1)} (hi : i ∈ extSet (k.trans j)) :
    ∃ j' ∈ extSet j, ∃ k' ∈ extSet k, k'.trans j' = i := by
  by_cases hz : ∃ y, i (Fin.last l) = (j y).castSucc
  · obtain ⟨y, hy⟩ := hz
    have hyk : ∀ x, (y.castSucc : Fin (m + 1)) ≠ (k x).castSucc := by
      intro x h
      rw [Fin.castSucc_inj] at h
      exact hi.2 x (by rw [hy, h]; rfl)
    refine ⟨extLast j, extLast_mem j, extTo k _ hyk, extTo_mem _ _ _, ?_⟩
    refine Function.Embedding.ext fun a ↦ ?_
    induction a using Fin.lastCases with
    | last => rw [Function.Embedding.trans_apply, extTo_last, extLast_castSucc, hy]
    | cast a =>
      rw [Function.Embedding.trans_apply, extTo_castSucc, extLast_castSucc, hi.1 a]
      rfl
  · have hz' : ∀ y, i (Fin.last l) ≠ (j y).castSucc := fun y h ↦ hz ⟨y, h⟩
    refine ⟨extTo j _ hz', extTo_mem _ _ _, extLast k, extLast_mem k, ?_⟩
    refine Function.Embedding.ext fun a ↦ ?_
    induction a using Fin.lastCases with
    | last => rw [Function.Embedding.trans_apply, extLast_last, extTo_last]
    | cast a =>
      rw [Function.Embedding.trans_apply, extLast_castSucc, extTo_castSucc, hi.1 a]
      rfl

/-- The columns of the successor row: `Ψ^n_{α+1} = Ψ^n_α × {E ⊆ Ψ^{n+1}_α nonempty}`. -/
abbrev succΨ {α : Ordinal.{0}} (L : Level.{w} α) (n : ℕ) : Type (w + 1) :=
  L.Ψ n × {E : Set (L.Ψ (n + 1)) // E.Nonempty}

/-- The horizontal maps of the successor row (Definition 2.11(3)). -/
def succH {α : Ordinal.{0}} (L : Level.{w} α) (n m : ℕ) (j : Fin m ↪ Fin n)
    (x : succΨ L n) : succΨ L m :=
  (L.H n m j x.1,
    ⟨Set.image2 (fun ψ j' ↦ L.H (n + 1) (m + 1) j' ψ) x.2.1 (extSet j),
      x.2.2.image2 ⟨_, extLast_mem j⟩⟩)

/-- The first component of `succH` is the horizontal map of the lower row. -/
@[simp] theorem succH_fst {α : Ordinal.{0}} (L : Level.{w} α) (n m : ℕ) (j : Fin m ↪ Fin n)
    (x : succΨ L n) : (succH L n m j x).1 = L.H n m j x.1 :=
  rfl

/-- The extension set of `succH` is the image of `E × extSet j` (Definition 2.11(3)). -/
@[simp] theorem succH_snd {α : Ordinal.{0}} (L : Level.{w} α) (n m : ℕ) (j : Fin m ↪ Fin n)
    (x : succΨ L n) :
    (succH L n m j x).2.1 =
      Set.image2 (fun ψ j' ↦ L.H (n + 1) (m + 1) j' ψ) x.2.1 (extSet j) :=
  rfl

/-- The successor row. -/
def succLevel {α : Ordinal.{0}} (L : Level.{w} α) : Level.{w} (α + 1) where
  Ψ := succΨ L
  H := succH L
  proj n x β := if β ≤ α then L.proj n x.1 β else ⟨⟨succΨ L, succH L⟩, x⟩
  proj_of_le n x β h := by
    have : ¬ β ≤ α := not_le.2 (add_one_le_iff.1 h)
    simp only [this, ↓reduceIte]
  proj_H n m j x β := by
    by_cases h : β ≤ α
    · rw [ite_eq_left h, ite_eq_left h]
      exact L.proj_H n m j x.1 β
    · rw [ite_eq_right h, ite_eq_right h]

/-- The projection record of a successor row to `β ≤ α` is that of the first component. -/
private theorem succLevel_proj_of_le {α : Ordinal.{0}} (L : Level.{w} α) {n : ℕ}
    (x : succΨ L n) {β : Ordinal.{0}} (h : β ≤ α) :
    (succLevel L).proj n x β = L.proj n x.1 β :=
  ite_eq_left h

/-! ### The limit step -/

/-- Threads over a family of lower rows (Definition 2.1(3)): an entry in each row `β < λ`,
such that (a) the entry at `β + 1` projects to the entry at `β`, and (b) at each limit
`β < λ` the entry projects to every earlier entry. -/
abbrev Thread (lam : Ordinal.{0}) (f : ∀ β < lam, Level.{w} β) (n : ℕ) : Type (w + 1) :=
  {ψ : ∀ β (h : β < lam), (f β h).Ψ n //
    (∀ β (h : β + 1 < lam), (f (β + 1) h).proj n (ψ (β + 1) h) β =
      ⟨(f β ((lt_add_one β).trans h)).pkg, ψ β ((lt_add_one β).trans h)⟩) ∧
    (∀ β (h : β < lam), IsSuccLimit β → ∀ δ (hδ : δ < β),
      (f β h).proj n (ψ β h) δ = ⟨(f δ (hδ.trans h)).pkg, ψ δ (hδ.trans h)⟩)}

/-- The horizontal maps on threads (Definition 2.11(4)). -/
def threadH (lam : Ordinal.{0}) (f : ∀ β < lam, Level.{w} β) (n m : ℕ) (j : Fin m ↪ Fin n)
    (ψ : Thread lam f n) : Thread lam f m :=
  ⟨fun β h ↦ (f β h).H n m j (ψ.1 β h), by
    refine ⟨fun β h ↦ ?_, fun β h hβ δ hδ ↦ ?_⟩
    · rw [(f (β + 1) h).proj_H, ψ.2.1 β h]
    · rw [(f β h).proj_H, ψ.2.2 β h hβ δ hδ]⟩

/-- `threadH` acts entry-wise (Definition 2.11(4)). -/
@[simp] theorem threadH_coe (lam : Ordinal.{0}) (f : ∀ β < lam, Level.{w} β) (n m : ℕ)
    (j : Fin m ↪ Fin n) (ψ : Thread lam f n) :
    (threadH lam f n m j ψ).1 = fun β h ↦ (f β h).H n m j (ψ.1 β h) :=
  rfl

/-- The limit row. -/
def limLevel (lam : Ordinal.{0}) (f : ∀ β < lam, Level.{w} β) : Level.{w} lam where
  Ψ := Thread lam f
  H := threadH lam f
  proj n x β := if h : β < lam then ⟨(f β h).pkg, x.1 β h⟩ else ⟨⟨Thread lam f, threadH lam f⟩, x⟩
  proj_of_le n x β h := by
    simp only [not_lt.2 h, ↓reduceDIte]
  proj_H n m j x β := by
    by_cases h : β < lam
    · rw [dite_eq_left h, dite_eq_left h, threadH_coe]
    · rw [dite_eq_right h, dite_eq_right h]

/-- The projection record of a limit row to `β < λ` is the `β`-th entry. -/
private theorem limLevel_proj_of_lt (lam : Ordinal.{0}) (f : ∀ β < lam, Level.{w} β) {n : ℕ}
    (x : Thread lam f n) {β : Ordinal.{0}} (h : β < lam) :
    (limLevel lam f).proj n x β = ⟨(f β h).pkg, x.1 β h⟩ :=
  dite_eq_left h

/-! ### The recursion -/

/-- The row `α` of the free array over the level-`0` data `A`. -/
def level (A : AtomicData.{w}) (α : Ordinal.{0}) : Level.{w} α :=
  Ordinal.limitRecOn α (zeroLevel A) (fun _ L ↦ succLevel L) (fun lam _ f ↦ limLevel lam f)

/-- Unfolding the recursion at row `0`. -/
theorem level_zero (A : AtomicData.{w}) : level A 0 = zeroLevel A :=
  Ordinal.limitRecOn_zero ..

/-- Unfolding the recursion at a successor row. -/
theorem level_add_one (A : AtomicData.{w}) (α : Ordinal.{0}) :
    level A (α + 1) = succLevel (level A α) :=
  Ordinal.limitRecOn_add_one ..

/-- Unfolding the recursion at a limit row. -/
theorem level_limit (A : AtomicData.{w}) {lam : Ordinal.{0}} (h : IsSuccLimit lam) :
    level A lam = limLevel lam (fun β _ ↦ level A β) :=
  Ordinal.limitRecOn_limit _ _ _ _ h

/-! ### Transport along equalities of levels -/

namespace Level

/-- The transport of a column along an equality of levels. -/
private theorem Ψ_congr {α : Ordinal.{0}} {L L' : Level.{w} α} (e : L = L') (n : ℕ) :
    L.Ψ n = L'.Ψ n :=
  congrArg (fun K : Level.{w} α ↦ K.Ψ n) e

/-- The projection record is invariant under transport along an equality of levels. -/
private theorem proj_cast {α : Ordinal.{0}} {L L' : Level.{w} α} (e : L = L') (n : ℕ) (x : L.Ψ n)
    (β : Ordinal.{0}) : L.proj n x β = L'.proj n (cast (Ψ_congr e n) x) β := by
  subst e
  rfl

/-- The horizontal maps commute with transport along an equality of levels. -/
private theorem H_cast {α : Ordinal.{0}} {L L' : Level.{w} α} (e : L = L') (n m : ℕ)
    (j : Fin m ↪ Fin n) (x : L.Ψ n) :
    cast (Ψ_congr e m) (L.H n m j x) = L'.H n m j (cast (Ψ_congr e n) x) := by
  subst e
  rfl

/-- The projection record of a level at its own row is the element itself. -/
theorem proj_self {α : Ordinal.{0}} (L : Level.{w} α) (n : ℕ) (x : L.Ψ n) :
    L.proj n x α = ⟨L.pkg, x⟩ :=
  L.proj_of_le n x α le_rfl

end Level

/-- Reading a value out of a dependent pair whose package is known. -/
private theorem cast_snd_eq_iff {n : ℕ} {q : Pkg.{w}} (s : Σ p : Pkg.{w}, p.1 n) (e : s.1 = q)
    (y : q.1 n) : cast (congrArg (fun p : Pkg.{w} ↦ p.1 n) e) s.2 = y ↔ s = ⟨q, y⟩ := by
  obtain ⟨p, v⟩ := s
  subst e
  simp

/-! ### The array -/

variable (A : AtomicData.{w})

/-- The column `Ψ^n_α` of the free array (Definition 2.1). -/
abbrev Ψ (α : Ordinal.{0}) (n : ℕ) : Type (w + 1) := (level A α).Ψ n

variable {A}

/-- The horizontal projection `H^n_α(φ, j)` for `j : Fin m ↪ Fin n` (Definition 2.11). -/
abbrev H {α : Ordinal.{0}} {n m : ℕ} (j : Fin m ↪ Fin n) (φ : Ψ A α n) : Ψ A α m :=
  (level A α).H n m j φ

/-- The recorded package of every projection is the package of the target row. -/
private theorem proj_fst (α : Ordinal.{0}) (n : ℕ) (x : Ψ A α n) (β : Ordinal.{0}) (hβ : β ≤ α) :
    ((level A α).proj n x β).1 = (level A β).pkg := by
  rcases hβ.eq_or_lt with rfl | hlt
  · rw [Level.proj_self]
  revert x
  induction α using Ordinal.limitRecOn with
  | zero => simp at hlt
  | add_one α ih =>
    have hβα : β ≤ α := lt_add_one_iff.1 hlt
    -- `Ψ A (α + 1) n` is the abbreviation `(level A (α + 1)).Ψ n`; it is restated in that form so
    -- that `level_add_one` can rewrite `level` in the binder type as well.
    change ∀ x : (level A (α + 1)).Ψ n, _
    rw [level_add_one]
    intro x
    rw [succLevel_proj_of_le _ x hβα]
    rcases hβα.eq_or_lt with rfl | h
    · rw [Level.proj_self]
    · exact ih h.le h x.1
  | limit lam hlam _ =>
    -- As above, restated so that `level_limit` rewrites `level` in the binder type.
    change ∀ x : (level A lam).Ψ n, _
    rw [level_limit A hlam]
    intro x
    rw [limLevel_proj_of_lt _ _ x hlt]

/-- The vertical projection `V_{β,α} : Ψ^n_α → Ψ^n_β` for `β ≤ α` (Definition 2.6). -/
def V {α β : Ordinal.{0}} (h : β ≤ α) {n : ℕ} (x : Ψ A α n) : Ψ A β n :=
  cast (congrArg (fun p : Pkg.{w} ↦ p.1 n) (proj_fst α n x β h)) ((level A α).proj n x β).2

/-- Characterization of `V` through the projection record. -/
theorem V_eq_iff {α β : Ordinal.{0}} (h : β ≤ α) {n : ℕ} (x : Ψ A α n) (y : Ψ A β n) :
    V h x = y ↔ (level A α).proj n x β = ⟨(level A β).pkg, y⟩ :=
  cast_snd_eq_iff (q := (level A β).pkg) _ (proj_fst α n x β h) y

/-- The projection record at `β ≤ α` is the value of `V`. -/
private theorem proj_eq_V {α β : Ordinal.{0}} (h : β ≤ α) {n : ℕ} (x : Ψ A α n) :
    (level A α).proj n x β = ⟨(level A β).pkg, V h x⟩ :=
  (V_eq_iff h x _).1 rfl

/-- `V_{α,α}` is the identity (Definition 2.6(1)). -/
@[simp] theorem V_self {α : Ordinal.{0}} (h : α ≤ α) {n : ℕ} (x : Ψ A α n) : V h x = x :=
  (V_eq_iff h x x).2 (Level.proj_self _ n x)

/-! ### Unfolding the rows -/

variable (A) in
/-- Row `0` is the level-`0` data. -/
def zeroEquiv (n : ℕ) : Ψ A 0 n ≃ A.Ψ0 n :=
  Equiv.cast (Level.Ψ_congr (level_zero A) n)

variable (A) in
/-- A successor row is a pair `(φ', E)` (Definition 2.1(2)). -/
def succEquiv (α : Ordinal.{0}) (n : ℕ) : Ψ A (α + 1) n ≃ succΨ (level A α) n :=
  Equiv.cast (Level.Ψ_congr (level_add_one A α) n)

variable (A) in
/-- A limit row is the type of threads through the lower rows (Definition 2.1(3)). -/
def limEquiv {lam : Ordinal.{0}} (hlam : IsSuccLimit lam) (n : ℕ) :
    Ψ A lam n ≃ Thread lam (fun β _ ↦ level A β) n :=
  Equiv.cast (Level.Ψ_congr (level_limit A hlam) n)

/-- The extension set `E(φ) ⊆ Ψ^{n+1}_α` of `φ ∈ Ψ^n_{α+1}` (Definition 2.4). -/
def E {α : Ordinal.{0}} {n : ℕ} (φ : Ψ A (α + 1) n) : Set (Ψ A α (n + 1)) :=
  (succEquiv A α n φ).2.1

/-- Extension sets are nonempty (Definition 2.1(2)). -/
theorem E_nonempty {α : Ordinal.{0}} {n : ℕ} (φ : Ψ A (α + 1) n) : (E φ).Nonempty :=
  (succEquiv A α n φ).2.2

/-- At a successor row, the projection record to `β ≤ α` is read off the first
component. -/
private theorem proj_succ {α β : Ordinal.{0}} (hβ : β ≤ α) {n : ℕ} (φ : Ψ A (α + 1) n) :
    (level A (α + 1)).proj n φ β = (level A α).proj n (succEquiv A α n φ).1 β := by
  rw [Level.proj_cast (level_add_one A α)]
  exact succLevel_proj_of_le _ _ hβ

/-- At a limit row, the projection record to `β < λ` is the `β`-th entry. -/
private theorem proj_limit {lam β : Ordinal.{0}} (hlam : IsSuccLimit lam) (hβ : β < lam)
    {n : ℕ} (φ : Ψ A lam n) :
    (level A lam).proj n φ β = ⟨(level A β).pkg, (limEquiv A hlam n φ).1 β hβ⟩ := by
  rw [Level.proj_cast (level_limit A hlam)]
  exact limLevel_proj_of_lt _ _ _ hβ

/-- `V_{α,α+1}(φ)` is the first component `φ'` (Definition 2.6(2)). -/
theorem V_succ_eq_fst {α : Ordinal.{0}} {n : ℕ} (φ : Ψ A (α + 1) n) :
    V (lt_add_one α).le φ = (succEquiv A α n φ).1 := by
  rw [V_eq_iff, proj_succ le_rfl, Level.proj_self]

/-- `E(φ)` is the second component (Definition 2.4). -/
theorem E_eq_snd {α : Ordinal.{0}} {n : ℕ} (φ : Ψ A (α + 1) n) :
    E φ = (succEquiv A α n φ).2.1 :=
  rfl

/-- At a limit row, `V_{β,λ}(φ)` is the `β`-th entry of the thread (Definition 2.6(3)). -/
theorem V_limit_eq_entry {lam β : Ordinal.{0}} (hlam : IsSuccLimit lam) (hβ : β < lam)
    {n : ℕ} (φ : Ψ A lam n) : V hβ.le φ = (limEquiv A hlam n φ).1 β hβ := by
  rw [V_eq_iff, proj_limit hlam hβ]

/-- `H^n_0` is restriction of level-`0` data (Definition 2.11(2)). -/
theorem H_zero_eq_restrict {n m : ℕ} (j : Fin m ↪ Fin n) (φ : Ψ A 0 n) :
    zeroEquiv A m (H j φ) = A.H0 n m j (zeroEquiv A n φ) :=
  (Level.H_cast (level_zero A) n m j φ)

/-- At a successor row, `H` is the successor-step horizontal map (Definition 2.11(3)). -/
theorem succEquiv_H {α : Ordinal.{0}} {n m : ℕ} (j : Fin m ↪ Fin n) (φ : Ψ A (α + 1) n) :
    succEquiv A α m (H j φ) = succH (level A α) n m j (succEquiv A α n φ) :=
  Level.H_cast (level_add_one A α) n m j φ

/-- At a limit row, `H` is the thread horizontal map (Definition 2.11(4)). -/
theorem limEquiv_H {lam : Ordinal.{0}} (hlam : IsSuccLimit lam) {n m : ℕ} (j : Fin m ↪ Fin n)
    (φ : Ψ A lam n) :
    limEquiv A hlam m (H j φ) = threadH lam (fun β _ ↦ level A β) n m j (limEquiv A hlam n φ) :=
  Level.H_cast (level_limit A hlam) n m j φ

/-- Proposition 2.15: `V_{β,α}(H^n_α(φ, j)) = H^n_β(V_{β,α}(φ), j)`. -/
theorem V_H_comm {α β : Ordinal.{0}} (h : β ≤ α) {n m : ℕ} (j : Fin m ↪ Fin n)
    (φ : Ψ A α n) : V h (H j φ) = H j (V h φ) := by
  rw [V_eq_iff, H, (level A α).proj_H, proj_eq_V h φ]

/-- Definition 2.11(3), second clause: `E(H^n_{α+1}(φ, j))` is the image of
`E(φ) × {j' extending j with the new coordinate sent outside range j}` under `H^{n+1}_α`. -/
theorem E_H {α : Ordinal.{0}} {n m : ℕ} (j : Fin m ↪ Fin n) (φ : Ψ A (α + 1) n) :
    E (H j φ) = Set.image2 (fun ψ j' ↦ H j' ψ) (E φ) (extSet j) := by
  rw [E, E, succEquiv_H, succH_snd]

/-! ### Building and comparing successor and limit elements -/

/-- The successor-row element `(φ', E')` with first component `φ'` and extension set `E'`
(Definition 2.1(2)). -/
def mkSucc {α : Ordinal.{0}} {n : ℕ} (φ' : Ψ A α n) (E' : Set (Ψ A α (n + 1)))
    (hE : E'.Nonempty) : Ψ A (α + 1) n :=
  (succEquiv A α n).symm (φ', ⟨E', hE⟩)

/-- `V_{α,α+1}` of `mkSucc φ' E' hE` is `φ'`. -/
@[simp] theorem V_mkSucc {α : Ordinal.{0}} {n : ℕ} (φ' : Ψ A α n) (E' : Set (Ψ A α (n + 1)))
    (hE : E'.Nonempty) : V (lt_add_one α).le (mkSucc φ' E' hE) = φ' := by
  rw [V_succ_eq_fst, mkSucc, Equiv.apply_symm_apply]

/-- The extension set of `mkSucc φ' E' hE` is `E'`. -/
@[simp] theorem E_mkSucc {α : Ordinal.{0}} {n : ℕ} (φ' : Ψ A α n) (E' : Set (Ψ A α (n + 1)))
    (hE : E'.Nonempty) : E (mkSucc φ' E' hE) = E' := by
  rw [E_eq_snd, mkSucc, Equiv.apply_symm_apply]

/-- `H` on `mkSucc`, by Definition 2.11(3). -/
@[simp] theorem H_mkSucc {α : Ordinal.{0}} {n m : ℕ} (j : Fin m ↪ Fin n) (φ' : Ψ A α n)
    (E' : Set (Ψ A α (n + 1))) (hE : E'.Nonempty) :
    H j (mkSucc φ' E' hE) =
      mkSucc (H j φ') (Set.image2 (fun ψ j' ↦ H j' ψ) E' (extSet j))
        (hE.image2 ⟨_, extLast_mem j⟩) := by
  apply (succEquiv A α m).injective
  rw [succEquiv_H, mkSucc, mkSucc, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  exact Prod.ext (succH_fst ..) (Subtype.ext (succH_snd ..))

/-- A successor-row element is determined by `V_{α,α+1}` and its extension set. -/
theorem Ψ.ext_succ {α : Ordinal.{0}} {n : ℕ} {φ ψ : Ψ A (α + 1) n}
    (hV : V (lt_add_one α).le φ = V (lt_add_one α).le ψ) (hE : E φ = E ψ) : φ = ψ := by
  apply (succEquiv A α n).injective
  rw [V_succ_eq_fst, V_succ_eq_fst] at hV
  exact Prod.ext hV (Subtype.ext hE)

/-- A limit-row element is determined by its vertical projections to the lower rows. -/
theorem Ψ.ext_limit {lam : Ordinal.{0}} (hlam : IsSuccLimit lam) {n : ℕ} {φ ψ : Ψ A lam n}
    (h : ∀ β (hβ : β < lam), V hβ.le φ = V hβ.le ψ) : φ = ψ := by
  apply (limEquiv A hlam n).injective
  refine Subtype.ext (funext fun β ↦ funext fun hβ ↦ ?_)
  rw [← V_limit_eq_entry hlam hβ φ, ← V_limit_eq_entry hlam hβ ψ, h β hβ]

/-! ### Composition of vertical projections -/

/-- Definition 2.6(4): `V_{β,α+1} = V_{β,α} ∘ V_{α,α+1}` for `β ≤ α`. -/
theorem V_succ_of_le {α β : Ordinal.{0}} (hβ : β ≤ α) {n : ℕ} (φ : Ψ A (α + 1) n) :
    V (hβ.trans (lt_add_one α).le) φ = V hβ (V (lt_add_one α).le φ) := by
  rw [V_eq_iff, proj_succ hβ, V_succ_eq_fst, proj_eq_V hβ]

/-- At a successor row, the projection record to `β ≤ α` factors through
`V_{α,α+1}`. -/
private theorem proj_succ' {α β : Ordinal.{0}} (hβ : β ≤ α) {n : ℕ} (φ : Ψ A (α + 1) n) :
    (level A (α + 1)).proj n φ β = (level A α).proj n (V (lt_add_one α).le φ) β := by
  rw [proj_succ hβ, V_succ_eq_fst]

/-- Every thread is coherent between all pairs of its entries. -/
private theorem Thread.proj_entry {lam : Ordinal.{0}} {n : ℕ}
    (t : Thread lam (fun β _ ↦ level A β) n) (β : Ordinal.{0}) (hβ : β < lam)
    (δ : Ordinal.{0}) (hδ : δ ≤ β) :
    (level A β).proj n (t.1 β hβ) δ = ⟨(level A δ).pkg, t.1 δ (hδ.trans_lt hβ)⟩ := by
  rcases hδ.eq_or_lt with rfl | hlt
  · exact Level.proj_self _ n _
  induction β using Ordinal.limitRecOn with
  | zero => simp at hlt
  | add_one β ih =>
    have hδβ : δ ≤ β := lt_add_one_iff.1 hlt
    have hβ' : β < lam := (lt_add_one β).trans hβ
    rw [proj_succ' hδβ]
    have ha : V (lt_add_one β).le (t.1 (β + 1) hβ) = t.1 β hβ' :=
      (V_eq_iff _ _ _).2 (t.2.1 β hβ)
    rw [ha]
    rcases hδβ.eq_or_lt with rfl | h
    · exact Level.proj_self _ n _
    · exact ih hβ' hδβ h
  | limit β hβl _ => exact t.2.2 β hβ hβl δ hlt

/-- The projection record commutes with vertical projection. -/
private theorem proj_V {α β : Ordinal.{0}} (hβ : β ≤ α) {n : ℕ} (x : Ψ A α n) (δ : Ordinal.{0})
    (hδ : δ ≤ β) : (level A β).proj n (V hβ x) δ = (level A α).proj n x δ := by
  rcases hβ.eq_or_lt with rfl | hlt
  · rw [V_self]
  induction α using Ordinal.limitRecOn generalizing β with
  | zero => simp at hlt
  | add_one α ih =>
    have hβα : β ≤ α := lt_add_one_iff.1 hlt
    rw [V_succ_of_le hβα, proj_succ' (hδ.trans hβα)]
    rcases hβα.eq_or_lt with rfl | h
    · rw [V_self]
    · exact ih hβα _ hδ h
  | limit lam hlam _ =>
    rw [V_limit_eq_entry hlam hlt, proj_limit hlam (hδ.trans_lt hlt)]
    exact Thread.proj_entry _ β hlt δ hδ

/-- Remark 2.8: `V_{δ,α} = V_{δ,β} ∘ V_{β,α}` for `δ ≤ β ≤ α`. -/
@[simp] theorem V_comp {α β δ : Ordinal.{0}} (hδ : δ ≤ β) (hβ : β ≤ α) {n : ℕ} (x : Ψ A α n) :
    V hδ (V hβ x) = V (hδ.trans hβ) x := by
  rw [V_eq_iff, proj_V hβ x δ hδ, proj_eq_V]

/-! ### Fullness -/

/-- Every pair `(φ', E)` with `E` nonempty is realized at the successor row. -/
theorem exists_succ_of_V_E {α : Ordinal.{0}} {n : ℕ} (φ' : Ψ A α n)
    (E' : Set (Ψ A α (n + 1))) (hE : E'.Nonempty) :
    ∃ φ : Ψ A (α + 1) n, V (lt_add_one α).le φ = φ' ∧ E φ = E' :=
  ⟨mkSucc φ' E' hE, V_mkSucc .., E_mkSucc ..⟩

/-- Every family satisfying Definition 2.1(3)(a),(b) is realized at the limit row. -/
theorem exists_limit_of_thread {lam : Ordinal.{0}} (hlam : IsSuccLimit lam) {n : ℕ}
    (ψ : ∀ β < lam, Ψ A β n)
    (ha : ∀ β (h : β + 1 < lam),
      V (lt_add_one β).le (ψ (β + 1) h) = ψ β ((lt_add_one β).trans h))
    (hb : ∀ β (h : β < lam), IsSuccLimit β → ∀ δ (hδ : δ < β),
      V hδ.le (ψ β h) = ψ δ (hδ.trans h)) :
    ∃ φ : Ψ A lam n, ∀ β (h : β < lam), V h.le φ = ψ β h := by
  let t : Thread lam (fun β _ ↦ level A β) n :=
    ⟨ψ, fun β h ↦ (V_eq_iff _ _ _).1 (ha β h),
      fun β h hβ δ hδ ↦ (V_eq_iff _ _ _).1 (hb β h hβ δ hδ)⟩
  refine ⟨(limEquiv A hlam n).symm t, fun β h ↦ ?_⟩
  rw [V_limit_eq_entry hlam h, Equiv.apply_symm_apply]

/-! ### Horizontal identities -/

/-- Definition 2.11(4): at a limit row, `H` acts entrywise on threads. -/
theorem H_limit_entry {lam β : Ordinal.{0}} (hlam : IsSuccLimit lam) (hβ : β < lam)
    {n m : ℕ} (j : Fin m ↪ Fin n) (φ : Ψ A lam n) :
    (limEquiv A hlam m (H j φ)).1 β hβ = H j ((limEquiv A hlam n φ).1 β hβ) := by
  rw [limEquiv_H, threadH_coe]

/-- Remark 2.13: `H^n_α(φ, id) = φ`. -/
@[simp] theorem H_id {α : Ordinal.{0}} {n : ℕ} (φ : Ψ A α n) :
    H (Function.Embedding.refl (Fin n)) φ = φ := by
  induction α using Ordinal.limitRecOn generalizing n with
  | zero =>
    apply (zeroEquiv A n).injective
    rw [H_zero_eq_restrict, A.H0_id]
  | add_one α ih =>
    apply (succEquiv A α n).injective
    rw [succEquiv_H]
    generalize succEquiv A α n φ = x
    refine Prod.ext ((succH_fst ..).trans (ih x.1)) (Subtype.ext ?_)
    rw [succH_snd, extSet_refl, Set.image2_singleton_right]
    conv_rhs => rw [← Set.image_id x.2.1]
    exact Set.image_congr fun ψ _ ↦ ih ψ
  | limit lam hlam ih =>
    apply (limEquiv A hlam n).injective
    rw [limEquiv_H]
    refine Subtype.ext (funext fun β ↦ funext fun hβ ↦ ?_)
    rw [threadH_coe]
    exact ih β hβ _

/-- Remark 2.14(2): `H^m_α(H^n_α(φ, j), k) = H^n_α(φ, j ∘ k)`. -/
@[simp] theorem H_comp {α : Ordinal.{0}} {n m l : ℕ} (j : Fin m ↪ Fin n) (k : Fin l ↪ Fin m)
    (φ : Ψ A α n) : H k (H j φ) = H (k.trans j) φ := by
  induction α using Ordinal.limitRecOn generalizing n m l with
  | zero =>
    apply (zeroEquiv A l).injective
    rw [H_zero_eq_restrict, H_zero_eq_restrict, H_zero_eq_restrict, A.H0_comp]
  | add_one α ih =>
    apply (succEquiv A α l).injective
    rw [succEquiv_H, succEquiv_H, succEquiv_H]
    generalize succEquiv A α n φ = x
    refine Prod.ext ?_ (Subtype.ext ?_)
    · rw [succH_fst, succH_fst, succH_fst]
      exact ih j k x.1
    rw [succH_snd, succH_snd, succH_snd]
    ext z
    constructor
    · rintro ⟨_, ⟨ψ, hψ, j', hj', rfl⟩, k', hk', rfl⟩
      exact ⟨ψ, hψ, k'.trans j', trans_mem_extSet hj' hk', (ih j' k' ψ).symm⟩
    · rintro ⟨ψ, hψ, i, hi, rfl⟩
      obtain ⟨j', hj', k', hk', rfl⟩ := exists_trans_of_mem_extSet hi
      exact ⟨_, ⟨ψ, hψ, j', hj', rfl⟩, k', hk', ih j' k' ψ⟩
  | limit lam hlam ih =>
    apply (limEquiv A hlam l).injective
    rw [limEquiv_H, limEquiv_H, limEquiv_H]
    refine Subtype.ext (funext fun β ↦ funext fun hβ ↦ ?_)
    simp only [threadH_coe]
    exact ih β hβ _ _ _

/-! ### The concrete level `0` for a relational language -/

section Relational

universe u v

open FirstOrder.Language

variable {L : FirstOrder.Language.{u, v}}

/-- An atomic index is a relation instance `AtomicIdx.rel R f` (not an equality). -/
def IsRelIdx {n : ℕ} : L.AtomicIdx n → Prop
  | .eq _ _ => False
  | .rel _ _ => True

/-- `AtomicIdx.pushforward` sends relation instances to relation instances. -/
theorem IsRelIdx.pushforward {n m : ℕ} {a : L.AtomicIdx m} (ha : IsRelIdx a)
    (f : Fin m → Fin n) : IsRelIdx (a.pushforward f) := by
  cases a with
  | eq => exact ha.elim
  | rel => trivial

variable (L) in
/-- Atomic relation instances `R(x_{f 0}, …, x_{f (l-1)})` on the variables `Fin n`: the
`AtomicIdx.rel` indices of `Scott/AtomicDiagram.lean`. -/
abbrev AtomInst (n : ℕ) : Type (max u v) :=
  {a : L.AtomicIdx n // IsRelIdx a}

/-- Relabel an atomic instance along a map of variables (`AtomicIdx.pushforward`). -/
def AtomInst.map {n m : ℕ} (f : Fin m → Fin n) (a : AtomInst L m) : AtomInst L n :=
  ⟨a.1.pushforward f, a.2.pushforward f⟩

/-- The underlying atomic index of a relabelled instance is its pushforward. -/
@[simp] theorem AtomInst.coe_map {n m : ℕ} (f : Fin m → Fin n) (a : AtomInst L m) :
    (a.map f).1 = a.1.pushforward f :=
  rfl

/-- Relabelling along the identity is the identity. -/
@[simp] theorem AtomInst.map_id {n : ℕ} (a : AtomInst L n) : a.map id = a := by
  obtain ⟨_ | _, h⟩ := a
  · exact h.elim
  · rfl

/-- Relabelling is functorial. -/
theorem AtomInst.map_map {n m l : ℕ} (f : Fin m → Fin n) (g : Fin l → Fin m)
    (a : AtomInst L l) : (a.map g).map f = a.map (f ∘ g) := by
  obtain ⟨_ | _, h⟩ := a
  · exact h.elim
  · rfl

variable (L) in
/-- Level-`0` data for a relational language (Definition 2.1(1)): a complete atomic type on the
`n` distinct variables `Fin n` is a truth value for every relation instance (equalities are
fixed by distinctness and are not stored); `H^n_0(·, j)` restricts along `j`, through
`AtomicIdx.pushforward`. -/
def relAtomic [L.IsRelational] : AtomicData.{max u v} where
  Ψ0 n := ULift.{max u v + 1} (AtomInst L n → Bool)
  H0 _ _ j t := ⟨fun a ↦ t.down (a.map j)⟩
  H0_id _ t := congrArg ULift.up (funext fun a ↦ congrArg t.down (AtomInst.map_id a))
  H0_comp _ _ _ j k t :=
    congrArg ULift.up (funext fun a ↦ congrArg t.down (AtomInst.map_map j k a))

/-- The horizontal restriction of `relAtomic L`, read on an instance. -/
@[simp] theorem relAtomic_H0_down [L.IsRelational] {n m : ℕ} (j : Fin m ↪ Fin n)
    (t : (relAtomic L).Ψ0 n) (a : AtomInst L m) :
    ((relAtomic L).H0 n m j t).down a = t.down (a.map j) :=
  rfl

/-- Definition 2.11(2) for the relational level `0`: `H^n_0(φ, j)` assigns to an instance on
`Fin m` the value `φ` assigns to its relabelling along `j`. -/
theorem H_zero_rel [L.IsRelational] {n m : ℕ} (j : Fin m ↪ Fin n)
    (φ : Ψ (relAtomic L) 0 n) (a : AtomInst L m) :
    (zeroEquiv (relAtomic L) m (H j φ)).down a =
      (zeroEquiv (relAtomic L) n φ).down (a.map j) := by
  rw [H_zero_eq_restrict, relAtomic_H0_down]

end Relational

end InfinitaryLogic.ScottProcess.FreeArray

end
