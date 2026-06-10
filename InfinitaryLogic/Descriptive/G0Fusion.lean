/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Descriptive.GSGraph
import InfinitaryLogic.Descriptive.G0Dichotomy
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Fusion for the `G₀`-dichotomy: level objects and edge bookkeeping

Infrastructure for the fusion recursion of the classical `G₀`-dichotomy (2C-b sub-block 4;
see `docs/silver-phase2-route.md`), building on the positivity machinery of
`InfinitaryLogic/Descriptive/G0Dichotomy.lean`:

* **Finite-word API**: coercion-tame access lemmas for `Fin.snoc`
  (`snoc_apply_of_lt`/`snoc_apply_last`), level restrictions `restr n x` of branches with
  `restr_succ`, and canonical-word vertices `cvert m n`.
* **Edge bookkeeping**: `LvlEdgeAt m n u v` is the oriented level-`n` trace of the
  `GSGraph canonicalS` edge created by `canonicalWord m`. The three structural lemmas:
  `lvlEdgeAt_fresh` (the cross pair at the level just past the word), `lvlEdgeAt_succ_elim`
  (every level-`(n+1)` edge is the fresh cross pair or the `snoc` of a level-`n` edge),
  and `lvlEdgeAt_restr` (restrictions of a `GSGraph` edge pair are level edges), with
  `gsGraph_oriented` translating `GSGraph` edges into oriented prepended form.
* **Witness words**: `prepw c w` prepends a finite `ℕ`-word to a Baire-space point;
  `WitSet g u v c` is the (analytic) set of assignments whose `(u, v)`-value pair is
  `g`-witnessed through the cylinder of `c`, with `witSet_cover` feeding the positivity
  pigeonhole (`exists_not_smallFam_inter`) to extend witness words one coordinate at a
  time (`exists_extend_witnesses`, a fold over the finitely many tracked edges).
* **Vertex shrinking**: `exists_shrink` restricts a positive analytic family so that all
  members are uniformly `(1/2)^n`-close at every vertex, by the pigeonhole over a countable
  cover of `α` by small balls.

The fusion recursion itself (the `FusionStage` tower and the limit extraction) is built on
top of these in the sequel.
-/

open Set Function MeasureTheory

namespace G0Fusion

/-! ### Finite-word API -/

theorem snoc_apply_mk_of_lt {n : ℕ} (u : Fin n → Bool) (i : Bool) {j : ℕ} (hj : j < n)
    (hj' : j < n + 1) : (Fin.snoc u i : Fin (n + 1) → Bool) ⟨j, hj'⟩ = u ⟨j, hj⟩ := by
  have h : (⟨j, hj'⟩ : Fin (n + 1)) = Fin.castSucc ⟨j, hj⟩ := by
    ext
    simp
  rw [h, Fin.snoc_castSucc]

/-- Coercion-tame access below the last position. -/
theorem snoc_apply_lt {n : ℕ} (u : Fin n → Bool) (i : Bool) (j : Fin (n + 1))
    (hj : (j : ℕ) < n) : (Fin.snoc u i : Fin (n + 1) → Bool) j = u ⟨j, hj⟩ := by
  rcases j with ⟨j, hj'⟩
  exact snoc_apply_mk_of_lt u i hj hj'

/-- Coercion-tame access at the last position. -/
theorem snoc_apply_eq {n : ℕ} (u : Fin n → Bool) (i : Bool) (j : Fin (n + 1))
    (hj : (j : ℕ) = n) : (Fin.snoc u i : Fin (n + 1) → Bool) j = i := by
  have h : j = Fin.last n := Fin.ext (by simpa using hj)
  rw [h, Fin.snoc_last]

/-- The level-`n` restriction of an infinite branch. -/
def restr (n : ℕ) (x : ℕ → Bool) : Fin n → Bool := fun j => x j

theorem restr_succ (n : ℕ) (x : ℕ → Bool) :
    restr (n + 1) x = Fin.snoc (restr n x) (x n) := by
  funext j
  rcases lt_or_ge (j : ℕ) n with hj | hj
  · rw [snoc_apply_lt _ _ j hj]
    rfl
  · have hjn : (j : ℕ) = n := by
      have := j.isLt
      omega
    rw [snoc_apply_eq _ _ j hjn]
    show x (j : ℕ) = x n
    rw [hjn]

theorem restr_eq_restr_of_mem_cylinder {x y : ℕ → Bool} {N : ℕ}
    (h : y ∈ PiNat.cylinder x N) : restr N y = restr N x :=
  funext fun j => PiNat.mem_cylinder_iff.mp h j j.2

/-- The canonical word `m` as a level-`n` vertex (positions beyond the word read `false`). -/
def cvert (m n : ℕ) : Fin n → Bool := fun j => (canonicalWord m).getD j false

/-! ### Edge bookkeeping -/

/-- The oriented level-`n` trace of the `GSGraph canonicalS` edge created by the canonical
word `m`: both vertices extend the word, the cross position carries `false` on the left and
`true` on the right, and the tails agree. -/
def LvlEdgeAt (m n : ℕ) (u v : Fin n → Bool) : Prop :=
  canonicalLen m + 1 ≤ n ∧
  (∀ j : Fin n, (j : ℕ) < canonicalLen m →
    u j = (canonicalWord m).getD j false ∧ v j = (canonicalWord m).getD j false) ∧
  (∀ j : Fin n, (j : ℕ) = canonicalLen m → u j = false ∧ v j = true) ∧
  (∀ j : Fin n, canonicalLen m < (j : ℕ) → u j = v j)

/-- The fresh cross pair at the level just past the canonical word. -/
theorem lvlEdgeAt_fresh (m n : ℕ) (h : canonicalLen m = n) :
    LvlEdgeAt m (n + 1) (Fin.snoc (cvert m n) false) (Fin.snoc (cvert m n) true) := by
  refine ⟨by omega, ?_, ?_, ?_⟩
  · intro j hjm
    have hjn : (j : ℕ) < n := by omega
    rw [snoc_apply_lt _ _ j hjn, snoc_apply_lt _ _ j hjn]
    exact ⟨rfl, rfl⟩
  · intro j hjm
    have hjn : (j : ℕ) = n := by omega
    rw [snoc_apply_eq _ _ j hjn, snoc_apply_eq _ _ j hjn]
    exact ⟨rfl, rfl⟩
  · intro j hjm
    have := j.isLt
    exact absurd hjm (by omega)

/-- Every level-`(n + 1)` edge is the fresh cross pair (when the word has length exactly
`n`) or the `snoc` of a level-`n` edge by a common last bit. -/
theorem lvlEdgeAt_succ_elim {m n : ℕ} {u v : Fin (n + 1) → Bool}
    (h : LvlEdgeAt m (n + 1) u v) :
    (canonicalLen m = n ∧ u = Fin.snoc (cvert m n) false ∧ v = Fin.snoc (cvert m n) true) ∨
    (canonicalLen m + 1 ≤ n ∧ u (Fin.last n) = v (Fin.last n) ∧
      LvlEdgeAt m n (Fin.init u) (Fin.init v)) := by
  obtain ⟨hle, hword, hcross, htail⟩ := h
  have hLn : canonicalLen m ≤ n := by omega
  rcases eq_or_lt_of_le hLn with heq | hlt
  · left
    have hu : ∀ b : Bool, ∀ w : Fin (n + 1) → Bool,
        (∀ j : Fin (n + 1), (j : ℕ) < canonicalLen m →
          w j = (canonicalWord m).getD j false) →
        (∀ j : Fin (n + 1), (j : ℕ) = canonicalLen m → w j = b) →
        w = Fin.snoc (cvert m n) b := by
      intro b w hw hwc
      funext j
      rcases lt_or_ge (j : ℕ) n with hjn | hjn
      · rw [snoc_apply_lt _ _ j hjn]
        exact hw j (by omega)
      · have hjeq : (j : ℕ) = n := by
          have := j.isLt
          omega
        rw [snoc_apply_eq _ _ j hjeq]
        exact hwc j (by omega)
    exact ⟨heq, hu false u (fun j hj => (hword j hj).1) (fun j hj => (hcross j hj).1),
      hu true v (fun j hj => (hword j hj).2) (fun j hj => (hcross j hj).2)⟩
  · right
    refine ⟨by omega, htail (Fin.last n) (by simp [Fin.val_last]; omega), by omega, ?_, ?_, ?_⟩
    · intro j hjm
      exact hword (Fin.castSucc j) (by simpa using hjm)
    · intro j hjm
      exact hcross (Fin.castSucc j) (by simpa using hjm)
    · intro j hjm
      exact htail (Fin.castSucc j) (by simpa using hjm)

/-- The level restrictions of an oriented `GSGraph` edge pair are level edges. -/
theorem lvlEdgeAt_restr {m n : ℕ} (h : canonicalLen m + 1 ≤ n) (x : ℕ → Bool) :
    LvlEdgeAt m n
      (restr n (prependWord (canonicalWord m ++ [false]) x))
      (restr n (prependWord (canonicalWord m ++ [true]) x)) := by
  have hlen : ∀ b : Bool, (canonicalWord m ++ [b]).length = canonicalLen m + 1 := by
    intro b
    simp [length_canonicalWord]
  refine ⟨h, ?_, ?_, ?_⟩
  · intro j hjm
    constructor <;>
    · show prependWord _ x (j : ℕ) = _
      rw [prependWord_apply_of_lt (by rw [hlen]; omega),
        List.getD_append _ _ _ _ (by rw [length_canonicalWord]; exact hjm)]
  · intro j hjm
    constructor <;>
    · show prependWord _ x (j : ℕ) = _
      rw [prependWord_apply_of_lt (by rw [hlen]; omega), hjm,
        List.getD_append_right _ _ _ _ (by rw [length_canonicalWord])]
      simp [length_canonicalWord]
  · intro j hjm
    show prependWord _ x (j : ℕ) = prependWord _ x (j : ℕ)
    rw [prependWord_apply_of_le (by rw [hlen]; omega),
      prependWord_apply_of_le (by rw [hlen]; omega), hlen, hlen]

/-- Every `GSGraph canonicalS` edge comes from a canonical word in one of the two
orientations. -/
theorem gsGraph_oriented {y z : ℕ → Bool} (h : GSGraph canonicalS y z) :
    ∃ m, ∃ x : ℕ → Bool,
      (y = prependWord (canonicalWord m ++ [false]) x ∧
        z = prependWord (canonicalWord m ++ [true]) x) ∨
      (y = prependWord (canonicalWord m ++ [true]) x ∧
        z = prependWord (canonicalWord m ++ [false]) x) := by
  obtain ⟨s, hs, i, x, hy, hz⟩ := h
  obtain ⟨m, rfl⟩ := hs
  cases i
  · exact ⟨m, x, Or.inl ⟨hy, by simpa using hz⟩⟩
  · exact ⟨m, x, Or.inr ⟨hy, by simpa using hz⟩⟩

/-! ### Witness words in Baire space -/

/-- Prepend a finite `ℕ`-word to a point of Baire space. -/
def prepw (c : List ℕ) (w : ℕ → ℕ) : ℕ → ℕ := fun j =>
  if j < c.length then c.getD j 0 else w (j - c.length)

theorem prepw_apply_of_lt {c : List ℕ} {j : ℕ} (h : j < c.length) (w : ℕ → ℕ) :
    prepw c w j = c.getD j 0 := if_pos h

theorem prepw_apply_of_le {c : List ℕ} {j : ℕ} (h : c.length ≤ j) (w : ℕ → ℕ) :
    prepw c w j = w (j - c.length) := if_neg (not_lt.mpr h)

theorem prepw_nil (w : ℕ → ℕ) : prepw [] w = w :=
  funext fun j => by simp [prepw]

theorem continuous_prepw (c : List ℕ) : Continuous (prepw c) := by
  refine continuous_pi fun j => ?_
  rcases lt_or_ge j c.length with hj | hj
  · have h : (fun w : ℕ → ℕ => prepw c w j) = fun _ => c.getD j 0 :=
      funext fun w => prepw_apply_of_lt hj w
    rw [h]
    exact continuous_const
  · have h : (fun w : ℕ → ℕ => prepw c w j) = fun w => w (j - c.length) :=
      funext fun w => prepw_apply_of_le hj w
    rw [h]
    exact continuous_apply _

/-- Splitting off the head of the tail extends the word. -/
theorem prepw_append_head (c : List ℕ) (w : ℕ → ℕ) :
    prepw (c ++ [w 0]) (fun j => w (j + 1)) = prepw c w := by
  funext j
  rcases lt_trichotomy j c.length with h | h | h
  · rw [prepw_apply_of_lt (by simp; omega), prepw_apply_of_lt h,
      List.getD_append _ _ _ _ h]
  · subst h
    rw [prepw_apply_of_lt (by simp), prepw_apply_of_le le_rfl,
      List.getD_append_right _ _ _ _ le_rfl]
    simp
  · rw [prepw_apply_of_le (by simp; omega), prepw_apply_of_le (by omega)]
    simp only [List.length_append, List.length_singleton]
    congr 1
    omega

theorem getD_of_prefix {c d : List ℕ} (h : c <+: d) {j : ℕ} (hj : j < c.length) :
    d.getD j 0 = c.getD j 0 := by
  obtain ⟨t, rfl⟩ := h
  exact List.getD_append _ _ _ _ hj

/-! ### Witness-constraint sets -/

section WitSet

variable {α : Type*} [TopologicalSpace α] [PolishSpace α]
variable {ι : Type*} [Countable ι]

/-- The set of assignments whose `(u, v)`-value pair is `g`-witnessed through the cylinder
of the word `c`. -/
def WitSet (g : (ℕ → ℕ) → α × α) (u v : ι) (c : List ℕ) : Set (ι → α) :=
  {φ | ∃ w : ℕ → ℕ, g (prepw c w) = (φ u, φ v)}

theorem analyticSet_witSet {g : (ℕ → ℕ) → α × α} (hg : Continuous g) (u v : ι)
    (c : List ℕ) : AnalyticSet (WitSet g u v c) := by
  have hclosed : IsClosed {p : (ι → α) × (ℕ → ℕ) | g (prepw c p.2) = (p.1 u, p.1 v)} :=
    isClosed_eq (hg.comp ((continuous_prepw c).comp continuous_snd))
      (((continuous_apply u).comp continuous_fst).prodMk
        ((continuous_apply v).comp continuous_fst))
  have h : WitSet g u v c =
      Prod.fst '' {p : (ι → α) × (ℕ → ℕ) | g (prepw c p.2) = (p.1 u, p.1 v)} := by
    ext φ
    constructor
    · rintro ⟨w, hw⟩
      exact ⟨(φ, w), hw, rfl⟩
    · rintro ⟨⟨φ', w⟩, hw, rfl⟩
      exact ⟨w, hw⟩
  rw [h]
  exact hclosed.analyticSet.image_of_continuous continuous_fst

omit [TopologicalSpace α] [PolishSpace α] [Countable ι] in
/-- Witnessed families are covered by the one-step extensions of the witness word. -/
theorem witSet_cover {g : (ℕ → ℕ) → α × α} {u v : ι} {c : List ℕ} {Φ : Set (ι → α)}
    (hwit : ∀ φ ∈ Φ, φ ∈ WitSet g u v c) :
    Φ ⊆ ⋃ k : ℕ, WitSet g u v (c ++ [k]) := by
  intro φ hφ
  obtain ⟨w, hw⟩ := hwit φ hφ
  refine mem_iUnion.mpr ⟨w 0, ⟨fun j => w (j + 1), ?_⟩⟩
  rw [prepw_append_head]
  exact hw

end WitSet

/-! ### Pigeonhole over countable index types -/

theorem exists_not_smallFam_inter' {α : Type*} [MeasurableSpace α] {G : Set (α × α)}
    {ι : Type*} {Φ : Set (ι → α)} (hΦ : ¬ SmallFam G Φ)
    {κ : Type*} [Countable κ] [Nonempty κ] {Ψ : κ → Set (ι → α)}
    (hcov : Φ ⊆ ⋃ c : κ, Ψ c) :
    ∃ c : κ, ¬ SmallFam G (Φ ∩ Ψ c) := by
  obtain ⟨f, hf⟩ := exists_surjective_nat κ
  have hcov' : Φ ⊆ ⋃ n : ℕ, Ψ (f n) := by
    intro φ hφ
    obtain ⟨c, hc⟩ := mem_iUnion.mp (hcov hφ)
    obtain ⟨n, rfl⟩ := hf c
    exact mem_iUnion.mpr ⟨n, hc⟩
  obtain ⟨n, hn⟩ := exists_not_smallFam_inter hΦ hcov'
  exact ⟨f n, hn⟩

/-! ### Vertex shrinking -/

section Shrink

variable {α : Type*} [MetricSpace α] [SecondCountableTopology α] [CompleteSpace α]
  [MeasurableSpace α] [BorelSpace α]

omit [CompleteSpace α] in
/-- A countable cover of a separable metric space by measurable sets of diameter at most
`(1/2)^n`. -/
theorem exists_smallOpens [Nonempty α] (n : ℕ) :
    ∃ O : ℕ → Set α, (∀ k, MeasurableSet (O k)) ∧ (∀ x : α, ∃ k, x ∈ O k) ∧
      ∀ k, ∀ a ∈ O k, ∀ b ∈ O k, dist a b ≤ (1 / 2) ^ n := by
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense α
  obtain ⟨e, he⟩ := hDc.exists_eq_range hDd.nonempty
  refine ⟨fun k => Metric.ball (e k) ((1 / 2) ^ (n + 2)), fun k =>
    Metric.isOpen_ball.measurableSet, ?_, ?_⟩
  · intro x
    obtain ⟨d, hd, hdD⟩ := Metric.dense_iff.mp hDd x ((1 / 2) ^ (n + 2)) (by positivity)
    rw [he] at hdD
    obtain ⟨k, rfl⟩ := hdD
    refine ⟨k, Metric.mem_ball.mpr ?_⟩
    rw [dist_comm]
    exact Metric.mem_ball.mp hd
  · intro k a ha b hb
    rw [Metric.mem_ball] at ha hb
    calc dist a b ≤ dist a (e k) + dist (e k) b := dist_triangle _ _ _
      _ ≤ (1 / 2) ^ (n + 2) + (1 / 2) ^ (n + 2) := by
          rw [dist_comm (e k) b]
          exact add_le_add ha.le hb.le
      _ ≤ (1 / 2) ^ n := by
          rw [pow_succ, pow_succ]
          nlinarith [pow_pos (by norm_num : (0:ℝ) < 1/2) n]

/-- **Vertex shrinking**: a positive analytic family can be refined to a positive analytic
subfamily whose members are uniformly `(1/2)^n`-close at every vertex. -/
theorem exists_shrink {G : Set (α × α)} {ι : Type*} [Finite ι] [Nonempty α]
    {Φ : Set (ι → α)} (hana : AnalyticSet Φ) (hpos : ¬ SmallFam G Φ) (n : ℕ) :
    ∃ Φ' : Set (ι → α), Φ' ⊆ Φ ∧ AnalyticSet Φ' ∧ ¬ SmallFam G Φ' ∧
      ∀ φ ∈ Φ', ∀ φ' ∈ Φ', ∀ u, dist (φ u) (φ' u) ≤ (1 / 2) ^ n := by
  classical
  obtain ⟨O, hOm, hOcov, hOdiam⟩ := exists_smallOpens (α := α) n
  set Ψ : (ι → ℕ) → Set (ι → α) := fun c => {φ | ∀ u, φ u ∈ O (c u)} with hΨ
  have hcov : Φ ⊆ ⋃ c : ι → ℕ, Ψ c := by
    intro φ hφ
    choose c hc using fun u => hOcov (φ u)
    exact mem_iUnion.mpr ⟨c, hc⟩
  obtain ⟨c, hc⟩ := exists_not_smallFam_inter' hpos hcov
  have hΨm : MeasurableSet (Ψ c) := by
    have h : Ψ c = ⋂ u, (fun φ : ι → α => φ u) ⁻¹' O (c u) := by
      ext φ
      simp [hΨ]
    rw [h]
    exact MeasurableSet.iInter fun u => measurable_pi_apply u (hOm (c u))
  refine ⟨Φ ∩ Ψ c, inter_subset_left, hana.inter_measurableSet hΨm, hc, ?_⟩
  rintro φ ⟨-, hφ⟩ φ' ⟨-, hφ'⟩ u
  exact hOdiam (c u) _ (hφ u) _ (hφ' u)

end Shrink

/-! ### Witness extension fold -/

section WitnessFold

variable {α : Type*} [TopologicalSpace α] [PolishSpace α]
  [MeasurableSpace α] [BorelSpace α]
variable {ι : Type*} [Countable ι] [DecidableEq ι]

omit [BorelSpace α] in
/-- **Witness extension**: given a positive analytic family whose tracked edge pairs are
all witnessed at their current words, the family can be refined to a positive analytic
subfamily with every tracked witness word properly extended. -/
theorem exists_extend_witnesses {G : Set (α × α)}
    {g : (ℕ → ℕ) → α × α} (hg : Continuous g)
    (L : List (ι × ι)) (hnodup : L.Nodup)
    {Φ : Set (ι → α)} (hana : AnalyticSet Φ) (hpos : ¬ SmallFam G Φ)
    (c₀ : ι × ι → List ℕ)
    (hwit : ∀ p ∈ L, ∀ φ ∈ Φ, φ ∈ WitSet g p.1 p.2 (c₀ p)) :
    ∃ (Φ' : Set (ι → α)) (c' : ι × ι → List ℕ), Φ' ⊆ Φ ∧ AnalyticSet Φ' ∧
      ¬ SmallFam G Φ' ∧
      (∀ p ∈ L, c₀ p <+: c' p ∧ (c₀ p).length < (c' p).length ∧
        ∀ φ ∈ Φ', φ ∈ WitSet g p.1 p.2 (c' p)) ∧
      (∀ p ∉ L, c' p = c₀ p) := by
  classical
  induction L generalizing Φ with
  | nil => exact ⟨Φ, c₀, subset_rfl, hana, hpos, by simp, fun p _ => rfl⟩
  | cons p L IH =>
    obtain ⟨Φ₁, c₁, hsub₁, hana₁, hpos₁, hL₁, hout₁⟩ :=
      IH (List.Nodup.of_cons hnodup) hana hpos
        (fun q hq φ hφ => hwit q (List.mem_cons_of_mem p hq) φ hφ)
    have hpL : p ∉ L := (List.nodup_cons.mp hnodup).1
    have hwitp : ∀ φ ∈ Φ₁, φ ∈ WitSet g p.1 p.2 (c₀ p) :=
      fun φ hφ => hwit p List.mem_cons_self φ (hsub₁ hφ)
    obtain ⟨k, hk⟩ := exists_not_smallFam_inter hpos₁ (witSet_cover hwitp)
    refine ⟨Φ₁ ∩ WitSet g p.1 p.2 (c₀ p ++ [k]),
      Function.update c₁ p (c₀ p ++ [k]),
      inter_subset_left.trans hsub₁,
      hana₁.inter (analyticSet_witSet hg p.1 p.2 _), hk, ?_, ?_⟩
    · rintro q hq
      rcases List.mem_cons.mp hq with rfl | hqL
      · rw [Function.update_self]
        exact ⟨⟨[k], rfl⟩, by simp, fun φ hφ => hφ.2⟩
      · have hqp : q ≠ p := fun h => hpL (h ▸ hqL)
        rw [Function.update_of_ne hqp]
        obtain ⟨hpre, hlen, hwit'⟩ := hL₁ q hqL
        exact ⟨hpre, hlen, fun φ hφ => hwit' φ hφ.1⟩
    · intro q hq
      have hqp : q ≠ p := fun h => hq (h ▸ List.mem_cons_self)
      rw [Function.update_of_ne hqp]
      exact hout₁ q (fun h => hq (List.mem_cons_of_mem p h))

end WitnessFold

end G0Fusion
