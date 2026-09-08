/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Scott.BackAndForth
import InfinitaryLogic.Scott.Stabilization
import InfinitaryLogic.Karp.PotentialIso
import Mathlib.Data.Set.Finite.Range

/-!
# Orbit ranks of finite tuples and the internal Scott rank

The **internal** finite-tuple invariant of a single structure `M`: for a tuple `a : Fin n → M`,
its orbit rank `orbitRank a` is the least ordinal `α` such that every tuple `b` of `M` that is
back-and-forth equivalent to `a` at level `α` is equivalent to `a` at **every** level.  For
countable `M` that is exactly "the level-`α` class of `a` is its automorphism orbit"
(`bfEquiv_orbitRank_iff_exists_automorphism`).  The internal Scott rank
`internalScottRank M = ⨆ (orbitRank a + 1)` is the `SR(M)` convention.

**Convention, and a source discrepancy.**  Marker (*Lectures on Infinitary Model Theory*, 2016,
Definition 2.2.4) prints the one-step condition "`a ∼_α b ⇒ a ∼_{α+1} b`".  That condition does
not define orbits: a class can pause for one level and split later (the graph `K₂ ⊔ K₃`: all
vertices are equivalent at levels `0` and `1`, a `K₂`-vertex and a `K₃`-vertex are not
automorphic and separate at level `2`; see `scripts/check_orbit_rank_regressions.lean`).  The
production definition here is the all-levels form, as in the Scott-rank survey
(arXiv:2011.03923, Definition 2.6), which is what the orbit reading requires.

This is deliberately distinct from `elementRank`/`scottRank` (`Scott/Rank.lean`), which compare a
singleton of `M` with tuples of arbitrary countable structures.  No comparison between the two
conventions is supplied here.

Contents:

* `orbitStable a`: the levels at which the orbit of `a` has stabilized (all-levels form);
  upward closed; nonempty for every structure (`orbitStable_nonempty`, via the set-sized
  stabilization ordinal of `M` with itself), so `orbitRank` is never an infimum over an empty
  set.
* `orbitRank`, its membership and least-element lemmas; for countable `M`, equivalence at the
  orbit rank is equivalent to an automorphism carrying the tuple.
* `internalScottRank`: the supremum API (`internalScottRank_le`, cofinal lower bound,
  `internalScottRank_eq_iff`) and, on top of it, the **semantic exact-rank criterion**:
  `internalScottRank_le_of_orbits_determined` (every tuple's orbit is determined at some level
  below `α`) and `le_internalScottRank_of_not_automorphic` (below every `β < α` some
  `β`-equivalent tuples are not automorphic), assembled in `internalScottRank_eq_of_orbits`.
* Transport of `BFEquiv` along isomorphisms (`BFEquiv.map_equiv`) and isomorphism invariance of
  both ranks.
* `exists_automorphism_of_bfEquiv_all`: for countable `M`, two tuples equivalent at **every**
  level are carried to each other by an automorphism (pointed Karp).  The proof builds a pointed
  potential isomorphism and reads the tuple off the graph specification of the countable
  back-and-forth construction through the equality atoms.
* Infinite pure sets: every orbit rank is `0` and the internal Scott rank is `1`.

Ordinals live in `Ordinal.{w}` for `M : Type w`, the universe the stabilization argument uses.
No computability or admissibility enters.
-/

namespace FirstOrder.Language

open Fin Ordinal

variable {L : Language.{u, v}} [L.IsRelational]
variable {M : Type w} [L.Structure M] {N : Type w'} [L.Structure N]

/-! ### Transport along isomorphisms -/

omit [L.IsRelational] in
/-- Atomic types are transported along isomorphisms. -/
theorem SameAtomicType.map_equiv {M' : Type*} {N' : Type*} [L.Structure M'] [L.Structure N']
    (e : M ≃[L] M') (e' : N ≃[L] N') {n : ℕ} {a : Fin n → M} {b : Fin n → N} :
    SameAtomicType (L := L) (⇑e ∘ a) (⇑e' ∘ b) ↔ SameAtomicType (L := L) a b := by
  constructor <;> intro h idx <;> have hidx := h idx <;> cases idx with
  | eq i j =>
    simp only [AtomicIdx.holds, Function.comp] at hidx ⊢
    first
    | exact ⟨fun hij => e'.injective (hidx.mp (congrArg e hij)),
        fun hij => e.injective (hidx.mpr (congrArg e' hij))⟩
    | exact ⟨fun hij => congrArg e' (hidx.mp (e.injective hij)),
        fun hij => congrArg e (hidx.mpr (e'.injective hij))⟩
  | rel R f =>
    simp only [AtomicIdx.holds] at hidx ⊢
    first
    | rwa [Function.comp_assoc, Function.comp_assoc, e.map_rel, e'.map_rel] at hidx
    | rwa [Function.comp_assoc, Function.comp_assoc, e.map_rel, e'.map_rel]

omit [L.IsRelational] in
/-- Back-and-forth equivalence is transported along isomorphisms of both sides. -/
theorem BFEquiv.map_equiv {M' : Type w} {N' : Type w'} [L.Structure M'] [L.Structure N']
    (e : M ≃[L] M') (e' : N ≃[L] N') (α : Ordinal) {n : ℕ} {a : Fin n → M} {b : Fin n → N} :
    BFEquiv (L := L) α n (⇑e ∘ a) (⇑e' ∘ b) ↔ BFEquiv (L := L) α n a b := by
  induction α using Ordinal.limitRecOn generalizing n a b with
  | zero =>
    rw [BFEquiv.zero, BFEquiv.zero]
    exact SameAtomicType.map_equiv e e'
  | add_one β ih =>
    rw [← Order.succ_eq_add_one, BFEquiv.succ, BFEquiv.succ]
    refine and_congr (ih) (and_congr ?_ ?_)
    · constructor
      · intro h m
        obtain ⟨n', hn'⟩ := h (e m)
        refine ⟨e'.symm n', ?_⟩
        have := (ih (a := snoc a m) (b := snoc b (e'.symm n'))).mp
        rw [Fin.comp_snoc, Fin.comp_snoc, Equiv.apply_symm_apply] at this
        exact this hn'
      · intro h m'
        obtain ⟨n', hn'⟩ := h (e.symm m')
        refine ⟨e' n', ?_⟩
        have := (ih (a := snoc a (e.symm m')) (b := snoc b n')).mpr hn'
        rwa [Fin.comp_snoc, Fin.comp_snoc, Equiv.apply_symm_apply] at this
    · constructor
      · intro h n'
        obtain ⟨m, hm⟩ := h (e' n')
        refine ⟨e.symm m, ?_⟩
        have := (ih (a := snoc a (e.symm m)) (b := snoc b n')).mp
        rw [Fin.comp_snoc, Fin.comp_snoc, Equiv.apply_symm_apply] at this
        exact this hm
      · intro h n''
        obtain ⟨m, hm⟩ := h (e'.symm n'')
        refine ⟨e m, ?_⟩
        have := (ih (a := snoc a m) (b := snoc b (e'.symm n''))).mpr hm
        rwa [Fin.comp_snoc, Fin.comp_snoc, Equiv.apply_symm_apply] at this
  | limit β hβ ih =>
    rw [BFEquiv.limit β hβ, BFEquiv.limit β hβ]
    exact forall_congr' fun γ => forall_congr' fun hγ => ih γ hγ

/-! ### Orbit rank -/

/-- The levels at which the orbit of `a` inside `M` has stabilized: every `b` in `M` equivalent
to `a` at level `α` is equivalent to `a` at every level. -/
def orbitStable {n : ℕ} (a : Fin n → M) : Set Ordinal.{w} :=
  {α | ∀ b : Fin n → M, BFEquiv (L := L) α n a b → ∀ γ : Ordinal.{w}, BFEquiv (L := L) γ n a b}

omit [L.IsRelational] in
/-- **The stabilization set is never empty**: the set-sized stabilization ordinal of `M` with
itself belongs to it.  No countability of `M` is needed. -/
theorem orbitStable_nonempty {n : ℕ} (a : Fin n → M) : (orbitStable (L := L) a).Nonempty :=
  ⟨bfStabilizationOrdinal.{u, v, w} L M M, fun _ hb =>
    bfEquiv_bfStabilizationOrdinal_iff_all.mp hb⟩

omit [L.IsRelational] in
/-- Stabilization persists upward. -/
theorem orbitStable_upward {n : ℕ} {a : Fin n → M} {α β : Ordinal.{w}}
    (h : α ∈ orbitStable (L := L) a) (hαβ : α ≤ β) : β ∈ orbitStable (L := L) a :=
  fun b hb => h b (BFEquiv.monotone hαβ hb)

/-- **Orbit rank** of a tuple: the least level at which its class is its orbit. -/
noncomputable def orbitRank {n : ℕ} (a : Fin n → M) : Ordinal.{w} :=
  sInf (orbitStable (L := L) a)

omit [L.IsRelational] in
theorem orbitRank_mem {n : ℕ} (a : Fin n → M) : orbitRank (L := L) a ∈ orbitStable (L := L) a :=
  csInf_mem (orbitStable_nonempty a)

omit [L.IsRelational] in
/-- The defining property at the orbit rank: equivalence there is equivalence at every level. -/
theorem bfEquiv_all_of_bfEquiv_orbitRank {n : ℕ} {a b : Fin n → M}
    (h : BFEquiv (L := L) (orbitRank (L := L) a) n a b) (γ : Ordinal.{w}) :
    BFEquiv (L := L) γ n a b :=
  orbitRank_mem a b h γ

omit [L.IsRelational] in
theorem orbitRank_le_of_mem {n : ℕ} {a : Fin n → M} {α : Ordinal.{w}}
    (h : α ∈ orbitStable (L := L) a) : orbitRank (L := L) a ≤ α :=
  csInf_le' h

omit [L.IsRelational] in
theorem mem_orbitStable_iff_orbitRank_le {n : ℕ} {a : Fin n → M} {α : Ordinal.{w}} :
    α ∈ orbitStable (L := L) a ↔ orbitRank (L := L) a ≤ α :=
  ⟨orbitRank_le_of_mem, fun h => orbitStable_upward (orbitRank_mem a) h⟩

omit [L.IsRelational] in
/-- Below the orbit rank, stabilization fails: some `b` is equivalent at that level but not at
every level. -/
theorem exists_not_all_of_lt_orbitRank {n : ℕ} {a : Fin n → M} {β : Ordinal.{w}}
    (h : β < orbitRank (L := L) a) :
    ∃ b : Fin n → M, BFEquiv (L := L) β n a b ∧ ¬ ∀ γ : Ordinal.{w}, BFEquiv (L := L) γ n a b := by
  by_contra hcon
  push Not at hcon
  exact (not_le.mpr h) (orbitRank_le_of_mem fun b hb => hcon b hb)

omit [L.IsRelational] in
/-- Automorphic tuples are equivalent at every level. -/
theorem bfEquiv_all_of_automorphism {n : ℕ} {a b : Fin n → M} (e : M ≃[L] M)
    (he : ⇑e ∘ a = b) (γ : Ordinal.{w}) : BFEquiv (L := L) γ n a b := by
  subst he
  have := (BFEquiv.map_equiv (Language.Equiv.refl L M) e γ (a := a) (b := a)).mpr
    (BFEquiv.refl γ a)
  have hid : ⇑(Language.Equiv.refl L M) ∘ a = a := funext fun i => rfl
  rwa [hid] at this

omit [L.IsRelational] in
/-- **Isomorphism invariance of the orbit rank.** -/
theorem orbitRank_map_equiv {M' : Type w} [L.Structure M'] (e : M ≃[L] M') {n : ℕ}
    (a : Fin n → M) : orbitRank (L := L) (⇑e ∘ a) = orbitRank (L := L) a := by
  unfold orbitRank
  congr 1
  ext α
  constructor
  · intro h b hb γ
    have := h (⇑e ∘ b) ((BFEquiv.map_equiv e e α).mpr hb) γ
    exact (BFEquiv.map_equiv e e _).mp this
  · intro h b' hb' γ
    have hb : BFEquiv (L := L) α n a (⇑e.symm ∘ b') := by
      have := (BFEquiv.map_equiv e e α (a := a) (b := ⇑e.symm ∘ b')).mp
      apply this
      rwa [← Function.comp_assoc, show ⇑e ∘ ⇑e.symm = id from funext e.apply_symm_apply,
        Function.id_comp]
    have := (BFEquiv.map_equiv e e _).mpr (h _ hb γ)
    rwa [← Function.comp_assoc, show ⇑e ∘ ⇑e.symm = id from funext e.apply_symm_apply,
      Function.id_comp] at this

/-! ### Internal Scott rank -/

/-- **Internal Scott rank** `SR(M) = ⨆ (r(a) + 1)` over all finite tuples (Marker Definition
2.2.4). -/
noncomputable def internalScottRank (M : Type w) [L.Structure M] : Ordinal.{w} :=
  ⨆ x : (Σ n : ℕ, Fin n → M), orbitRank (L := L) x.2 + 1

omit [L.IsRelational] in
/-- **Lower bound**: every tuple's orbit rank plus one is at most the internal Scott rank. -/
theorem orbitRank_add_one_le_internalScottRank {n : ℕ} (a : Fin n → M) :
    orbitRank (L := L) a + 1 ≤ internalScottRank (L := L) M :=
  Ordinal.le_iSup (fun x : (Σ n : ℕ, Fin n → M) => orbitRank (L := L) x.2 + 1) ⟨n, a⟩

omit [L.IsRelational] in
/-- **Upper bound**: a bound on every `orbitRank a + 1` bounds the internal Scott rank. -/
theorem internalScottRank_le {β : Ordinal.{w}}
    (h : ∀ (n : ℕ) (a : Fin n → M), orbitRank (L := L) a + 1 ≤ β) :
    internalScottRank (L := L) M ≤ β :=
  Ordinal.iSup_le fun x => h x.1 x.2

omit [L.IsRelational] in
/-- **Cofinal lower bound**: every ordinal below the internal Scott rank is exceeded by some
`orbitRank a + 1`. -/
theorem exists_orbitRank_add_one_gt_of_lt_internalScottRank {γ : Ordinal.{w}}
    (h : γ < internalScottRank (L := L) M) :
    ∃ (n : ℕ) (a : Fin n → M), γ < orbitRank (L := L) a + 1 := by
  by_contra hcon
  push Not at hcon
  exact (not_le.mpr h) (internalScottRank_le hcon)

omit [L.IsRelational] in
/-- **Exact-rank criterion**: `internalScottRank M = β` iff `β` bounds every `orbitRank a + 1`
and every ordinal below `β` is exceeded by some `orbitRank a + 1`. -/
theorem internalScottRank_eq_iff {β : Ordinal.{w}} :
    internalScottRank (L := L) M = β ↔
      (∀ (n : ℕ) (a : Fin n → M), orbitRank (L := L) a + 1 ≤ β) ∧
      (∀ γ < β, ∃ (n : ℕ) (a : Fin n → M), γ < orbitRank (L := L) a + 1) := by
  constructor
  · rintro rfl
    exact ⟨fun n a => orbitRank_add_one_le_internalScottRank a,
      fun γ hγ => exists_orbitRank_add_one_gt_of_lt_internalScottRank hγ⟩
  · rintro ⟨hub, hcof⟩
    refine le_antisymm (internalScottRank_le hub) (le_of_not_gt fun hlt => ?_)
    obtain ⟨n, a, ha⟩ := hcof _ hlt
    exact (not_le.mpr ha) (orbitRank_add_one_le_internalScottRank a)

omit [L.IsRelational] in
/-- **Isomorphism invariance of the internal Scott rank.** -/
theorem internalScottRank_map_equiv {M' : Type w} [L.Structure M'] (e : M ≃[L] M') :
    internalScottRank (L := L) M' = internalScottRank (L := L) M := by
  apply le_antisymm
  · refine internalScottRank_le fun n a' => ?_
    have := orbitRank_add_one_le_internalScottRank (L := L) (⇑e.symm ∘ a')
    rwa [orbitRank_map_equiv e.symm] at this
  · refine internalScottRank_le fun n a => ?_
    have := orbitRank_add_one_le_internalScottRank (L := L) (⇑e ∘ a)
    rwa [orbitRank_map_equiv e] at this

/-! ### Pointed automorphisms -/

/-- The pointed potential isomorphism: pairs of extensions of `a` and `b` that are equivalent at
every level. -/
private noncomputable def pointedPotentialIso {n : ℕ} (a b : Fin n → M)
    (h : ∀ α : Ordinal.{w}, BFEquiv (L := L) α n a b) : PotentialIso L M M where
  family := {p | ∀ α : Ordinal.{w},
    BFEquiv (L := L) α (n + p.1) (Fin.append a p.2.1) (Fin.append b p.2.2)}
  empty_mem := by
    intro α
    simpa [Fin.append_elim0] using h α
  compatible := by
    intro p hp
    have h0 := (BFEquiv.zero _ _).mp (hp 0)
    have := h0.relabel (Fin.natAdd n)
    simpa [Function.comp_def, Fin.append_right] using this
  forth := by
    rintro ⟨k, c, d⟩ hfam m
    simp only [Set.mem_ofPred_eq] at hfam ⊢
    by_contra h_no
    push Not at h_no
    choose αbad hbad using h_no
    have hbdd : BddAbove (Set.range αbad) := Ordinal.bddAbove_of_small
    obtain ⟨n'₀, hn'₀⟩ := BFEquiv.forth (hfam (Order.succ (⨆ n', αbad n'))) m
    apply hbad n'₀
    have := BFEquiv.monotone (le_ciSup hbdd n'₀) hn'₀
    rwa [← Fin.append_snoc, ← Fin.append_snoc] at this
  back := by
    rintro ⟨k, c, d⟩ hfam m'
    simp only [Set.mem_ofPred_eq] at hfam ⊢
    by_contra h_no
    push Not at h_no
    choose αbad hbad using h_no
    have hbdd : BddAbove (Set.range αbad) := Ordinal.bddAbove_of_small
    obtain ⟨m₀, hm₀⟩ := BFEquiv.back (hfam (Order.succ (⨆ m, αbad m))) m'
    apply hbad m₀
    have := BFEquiv.monotone (le_ciSup hbdd m₀) hm₀
    rwa [← Fin.append_snoc, ← Fin.append_snoc] at this

/-- **Pointed Karp.**  In a countable structure, two tuples back-and-forth equivalent at every
level are carried to each other by an automorphism.  The automorphism comes from the countable
back-and-forth construction applied to the pointed family; that it carries `a` to `b` is read
off the graph specification through the equality atoms of the extended tuples. -/
theorem exists_automorphism_of_bfEquiv_all [Countable M] {n : ℕ} {a b : Fin n → M}
    (h : ∀ α : Ordinal.{w}, BFEquiv (L := L) α n a b) :
    ∃ e : M ≃[L] M, ⇑e ∘ a = b := by
  obtain ⟨e, he⟩ := (pointedPotentialIso a b h).countable_toEquiv_graph
  refine ⟨e, funext fun j => ?_⟩
  obtain ⟨⟨k, c, d⟩, hp, i, hci, hdi⟩ := he (a j)
  have h0 := (BFEquiv.zero _ _).mp (hp 0)
  have heq := h0 (AtomicIdx.eq (Fin.castAdd k j) (Fin.natAdd n i))
  simp only [AtomicIdx.holds, Fin.append_left, Fin.append_right] at heq
  show e (a j) = b j
  exact hdi.symm.trans (heq.mp hci.symm).symm

/-! ### The orbit characterization and the semantic exact-rank criterion -/

/-- **Equivalence at the orbit rank is automorphism.**  For countable `M`, `b` is equivalent to
`a` at level `orbitRank a` iff an automorphism carries `a` to `b`. -/
theorem bfEquiv_orbitRank_iff_exists_automorphism [Countable M] {n : ℕ} {a b : Fin n → M} :
    BFEquiv (L := L) (orbitRank (L := L) a) n a b ↔ ∃ e : M ≃[L] M, ⇑e ∘ a = b :=
  ⟨fun h => exists_automorphism_of_bfEquiv_all (bfEquiv_all_of_bfEquiv_orbitRank h),
    fun ⟨e, he⟩ => bfEquiv_all_of_automorphism e he _⟩

/-- Equivalence at every level is automorphism, for countable `M`. -/
theorem bfEquiv_all_iff_exists_automorphism [Countable M] {n : ℕ} {a b : Fin n → M} :
    (∀ γ : Ordinal.{w}, BFEquiv (L := L) γ n a b) ↔ ∃ e : M ≃[L] M, ⇑e ∘ a = b :=
  ⟨exists_automorphism_of_bfEquiv_all, fun ⟨e, he⟩ => bfEquiv_all_of_automorphism e he⟩

omit [L.IsRelational] in
/-- A level at which the class of `a` is its automorphism orbit is a stabilization level. -/
theorem mem_orbitStable_of_orbit_determined {n : ℕ} {a : Fin n → M} {β : Ordinal.{w}}
    (h : ∀ b : Fin n → M, BFEquiv (L := L) β n a b → ∃ e : M ≃[L] M, ⇑e ∘ a = b) :
    β ∈ orbitStable (L := L) a :=
  fun b hb => let ⟨e, he⟩ := h b hb; bfEquiv_all_of_automorphism e he

omit [L.IsRelational] in
/-- **Semantic upper bound.**  If every tuple has some level below `α` at which its class is its
automorphism orbit, the internal Scott rank is at most `α`. -/
theorem internalScottRank_le_of_orbits_determined {α : Ordinal.{w}}
    (h : ∀ (n : ℕ) (a : Fin n → M), ∃ β < α,
      ∀ b : Fin n → M, BFEquiv (L := L) β n a b → ∃ e : M ≃[L] M, ⇑e ∘ a = b) :
    internalScottRank (L := L) M ≤ α := by
  refine internalScottRank_le fun n a => ?_
  obtain ⟨β, hβ, hdet⟩ := h n a
  exact Order.succ_le_of_lt
    ((orbitRank_le_of_mem (mem_orbitStable_of_orbit_determined hdet)).trans_lt hβ)

/-- **Semantic lower bound.**  If below every `β < α` some tuples are `β`-equivalent but not
automorphic, the internal Scott rank is at least `α`.  Countability of `M` enters through the
pointed automorphism theorem. -/
theorem le_internalScottRank_of_not_automorphic [Countable M] {α : Ordinal.{w}}
    (h : ∀ β < α, ∃ (n : ℕ) (a b : Fin n → M),
      BFEquiv (L := L) β n a b ∧ ¬ ∃ e : M ≃[L] M, ⇑e ∘ a = b) :
    α ≤ internalScottRank (L := L) M := by
  refine le_of_forall_lt fun β hβ => ?_
  obtain ⟨n, a, b, hab, hno⟩ := h β hβ
  have hβa : β < orbitRank (L := L) a := by
    by_contra hle
    push Not at hle
    exact hno (bfEquiv_orbitRank_iff_exists_automorphism.mp (BFEquiv.monotone hle hab))
  exact lt_of_lt_of_le (lt_of_lt_of_le hβa (Order.le_succ _))
    (orbitRank_add_one_le_internalScottRank a)

/-- **Semantic exact-rank criterion**: the internal Scott rank is `α` when every tuple's orbit is
determined below `α` and below every `β < α` some `β`-equivalent tuples are not automorphic. -/
theorem internalScottRank_eq_of_orbits [Countable M] {α : Ordinal.{w}}
    (hup : ∀ (n : ℕ) (a : Fin n → M), ∃ β < α,
      ∀ b : Fin n → M, BFEquiv (L := L) β n a b → ∃ e : M ≃[L] M, ⇑e ∘ a = b)
    (hlow : ∀ β < α, ∃ (n : ℕ) (a b : Fin n → M),
      BFEquiv (L := L) β n a b ∧ ¬ ∃ e : M ≃[L] M, ⇑e ∘ a = b) :
    internalScottRank (L := L) M = α :=
  le_antisymm (internalScottRank_le_of_orbits_determined hup)
    (le_internalScottRank_of_not_automorphic hlow)

/-! ### Infinite pure sets -/

section PureSet

variable {X : Type w} [Infinite X]

/-- The unique empty-language structure on `X`, local to this section. -/
local instance : Language.empty.Structure X := Language.emptyStructure

omit [Infinite X] in
/-- In the empty language, atomic agreement is agreement of the equality pattern. -/
theorem sameAtomicType_empty_iff {n : ℕ} (a b : Fin n → X) :
    SameAtomicType (L := Language.empty) (M := X) (N := X) a b ↔
      ∀ i j, a i = a j ↔ b i = b j := by
  constructor
  · intro h i j
    have := h (AtomicIdx.eq i j)
    simpa [AtomicIdx.holds] using this
  · intro h idx
    cases idx with
    | eq i j => simpa [AtomicIdx.holds] using h i j
    | rel R _ => exact (IsEmpty.false R).elim

/-- In an infinite pure set, tuples with the same equality pattern are equivalent at every
level: extend by a matching old coordinate, or by a fresh element. -/
theorem bfEquiv_all_of_pattern {n : ℕ} (a b : Fin n → X) (h : ∀ i j, a i = a j ↔ b i = b j)
    (α : Ordinal.{w}) : BFEquiv (L := Language.empty) (M := X) (N := X) α n a b := by
  induction α using Ordinal.limitRecOn generalizing n a b with
  | zero => exact (BFEquiv.zero _ _).mpr ((sameAtomicType_empty_iff a b).mpr h)
  | add_one β ih =>
    rw [← Order.succ_eq_add_one, BFEquiv.succ]
    refine ⟨ih a b h, ?_, ?_⟩
    · intro m
      by_cases hm : ∃ i, a i = m
      · obtain ⟨i, rfl⟩ := hm
        refine ⟨b i, ih _ _ ?_⟩
        intro p q
        refine Fin.lastCases ?_ (fun p => ?_) p <;> refine Fin.lastCases ?_ (fun q => ?_) q <;>
          simp only [Fin.snoc_last, Fin.snoc_castSucc] <;> exact h _ _
      · push Not at hm
        obtain ⟨y, -, hy⟩ := (Set.infinite_univ (α := X)).exists_notMem_finite
          (Set.finite_range b)
        refine ⟨y, ih _ _ ?_⟩
        have hy' : ∀ i, b i ≠ y := fun i hi => hy ⟨i, hi⟩
        intro p q
        refine Fin.lastCases ?_ (fun p => ?_) p <;> refine Fin.lastCases ?_ (fun q => ?_) q <;>
          simp only [Fin.snoc_last, Fin.snoc_castSucc] <;>
          first
          | exact h _ _
          | exact ⟨fun e => ((hm _) e.symm).elim, fun e => ((hy' _) e.symm).elim⟩
          | exact ⟨fun e => ((hm _) e).elim, fun e => ((hy' _) e).elim⟩
    · intro m
      by_cases hm : ∃ i, b i = m
      · obtain ⟨i, rfl⟩ := hm
        refine ⟨a i, ih _ _ ?_⟩
        intro p q
        refine Fin.lastCases ?_ (fun p => ?_) p <;> refine Fin.lastCases ?_ (fun q => ?_) q <;>
          simp only [Fin.snoc_last, Fin.snoc_castSucc] <;> exact h _ _
      · push Not at hm
        obtain ⟨y, -, hy⟩ := (Set.infinite_univ (α := X)).exists_notMem_finite
          (Set.finite_range a)
        refine ⟨y, ih _ _ ?_⟩
        have hy' : ∀ i, a i ≠ y := fun i hi => hy ⟨i, hi⟩
        intro p q
        refine Fin.lastCases ?_ (fun p => ?_) p <;> refine Fin.lastCases ?_ (fun q => ?_) q <;>
          simp only [Fin.snoc_last, Fin.snoc_castSucc] <;>
          first
          | exact h _ _
          | exact ⟨fun e => ((hy' _) e.symm).elim, fun e => ((hm _) e.symm).elim⟩
          | exact ⟨fun e => ((hy' _) e).elim, fun e => ((hm _) e).elim⟩
  | limit β hβ ih =>
    rw [BFEquiv.limit β hβ]
    exact fun γ hγ => ih γ hγ a b h

/-- **Every tuple of an infinite pure set has orbit rank `0`.** -/
theorem orbitRank_pureSet {n : ℕ} (a : Fin n → X) :
    orbitRank (L := Language.empty) (M := X) a = 0 := by
  apply le_antisymm _ (_root_.zero_le)
  apply orbitRank_le_of_mem
  intro b hb γ
  exact bfEquiv_all_of_pattern a b
    ((sameAtomicType_empty_iff a b).mp ((BFEquiv.zero _ _).mp hb)) γ

/-- **An infinite pure set has internal Scott rank `1`.** -/
theorem internalScottRank_pureSet :
    internalScottRank (L := Language.empty) X = 1 := by
  rw [internalScottRank_eq_iff]
  refine ⟨fun n a => by rw [orbitRank_pureSet]; simp, fun γ hγ => ⟨0, Fin.elim0, ?_⟩⟩
  rw [orbitRank_pureSet]; simpa using hγ

end PureSet

end FirstOrder.Language
