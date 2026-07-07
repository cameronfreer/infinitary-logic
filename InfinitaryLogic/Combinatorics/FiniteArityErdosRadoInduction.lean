/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Combinatorics.PairErdosRadoGeneral

/-!
# Finite-arity Erdős–Rado: the induction scaffold

The finite-arity induction SCAFFOLD toward the bounded finite-arity Erdős–Rado theorem:
the cardinal ladder `finiteERBound` (with its arithmetic validated against the beth scale),
the validated API (`FiniteArityHomogeneousUpTo`, `FiniteArityErdosRadoBounded`), and the easy
arities `0`, `1`, `2` (`finiteArityHomogeneousUpTo_zero`/`_one`/`_two`), the last consuming the
proven generalized pair theorem `pairErdosRado_general_of_large`.

The hard `n → n+1` induction step — coloring pairs by induced `n`-types and applying
`pairErdosRado_general_of_large` at the previous ladder level — is deliberately the NEXT
chunk. The eventual chain is
`FiniteArityErdosRadoBounded ℶ₁ → FiniteArityErdosRadoOmega1 ℶ₁ → morley_hanf`, where the
first arrow needs care: the per-`N` outputs cannot be iterated (each output `κ⁺`-suborder is
far too small to source the next pass), so the all-arity version must recurse internally over
the arity, not iterate over the external sequence.

## The ladder

Level `N` of `finiteERBound κ` is enough source to homogenize all arities `≤ N` with output
`κ⁺`. The recursion `level (n+2) = succ (2 ^ level (n+1))` is sized so that generalized pair
ER at color bound `finiteERBound κ (n+1)`, applied to a source of size `finiteERBound κ (n+2)`,
outputs a suborder of size `succ (finiteERBound κ (n+1))` — ample source for stage `n+1`.
At `κ = ℶ₁` every level sits below `ℶ_{ω₁}` (`finiteERBound_le_beth_omega1`): each ladder step
`succ ∘ (2 ^ ·)` is absorbed by two beth steps (`finiteERBound_beth_one_le`).
-/

open FirstOrder.Combinatorics.PairERGen

/-! ## The cardinal ladder -/

/-- Source-size ladder; level `N` is enough source to homogenize all arities `≤ N` with
output `κ⁺`. Level `0`/`1` = `κ⁺` (nothing to do / point pigeonhole);
level `n+2` = `succ (2 ^ level (n+1))`, sized so that generalized pair ER **at color bound
`finiteERBound κ (n+1)`** applied to a source of size `finiteERBound κ (n+2)` outputs a
suborder of size `succ (finiteERBound κ (n+1))`, ample source for stage `n+1`. -/
noncomputable def finiteERBound (κ : Cardinal.{0}) : ℕ → Cardinal.{0}
  | 0 => Order.succ κ
  | 1 => Order.succ κ
  | (n + 2) => Order.succ ((2 : Cardinal.{0}) ^ finiteERBound κ (n + 1))

/-! ## Ladder lemmas -/

section LadderLemmas

/-- Ladder level `0` is `κ⁺`. -/
theorem finiteERBound_zero (κ : Cardinal.{0}) : finiteERBound κ 0 = Order.succ κ := rfl

/-- Ladder level `1` is `κ⁺`. -/
theorem finiteERBound_one (κ : Cardinal.{0}) : finiteERBound κ 1 = Order.succ κ := rfl

/-- The ladder recursion, as an equality: level `n+2` is exactly the generalized-pair-ER
source bound for color bound `finiteERBound κ (n+1)`. -/
theorem finiteERBound_succ_succ (κ : Cardinal.{0}) (n : ℕ) :
    finiteERBound κ (n + 2) = Order.succ ((2 : Cardinal.{0}) ^ finiteERBound κ (n + 1)) := rfl

/-- Every ladder level dominates `κ⁺`. -/
theorem succ_le_finiteERBound (κ : Cardinal.{0}) : ∀ n : ℕ, Order.succ κ ≤ finiteERBound κ n
  | 0 => le_rfl
  | 1 => le_rfl
  | (n + 2) => by
    rw [finiteERBound_succ_succ]
    have hκ : κ ≤ (2 : Cardinal.{0}) ^ finiteERBound κ (n + 1) :=
      ((Order.le_succ κ).trans (succ_le_finiteERBound κ (n + 1))).trans (Cardinal.cantor _).le
    exact Order.succ_le_succ hκ

/-- The ladder is monotone in the arity. -/
theorem finiteERBound_mono (κ : Cardinal.{0}) : Monotone (finiteERBound κ) := by
  apply monotone_nat_of_le_succ
  intro n
  match n with
  | 0 => exact le_rfl
  | (m + 1) =>
    show finiteERBound κ (m + 1) ≤ finiteERBound κ (m + 2)
    rw [finiteERBound_succ_succ]
    exact (Cardinal.cantor _).le.trans (Order.le_succ _)

/-- Every ladder level of index `≥ 2` dominates the generalized pair-ER source bound
`succ (2 ^ κ)` — this is what lets the arity-2 theorem consume any level `≥ 2`. -/
theorem pair_source_le_finiteERBound (κ : Cardinal.{0}) (n : ℕ) :
    Order.succ ((2 : Cardinal.{0}) ^ κ) ≤ finiteERBound κ (n + 2) := by
  rw [finiteERBound_succ_succ]
  have hκ : κ ≤ finiteERBound κ (n + 1) :=
    (Order.le_succ κ).trans (succ_le_finiteERBound κ (n + 1))
  exact Order.succ_le_succ (Cardinal.power_le_power_left two_ne_zero hκ)

/-- `ℵ₀ ≤ ℶ₁` — the infinite-cardinal hypothesis for the ladder at the Morley–Hanf color
bound. -/
theorem aleph0_le_beth_one : Cardinal.aleph0 ≤ Cardinal.beth 1 := Cardinal.aleph0_le_beth 1

/-- `ℶ_{o+1} = 2 ^ ℶ_o`, with the successor index written additively. -/
private lemma beth_add_one (o : Ordinal.{0}) :
    Cardinal.beth (o + 1) = 2 ^ Cardinal.beth o := by
  rw [← Order.succ_eq_add_one, Cardinal.beth_succ]

/-- `(ℶ_o)⁺ ≤ ℶ_{o+1}`: one beth step absorbs a cardinal successor (Cantor). -/
private lemma succ_beth_le (o : Ordinal.{0}) :
    Order.succ (Cardinal.beth o) ≤ Cardinal.beth (o + 1) := by
  rw [beth_add_one]
  exact succ_le_two_power _

/-- At `κ = ℶ₁`, ladder level `n` is bounded by `ℶ_{2n+2}`: each ladder step
`succ ∘ (2 ^ ·)` costs strictly more than one beth step (the inner `succ`), but two beth
steps absorb it. -/
theorem finiteERBound_beth_one_le :
    ∀ n : ℕ, finiteERBound (Cardinal.beth 1) n ≤ Cardinal.beth ((2 * n + 2 : ℕ) : Ordinal)
  | 0 => by
    have h : ((2 * 0 + 2 : ℕ) : Ordinal.{0}) = (1 : Ordinal) + 1 := by
      rw [show (2 * 0 + 2 : ℕ) = 2 from rfl, Nat.cast_ofNat, one_add_one_eq_two]
    rw [finiteERBound_zero, h]
    exact succ_beth_le 1
  | 1 => by
    have h0 : finiteERBound (Cardinal.beth 1) 0 ≤ Cardinal.beth ((2 * 0 + 2 : ℕ) : Ordinal) :=
      finiteERBound_beth_one_le 0
    have hle : ((2 * 0 + 2 : ℕ) : Ordinal.{0}) ≤ ((2 * 1 + 2 : ℕ) : Ordinal.{0}) :=
      Nat.mono_cast (by omega)
    exact h0.trans (Cardinal.beth_le_beth.mpr hle)
  | (n + 2) => by
    have ih : finiteERBound (Cardinal.beth 1) (n + 1)
        ≤ Cardinal.beth ((2 * (n + 1) + 2 : ℕ) : Ordinal) := finiteERBound_beth_one_le (n + 1)
    calc finiteERBound (Cardinal.beth 1) (n + 2)
        = Order.succ (2 ^ finiteERBound (Cardinal.beth 1) (n + 1)) :=
          finiteERBound_succ_succ _ n
      _ ≤ Order.succ (2 ^ Cardinal.beth ((2 * (n + 1) + 2 : ℕ) : Ordinal)) :=
          Order.succ_le_succ (Cardinal.power_le_power_left two_ne_zero ih)
      _ = Order.succ (Cardinal.beth (((2 * (n + 1) + 2 : ℕ) : Ordinal) + 1)) := by
          rw [beth_add_one]
      _ ≤ Cardinal.beth ((((2 * (n + 1) + 2 : ℕ) : Ordinal) + 1) + 1) := succ_beth_le _
      _ = Cardinal.beth ((2 * (n + 2) + 2 : ℕ) : Ordinal) := by
          -- `↑(2*(n+1)+2) + 1 + 1` and `↑(2*(n+2)+2)` are definitionally equal ordinals.
          congr 1

/-- At `κ = ℶ₁`, every ladder level is strictly below `ℶ_{ω₁}` — the source size the
Morley–Hanf chain supplies dominates every finite stage. -/
theorem finiteERBound_lt_beth_omega1 (n : ℕ) :
    finiteERBound (Cardinal.beth 1) n < Cardinal.beth (Ordinal.omega 1) :=
  (finiteERBound_beth_one_le n).trans_lt (Cardinal.beth_lt_beth.mpr
    ((Ordinal.natCast_lt_omega0 _).trans Ordinal.omega0_lt_omega_one))

/-- At `κ = ℶ₁`, every ladder level is at most `ℶ_{ω₁}` (the form consumed when feeding a
`ℶ_{ω₁}`-sized source into a finite ladder stage). -/
theorem finiteERBound_le_beth_omega1 (n : ℕ) :
    finiteERBound (Cardinal.beth 1) n ≤ Cardinal.beth (Ordinal.omega 1) :=
  (finiteERBound_lt_beth_omega1 n).le

end LadderLemmas

/-! ## The API -/

/-- Homogeneity up to arity `N`: the exact statement the finite-arity induction will prove.
Any well-ordered source of size `≥ finiteERBound κ N` and any `ℕ`-indexed family of colorings
with color types of size `≤ κ` admit a single `κ⁺`-suborder homogeneous for **all** arities
`≤ N` simultaneously. The family is `ℕ`-indexed from the start, per the design note that the
all-arity theorem must recurse internally over arity, not iterate over the external
sequence. -/
def FiniteArityHomogeneousUpTo (κ : Cardinal.{0}) (N : ℕ) : Prop :=
  ∀ (I : Type) [LinearOrder I] [WellFoundedLT I],
    Cardinal.mk I ≥ finiteERBound κ N →
    ∀ (C : ℕ → Type) (_ : ∀ n, Cardinal.mk (C n) ≤ κ) (c : ∀ n, (Fin n ↪o I) → C n),
    ∃ e : (Order.succ κ).ord.ToType ↪o I,
      ∀ n, n ≤ N → ∀ t t' : Fin n ↪o I,
        (∀ k, t k ∈ Set.range e) → (∀ k, t' k ∈ Set.range e) →
        c n t = c n t'

/-- The bounded finite-arity residual: homogeneity up to every finite arity, each stage fed
by its own ladder level. This is the target of the finite-arity induction; the arrow
`FiniteArityErdosRadoBounded ℶ₁ → FiniteArityErdosRadoOmega1 ℶ₁` (one `ω₁`-suborder for all
arities at once from a `ℶ_{ω₁}`-sized source) is a separate, careful step — the per-`N`
outputs cannot be iterated. -/
def FiniteArityErdosRadoBounded (κ : Cardinal.{0}) : Prop :=
  ∀ N : ℕ, FiniteArityHomogeneousUpTo κ N

/-! ## Small utilities: arity-0/1/2 order embeddings and no-max output -/

section Utilities

variable {I : Type*} [LinearOrder I]

instance : Subsingleton (Fin 0 ↪o I) :=
  ⟨fun t t' => DFunLike.ext t t' fun k => k.elim0⟩

/-- The one-point order embedding `Fin 1 ↪o I` at `x` (strict monotonicity is vacuous on the
subsingleton `Fin 1`). -/
def singletonOE (x : I) : Fin 1 ↪o I :=
  OrderEmbedding.ofStrictMono (fun _ => x) fun a b hab =>
    absurd (Subsingleton.elim a b) (ne_of_lt hab)

/-- Every `Fin 1 ↪o I` is the one-point embedding at its value. -/
theorem orderEmbedding_fin_one_eq (t : Fin 1 ↪o I) : t = singletonOE (t 0) := by
  refine DFunLike.ext t _ fun k => ?_
  rw [Fin.eq_zero k]
  rfl

/-- Every `Fin 2 ↪o I` with prescribed endpoint values is the corresponding `pairEmbed`
(stated flexibly so the `<`-proof can be supplied through the endpoints of any suborder). -/
theorem orderEmbedding_fin_two_eq_pairEmbed (t : Fin 2 ↪o I) {u v : I} (h : u < v)
    (h0 : t 0 = u) (h1 : t 1 = v) : t = pairEmbed h := by
  refine DFunLike.ext t _ fun k => ?_
  match k with
  | ⟨0, _⟩ => exact h0
  | ⟨1, _⟩ => exact h1

/-- The output order `(succ κ).ord.ToType` has no maximum for infinite `κ`: `(succ κ).ord`
is closed under ordinal successor (`succ_lt_ord_of_lt`), so every element has a strict
upper bound. Supplies the second pair element the arity-1 endgame of the arity-2 theorem
needs. -/
theorem exists_gt_succOrdToType {κ : Cardinal.{0}} (hκ : Cardinal.aleph0 ≤ κ)
    (x : (Order.succ κ).ord.ToType) : ∃ y : (Order.succ κ).ord.ToType, x < y := by
  set d : Set.Iio (Order.succ κ).ord := Ordinal.ToType.mk.symm x
  have hδ : d.1 < (Order.succ κ).ord := d.2
  have hsucc : Order.succ d.1 < (Order.succ κ).ord := succ_lt_ord_of_lt hκ hδ
  refine ⟨Ordinal.ToType.mk ⟨Order.succ d.1, hsucc⟩, ?_⟩
  have hx : x = Ordinal.ToType.mk d := (Ordinal.ToType.mk.apply_symm_apply x).symm
  rw [hx]
  exact Ordinal.ToType.mk.lt_iff_lt.mpr
    (show d < ⟨Order.succ d.1, hsucc⟩ from Order.lt_succ d.1)

end Utilities

/-! ## The easy arities: `0`, `1`, `2` -/

/-- **Arity `≤ 0`.** Homogeneity up to arity `0` from a `κ⁺`-sized source: there is nothing
to homogenize (`Fin 0 ↪o I` is a subsingleton), so any `κ⁺`-suborder works. -/
theorem finiteArityHomogeneousUpTo_zero (κ : Cardinal.{0}) (_hκ : Cardinal.aleph0 ≤ κ) :
    FiniteArityHomogeneousUpTo κ 0 := by
  intro I _ _ hI C hC c
  have hI' : Order.succ κ ≤ Cardinal.mk I := hI
  obtain ⟨e⟩ := exists_ordToType_embedding_of_card_ge hI'
  refine ⟨e, ?_⟩
  intro n hn t t' ht ht'
  match n, hn with
  | 0, _ => exact congrArg (c 0) (Subsingleton.elim t t')
  | (m + 1), h => exact absurd h (by omega)

/-- **Arity `≤ 1`.** Homogeneity up to arity `1` from a `κ⁺`-sized source: point pigeonhole
(`exists_large_fiber_of_small_codomain`) on the point coloring `x ↦ c 1 (singletonOE x)`
yields a `κ⁺`-sized monochromatic fiber, which re-well-orders into a `κ⁺`-suborder. -/
theorem finiteArityHomogeneousUpTo_one (κ : Cardinal.{0}) (hκ : Cardinal.aleph0 ≤ κ) :
    FiniteArityHomogeneousUpTo κ 1 := by
  intro I _ _ hI C hC c
  have hI' : Order.succ κ ≤ Cardinal.mk I := hI
  obtain ⟨b, hb⟩ := exists_large_fiber_of_small_codomain hκ hI' (hC 1)
    (fun x => c 1 (singletonOE x))
  obtain ⟨e₀⟩ := exists_ordToType_embedding_of_card_ge hb
  refine ⟨e₀.trans (OrderEmbedding.subtype _), ?_⟩
  have key : ∀ t : Fin 1 ↪o I,
      (∀ k, t k ∈ Set.range (e₀.trans (OrderEmbedding.subtype _))) → c 1 t = b := by
    intro t ht
    obtain ⟨m, hm⟩ := ht 0
    have hmem : c 1 (singletonOE (t 0)) = b := by
      rw [← hm]
      exact (e₀ m).2
    rw [orderEmbedding_fin_one_eq t]
    exact hmem
  intro n hn t t' ht ht'
  match n, hn with
  | 0, _ => exact congrArg (c 0) (Subsingleton.elim t t')
  | 1, _ => rw [key t ht, key t' ht']
  | (m + 2), h => exact absurd h (by omega)

/-- **Arity `≤ 2`.** Homogeneity up to arity `2` from a `finiteERBound κ 2`-sized source:
pack the pair color and the induced point color into `C 2 × C 1` (still of size `≤ κ`),
apply the generalized pair theorem `pairErdosRado_general_of_large`, and read the two
components back off the homogeneous suborder — arity `1` via the no-max lemma
(`exists_gt_succOrdToType` supplies a second pair element above any given point). -/
theorem finiteArityHomogeneousUpTo_two (κ : Cardinal.{0}) (hκ : Cardinal.aleph0 ≤ κ) :
    FiniteArityHomogeneousUpTo κ 2 := by
  intro I _ _ hI C hC c
  have hD : Cardinal.mk (C 2 × C 1) ≤ κ := by
    calc Cardinal.mk (C 2 × C 1)
        = Cardinal.mk (C 2) * Cardinal.mk (C 1) := by simp
      _ ≤ κ * κ := mul_le_mul' (hC 2) (hC 1)
      _ = κ := Cardinal.mul_eq_self hκ
  have hI' : Order.succ ((2 : Cardinal.{0}) ^ κ) ≤ Cardinal.mk I :=
    (pair_source_le_finiteERBound κ 0).trans hI
  obtain ⟨f, b, hb⟩ := pairErdosRado_general_of_large κ hκ hD hI'
    (fun t => (c 2 t, c 1 (singletonOE (t 0))))
  refine ⟨f, ?_⟩
  have key1 : ∀ t : Fin 1 ↪o I, (∀ k, t k ∈ Set.range f) → c 1 t = b.2 := by
    intro t ht
    obtain ⟨x, hx⟩ := ht 0
    obtain ⟨y, hxy⟩ := exists_gt_succOrdToType hκ x
    have hcp := hb hxy
    have h0 : pairEmbed (f.strictMono hxy) 0 = f x := by simp [pairEmbed]
    rw [orderEmbedding_fin_one_eq t, ← hx, ← h0]
    exact congrArg Prod.snd hcp
  have key2 : ∀ t : Fin 2 ↪o I, (∀ k, t k ∈ Set.range f) → c 2 t = b.1 := by
    intro t ht
    obtain ⟨x, hx⟩ := ht 0
    obtain ⟨y, hy⟩ := ht 1
    have ht01 : t 0 < t 1 := t.strictMono (by decide)
    have hxy : x < y := f.lt_iff_lt.mp (by rw [hx, hy]; exact ht01)
    rw [orderEmbedding_fin_two_eq_pairEmbed t (f.strictMono hxy) hx.symm hy.symm]
    exact congrArg Prod.fst (hb hxy)
  intro n hn t t' ht ht'
  match n, hn with
  | 0, _ => exact congrArg (c 0) (Subsingleton.elim t t')
  | 1, _ => rw [key1 t ht, key1 t' ht']
  | 2, _ => rw [key2 t ht, key2 t' ht']
  | (m + 3), h => exact absurd h (by omega)
