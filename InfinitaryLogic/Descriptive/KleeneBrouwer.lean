/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.SetTheory.Descriptive.Tree
import Mathlib.SetTheory.Ordinal.Rank
import Mathlib.SetTheory.Ordinal.Family
import Mathlib.Order.OrderIsoNat
import Mathlib.Data.List.Lex
import Mathlib.Data.ENat.Basic
import InfinitaryLogic.OrdinalUtil

/-!
# The Kleene–Brouwer order on a tree

Pure combinatorics on `Descriptive.tree ℕ` (prefix-closed sets of `List ℕ`), no codes: the raw
mathematics behind analytic boundedness for well-founded trees (issue #73).

* `HasInfiniteBranch T` is a **descending chain in strict extension** — a sequence of nodes each
  properly extending the previous — so "no infinite branch" is well-foundedness of `extBelow T`
  on the nose (`wellFounded_extBelow_iff_not_hasInfiniteBranch`), with no appeal to König.
* The Kleene–Brouwer order is the lexicographic order on `List ℕ∞` pulled back along
  `kbEncode x = x.map (↑) ++ [⊤]`: appending `⊤` makes every proper extension of a node *smaller*
  than the node, and among incomparable nodes the leftmost first difference decides.  Linearity is
  inherited (`kbLinearOrder`); `kbLT_of_extBelow` records that strict extension is a
  subrelation.
* `wellFounded_kbLT`: KB is well-founded on a well-founded tree.  Along a strictly KB-descending
  sequence every `k`-prefix stabilizes (`exists_stable_prefix`): once the `k`-prefix is fixed, the
  `k`-th KB head is antitone in `ℕ∞` and hence eventually constant, and it cannot stabilize at
  `⊤`, since the sequence would then repeat a list.  The stabilized prefixes form an infinite
  branch.
* `treeHeight T` is the strict supremum of the ranks of the nodes under strict extension, and
  `treeHeight_le_type` bounds it by the KB order type, through the monotonicity of
  `IsWellFounded.rank` in the relation (`InfinitaryLogic.rank_le_rank_of_imp`).

The encoding lands in `ℕ∞`, which is defined as `WithTop ℕ`; the named type is what carries the
derived `WellFoundedLT` instance the chain condition uses.
-/

namespace KleeneBrouwer

open Descriptive

/-! ## Strict extension and branches -/

/-- `x` is a proper prefix of `y`. -/
def ProperPrefix (x y : List ℕ) : Prop := x <+: y ∧ x ≠ y

/-- The "descending" direction for well-foundedness: `y` sits below `x` when it properly
extends `x`. -/
def ExtBelow (y x : List ℕ) : Prop := ProperPrefix x y

/-- An infinite branch, as a descending chain in strict extension: a sequence of nodes of `T`
each properly extending the previous one. -/
def HasInfiniteBranch (T : tree ℕ) : Prop :=
  ∃ f : ℕ → List ℕ, (∀ n, f n ∈ T) ∧ ∀ n, ProperPrefix (f n) (f (n + 1))

/-- The strict-extension relation restricted to the nodes of `T`. -/
def extBelow (T : tree ℕ) (y x : ↥T) : Prop := ExtBelow (y : List ℕ) x

theorem ProperPrefix.trans {x y z : List ℕ} (h₁ : ProperPrefix x y) (h₂ : ProperPrefix y z) :
    ProperPrefix x z := by
  refine ⟨h₁.1.trans h₂.1, fun hxz => ?_⟩
  subst hxz
  exact h₂.2 (h₁.1.eq_of_length_le h₂.1.length_le).symm

instance (T : tree ℕ) : IsStrictOrder ↥T (extBelow T) where
  irrefl _ h := h.2 rfl
  trans _ _ _ h₁ h₂ := ProperPrefix.trans h₂ h₁

theorem wellFounded_extBelow_iff_not_hasInfiniteBranch (T : tree ℕ) :
    WellFounded (extBelow T) ↔ ¬ HasInfiniteBranch T := by
  rw [RelEmbedding.wellFounded_iff_isEmpty]
  constructor
  · rintro ⟨h⟩ ⟨f, hf, hstep⟩
    exact h (RelEmbedding.natGT (fun n => (⟨f n, hf n⟩ : ↥T)) fun n => hstep n)
  · intro h
    refine ⟨fun e => h ⟨fun n => (e n : List ℕ), fun n => (e n).2, fun n => ?_⟩⟩
    exact e.map_rel_iff.mpr (Nat.lt_succ_self n)

/-! ## The Kleene–Brouwer order, via lexicographic order on `WithTop ℕ` -/

/-- Encode a node so that a proper prefix becomes *larger* than its extensions: append `⊤`. -/
def kbEncode (x : List ℕ) : List ℕ∞ := x.map (fun a : ℕ => (a : ℕ∞)) ++ [⊤]

theorem kbEncode_injective : Function.Injective kbEncode := by
  intro x y h
  have := List.append_inj_left' h (by simp)
  exact (List.map_injective_iff (f := fun a : ℕ => (a : ℕ∞))).mpr
    (fun _ _ hab => ENat.natCast_inj.mp hab) this

private theorem kbEncode_append (p r : List ℕ) :
    kbEncode (p ++ r) = p.map (fun a : ℕ => (a : ℕ∞)) ++ kbEncode r := by
  simp [kbEncode]

/-- The Kleene–Brouwer order: proper extensions come first, then leftmost-first differences. -/
def KBLT (x y : List ℕ) : Prop := kbEncode x < kbEncode y

instance : DecidableRel KBLT := fun x y => inferInstanceAs (Decidable (kbEncode x < kbEncode y))

instance : DecidableRel KBLT := fun x y => inferInstanceAs (Decidable (kbEncode x < kbEncode y))

instance : DecidableRel KBLT := fun x y => inferInstanceAs (Decidable (kbEncode x < kbEncode y))

/-- The KB order on the nodes of `T`. -/
def kbLT (T : tree ℕ) (x y : ↥T) : Prop := KBLT (x : List ℕ) y

/-- The nodes of `T`, linearly ordered by KB (pulled back from `List ℕ∞`). -/
@[instance_reducible] noncomputable def kbLinearOrder (T : tree ℕ) : LinearOrder ↥T :=
  LinearOrder.lift' (fun x : ↥T => kbEncode (x : List ℕ))
    (fun _ _ h => Subtype.ext (kbEncode_injective h))

theorem kbLT_iff (T : tree ℕ) (x y : ↥T) :
    kbLT T x y ↔ @LT.lt ↥T (kbLinearOrder T).toLT x y := Iff.rfl

/-! ## Proper extensions are KB-below -/

theorem kbEncode_lt_of_properPrefix {x y : List ℕ} (h : ProperPrefix x y) :
    kbEncode y < kbEncode x := by
  obtain ⟨⟨t, rfl⟩, hne⟩ := h
  have ht : t ≠ [] := by rintro rfl; exact hne (by simp)
  obtain ⟨a, t', rfl⟩ := List.exists_cons_of_ne_nil ht
  simp only [kbEncode, List.map_append, List.map_cons, List.append_assoc, List.cons_append]
  show List.Lex (· < ·) _ _
  apply List.Lex.append_left
  exact List.Lex.rel (ENat.natCast_lt_top a)

theorem kbLT_of_extBelow (T : tree ℕ) {y x : ↥T} (h : extBelow T y x) : kbLT T y x :=
  kbEncode_lt_of_properPrefix h

/-! ## KB is well-founded on a well-founded tree -/

/-- `Lex` is invariant under a common left factor (for irreflexive `r`). -/
private theorem lex_append_left_iff {α : Type*} {r : α → α → Prop} [Std.Irrefl r] :
    ∀ (p l₁ l₂ : List α), List.Lex r (p ++ l₁) (p ++ l₂) ↔ List.Lex r l₁ l₂
  | [], _, _ => Iff.rfl
  | a :: p, l₁, l₂ => by
    simp only [List.cons_append, List.lex_cons_iff]
    exact lex_append_left_iff p l₁ l₂

/-- The KB head of a tail: `⊤` for the empty tail, the first entry otherwise. -/
private def kbHead (r : List ℕ) : ℕ∞ := (kbEncode r).headD ⊤

private theorem kbEncode_eq_cons (r : List ℕ) : kbEncode r = kbHead r :: (kbEncode r).tail := by
  cases r <;> simp [kbEncode, kbHead]

private theorem kbHead_eq_top_iff (r : List ℕ) : kbHead r = ⊤ ↔ r = [] := by
  cases r <;> simp [kbHead, kbEncode]

private theorem exists_cons_of_kbHead_eq_coe (r : List ℕ) (a : ℕ) (h : kbHead r = a) :
    ∃ r', r = a :: r' := by
  cases r with
  | nil => exact absurd h (by simp [kbHead, kbEncode])
  | cons b r' =>
    have hb : (b : ℕ∞) = a := by simpa [kbHead, kbEncode] using h
    have hba : b = a := ENat.natCast_inj.mp hb
    exact ⟨r', by rw [hba]⟩

/-- Along a strictly KB-descending sequence whose `k`-prefixes agree, the `k`-th KB heads are
antitone. -/
private theorem kbHead_drop_antitone {f : ℕ → List ℕ} (hf : ∀ n, KBLT (f (n + 1)) (f n)) {k : ℕ}
    {p : List ℕ} {N : ℕ} (hp : ∀ n, N ≤ n → (f n).take k = p) :
    Antitone fun m => kbHead ((f (N + m)).drop k) := by
  refine antitone_nat_of_succ_le fun m => ?_
  have h := hf (N + m)
  unfold KBLT at h
  rw [← List.take_append_drop k (f (N + m + 1)), ← List.take_append_drop k (f (N + m)),
    hp _ (by omega), hp _ (by omega), kbEncode_append, kbEncode_append] at h
  have h' : kbEncode ((f (N + m + 1)).drop k) < kbEncode ((f (N + m)).drop k) :=
    (lex_append_left_iff _ _ _).mp h
  rw [kbEncode_eq_cons ((f (N + m + 1)).drop k), kbEncode_eq_cons ((f (N + m)).drop k)] at h'
  exact List.head_le_of_lt h'

/-- **Prefix stabilization**: along a strictly KB-descending sequence in a tree, every `k`-prefix
is eventually constant, with full length `k`. -/
theorem exists_stable_prefix {f : ℕ → List ℕ} (hf : ∀ n, KBLT (f (n + 1)) (f n)) :
    ∀ k : ℕ, ∃ (p : List ℕ) (N : ℕ), p.length = k ∧ ∀ n, N ≤ n → (f n).take k = p
  | 0 => ⟨[], 0, rfl, fun _ _ => List.take_zero⟩
  | k + 1 => by
    obtain ⟨p, N, hlen, hp⟩ := exists_stable_prefix hf k
    obtain ⟨M, hM⟩ := WellFoundedLT.antitone_chain_condition (kbHead_drop_antitone hf hp)
    -- the stabilized head cannot be `⊤`: the sequence would then be constant
    rcases hv : kbHead ((f (N + M)).drop k) with _ | a
    · exfalso
      have h1 : (f (N + M)).drop k = [] := (kbHead_eq_top_iff _).mp hv
      have h2 : (f (N + M + 1)).drop k = [] := by
        have := hM (M + 1) (by omega)
        rw [hv, show N + (M + 1) = N + M + 1 by omega] at this
        exact (kbHead_eq_top_iff _).mp this.symm
      have e1 : f (N + M) = p := by
        rw [← List.take_append_drop k (f (N + M)), hp _ (by omega), h1, List.append_nil]
      have e2 : f (N + M + 1) = p := by
        rw [← List.take_append_drop k (f (N + M + 1)), hp _ (by omega), h2, List.append_nil]
      have := hf (N + M)
      rw [e1, e2] at this
      exact lt_irrefl _ this
    · refine ⟨p ++ [a], N + M, by simp [hlen], fun n hn => ?_⟩
      have hhead : kbHead ((f n).drop k) = a := by
        have := hM (n - N) (by omega)
        rw [hv, show N + (n - N) = n by omega] at this
        exact this.symm
      obtain ⟨r', hr'⟩ := exists_cons_of_kbHead_eq_coe _ _ hhead
      rw [← List.take_append_drop k (f n), hp n (by omega), hr', List.take_append,
        List.take_of_length_le (by omega), hlen, Nat.add_sub_cancel_left, List.take_succ_cons,
        List.take_zero]

instance (T : tree ℕ) : IsStrictOrder ↥T (kbLT T) where
  irrefl x h := lt_irrefl (kbEncode (x : List ℕ)) h
  trans _ _ _ h₁ h₂ := lt_trans (α := List ℕ∞) h₁ h₂

/-- **Kleene–Brouwer is well-founded on a well-founded tree.** -/
theorem wellFounded_kbLT (T : tree ℕ) (hT : WellFounded (extBelow T)) :
    WellFounded (kbLT T) := by
  rw [RelEmbedding.wellFounded_iff_isEmpty]
  refine ⟨fun e => ?_⟩
  have hf : ∀ n, KBLT ((e (n + 1) : ↥T) : List ℕ) (e n : ↥T) :=
    fun n => e.map_rel_iff.mpr (Nat.lt_succ_self n)
  have hstab := exists_stable_prefix (f := fun n => ((e n : ↥T) : List ℕ)) hf
  choose p N hlen hp using hstab
  -- the stabilized prefixes form an infinite branch
  refine (wellFounded_extBelow_iff_not_hasInfiniteBranch T).mp hT ⟨p, fun k => ?_, fun k => ?_⟩
  · rw [← hp k (N k) le_rfl]
    exact Tree.take_mem (e (N k))
  · have hk : ((e (N k + N (k + 1)) : ↥T) : List ℕ).take k = p k := hp k _ (by omega)
    have hk1 : ((e (N k + N (k + 1)) : ↥T) : List ℕ).take (k + 1) = p (k + 1) :=
      hp (k + 1) _ (by omega)
    have hpk : p k = (p (k + 1)).take k := by
      rw [← hk, ← hk1, List.take_take, Nat.min_eq_left (by omega)]
    refine ⟨?_, fun h => ?_⟩
    · rw [hpk]; exact List.take_prefix _ _
    · have := congrArg List.length h
      rw [hlen k, hlen (k + 1)] at this
      omega

/-- **KB is a well-order on a well-founded tree**: the linear order from the encoding plus
well-foundedness. -/
theorem isWellOrder_kbLT (T : tree ℕ) (hT : WellFounded (extBelow T)) :
    IsWellOrder ↥T (kbLT T) :=
  haveI : Std.Trichotomous (kbLT T) :=
    ⟨fun _ _ h₁ h₂ => Subtype.ext (kbEncode_injective
      (le_antisymm (not_lt.mp h₂) (not_lt.mp h₁)))⟩
  haveI : IsWellFounded ↥T (kbLT T) := ⟨wellFounded_kbLT T hT⟩
  IsWellOrder.mk

/-- The height of the tree: the strict supremum of the ranks of its nodes under strict
extension. -/
noncomputable def treeHeight (T : tree ℕ) [IsWellFounded ↥T (extBelow T)] : Ordinal :=
  ⨆ x : ↥T, Order.succ (IsWellFounded.rank (extBelow T) x)

/-- Given that KB is a well-order on `T`, the height is at most its order type. -/
theorem treeHeight_le_type (T : tree ℕ) [IsWellFounded ↥T (extBelow T)]
    [IsWellOrder ↥T (kbLT T)] : treeHeight T ≤ Ordinal.type (kbLT T) := by
  refine Ordinal.iSup_le fun x => ?_
  rw [Order.succ_le_iff]
  calc IsWellFounded.rank (extBelow T) x
      ≤ IsWellFounded.rank (kbLT T) x :=
        InfinitaryLogic.rank_le_rank_of_imp (fun _ _ => kbLT_of_extBelow T) x
    _ = Ordinal.typein (kbLT T) x := by rw [IsWellFounded.rank_eq_typein]
    _ < Ordinal.type (kbLT T) := Ordinal.typein_lt_type _ _

end KleeneBrouwer
