/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Scott.OrbitRank

/-!
# Nullary tags

Expanding a language by countably many **nullary** relation symbols `P_n`, interpreted by a set
`X ⊆ ℕ` (`P_n` holds iff `n ∈ X`), the same way in every structure considered.  The signature
`L.withTags` is fixed independently of `X`; only the interpretation varies.

* `tagLang`: the language with nullary symbols indexed by `ℕ` and nothing else.
* `L.withTags := L.sum tagLang`.
* `Tagged X M`: the structure `M` expanded by the tags `X` (a type synonym carrying the
  expanded structure).

**Semantic invariance**, for expansions with **matching** tags:

* `bfEquiv_tagged_iff`: back-and-forth equivalence is preserved and reflected at every level.
* `Equiv.toTagged`, `Equiv.ofTagged`, `taggedEquivEquiv`: isomorphisms (hence automorphisms)
  are the same before and after tagging.
* `orbitRank_tagged`, `internalScottRank_tagged`: the orbit rank of every tuple and the
  internal Scott rank are unchanged.  (`Tagged X M` carries `M`'s own `L`-structure, so the
  right-hand sides are the untagged ranks; the type synonym keeps both sides syntactically
  well-typed at every transparency.)

With **differing** tags the expansions are already inequivalent at level `0`
(`not_bfEquiv_tagged_of_ne`): a nullary atom distinguishes them, on any carrier, including the
empty one.

Nothing here is effective: the diagram reductions `D(M̂) ≡_T X` and `A ≅ M̂ → X ≤_T D(A)` are
downstream statements about presentations, not about these semantic invariances.
-/

namespace FirstOrder.Language

universe u v w w'

/-! ### The tag language -/

/-- Tag symbols: countably many at arity `0`, none elsewhere. -/
def TagSym : ℕ → Type
  | 0 => ℕ
  | _ + 1 => Empty

/-- The language of nullary tags. -/
def tagLang : Language.{0, 0} := ⟨fun _ => Empty, TagSym⟩

instance : tagLang.IsRelational := fun _ => inferInstanceAs (IsEmpty Empty)

/-- A language with nullary tags. -/
abbrev withTags (L : Language.{u, v}) : Language := L.sum tagLang

instance (L : Language.{u, v}) [L.IsRelational] : (withTags L).IsRelational :=
  inferInstanceAs (L.sum tagLang).IsRelational

/-! ### Tagged structures -/

/-- The structure `M` expanded by the tags `X`. -/
def Tagged (_X : Set ℕ) (M : Type w) : Type w := M

variable {L : Language.{u, v}} {M : Type w} {N : Type w'} [L.Structure M] [L.Structure N]

instance instTaggedBase (X : Set ℕ) : L.Structure (Tagged X M) := inferInstanceAs (L.Structure M)

/-- The tags: `P_n` holds iff `n ∈ X`; the tuple is ignored. -/
instance instTaggedTags (X : Set ℕ) : tagLang.Structure (Tagged X M) where
  funMap f _ := (f : Empty).elim
  RelMap {n} t _ := match n, t with
    | 0, t => t ∈ X
    | _ + 1, t => (t : Empty).elim

/-! ### Atoms -/

/-- Tagged atomic agreement is atomic agreement, for matching tags. -/
theorem sameAtomicType_tagged_iff (X : Set ℕ) {n : ℕ} (a : Fin n → Tagged X M)
    (b : Fin n → Tagged X N) :
    SameAtomicType (L := withTags L) a b ↔
      SameAtomicType (L := L) (M := Tagged X M) (N := Tagged X N) a b := by
  constructor
  · intro h idx
    cases idx with
    | eq i j => exact h (AtomicIdx.eq i j)
    | rel R f => exact h (AtomicIdx.rel (Sum.inl R) f)
  · intro h idx
    cases idx with
    | eq i j => exact h (AtomicIdx.eq i j)
    | rel R f =>
      cases R with
      | inl R => exact h (AtomicIdx.rel R f)
      | inr t =>
        rename_i l
        cases l with
        | zero => exact Iff.rfl
        | succ l => exact (t : Empty).elim

/-! ### Back-and-forth equivalence -/

/-- **Back-and-forth equivalence is preserved and reflected by tagging with matching tags**, at
every level. -/
theorem bfEquiv_tagged_iff (X : Set ℕ) (α : Ordinal) :
    ∀ {n : ℕ} (a : Fin n → Tagged X M) (b : Fin n → Tagged X N),
      BFEquiv (L := withTags L) α n a b ↔
        BFEquiv (L := L) (M := Tagged X M) (N := Tagged X N) α n a b := by
  induction α using Ordinal.limitRecOn with
  | zero =>
    intro n a b
    rw [BFEquiv.zero, BFEquiv.zero]
    exact sameAtomicType_tagged_iff X a b
  | add_one β ih =>
    intro n a b
    rw [← Order.succ_eq_add_one, BFEquiv.succ, BFEquiv.succ]
    refine and_congr (ih a b) (and_congr ?_ ?_)
    · exact forall_congr' fun m => exists_congr fun m' => ih _ _
    · exact forall_congr' fun m' => exists_congr fun m => ih _ _
  | limit β hβ ih =>
    intro n a b
    rw [BFEquiv.limit β hβ, BFEquiv.limit β hβ]
    exact forall_congr' fun γ => forall_congr' fun hγ => ih γ hγ a b

/-- With differing tags, the expansions are inequivalent already at level `0`, on any carrier. -/
theorem not_bfEquiv_tagged_of_ne {X Y : Set ℕ} {k : ℕ} (hk : (k ∈ X) ≠ (k ∈ Y)) {n : ℕ}
    (a : Fin n → Tagged X M) (b : Fin n → Tagged Y N) :
    ¬ BFEquiv (L := withTags L) 0 n a b := by
  intro h
  have h0 := (BFEquiv.zero _ _).mp h
    (AtomicIdx.rel (Sum.inr (show tagLang.Relations 0 from k)) Fin.elim0)
  simp only [AtomicIdx.holds] at h0
  exact hk (propext (show (k ∈ X) ↔ (k ∈ Y) from h0))

/-! ### Isomorphisms -/

/-- An isomorphism is one of the tagged expansions with matching tags. -/
def Equiv.toTagged (X : Set ℕ) (f : M ≃[L] N) : Tagged X M ≃[withTags L] Tagged X N where
  toEquiv := f.toEquiv
  map_fun' := by
    intro n F x
    cases F with
    | inl F => exact f.map_fun F x
    | inr F => exact (F : Empty).elim
  map_rel' := by
    intro n R x
    cases R with
    | inl R => exact f.map_rel R x
    | inr t =>
      cases n with
      | zero => exact Iff.rfl
      | succ l => exact (t : Empty).elim

/-- An isomorphism of tagged expansions is an isomorphism of the underlying structures. -/
def Equiv.ofTagged (X : Set ℕ) (g : Tagged X M ≃[withTags L] Tagged X N) : M ≃[L] N where
  toEquiv := g.toEquiv
  map_fun' := fun {_} F x => g.map_fun (Sum.inl F) x
  map_rel' := fun {_} R x => g.map_rel (Sum.inl R) x

/-- **Isomorphisms are unchanged by tagging**: the two notions correspond bijectively. -/
def taggedEquivEquiv (X : Set ℕ) : (Tagged X M ≃[withTags L] Tagged X N) ≃ (M ≃[L] N) where
  toFun := Equiv.ofTagged X
  invFun := Equiv.toTagged X
  left_inv := fun _ => Language.Equiv.ext fun _ => rfl
  right_inv := fun _ => Language.Equiv.ext fun _ => rfl

@[simp] theorem Equiv.toTagged_apply (X : Set ℕ) (f : M ≃[L] N) (x : M) :
    Equiv.toTagged X f x = f x := rfl

@[simp] theorem Equiv.ofTagged_apply (X : Set ℕ) (g : Tagged X M ≃[withTags L] Tagged X N)
    (x : M) : Equiv.ofTagged X g x = g x := rfl

/-! ### Ranks -/

/-- **Orbit ranks are unchanged by tagging.** -/
theorem orbitRank_tagged (X : Set ℕ) {n : ℕ} (a : Fin n → Tagged X M) :
    orbitRank (L := withTags L) a = orbitRank (L := L) (M := Tagged X M) a := by
  unfold orbitRank
  congr 1
  ext α
  simp only [orbitStable, Set.mem_ofPred_eq]
  exact forall_congr' fun b => imp_congr (bfEquiv_tagged_iff X α a b)
    (forall_congr' fun γ => bfEquiv_tagged_iff X γ a b)

/-- **Internal Scott ranks are unchanged by tagging.** -/
theorem internalScottRank_tagged (X : Set ℕ) :
    internalScottRank (L := withTags L) (Tagged X M) =
      internalScottRank (L := L) (Tagged X M) := by
  unfold internalScottRank
  congr 1
  funext x
  rw [orbitRank_tagged]

end FirstOrder.Language
