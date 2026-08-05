/-
SPIKE — the generalized Scott sentence: a single formula characterizing potential
isomorphism of ARBITRARY structures.

Built from the carrier-general Scott approximants (`ScottMigration`). The chain:

1. `alls`: iterated universal closure on bound variables (no relabeling, as everywhere in
   this development).
2. `PotentialIso.exists_left`: every finite `N`-tuple is matched through a potential
   isomorphism (iterated `back`).
3. `PotentialIso.family_bfEquiv`: family members are `BFEquiv` at every level — reproved
   here WITHOUT the vestigial countable-language hypothesis of the production version.
4. `bfStab`: the stabilization ordinal, by the least-failure-level supremum;
   `bfEquiv_bfStab_iff_all`: equivalence at `bfStab` already means equivalence everywhere.
5. `scottSentenceAt`: the sentence  σ_{α,∅} ⊓ ⋀_{(n,a)} ∀ⁿx̄ (σ_{α,a}(x̄) → σ_{α+1,a}(x̄)).
6. Forward (`potentialIso_of_realize_scottSentenceAt`): satisfaction implies potential
   isomorphism — for EVERY ordinal `α`, with no stabilization hypothesis.
7. Backward (`realize_scottSentenceAt_of_potentialIso`): under `M`-self-stability at `α`
   (which `α := bfStab L M M` provides), potential isomorphism implies satisfaction — via
   `exists_left`, `BFEquiv.symm`/`.trans`, and self-stability.
8. **Headline** (`realize_scottSentence_iff_potentialIso`): at `α := bfStab L M M`,
   `N ⊨ σ_M ↔ Nonempty (PotentialIso L M N)` — for arbitrary structures, arbitrary
   languages, no countability anywhere.

Build with:  lake build ScottSentence    (the Spike lib is not a CI target)
-/
import ScottMigration

universe u v uι w w'

namespace FirstOrder.Language

open BoundedFormulaIdx Fin

variable {L : Language.{u, v}}

/-! ## 1. Iterated universal closure on bound variables -/

namespace BoundedFormulaIdx

variable {ι : Type uι}

/-- Universal closure of all bound variables. -/
def alls : ∀ {n : ℕ}, L.BoundedFormulaIdx ι Empty n → L.BoundedFormulaIdx ι Empty 0
  | 0, φ => φ
  | _ + 1, φ => alls φ.all

theorem realize_alls {N : Type w'} [L.Structure N] :
    ∀ {n : ℕ} (φ : L.BoundedFormulaIdx ι Empty n),
      (alls φ).Realize Empty.elim (Fin.elim0 : Fin 0 → N) ↔
        ∀ b : Fin n → N, φ.Realize Empty.elim b := by
  intro n
  induction n with
  | zero =>
    intro φ
    constructor
    · intro h b
      have hb : b = Fin.elim0 := funext fun i => i.elim0
      rwa [hb]
    · intro h
      exact h _
  | succ n ih =>
    intro φ
    rw [show (alls φ : L.BoundedFormulaIdx ι Empty 0) = alls φ.all from rfl, ih]
    constructor
    · intro h b
      have hall := h (Fin.init b)
      rw [realize_all] at hall
      have h2 := hall (b (Fin.last n))
      rwa [Fin.snoc_init_self] at h2
    · intro h b
      rw [realize_all]
      intro y
      exact h (Fin.snoc b y)

end BoundedFormulaIdx

/-! ## 2–3. Potential-isomorphism plumbing, countability-free -/

section PotentialIsoPlumbing

variable [L.IsRelational] {M : Type w} {N : Type w'} [L.Structure M] [L.Structure N]

/-- Every finite `N`-tuple is matched to an `M`-tuple through a potential isomorphism, by
iterating `back` along the tuple. -/
theorem PotentialIso.exists_left (P : PotentialIso L M N) :
    ∀ {n : ℕ} (b : Fin n → N),
      ∃ a : Fin n → M, (⟨n, a, b⟩ : Σ n : ℕ, (Fin n → M) × (Fin n → N)) ∈ P.family := by
  intro n
  induction n with
  | zero =>
    intro b
    refine ⟨Fin.elim0, ?_⟩
    have hb : b = Fin.elim0 := funext fun i => i.elim0
    rw [hb]
    exact P.empty_mem
  | succ n ih =>
    intro b
    obtain ⟨a', ha'⟩ := ih (Fin.init b)
    obtain ⟨m, hm⟩ := P.back _ ha' (b (Fin.last n))
    refine ⟨Fin.snoc a' m, ?_⟩
    rwa [Fin.snoc_init_self] at hm

/-- Family members of a potential isomorphism are `BFEquiv` at every level. Identical to the
production `potentialIso_family_BFEquiv`, but with the vestigial countable-language
hypothesis dropped and heterogeneous structure universes allowed. -/
theorem PotentialIso.family_bfEquiv (P : PotentialIso L M N) (α : Ordinal)
    {n : ℕ} {a : Fin n → M} {b : Fin n → N}
    (hab : (⟨n, a, b⟩ : Σ n : ℕ, (Fin n → M) × (Fin n → N)) ∈ P.family) :
    BFEquiv (L := L) α n a b := by
  induction α using Ordinal.limitRecOn generalizing n a b with
  | zero => exact (BFEquiv.zero a b).mpr (P.compatible _ hab)
  | add_one β ih =>
    rw [← Order.succ_eq_add_one, BFEquiv.succ]
    refine ⟨ih hab, ?_, ?_⟩
    · intro m
      obtain ⟨n', hn'⟩ := P.forth _ hab m
      exact ⟨n', ih hn'⟩
    · intro n'
      obtain ⟨m, hm⟩ := P.back _ hab n'
      exact ⟨m, ih hm⟩
  | limit β hβ ih =>
    rw [BFEquiv.limit β hβ]
    exact fun γ hγ => ih γ hγ hab

end PotentialIsoPlumbing

/-! ## 4. The stabilization ordinal -/

section Stabilization

variable [L.IsRelational] {M : Type w} {N : Type w'} [L.Structure M] [L.Structure N]

variable (L M N) in
/-- The stabilization ordinal of the back-and-forth hierarchy between `M` and `N`: the
supremum, over all triples that fail somewhere, of their least failure level. -/
noncomputable def bfStab
    [Small.{uι} ((n : ℕ) × ((Fin n → M) × (Fin n → N)))] : Ordinal.{uι} :=
  ⨆ x : {x : (n : ℕ) × ((Fin n → M) × (Fin n → N)) //
      ∃ α : Ordinal.{uι}, ¬BFEquiv (L := L) α x.1 x.2.1 x.2.2},
    sInf {α : Ordinal.{uι} | ¬BFEquiv (L := L) α x.1.1 x.1.2.1 x.1.2.2}

/-- **Stabilization**: back-and-forth equivalence at the stabilization level already implies
equivalence at every level. The equivalence hierarchy of an arbitrary pair of structures
collapses at a set-sized ordinal. -/
omit [L.IsRelational] in
theorem bfEquiv_bfStab_iff_all
    [Small.{uι} ((n : ℕ) × ((Fin n → M) × (Fin n → N)))]
    {n : ℕ} {a : Fin n → M} {b : Fin n → N} :
    BFEquiv (L := L) (bfStab.{u, v, uι} L M N) n a b ↔
      ∀ β : Ordinal.{uι}, BFEquiv (L := L) β n a b := by
  constructor
  · intro h β
    by_contra hβ
    have hne : {α : Ordinal.{uι} | ¬BFEquiv (L := L) α n a b}.Nonempty := ⟨β, hβ⟩
    have hfail : ¬BFEquiv (L := L) (sInf {α : Ordinal.{uι} | ¬BFEquiv (L := L) α n a b})
        n a b := csInf_mem hne
    have hle : sInf {α : Ordinal.{uι} | ¬BFEquiv (L := L) α n a b} ≤
        bfStab.{u, v, uι} L M N :=
      le_ciSup (f := fun x : {x : (n : ℕ) × ((Fin n → M) × (Fin n → N)) //
          ∃ α : Ordinal.{uι}, ¬BFEquiv (L := L) α x.1 x.2.1 x.2.2} =>
        sInf {α : Ordinal.{uι} | ¬BFEquiv (L := L) α x.1.1 x.1.2.1 x.1.2.2})
        Ordinal.bddAbove_of_small ⟨⟨n, a, b⟩, β, hβ⟩
    exact hfail (BFEquiv.monotone hle h)
  · intro h
    exact h _

/-- Self-stability of `M` at its own stabilization ordinal: level-`bfStab` equivalence of two
`M`-tuples propagates to the successor level. This is the hypothesis the backward direction
of the Scott sentence needs. -/
omit [L.IsRelational] in
theorem bfEquiv_bfStab_succ [Small.{uι} ((n : ℕ) × ((Fin n → M) × (Fin n → M)))]
    {n : ℕ} {a a' : Fin n → M}
    (h : BFEquiv (L := L) (bfStab.{u, v, uι} L M M) n a a') :
    BFEquiv (L := L) (bfStab.{u, v, uι} L M M + 1) n a a' :=
  (bfEquiv_bfStab_iff_all.mp h) _

end Stabilization

/-! ## 5. The generalized Scott sentence -/

section ScottSentence

variable [L.IsRelational] {M : Type w} [L.Structure M] {ι : Type uι}

variable (cM : IndexCoding M ι) (cA : ∀ k : ℕ, IndexCoding (L.AtomicIdx k) ι)
  {α : Ordinal.{uι}}
  (cOrd : ∀ β : Ordinal.{uι}, β ≤ α + 1 → IndexCoding {γ : Ordinal.{uι} // γ < β} ι)
  (cT : IndexCoding ((n : ℕ) × (Fin n → M)) ι)

/-- The generalized Scott sentence of `M` at level `α`:

  σ_{α,∅}  ⊓  ⋀_{(n,a)} ∀ⁿx̄ (σ_{α,a}(x̄) → σ_{α+1,a}(x̄))

The outer conjunction runs along an explicit coding of the tuple family
`Σ n, (Fin n → M)`; the universal prefix is `alls` on bound variables. -/
noncomputable def scottSentenceAt : L.BoundedFormulaIdx ι Empty 0 :=
  scottApproxAt cM cA cOrd α (le_of_lt (Order.lt_succ α)) 0 Fin.elim0 ⊓
    iInfAlong cT fun p =>
      alls ((scottApproxAt cM cA cOrd α (le_of_lt (Order.lt_succ α)) p.1 p.2).imp
        (scottApproxAt cM cA cOrd (α + 1) le_rfl p.1 p.2))

variable {N : Type w'} [L.Structure N]

/-- **Forward, for EVERY level `α`**: satisfaction of the generalized Scott sentence yields a
potential isomorphism. The family is level-`α` equivalence; `forth`/`back` come from the
implication conjuncts, with no stabilization hypothesis. -/
theorem potentialIso_of_realize_scottSentenceAt
    (h : (scottSentenceAt cM cA cOrd cT).Realize Empty.elim (Fin.elim0 : Fin 0 → N)) :
    Nonempty (PotentialIso L M N) := by
  have h0α : (0 : Ordinal.{uι}) ≤ α := Ordinal.bot_eq_zero ▸ bot_le
  simp only [scottSentenceAt, realize_inf, realize_iInfAlong] at h
  obtain ⟨hroot, hconj⟩ := h
  refine ⟨{
    family := { p : Σ n : ℕ, (Fin n → M) × (Fin n → N) |
      BFEquiv (L := L) α p.1 p.2.1 p.2.2 }
    empty_mem := ?_
    compatible := ?_
    forth := ?_
    back := ?_ }⟩
  · exact (realize_scottApproxAt_iff_BFEquiv cM cA cOrd α _ _ _).mp hroot
  · intro p hp
    exact (BFEquiv.zero p.2.1 p.2.2).mp (BFEquiv.monotone h0α hp)
  · rintro ⟨n, a, b⟩ hab m
    have hc := hconj ⟨n, a⟩
    rw [realize_alls] at hc
    have himp := hc b
    rw [realize_imp] at himp
    have h1 : BFEquiv (L := L) (α + 1) n a b :=
      (realize_scottApproxAt_iff_BFEquiv cM cA cOrd (α + 1) le_rfl a b).mp
        (himp ((realize_scottApproxAt_iff_BFEquiv cM cA cOrd α _ a b).mpr hab))
    obtain ⟨-, hforth, -⟩ := (BFEquiv.succ (L := L) α a b).mp h1
    obtain ⟨n', hn'⟩ := hforth m
    exact ⟨n', hn'⟩
  · rintro ⟨n, a, b⟩ hab n'
    have hc := hconj ⟨n, a⟩
    rw [realize_alls] at hc
    have himp := hc b
    rw [realize_imp] at himp
    have h1 : BFEquiv (L := L) (α + 1) n a b :=
      (realize_scottApproxAt_iff_BFEquiv cM cA cOrd (α + 1) le_rfl a b).mp
        (himp ((realize_scottApproxAt_iff_BFEquiv cM cA cOrd α _ a b).mpr hab))
    obtain ⟨-, -, hback⟩ := (BFEquiv.succ (L := L) α a b).mp h1
    obtain ⟨m, hm⟩ := hback n'
    exact ⟨m, hm⟩

/-- **Backward, under `M`-self-stability at `α`**: a potential isomorphism forces
satisfaction of the generalized Scott sentence. The tuple conjuncts are verified by matching
`b` through the potential isomorphism (`exists_left`), transporting with
`BFEquiv.symm`/`.trans`, and applying self-stability. -/
theorem realize_scottSentenceAt_of_potentialIso (P : PotentialIso L M N)
    (hstab : ∀ (n : ℕ) (a a' : Fin n → M),
      BFEquiv (L := L) α n a a' → BFEquiv (L := L) (α + 1) n a a') :
    (scottSentenceAt cM cA cOrd cT).Realize Empty.elim (Fin.elim0 : Fin 0 → N) := by
  simp only [scottSentenceAt, realize_inf, realize_iInfAlong]
  refine ⟨(realize_scottApproxAt_iff_BFEquiv cM cA cOrd α _ _ _).mpr
    (P.family_bfEquiv α P.empty_mem), ?_⟩
  intro p
  rw [realize_alls]
  intro b
  rw [realize_imp]
  intro hb
  have hab : BFEquiv (L := L) α p.1 p.2 b :=
    (realize_scottApproxAt_iff_BFEquiv cM cA cOrd α _ p.2 b).mp hb
  obtain ⟨a', ha'⟩ := P.exists_left b
  have hall : ∀ β : Ordinal.{uι}, BFEquiv (L := L) β p.1 a' b :=
    fun β => P.family_bfEquiv β ha'
  have haa' : BFEquiv (L := L) α p.1 p.2 a' := BFEquiv.trans hab (BFEquiv.symm (hall α))
  have haa'' : BFEquiv (L := L) (α + 1) p.1 p.2 a' := hstab _ _ _ haa'
  exact (realize_scottApproxAt_iff_BFEquiv cM cA cOrd (α + 1) le_rfl p.2 b).mpr
    (BFEquiv.trans haa'' (hall (α + 1)))

end ScottSentence

/-! ## 8. The headline: `N ⊨ σ_M ↔ M ≅p N`, for arbitrary structures -/

section Headline

variable [L.IsRelational] {M : Type w} [L.Structure M] {ι : Type uι}

/-- **The generalized Scott sentence theorem**: with the level chosen as `M`'s own
stabilization ordinal, satisfaction of the single sentence `scottSentenceAt` characterizes
potential isomorphism with `M` — for arbitrary structures over arbitrary relational
languages, with no countability hypotheses and no `ω₁` bound. Combined with
`karp_theorem_at`, satisfaction of one formula characterizes full `L∞ω`-equivalence. -/
theorem realize_scottSentence_iff_potentialIso
    [Small.{uι} ((n : ℕ) × ((Fin n → M) × (Fin n → M)))]
    (cM : IndexCoding M ι) (cA : ∀ k : ℕ, IndexCoding (L.AtomicIdx k) ι)
    (cOrd : ∀ β : Ordinal.{uι}, β ≤ bfStab.{u, v, uι} L M M + 1 →
      IndexCoding {γ : Ordinal.{uι} // γ < β} ι)
    (cT : IndexCoding ((n : ℕ) × (Fin n → M)) ι)
    {N : Type w'} [L.Structure N] :
    (scottSentenceAt (α := bfStab.{u, v, uι} L M M) cM cA cOrd cT).Realize
        Empty.elim (Fin.elim0 : Fin 0 → N) ↔
      Nonempty (PotentialIso L M N) :=
  ⟨potentialIso_of_realize_scottSentenceAt cM cA cOrd cT,
   fun ⟨P⟩ => realize_scottSentenceAt_of_potentialIso cM cA cOrd cT P
     (fun _ _ _ h => bfEquiv_bfStab_succ h)⟩

end Headline

end FirstOrder.Language
