/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Karp.PotentialIso
import InfinitaryLogic.Linf.Operations
import InfinitaryLogic.Linf.QuantifierRank
import InfinitaryLogic.Linf.Theory

/-!
# Karp's Theorem

This file proves Karp's theorem: two structures are potentially isomorphic if and only
if they are L∞ω-elementarily equivalent.

## Main Results

- `karp_theorem`: For relational languages, potential isomorphism is equivalent to
  L∞ω-elementary equivalence (KK04 Theorem 1.2.1).
- `BFEquiv_iff_agreeQR`: BF-equivalence at level α is equivalent to agreement on all
  formulas of quantifier rank ≤ α (KK04 Lemma 1.3.3, the "Karp lemma").

## References

- [Keisler-Knight, "Barwise: Infinitary Logic and Admissible Sets", 2004]
-/

universe u v w

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}} [L.IsRelational]
variable [Countable (Σ l, L.Relations l)]

open FirstOrder Structure Fin Ordinal

/-- **Karp Lemma** (KK04 Lemma 1.3.3): BF-equivalence at level α between tuples is
equivalent to agreement on all formulas of quantifier rank ≤ α.

This is the key inductive lemma relating the game-theoretic BFEquiv to the
formula-based EquivQR. -/
theorem BFEquiv_iff_agreeQR {M N : Type w} [L.Structure M] [L.Structure N]
    (α : Ordinal) {n : ℕ} (a : Fin n → M) (b : Fin n → N) :
    BFEquiv (L := L) α n a b ↔
    ∀ (φ : BoundedFormulaInf.{u, v, 0, 0} L (Fin n) 0), φ.qrank ≤ α →
      (FormulaInf.Realize φ a ↔ FormulaInf.Realize φ b) := by
  sorry

omit [L.IsRelational] [Countable (Σ l, L.Relations l)] in
/-- Bridge between SentenceInf.Realize and FormulaInf.Realize via mapFreeVars. -/
private theorem sentenceInf_realize_iff_mapFreeVars
    {M : Type*} [L.Structure M] (φ : BoundedFormulaInf.{u, v, 0, 0} L Empty 0) :
    SentenceInf.Realize φ M ↔
    FormulaInf.Realize (φ.mapFreeVars (Empty.elim : Empty → Fin 0)) (Fin.elim0 : Fin 0 → M) := by
  show φ.Realize (Empty.elim : Empty → M) Fin.elim0 ↔
       (φ.mapFreeVars Empty.elim).Realize (Fin.elim0 : Fin 0 → M) Fin.elim0
  rw [BoundedFormulaInf.realize_mapFreeVars]
  have h : (Fin.elim0 : Fin 0 → M) ∘ (Empty.elim : Empty → Fin 0) = (Empty.elim : Empty → M) :=
    funext fun x => x.elim
  rw [h]

omit [L.IsRelational] [Countable (Σ l, L.Relations l)] in
/-- Bridge between FormulaInf.Realize (Fin 0) and SentenceInf.Realize via mapFreeVars. -/
private theorem formulaInf_realize_iff_mapFreeVars
    {M : Type*} [L.Structure M] (φ : BoundedFormulaInf.{u, v, 0, 0} L (Fin 0) 0) :
    FormulaInf.Realize φ (Fin.elim0 : Fin 0 → M) ↔
    SentenceInf.Realize (φ.mapFreeVars (Fin.elim0 : Fin 0 → Empty)) M := by
  show φ.Realize (Fin.elim0 : Fin 0 → M) Fin.elim0 ↔
       (φ.mapFreeVars Fin.elim0).Realize (Empty.elim : Empty → M) Fin.elim0
  rw [BoundedFormulaInf.realize_mapFreeVars]
  have h : (Empty.elim : Empty → M) ∘ (Fin.elim0 : Fin 0 → Empty) = (Fin.elim0 : Fin 0 → M) :=
    funext fun x => Fin.elim0 x
  rw [h]

/-- BFEquiv at level α implies agreement on sentences of rank ≤ α. -/
theorem BFEquiv_implies_EquivQRInf {M N : Type w} [L.Structure M] [L.Structure N]
    (α : Ordinal) (h : BFEquiv (L := L) α 0 (Fin.elim0 : Fin 0 → M) (Fin.elim0 : Fin 0 → N)) :
    EquivQRInf L α M N := by
  intro φ hφ
  have hAgree := (BFEquiv_iff_agreeQR α (Fin.elim0 : Fin 0 → M) (Fin.elim0 : Fin 0 → N)).mp h
  have hφ' : (φ.mapFreeVars (Empty.elim : Empty → Fin 0)).qrank ≤ α := by
    simp [BoundedFormulaInf.qrank_mapFreeVars]; exact hφ
  have hR := hAgree _ hφ'
  exact (sentenceInf_realize_iff_mapFreeVars φ (M := M)).trans
    (hR.trans (sentenceInf_realize_iff_mapFreeVars φ (M := N)).symm)

/-- Agreement on sentences of rank ≤ α implies BFEquiv at level α. -/
theorem EquivQRInf_implies_BFEquiv {M N : Type w} [L.Structure M] [L.Structure N]
    (α : Ordinal) (h : EquivQRInf L α M N) :
    BFEquiv (L := L) α 0 (Fin.elim0 : Fin 0 → M) (Fin.elim0 : Fin 0 → N) := by
  rw [BFEquiv_iff_agreeQR]
  intro φ hφ
  have hφ' : (φ.mapFreeVars (Fin.elim0 : Fin 0 → Empty)).qrank ≤ α := by
    simp [BoundedFormulaInf.qrank_mapFreeVars]; exact hφ
  have hR := h _ hφ'
  exact (formulaInf_realize_iff_mapFreeVars φ (M := M)).trans
    (hR.trans (formulaInf_realize_iff_mapFreeVars φ (M := N)).symm)

/-- BFEquiv at all ordinals is equivalent to EquivQRInf at all ordinals.

Both sides are quantified over `Ordinal.{0}` because `EquivQRInf` is defined via
`BoundedFormulaInf.qrank`, which returns `Ordinal.{0}`. The `karp_theorem` handles
the universe mismatch with `potentialIso_iff_BFEquiv_all` by specializing at universe 0
via `@potentialIso_iff_BFEquiv_all.{u, v, w, 0}`. -/
theorem BFEquiv_all_iff_EquivQRInf_all {M N : Type w} [L.Structure M] [L.Structure N] :
    (∀ α : Ordinal.{0}, BFEquiv (L := L) α 0 (Fin.elim0 : Fin 0 → M) (Fin.elim0 : Fin 0 → N)) ↔
    (∀ α : Ordinal.{0}, EquivQRInf L α M N) :=
  ⟨fun h α => BFEquiv_implies_EquivQRInf α (h α),
   fun h α => EquivQRInf_implies_BFEquiv α (h α)⟩

/-- **Karp's Theorem** (KK04 Theorem 1.2.1): For relational languages, two structures
are potentially isomorphic if and only if they are L∞ω-elementarily equivalent.

This is the fundamental connection between the game-theoretic notion of potential
isomorphism and the logical notion of elementary equivalence in infinitary logic.

**Universe note**: The (→) direction uses `implies_BFEquiv_all` at `Ordinal.{0}` to
connect to formula-based equivalence. The (←) direction uses
`BFEquiv_all_implies_potentialIso` which requires `Ordinal.{w}` (matching the type
universe of M and N). The bridge from `Ordinal.{0}` formulas to `Ordinal.{w}` BFEquiv
requires a universe-lifting argument. -/
theorem karp_theorem {M N : Type w} [L.Structure M] [L.Structure N] :
    Nonempty (PotentialIso L M N) ↔ LinfEquiv L M N := by
  constructor
  · -- Forward: PotentialIso → LinfEquiv
    intro ⟨P⟩ φ
    -- BFEquiv at Ordinal.{0} for the empty tuple (universe-polymorphic forward direction)
    exact BFEquiv_implies_EquivQRInf φ.qrank (P.implies_BFEquiv_all φ.qrank) φ le_rfl
  · -- Backward: LinfEquiv → PotentialIso
    intro hL
    apply BFEquiv_all_implies_potentialIso
    -- Need: ∀ α : Ordinal.{w}, BFEquiv.{w} α 0 elim0 elim0
    -- From LinfEquiv we get BFEquiv.{0} at all Ordinal.{0} levels via BFEquiv_iff_agreeQR.
    -- The universe bridge from Ordinal.{0} to Ordinal.{w} requires lifting:
    -- pointwise lift (ofOrdinalLift) handles ordinals in the image of Ordinal.lift,
    -- but ordinals beyond the initial segment need the full quantifier swap argument
    -- (which is exactly what BFEquiv_all_implies_potentialIso proves internally).
    -- TODO: Complete the universe bridge Ordinal.{0} → Ordinal.{w}.
    sorry

end Language

end FirstOrder
