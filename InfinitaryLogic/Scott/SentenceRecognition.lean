/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Scott.Sentence
import InfinitaryLogic.Karp.CarrierTheorem
import InfinitaryLogic.Lomega1omega.QuantifierRank

/-!
# Whole-model recognition from a Scott sentence of bounded rank

Let `M : Type w` be a countable structure in a relational language `L`, and let `σ : L.Sentenceω`
be an **absolute Scott specification** of `M`: for every countable `L`-structure `N` on a carrier
in the same universe `Type w`, `σ.Realize N ↔ Nonempty (M ≃[L] N)`.  If `σ.qrank ≤ β`, then
back-and-forth equivalence of the empty tuples at level `β` already recognizes `M` up to
isomorphism among those targets (`StabilizesAt M β`), so the least such ordinal
`stabilizationOrdinal M` is at most `β`.

The proof opens `σ` into a formula on `Fin 0` with the same rank and semantics
(`qrank_openBounds`, `realize_openBounds`), transfers its truth from `M` to `N` by the forward
Karp lemma `BFEquiv_implies_agreeQR`, and applies the specification; the converse is the
isomorphism invariance of back-and-forth equivalence (`equiv_implies_BFEquiv`).

## Main declarations

* `recognition_of_sentence_rank`: `σ.qrank ≤ β` gives `StabilizesAt M β`.
* `stabilizationOrdinal_le_of_sentence_rank`: `σ.qrank ≤ β` gives `stabilizationOrdinal M ≤ β`.
* `stabilizationOrdinal_le_qrank_of_sentence`: the case `β = σ.qrank`.

## Interpretation notes

* **Relational languages.**  The language `L` is assumed relational (`[L.IsRelational]`), as in
  the forward Karp lemma these results use; this is a limitation of the present statements.
* **Targets.**  The specification quantifies over all countable `L`-structures on carriers in
  the fixed universe `Type w` of `M`: no further modelhood condition and no restricted class of
  targets.
* **No further hypotheses.**  `M` is countable but not assumed nonempty.  Neither the language
  nor `β` is assumed countable.  As in the existing recognition API, `β : Ordinal.{0}` carries no
  universe lift, whatever `w` is.
* **What is recognized.**  This is recognition of the whole model through the empty tuple.  It
  is not a bound on stabilization for tuples of every length (complete stabilization), on
  `scottHeight`, or on the internal Scott rank.
-/

universe u v w

namespace FirstOrder.Language

variable {L : Language.{u, v}} [L.IsRelational] {M : Type w} [L.Structure M] [Countable M]

/-- **An absolute Scott specification of rank at most `β` recognizes the model at `β`.**  If
`σ` holds in exactly the countable `L`-structures on `Type w` isomorphic to `M` and
`σ.qrank ≤ β`, then back-and-forth equivalence of the empty tuples at level `β` characterizes
isomorphism with `M` among countable structures on `Type w`.

The language is relational.  Neither `β` nor the language is assumed countable, and `M` need
not be nonempty.  This is whole-model recognition through the empty tuple, not a bound on the
stabilization of longer tuples. -/
theorem recognition_of_sentence_rank (σ : L.Sentenceω)
    (hσ : ∀ (N : Type w) [L.Structure N] [Countable N],
      σ.Realize N ↔ Nonempty (M ≃[L] N))
    {β : Ordinal.{0}} (hq : σ.qrank ≤ β) : StabilizesAt (L := L) M β := by
  have hself : σ.Realize M := (hσ M).mpr ⟨Language.Equiv.refl L M⟩
  let φ : L.Formulaω (Fin 0) := σ.openBounds
  have hφ : φ.qrank ≤ β := (qrank_openBounds σ).le.trans hq
  have hsem (N : Type w) [L.Structure N] :
      φ.Realize (Fin.elim0 : Fin 0 → N) ↔ σ.Realize N :=
    realize_openBounds σ Fin.elim0
  intro N _ _
  constructor
  · intro h
    exact (hσ N).mp ((hsem N).mp
      ((BFEquiv_implies_agreeQR β Fin.elim0 Fin.elim0 h φ hφ).mp ((hsem M).mpr hself)))
  · rintro ⟨e⟩
    simpa only [comp_fin_elim0] using equiv_implies_BFEquiv e β 0 Fin.elim0

/-- **The stabilization ordinal is at most the rank budget of an absolute Scott
specification.**  Under the hypotheses of `recognition_of_sentence_rank`,
`stabilizationOrdinal M ≤ β`: the existing infimum of whole-model recognition ordinals.

This bounds empty-tuple recognition only, not `scottHeight` or the internal Scott rank. -/
theorem stabilizationOrdinal_le_of_sentence_rank (σ : L.Sentenceω)
    (hσ : ∀ (N : Type w) [L.Structure N] [Countable N],
      σ.Realize N ↔ Nonempty (M ≃[L] N))
    {β : Ordinal.{0}} (hq : σ.qrank ≤ β) : stabilizationOrdinal (L := L) M ≤ β :=
  csInf_le' (recognition_of_sentence_rank σ hσ hq)

/-- **The stabilization ordinal is at most the rank of an absolute Scott specification**: the
case `β = σ.qrank` of `stabilizationOrdinal_le_of_sentence_rank`. -/
theorem stabilizationOrdinal_le_qrank_of_sentence (σ : L.Sentenceω)
    (hσ : ∀ (N : Type w) [L.Structure N] [Countable N],
      σ.Realize N ↔ Nonempty (M ≃[L] N)) :
    stabilizationOrdinal (L := L) M ≤ σ.qrank :=
  stabilizationOrdinal_le_of_sentence_rank σ hσ le_rfl

end FirstOrder.Language
