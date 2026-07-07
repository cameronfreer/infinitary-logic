/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Data.Finset.Sort
import InfinitaryLogic.Combinatorics.FiniteArityErdosRadoInduction
import InfinitaryLogic.Lomega1omega.Semantics

/-!
# The Marker stage: finite-fragment support extraction and Erdős–Rado certification

First layer of the template/consistency-property reshape of the Morley–Hanf chain (the
replacement for the ZFC-refutable in-`M` extraction ladder — see the audit fences on
`PureColoringHypothesis`/`MorleyHanfExtraction` in `Conditional/MorleyHanfTransfer.lean`).
Following Marker, *Lectures on Infinitary Model Theory* §5.2, the consistency-property route
certifies each **finite** fragment of an `L'[[J]]` template/constant theory by a large
homogeneous set in the source model, with the indiscernible sequence materializing only in
the model built by Model Existence.

This file provides the syntactic/combinatorial bridge between "finite fragment of a
constant theory" and "finite-arity Erdős–Rado approximation":

* a finite fragment is presented by its **index data** — a finite family of pairs
  `(fml p : L'.BoundedFormulaω Empty (ar p), tup p : Fin (ar p) ↪o J)` (per the template
  machinery in `Methods/EM/Realization.lean`, membership in a template theory carries
  exactly this witness data, so no syntactic support extraction is ever needed);
* `exists_markerSupport_factor` — collect the finite `J`-constant support of the family,
  enumerate it as `enum : Fin k ↪o J`, and factor every `tup p` through `enum`
  (via `exists_orderEmbedding_factor`);
* `markerStage_homogeneous` — pull the family back to a single arity-`k` truth-vector
  coloring over the source model and apply `finiteArityHomogeneousUpTo_beth_stage`:
  for every `α < ω₁`, a source of size `≥ ℶ_{ω₁}` yields a `(ℶ_α)⁺`-suborder on which the
  truth vector of the whole fragment is tuple-independent.

The per-`α` conclusion (available for **every** `α < ω₁` at once) is the Marker schedule:
the upcoming `markerConsistencyPropertyEq` certifies its members by exactly this largeness,
with the disjunction condition `C4_iSup` discharged by re-homogenizing the disjunct index
(countably many colors, again `≤ ℶ_α`) and pigeonholing over the cofinal `α`-schedule.
-/

universe u

namespace FirstOrder.Language

open Cardinal

/-- Every finite ordinal step stays below `ω₁`: if `α < ω₁` then `α + n < ω₁` for every
natural `n` — the room the Marker `α`-schedule uses to absorb per-fragment ladder costs. -/
theorem add_natCast_lt_omega_one {α : Ordinal.{0}} (hα : α < Ordinal.omega 1) :
    ∀ n : ℕ, α + (n : Ordinal) < Ordinal.omega 1
  | 0 => by simpa using hα
  | (n + 1) => by
    have hn : α + (n : Ordinal) < Ordinal.omega 1 := add_natCast_lt_omega_one hα n
    have : α + ((n + 1 : ℕ) : Ordinal) = Order.succ (α + (n : Ordinal)) := by
      rw [Nat.cast_add, Nat.cast_one, ← add_assoc, ← Order.succ_eq_add_one]
    rw [this]
    exact (Cardinal.isSuccLimit_omega 1).succ_lt hn

/-- **Support factorization for a finite constant-fragment.** Given a finite family of
`J`-constant tuples `tup p : Fin (ar p) ↪o J` (the index data of a finite fragment of an
`L'[[J]]` constant theory), collect the finite support, enumerate it in increasing order as
`enum : Fin k ↪o J`, and factor every tuple through the enumeration. The range equation
identifies `enum` with the exact constant support of the fragment. -/
theorem exists_markerSupport_factor {J : Type u} [LinearOrder J]
    {m : ℕ} {ar : Fin m → ℕ} (tup : ∀ p, Fin (ar p) ↪o J) :
    ∃ (k : ℕ) (enum : Fin k ↪o J) (r : ∀ p, Fin (ar p) ↪o Fin k),
      (∀ p, (r p).trans enum = tup p) ∧
      Set.range ⇑enum = ⋃ p, Set.range ⇑(tup p) := by
  classical
  set S : Finset J := Finset.univ.biUnion fun p => Finset.univ.image ⇑(tup p) with hS
  have hrange : Set.range ⇑(S.orderEmbOfFin rfl) = ↑S := Finset.range_orderEmbOfFin S rfl
  have hmem : ∀ p (i : Fin (ar p)), tup p i ∈ Set.range ⇑(S.orderEmbOfFin rfl) := by
    intro p i
    rw [hrange]
    exact Finset.mem_coe.mpr (Finset.mem_biUnion.mpr
      ⟨p, Finset.mem_univ p, Finset.mem_image_of_mem _ (Finset.mem_univ i)⟩)
  choose r hr using fun p =>
    exists_orderEmbedding_factor (S.orderEmbOfFin rfl) (tup p) (hmem p)
  refine ⟨S.card, S.orderEmbOfFin rfl, r, hr, ?_⟩
  rw [hrange]
  simp [hS]

/-- **The Marker-stage Erdős–Rado certification.** A finite fragment of an `L'[[J]]`
constant theory, presented by its index data `(fml p, tup p)`, pulls back along the support
factorization to a single arity-`k` truth-vector coloring over the source model `M`; for
every `α < ω₁`, `finiteArityHomogeneousUpTo_beth_stage` then yields a `(ℶ_α)⁺`-suborder of
`M` on which the truth of every formula of the fragment (at its own positions `r p` inside
the support) is independent of the choice of increasing `k`-tuple.

This is the per-fragment certification of the Marker consistency property: available at
every `α < ω₁` simultaneously (the cofinal schedule), from the single hypothesis
`|M| ≥ ℶ_{ω₁}` — per-`α`, per-finite-fragment approximations, never one `ω₁`-suborder
homogeneous for all arities at once (that jump is ZFC-refutable; see the audit fences). -/
theorem markerStage_homogeneous {L' : Language.{0, 0}} (M : Type) [L'.Structure M]
    [LinearOrder M] [WellFoundedLT M]
    (hM : Cardinal.mk M ≥ Cardinal.beth (Ordinal.omega 1))
    (α : Ordinal.{0}) (hα : α < Ordinal.omega 1)
    {J : Type} [LinearOrder J]
    {m : ℕ} {ar : Fin m → ℕ} (fml : ∀ p : Fin m, L'.BoundedFormulaω Empty (ar p))
    (tup : ∀ p, Fin (ar p) ↪o J) :
    ∃ (k : ℕ) (enum : Fin k ↪o J) (r : ∀ p, Fin (ar p) ↪o Fin k),
      (∀ p, (r p).trans enum = tup p) ∧
      Set.range ⇑enum = ⋃ p, Set.range ⇑(tup p) ∧
      ∃ e : (Order.succ (Cardinal.beth α)).ord.ToType ↪o M,
        ∀ u u' : Fin k ↪o M,
          (∀ i, u i ∈ Set.range e) → (∀ i, u' i ∈ Set.range e) →
          ∀ p, ((fml p).Realize (Empty.elim : Empty → M) (⇑u ∘ ⇑(r p)) ↔
            (fml p).Realize (Empty.elim : Empty → M) (⇑u' ∘ ⇑(r p))) := by
  classical
  obtain ⟨k, enum, r, hr, hrange⟩ := exists_markerSupport_factor tup
  refine ⟨k, enum, r, hr, hrange, ?_⟩
  -- The truth-vector coloring at the support arity, defaulted elsewhere.
  let realColor : (Fin k ↪o M) → (Fin m → Prop) := fun u p =>
    (fml p).Realize (Empty.elim : Empty → M) (⇑u ∘ ⇑(r p))
  let c : ∀ n, (Fin n ↪o M) → (Fin m → Prop) :=
    Function.update (fun _ _ _ => True) k realColor
  have hc : c k = realColor := Function.update_self _ _ _
  have hsize : Cardinal.beth (α + ((2 * k + 2 : ℕ) : Ordinal)) ≤ Cardinal.mk M :=
    (Cardinal.beth_le_beth.mpr (add_natCast_lt_omega_one hα (2 * k + 2)).le).trans hM
  have hC : ∀ n : ℕ, Cardinal.mk (Fin m → Prop) ≤ Cardinal.beth α := fun _ =>
    (Cardinal.mk_lt_aleph0 (α := Fin m → Prop)).le.trans (Cardinal.aleph0_le_beth α)
  obtain ⟨e, he⟩ :=
    finiteArityHomogeneousUpTo_beth_stage α k hsize (fun _ => Fin m → Prop) hC c
  refine ⟨e, fun u u' hu hu' p => ?_⟩
  have h : c k u = c k u' := he k le_rfl u u' hu hu'
  have h' : realColor u = realColor u' := by rw [← hc]; exact h
  exact iff_of_eq (congrFun h' p)

end FirstOrder.Language
