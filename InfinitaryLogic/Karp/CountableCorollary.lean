/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Karp.CarrierTheorem
import InfinitaryLogic.Lomega1omega.Theory
import InfinitaryLogic.Scott.Sentence
import InfinitaryLogic.Scott.RefinementCount

/-!
# Countable Corollary to Karp's Theorem

This file proves that for countable structures, elementary equivalence in the infinitary
logics implies isomorphism.

The two results take genuinely different routes, and the `L∞ω` one is the stronger.
`L∞ω`-equivalence goes straight through Karp's theorem to a potential isomorphism and then to
an isomorphism by back-and-forth on countable structures — no Scott sentence, no refinement
counting, and no countable-language hypothesis. `Lω₁ω`-equivalence has no such route: it is
weaker than `L∞ω`-equivalence, so it must go through the Scott sentence, which is what drags
in `CountableRefinementHypothesis` and the countable relational language.

## Main Results

- `countable_InfEquivW_implies_iso`: for countable structures, `L∞ω`-elementary equivalence
  implies isomorphism. Unconditional — no refinement hypothesis, no countable language.
- `countable_LomegaEquiv_implies_iso`: for countable structures in a countable relational
  language, `Lω₁ω`-elementary equivalence implies isomorphism (KK04 Corollary 1.2.2).

## References

- [KK04], Corollary 1.2.2
-/

universe u v w

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}} [L.IsRelational]
variable [Countable (Σ l, L.Relations l)]

open FirstOrder Structure Ordinal

/-- Conditional variant of `countable_LomegaEquiv_implies_iso`. -/
theorem countable_LomegaEquiv_implies_iso_of
    (hcount : CountableRefinementHypothesis.{u, v, w} L)
    {M : Type w} [L.Structure M] [Countable M]
    {N : Type w} [L.Structure N] [Countable N] :
    LomegaEquiv L M N → Nonempty (M ≃[L] N) := by
  intro hEquiv
  apply scottSentence_realizes_implies_equiv_of hcount
  rw [Formulaω.realize_as_sentence_iff_toSentenceω]
  exact (hEquiv _).mp ((Formulaω.realize_as_sentence_iff_toSentenceω _ _).mp
    (scottSentence_self_of hcount M))

omit [Countable (Σ l, L.Relations l)] in
/-- For countable structures, potential isomorphism implies actual isomorphism.

This is proved by direct back-and-forth construction on the PotentialIso family,
avoiding the need for Scott sentences or Karp's theorem. -/
theorem countable_PotentialIso_implies_iso
    {M : Type w} [L.Structure M] [Countable M]
    {N : Type w} [L.Structure N] [Countable N] :
    Nonempty (PotentialIso L M N) → Nonempty (M ≃[L] N) := by
  intro ⟨P⟩
  exact P.countable_toEquiv

omit [Countable (Σ l, L.Relations l)] in
/-- **For countable structures, `L∞ω`-elementary equivalence implies isomorphism.**

Unconditional: Karp's theorem turns the equivalence into a potential isomorphism, and
back-and-forth on countable structures turns that into an isomorphism. Neither step needs a
refinement hypothesis or a countable language, so unlike the `Lω₁ω` statement below this one
has no `_of` variant to discharge. -/
theorem countable_InfEquivW_implies_iso
    {M N : Type w} [L.Structure M] [L.Structure N]
    [Countable M] [Countable N] :
    InfEquivW L M N → Nonempty (M ≃[L] N) :=
  fun h => countable_PotentialIso_implies_iso (karp_theorem_w.mpr h)

omit [Countable ((l : ℕ) × L.Relations l)] in
/-- For countable structures, BFEquiv at all ordinals implies isomorphism. -/
theorem countable_BFEquiv_all_implies_iso
    {M : Type w} [L.Structure M] [Countable M]
    {N : Type w} [L.Structure N] [Countable N]
    (h : ∀ α : Ordinal.{w}, BFEquiv (L := L) α 0 (Fin.elim0 : Fin 0 → M) (Fin.elim0 : Fin 0 → N)) :
    Nonempty (M ≃[L] N) := by
  apply countable_PotentialIso_implies_iso
  exact potentialIso_iff_BFEquiv_all.mpr h

/-! ### Unconditional Wrappers (via CRH) -/

/-- For countable structures in a countable relational language, Lω₁ω-elementary
equivalence implies isomorphism. -/
theorem countable_LomegaEquiv_implies_iso
    {M : Type w} [L.Structure M] [Countable M]
    {N : Type w} [L.Structure N] [Countable N] :
    LomegaEquiv L M N → Nonempty (M ≃[L] N) :=
  countable_LomegaEquiv_implies_iso_of countableRefinementHypothesis

/-! ## Witness-generated back-and-forth systems

Two endpoints for callers who already hold a back-and-forth system.  Both are the direct
composition with `PotentialIso.countable_toEquiv`, which remains the sole implementation of the
eventual isomorphism.

**Countability of the two carriers is the only countability needed** — in particular no
`[Countable (Σ l, L.Relations l)]`, which the `omit` clauses below enforce rather than merely
assert.  That matches `countable_InfEquivW_implies_iso` and contrasts with the `Lω₁ω` route. -/

omit [Countable (Σ l, L.Relations l)] in
/-- **From a relation-form extension family to an isomorphism.**

Tuples are arbitrary functions `Fin n → M`, so repeated coordinates are supported; atomic
compatibility is exactly `SameAtomicType`.  No complete types, elementary maps, Scott sentences or
formula invariance are involved, and the language may be arbitrary. -/
theorem countable_extensionFamily_implies_iso
    {M : Type w} [L.Structure M] [Countable M]
    {N : Type w} [L.Structure N] [Countable N]
    (R : ∀ n : ℕ, (Fin n → M) → (Fin n → N) → Prop)
    (empty : R 0 Fin.elim0 Fin.elim0)
    (compatible : ∀ {n a b}, R n a b → SameAtomicType (L := L) a b)
    (forth : ∀ {n a b}, R n a b → ∀ m : M,
      ∃ n' : N, R (n + 1) (Fin.snoc a m) (Fin.snoc b n'))
    (back : ∀ {n a b}, R n a b → ∀ n' : N,
      ∃ m : M, R (n + 1) (Fin.snoc a m) (Fin.snoc b n')) :
    Nonempty (M ≃[L] N) :=
  (PotentialIso.ofExtensionFamily R empty compatible forth back).countable_toEquiv

omit [Countable (Σ l, L.Relations l)] in
/-- **From a proof-relevant state presentation to an isomorphism.** -/
theorem ExtensionPresentation.countable_toEquiv
    {M : Type w} [L.Structure M] [Countable M]
    {N : Type w} [L.Structure N] [Countable N]
    (P : ExtensionPresentation L M N) : Nonempty (M ≃[L] N) :=
  P.toPotentialIso.countable_toEquiv

/-! ### Acceptance tests

The identity system, in both presentations, including the empty-tuple case. -/

/-- Relation form: the diagonal family. -/
example {M : Type w} [L.Structure M] : PotentialIso L M M :=
  PotentialIso.ofExtensionFamily (fun _ a b => a = b) rfl
    (fun h => h ▸ SameAtomicType.refl _)
    (fun h m => ⟨m, by rw [h]⟩)
    (fun h n' => ⟨n', by rw [h]⟩)

/-- State form: states *are* the tuples.  `empty := Fin.elim0` is the empty-tuple case. -/
example {M : Type w} [L.Structure M] : ExtensionPresentation L M M where
  State n := Fin n → M
  left s := s
  right s := s
  empty := Fin.elim0
  compatible _s := SameAtomicType.refl _
  forth s m := ⟨m, Fin.snoc s m, rfl, rfl⟩
  back s n' := ⟨n', Fin.snoc s n', rfl, rfl⟩

/-- …and a state presentation converts through to an isomorphism. -/
example {M : Type w} [L.Structure M] [Countable M]
    (P : ExtensionPresentation L M M) : Nonempty (M ≃[L] M) :=
  P.countable_toEquiv

end Language

end FirstOrder
