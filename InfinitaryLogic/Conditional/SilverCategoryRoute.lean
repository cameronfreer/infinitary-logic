/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Conditional.GandyHarrington

/-!
# Silver via the classical category route (Miller): interface layer

This file scaffolds the chosen route to `gandy_harrington_for_relation` (the project's one
remaining sorry): Benjamin Miller's classical, forcing-free, effective-DST-free proof of
Silver's theorem ["The graph-theoretic approach to descriptive set theory", BSL 18(4), 2012,
Theorem 11; also "Forceless, ineffective, powerless proofs of descriptive dichotomy theorems,
Lecture I"]. The proof composes:

1. **KST `G₀`-dichotomy** (classical proof via the σ-ideal of Borel `G`-independent sets):
   for the graph `G = ¬E` off the diagonal, either there is a Borel ℵ₀-coloring — giving
   countably many classes — or a continuous homomorphism `φ : 2^ℕ → α` from `G_S(2^ℕ)` to `G`.
2. **Pullback + Kuratowski–Ulam**: every class of `E' = (φ × φ)⁻¹(E)` is `G_S`-independent,
   hence meager (for dense `S`); Kuratowski–Ulam then makes `E'` itself meager.
3. **Mycielski**: a meager equivalence relation on Cantor space admits a continuous map
   `ψ : 2^ℕ → 2^ℕ` with distinct points inequivalent.
4. `f = φ ∘ ψ` is the desired perfect antichain.

Steps 1–2 are packaged here as `CategoryReductionHypothesis`, step 3 as
`MycielskiCantorHypothesis`, and step 4 is **proved**: `gandy_harrington_of_category_route`
derives the exact statement of `gandy_harrington_for_relation` from the two hypotheses.

## Design note (audit outcome)

An earlier candidate design — a Gandy–Harrington-style forcing layer
(`Cond`/`split`/`fusion` on subsets of `α`) feeding `CantorScheme.exists_antichain_map` — does
NOT match this route: in Miller's proof the forcing-style largeness lives on spaces of finite
partial homomorphisms `2^n → α` (the `I_n`-positive sets inside the classical `G₀`-dichotomy
proof), not on subsets of `α`, and the final antichain is a composite `φ ∘ ψ` rather than the
limit of a scheme on `α`. Sibling cross-avoidance at finite stages is impossible for dense
relations (e.g. the pullback of `E₀`), so `exists_antichain_map` is *not* the assembly point
for this route; it remains the assembly point for the closed case (`silver_core_closed`).

## Frontier decomposition (all classical; no effective DST)

* `MycielskiCantorHypothesis` — bounded next target: a Cantor-scheme construction with
  open boxes avoiding countably many nowhere dense closed sets scheduled across levels
  (Kechris, CDST 19.1). Mathlib has the meager/residual API but not this theorem.
* `CategoryReductionHypothesis` — decomposes further into: Kuratowski–Ulam (absent from
  mathlib; bounded), the `G_S(2^ℕ)` graphs with the dense-`S` independence lemma
  (Miller, Prop 6; bounded), and the classical `G₀`-dichotomy (Miller's proof of KST via
  `I_n`-positive sets of partial homomorphisms; the hard core). These should be interfaced
  only when work on them starts — freezing their statements now would repeat the
  premature-abstraction mistake this audit caught.
-/

universe u

open Set

/-- **Mycielski's theorem for Cantor space** (hypothesis form). A meager equivalence relation
on `ℕ → Bool` admits a continuous map of Cantor space into it with distinct points pairwise
inequivalent. Classical content: Kechris, CDST 19.1 (specialized); provable by a Cantor scheme
of basic clopen boxes avoiding, at level `n`, the first `n` nowhere dense closed sets covering
the relation. Injectivity is omitted: it follows from the antichain property and reflexivity
(see `gandy_harrington_of_category_route`). -/
def MycielskiCantorHypothesis : Prop :=
  ∀ E : Setoid (ℕ → Bool),
    IsMeagre {p : (ℕ → Bool) × (ℕ → Bool) | E.r p.1 p.2} →
    ∃ ψ : (ℕ → Bool) → (ℕ → Bool), Continuous ψ ∧
      ∀ a b : ℕ → Bool, a ≠ b → ¬ E.r (ψ a) (ψ b)

/-- **Category reduction** (hypothesis form): a Borel equivalence relation with uncountably
many classes on a Polish space admits a continuous `φ : 2^ℕ → α` whose pullback relation is
meager. This packages steps 1–2 of Miller's classical proof of Silver's theorem: the
`G₀`-dichotomy applied to the complement graph `¬r` (the coloring side is impossible with
uncountably many classes), followed by `G_S`-independence of the pullback classes and
Kuratowski–Ulam. -/
def CategoryReductionHypothesis : Prop :=
  ∀ {α : Type u} [MetricSpace α] [CompleteSpace α] [SecondCountableTopology α]
    [MeasurableSpace α] [BorelSpace α] (r : Setoid α),
    MeasurableSet {p : α × α | r.r p.1 p.2} → ¬ Countable (Quotient r) →
    ∃ φ : (ℕ → Bool) → α, Continuous φ ∧
      IsMeagre {p : (ℕ → Bool) × (ℕ → Bool) | r.r (φ p.1) (φ p.2)}

/-- **Assembly of the category route** (proved): the two hypotheses above compose to give
exactly the statement of `gandy_harrington_for_relation`. Pull `r` back along `φ` to a meager
equivalence relation on Cantor space, apply Mycielski to get `ψ`, and take `f = φ ∘ ψ`;
injectivity follows from the antichain property and reflexivity of `r`. -/
theorem gandy_harrington_of_category_route
    (hred : CategoryReductionHypothesis.{u}) (hmyc : MycielskiCantorHypothesis)
    {α : Type u} [MetricSpace α] [CompleteSpace α] [SecondCountableTopology α]
    [MeasurableSpace α] [BorelSpace α]
    (r : Setoid α) (hr : MeasurableSet {p : α × α | r.r p.1 p.2})
    (hunc : ¬ Countable (Quotient r)) :
    ∃ f : (ℕ → Bool) → α,
      Continuous f ∧ Function.Injective f ∧
      ∀ a b, a ≠ b → ¬ r.r (f a) (f b) := by
  obtain ⟨φ, hφ_cont, hφ_meager⟩ := hred r hr hunc
  -- Pull r back to Cantor space along φ
  let E : Setoid (ℕ → Bool) :=
    ⟨fun x y => r.r (φ x) (φ y),
      ⟨fun _ => r.iseqv.refl _,
       fun h => r.iseqv.symm h,
       fun h h' => r.iseqv.trans h h'⟩⟩
  obtain ⟨ψ, hψ_cont, hψ_anti⟩ := hmyc E hφ_meager
  refine ⟨φ ∘ ψ, hφ_cont.comp hψ_cont, ?_, fun a b hab => hψ_anti a b hab⟩
  intro a b hfab
  by_contra hne
  apply hψ_anti a b hne
  show r.r (φ (ψ a)) (φ (ψ b))
  rw [show φ (ψ a) = φ (ψ b) from hfab]
