/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Lomega1omega.Semantics

/-!
# Indiscernible Sequences for Lω₁ω

A sequence `(aᵢ)_{i ∈ I}` in a model M is Lω₁ω-indiscernible if for every
n-variable formula and every two strictly increasing n-tuples from I, the
formula holds on one iff it holds on the other.

Standalone API — does not advance the Hanf boundary.
-/

universe u v w

namespace FirstOrder.Language

variable {L : Language.{u, v}}

section Indiscernible

variable {I : Type w} [LinearOrder I] {M : Type*} [L.Structure M]

/-- A sequence `a : I → M` is Lω₁ω-indiscernible if for every n-variable
formula φ (no free variables) and every two strictly increasing maps
`s t : Fin n → I`, the formula holds on `a ∘ s` iff on `a ∘ t`. -/
def IsLomega1omegaIndiscernible (a : I → M) : Prop :=
  ∀ (n : ℕ) (φ : L.BoundedFormulaω Empty n)
    (s : Fin n → I) (_ : StrictMono s)
    (t : Fin n → I) (_ : StrictMono t),
    letI := ‹L.Structure M›
    φ.Realize (Empty.elim : Empty → M) (a ∘ s) ↔
    φ.Realize (Empty.elim : Empty → M) (a ∘ t)

/-- Restricting an indiscernible sequence to a sub-order. -/
theorem IsLomega1omegaIndiscernible.restrict {a : I → M}
    (h : IsLomega1omegaIndiscernible (L := L) a)
    {J : Type*} [LinearOrder J] (e : J ↪o I) :
    IsLomega1omegaIndiscernible (L := L) (a ∘ e) :=
  fun n φ s hs t ht => h n φ (e ∘ s) (e.strictMono.comp hs) (e ∘ t) (e.strictMono.comp ht)

/-- For a 1-variable formula, truth is the same at any two indices. -/
theorem IsLomega1omegaIndiscernible.unary_const {a : I → M}
    (h : IsLomega1omegaIndiscernible (L := L) a)
    (φ : L.BoundedFormulaω Empty 1) (i j : I) :
    letI := ‹L.Structure M›
    φ.Realize (Empty.elim : Empty → M) (fun _ => a i) ↔
    φ.Realize (Empty.elim : Empty → M) (fun _ => a j) :=
  h 1 φ (fun _ => i) (fun x y h => absurd h (by omega))
       (fun _ => j) (fun x y h => absurd h (by omega))

end Indiscernible

end FirstOrder.Language
