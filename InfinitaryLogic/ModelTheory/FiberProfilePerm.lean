/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.ModelTheory.FiberProfileBound
import InfinitaryLogic.Scott.FiniteMatching

/-!
# Extending a finite matching to a profile-preserving row permutation

The **generic lemma** `exists_equiv_of_matching` (a finite compatible matching respecting an
equivalence relation extends to a permutation respecting it and fixing everything outside the
sources and targets) lives in `Scott/FiniteMatching.lean`; it has no fiber content.

**Specialization** (`exists_profilePerm`): `SameProfile r s` (isomorphic fibers at every label)
is an equivalence relation on rows, so a finite compatible matching of rows with the same
profiles extends to a profile-preserving permutation of all rows.  Nothing here uses
countability, relationality, or any structure hypothesis.
-/

namespace FirstOrder.Language

namespace FiberAssembly

universe u v w


/-! ### Specialization to rows with the same profile -/

variable {U : Type u} [LinearOrder U] {Lc : Language.{v, w}} {Bstar : Type u} {B : U → Type u}
  [Lc.Structure Bstar] [∀ u, Lc.Structure (B u)] {A : ℕ → Set U}

/-- Two rows have the **same profile** when their fibers are isomorphic at every label. -/
def SameProfile (Lc : Language.{v, w}) (Bstar : Type u) (B : U → Type u) [Lc.Structure Bstar]
    [∀ u, Lc.Structure (B u)] (A : ℕ → Set U) (r s : Row A) : Prop :=
  ∀ τ : Label U, Nonempty (prefixFiber Bstar B A r τ ≃[Lc] prefixFiber Bstar B A s τ)

theorem sameProfile_equivalence : Equivalence (SameProfile Lc Bstar B A) where
  refl _ _ := ⟨Language.Equiv.refl Lc _⟩
  symm h τ := (h τ).elim fun e => ⟨e.symm⟩
  trans h₁ h₂ τ := (h₁ τ).elim fun e₁ => (h₂ τ).elim fun e₂ => ⟨Language.Equiv.comp e₂ e₁⟩

/-- **Profile-preserving row permutation.**  A finite compatible matching of rows with the same
profiles extends to a permutation of all rows preserving profiles and fixing every row outside
the sources and targets. -/
theorem exists_profilePerm {m : ℕ} (r s : Fin m → Row A) (hcomp : ∀ j j', r j = r j' ↔ s j = s j')
    (hp : ∀ j, SameProfile Lc Bstar B A (r j) (s j)) :
    ∃ e : Row A ≃ Row A, (∀ j, e (r j) = s j) ∧ (∀ t, SameProfile Lc Bstar B A t (e t)) ∧
      ∀ t, (∀ j, t ≠ r j ∧ t ≠ s j) → e t = t :=
  exists_equiv_of_matching sameProfile_equivalence m r s hcomp hp

end FiberAssembly

end FirstOrder.Language
