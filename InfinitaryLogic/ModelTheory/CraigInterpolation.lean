/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Methods.Interpolation.CraigSublanguage
import InfinitaryLogic.Methods.Interpolation.CraigSeparation
import InfinitaryLogic.Methods.Interpolation.CraigArbitrary

/-!
# Craig interpolation for `L_ω₁ω`: public facade

The stable entry point for the project's Craig-interpolation results (issue #8).  Importing this
file — or any bundle containing it, including the default `import InfinitaryLogic` — exposes:

* **`craig_interpolation`** — the headline: over an **arbitrary language** (no hypotheses on
  `L` whatsoever), an `L_ω₁ω`-entailment `r₁ ⊨ r₂` has an interpolant `θ` whose function and
  relation symbols each lie in the intersection of the two roots' occurrence sets, with
  `r₁ ⊨ θ` and `θ ⊨ r₂` (proved in `Methods/Interpolation/CraigArbitrary.lean`, blueprint node
  `thm:craig`);
* `craig_pcSeparation` — its disjunction (PC-separation) form in the shared-vocabulary
  `symbSublang` packaging;
* `craig_interpolation_relational` — the **relational core** (blueprint node
  `thm:craig-relational`): the same statement over a purely relational language, with no
  countability hypothesis, proved by the inseparability/finite-condition Henkin construction;
* `craig_pcSeparation_relational` — the relational PC-separation form, retained in exactly the
  packaging consumed by issue #10.

## Architecture

The headline is the relational core composed with a self-contained relationalization layer:
each `n`-ary function symbol becomes an `(n+1)`-ary graph relation `G_f`, terms flatten to
existential graph formulas, the totality/functionality axioms `Ax(F)` of the mentioned symbols
translate the entailment (`Ax(F₁) ∧ r₁ʳᵉˡ ⊨ Ax(F₂) → r₂ʳᵉˡ`, via structure reconstruction over
`F₁ ∪ F₂`), the relational interpolant's vocabulary passes through the exact occurrence
identities and the shared-vocabulary identity `relSym_inter`, and back-translation
`G_f(x⃗,y) ↦ f(x⃗)=y` lands the interpolant in `L` with the sharp occurrence bounds.

Nothing here has any sorry, and every result is axiom-clean
`[propext, Classical.choice, Quot.sound]`.
-/
