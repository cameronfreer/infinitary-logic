/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Methods.Interpolation.CraigSublanguage
import InfinitaryLogic.Methods.Interpolation.CraigSeparation

/-!
# Craig interpolation for `L_ω₁ω`: public facade (relational endpoint)

The stable entry point for the project's Craig-interpolation results (issue #8).  Importing this
file — or any bundle containing it, including the default `import InfinitaryLogic` — exposes the
**relational endpoint** of the interpolation arc:

* `craig_interpolation_relational` — over a purely relational language (with *arbitrarily many*
  symbols, no countability hypothesis), an `L_ω₁ω`-entailment `r₁ ⊨ r₂` has an interpolant `θ`
  whose function/relation symbols lie in the intersection of the two roots' occurrence sets, with
  `r₁ ⊨ θ` and `θ ⊨ r₂` (proved in `Methods/Interpolation/CraigSublanguage.lean`, blueprint node
  `thm:craig-relational`);
* `craig_pcSeparation_relational` — the disjunction (PC-separation) form in the shared-vocabulary
  `symbSublang` packaging (proved in `Methods/Interpolation/CraigSeparation.lean`); the deliverable
  consumed by issue #10.

## Scope of this endpoint

This is the **first publishable theorem** of the interpolation arc.  It is stated for *relational*
languages.  The full headline — Craig interpolation over an arbitrary language, with function
symbols in the conclusion's `functionsIn` bound — is delivered by a further *relationalization*
layer (function symbols translated to graph relations), a self-contained syntactic translation
still to be built; this facade will be extended to expose it once it lands.  Nothing here has any
sorry, and every result is axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
