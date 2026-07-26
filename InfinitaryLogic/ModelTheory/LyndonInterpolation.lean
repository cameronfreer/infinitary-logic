/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Methods.Interpolation.LyndonArbitrary

/-!
# Lyndon interpolation for `L_ω₁ω`: public facade

The stable entry point for the project's Lyndon-interpolation results (issue #14).  Importing this
file — or any bundle containing it, including the default `import InfinitaryLogic` — exposes:

* **`lyndon_interpolation`** — the headline: over an **arbitrary language** (no hypotheses on `L`
  whatsoever), an `L_ω₁ω`-entailment `r₁ ⊨ r₂` has an interpolant `θ` whose function symbols lie in
  the intersection of the roots' function occurrences, whose **positively** occurring relation
  symbols lie in the intersection of the roots' **positive** occurrences, and whose **negatively**
  occurring ones lie in the intersection of the roots' **negative** occurrences (proved in
  `Methods/Interpolation/LyndonArbitrary.lean`, blueprint node `thm:lyndon`);
* `lyndon_interpolation_relational` — the **relational core** (blueprint node
  `thm:lyndon-relational`): the same statement over a purely relational language, with no
  countability hypothesis;
* `craig_of_lyndon_interpolation` — the explicit recovery of Craig interpolation from the two
  signed bounds, through `relationsIn = positiveRelationsIn ∪ negativeRelationsIn`.  (The
  independently proved `craig_interpolation` remains the Craig headline; this is the *derivation*,
  recorded so the refinement relationship is visible rather than implicit.)

## What exactly is claimed

This is the **relation-polarity / logical-equality form** of López–Escobar 1965,
*An interpolation theorem for denumerably long formulas*, Theorem 4.1:

* clause (.4), the substantive Lyndon clause, is claimed **in full**: relation symbols satisfy the
  complete polarity condition — a symbol occurring positively (negatively) in the interpolant occurs
  positively (negatively) in *both* roots;
* clause (.3), the *equality-occurrence* condition, is **not** claimed: equality is treated as a
  **logical** symbol here, contributing to neither polarity class, and its occurrence in the
  interpolant is unconstrained.  Restoring (.3) would need a separate `equalityIn` occurrence
  recursion; no statement in this development depends on it.

Also not claimed: any **theory/set-level** Lyndon separation.  López–Escobar's Theorem 6.3 refutes
it for `L_ω₁ω` — there are disjoint `PC_Δ(L_ω₁ω)` classes not separable by an
`L_ω₁ω`-elementary class — so the sentence-level form above is the sharp statement.

## Architecture

Polarity is tracked by a **signed occurrence traversal** on the existing syntax
(`Lomega1omega/Polarity.lean`): antecedents flip the sign, quantifiers and the countable
connectives preserve it, and equality contributes nothing — no negation-normal form is constructed
anywhere.  Its semantic content is `realize_mono_of_signed` (`Lomega1omega/PolaritySemantics.lean`):
growing the positively-occurring relations and shrinking the negatively-occurring ones preserves
truth.

The proof refines the Craig engine rather than duplicating it: only the *separator class* changes,
from "base symbols in `(F, R)`" to "base functions in `F`, base positives in `P`, base negatives in
`N`" (`LyndonInsepAt`), with the paired family maintaining the flipped intersection class
`(F₁ ∩ F₂, P₁ ∩ N₂, N₁ ∩ P₂)`.  The countable-completion kernel — consistency property, fair
enumeration, quotient term model, truth lemma — is consumed unchanged, a fact enforced by the
truth-lemma dependency-cone guard, which lists `lyndon_interpolation` among its roots.  The
arbitrary-language wrapper reuses Craig's relationalization layer verbatim: base-relation polarity
is preserved on the nose by the translation, while the graph relations that carry arbitrary polarity
back-translate into *equalities*, which are polarity-free.

Nothing here has any sorry, and every result is axiom-clean
`[propext, Classical.choice, Quot.sound]`.
-/
