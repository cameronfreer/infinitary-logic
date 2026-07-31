/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Methods.Interpolation.MalitzSublanguage

/-!
# Malitz interpolation for `L_ω₁ω`: public facade

The stable entry point for the project's Malitz-interpolation results (issue #15).  Importing this
file — or any bundle containing it, including the default `import InfinitaryLogic` — exposes:

* **`malitz_interpolation`** — the headline: over a **relational** language of arbitrary
  cardinality, an `L_ω₁ω`-entailment `φ ⊨ ψ` whose consequent is **universal** has a **universal**
  interpolant, with the usual shared-vocabulary occurrence bounds;
* `malitz_interpolation_relational_countable` — the countable core it is built from.

## What exactly is claimed

This is López–Escobar / Malitz Theorem 4.5 in the function-free case: the interpolant can be taken
in the same quantifier class as the consequent.  "Universal" is the *signed occurrence* notion
`IsUniversal = universalSigned true`: every quantifier occurrence is a positive `∀`.  Countable
conjunctions and disjunctions are **not** counted as quantifiers, which is what makes this the
∀₁ hierarchy rather than a Π-hierarchy.

## How it is proved

Not by a proof calculus.  The engine is a **side-labelled budgeted pair** — Feferman's split-sequent
invariant in semantic form — whose separators carry a shared-vocabulary condition, a shared-constant
condition, and two quantifier permissions.  The interpolant's universality is *paid for* by the
budget: the right root `ψ.not` carries no positive universal occurrence exactly when `ψ` is
universal, so the separator can contain no existential occurrence.

See `Methods/Interpolation/BudgetedPair.lean` for the certificate and its closure gates.
-/
