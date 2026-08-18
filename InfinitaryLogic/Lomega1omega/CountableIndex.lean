/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Lomega1omega.Semantics
import Mathlib.ModelTheory.Infinitary.Reindex

/-!
# Countable connectives over arbitrary countable index types

`BoundedFormulaω`'s `iInf`/`iSup` branch over the fixed carrier `ℕ`. Constructions like the
Hanf beth ladder (clause families over pairs of countable ordinals) and countable fragments
quantify over countable-but-not-`ℕ` index types. This file provides the conjunction and
disjunction over any such index, as thin wrappers around Mathlib's carrier-transport
primitives `BoundedFormulaInf.iInfAlong`/`iSupAlong`.

**The index may live in any universe.** `ι` is encoded into `ℕ`, so nothing forces it into
`Type 0`; this is what lets the type-isolation chain be universe-polymorphic.

Choice has not disappeared — `Encodable.ofCountable` is noncomputable, so these definitions
are too. What the coding removes is the bespoke scaffolding the previous implementation
needed: a `Nonempty ι` case split, a chosen surjection `ℕ → ι`, ad-hoc defaults for the empty
family, and four hand-proved realization lemmas. Padding handles the empty carrier uniformly,
so each realization lemma is now the upstream one applied directly.

Only the realization lemmas are provided. No syntactic naturality API is built here: the
encoding is noncanonical, so definitional commutation statements would be unpleasant —
consumers should work through `realize_ciInf`/`realize_ciSup`.
-/

namespace FirstOrder

namespace Language

namespace BoundedFormulaω

variable {L : Language.{u, v}} {γ : Type u'} {n : ℕ}

/-- **Countable conjunction over a countable index type**, at any index universe.

The index is encoded into the fixed `ℕ` carrier by an `IndexCoding`, and branches outside the
image are padded with `⊤`. Padding is what makes the empty carrier need no special handling:
an empty `ι` pads every branch, and the conjunction is vacuously true. -/
noncomputable def ciInf {ι : Type uι} [Countable ι] (φs : ι → L.BoundedFormulaω γ n) :
    L.BoundedFormulaω γ n :=
  BoundedFormulaInf.iInfAlong (.ofEncodableWith (Encodable.ofCountable ι)) φs

/-- **Countable disjunction over a countable index type**, at any index universe. Dual to
`ciInf`; undecodable branches are padded with `⊥`, so an empty `ι` is vacuously false. -/
noncomputable def ciSup {ι : Type uι} [Countable ι] (φs : ι → L.BoundedFormulaω γ n) :
    L.BoundedFormulaω γ n :=
  BoundedFormulaInf.iSupAlong (.ofEncodableWith (Encodable.ofCountable ι)) φs

variable {M : Type w} [L.Structure M]

theorem realize_ciInf {ι : Type uι} [Countable ι] (φs : ι → L.BoundedFormulaω γ n)
    (v : γ → M) (xs : Fin n → M) :
    (ciInf φs).Realize v xs ↔ ∀ i, (φs i).Realize v xs :=
  BoundedFormulaInf.realize_iInfAlong

theorem realize_ciSup {ι : Type uι} [Countable ι] (φs : ι → L.BoundedFormulaω γ n)
    (v : γ → M) (xs : Fin n → M) :
    (ciSup φs).Realize v xs ↔ ∃ i, (φs i).Realize v xs :=
  BoundedFormulaInf.realize_iSupAlong

end BoundedFormulaω

end Language

end FirstOrder
