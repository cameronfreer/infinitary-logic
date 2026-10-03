/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Scott.MontalbanSentence
import InfinitaryLogic.Scott.QuantifierRank

/-!
# Quantifier rank of the tuple quantifier blocks

The tuple quantifiers of `Scott/MontalbanSentence.lean` iterate `existsLastVar` and
`forallLastVar`, each of which adds `1` to the quantifier rank (`qrank_existsLastVar`,
`qrank_forallLastVar`).  A block of `n` quantifiers therefore adds `n`, **on the right**:
`(existsTupleFrom k n φ).qrank = φ.qrank + n`, and likewise for `forallTupleFrom`,
`existsTuple` and `forallTuple`.  For ordinals the side matters at limits: `ω + 1 ≠ 1 + ω`.

## Main declarations

* `qrank_existsTupleFrom`, `qrank_forallTupleFrom`: closing the last `n` of `k + n` free
  variables adds `n`.
* `qrank_existsTuple`, `qrank_forallTuple`: closing all `n` free variables adds `n`.

## Implementation notes

This is a separate module so that `Scott/QuantifierRank.lean` need not import
`Scott/MontalbanSentence.lean`: that import would widen the cone of every module downstream of
the quantifier-rank file.  The import closure of this module is that of its two imports.
-/

universe u v

namespace FirstOrder.Language

open BoundedFormulaω

variable {L : Language.{u, v}}

private theorem one_add_natCast (n : ℕ) : (1 : Ordinal.{0}) + n = ((n + 1 : ℕ) : Ordinal) := by
  exact_mod_cast Nat.add_comm 1 n

/-- A block of `n` existential quantifiers adds `n` to the rank, on the right. -/
theorem qrank_existsTupleFrom (k : ℕ) :
    ∀ (n : ℕ) (φ : L.Formulaω (Fin (k + n))), (existsTupleFrom k n φ).qrank = φ.qrank + n
  | 0, φ => by simp [existsTupleFrom]
  | n + 1, φ => by
    simp only [existsTupleFrom, qrank_existsTupleFrom k n, qrank_existsLastVar, add_assoc,
      one_add_natCast]

/-- A block of `n` universal quantifiers adds `n` to the rank, on the right. -/
theorem qrank_forallTupleFrom (k : ℕ) :
    ∀ (n : ℕ) (φ : L.Formulaω (Fin (k + n))), (forallTupleFrom k n φ).qrank = φ.qrank + n
  | 0, φ => by simp [forallTupleFrom]
  | n + 1, φ => by
    simp only [forallTupleFrom, qrank_forallTupleFrom k n, qrank_forallLastVar, add_assoc,
      one_add_natCast]

/-- The universal closure of `n` free variables adds `n` to the rank, on the right. -/
theorem qrank_forallTuple :
    ∀ (n : ℕ) (φ : L.Formulaω (Fin n)), (forallTuple n φ).qrank = φ.qrank + n
  | 0, φ => by simp [forallTuple]
  | n + 1, φ => by
    simp only [forallTuple, qrank_forallTuple n, qrank_forallLastVar, add_assoc, one_add_natCast]

/-- The existential closure of `n` free variables adds `n` to the rank, on the right. -/
theorem qrank_existsTuple :
    ∀ (n : ℕ) (φ : L.Formulaω (Fin n)), (existsTuple n φ).qrank = φ.qrank + n
  | 0, φ => by simp [existsTuple]
  | n + 1, φ => by
    simp only [existsTuple, qrank_existsTuple n, qrank_existsLastVar, add_assoc, one_add_natCast]

end FirstOrder.Language
