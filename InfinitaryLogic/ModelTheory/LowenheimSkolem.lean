/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Lomega1omega.Theory
import InfinitaryLogic.ModelExistence.Theorem

/-!
# Downward Löwenheim-Skolem for Lω₁ω

This file proves the downward Löwenheim-Skolem theorem for Lω₁ω:
any satisfiable sentence in a countable language has a countable model.

## Main Results

- `downward_LS`: For a countable relational language, any satisfiable Lω₁ω sentence
  has a countable model.

## References

- [Marker, "Lectures on Infinitary Model Theory", 2016]
- [Keisler-Knight, "Barwise: Infinitary Logic and Admissible Sets", 2004]
-/

universe u v w

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}}

open FirstOrder Structure

/-- **Downward Löwenheim-Skolem for Lω₁ω**: Any satisfiable sentence in a countable
relational language has a countable model.

The proof uses the model existence theorem: from a model of φ, construct a
consistency property witnessing that {φ} is consistent, then apply model existence
to get a countable model. -/
theorem downward_LS [Countable (Σ l, L.Relations l)]
    (φ : L.Sentenceω) (M : Type*) [L.Structure M]
    (hM : Sentenceω.Realize φ M) :
    ∃ (N : Type) (_ : L.Structure N) (_ : Countable N),
      Sentenceω.Realize φ N := by
  sorry

/-- Downward LS for theories: any satisfiable Lω₁ω theory in a countable language
has a countable model. -/
theorem downward_LS_theory [Countable (Σ l, L.Relations l)]
    (T : L.Theoryω) (M : Type*) [L.Structure M]
    (hM : T.Model M) :
    ∃ (N : Type) (_ : L.Structure N) (_ : Countable N),
      T.Model N := by
  sorry

end Language

end FirstOrder
