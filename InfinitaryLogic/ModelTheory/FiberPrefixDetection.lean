/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.ModelTheory.FiberTwoRow

/-!
# Finite-prefix detection for nondecreasing words

The combinatorial core of the profile upper bound, stated for an arbitrary **upward-closed**
predicate `D : U → Prop` on a linear order (`u ≤ v → D u → D v`), read as "the letter `u` is
default-like".  For a word `r`, its **non-default prefixes** are the nonempty prefixes `τ ⪯ r`
with `¬ D (last τ)` (`ndPrefixes`).

**Theorem** (`exists_short_distinguishing_prefix`): if two nondecreasing words `r` and `s` have
different non-default prefix sets, there is a nonempty label `τ` of length at most
`r.length + 1`, with `¬ D (last τ)`, that prefixes exactly one of them.

The extra position: a longer non-default prefix of `s` is cut down to length `r.length + 1`;
the cut is still a prefix of `s`, is not a prefix of `r` (too long), and is non-default because
its last letter is at most the last letter of the longer prefix (nondecreasing) and `D` is
upward closed, so `¬ D` is downward closed.

Nothing here involves structures, ordinals, countability, allowed sets, or nesting.  The
specialization to `D u ↔ B u ≅ B_*` and the allowed-position membership enter afterward, in
the profile statement.
-/

namespace FirstOrder.Language

namespace FiberAssembly

universe u

variable {U : Type u} [LinearOrder U]

/-- An upward-closed predicate on the letters. -/
def UpwardClosed (D : U → Prop) : Prop := ∀ {u v : U}, u ≤ v → D u → D v

/-- The non-default prefixes of a word: nonempty prefixes whose last letter is not
default-like. -/
def ndPrefixes (D : U → Prop) (r : List U) : Set (Label U) :=
  {τ | τ.1 <+: r ∧ ¬ D τ.last}

omit [LinearOrder U] in
theorem mem_ndPrefixes {D : U → Prop} {r : List U} {τ : Label U} :
    τ ∈ ndPrefixes D r ↔ τ.1 <+: r ∧ ¬ D τ.last := Iff.rfl

/-- A nonempty prefix of a nondecreasing word has its last letter at most the last letter of
any longer prefix. -/
theorem last_le_last_of_prefix {p q : List U} (hq : q.Pairwise (· ≤ ·)) (hpq : p <+: q)
    (hp : p ≠ []) (hq' : q ≠ []) : p.getLast hp ≤ q.getLast hq' :=
  le_getLast_of_pairwise hq hq' (hpq.subset (List.getLast_mem hp))

/-- Cutting a label to length `n + 1` yields a label. -/
def cutLabel (τ : Label U) (n : ℕ) : Label U :=
  ⟨τ.1.take (n + 1), by
    intro h
    have := congrArg List.length h
    simp only [List.length_take, List.length_nil] at this
    have hpos : 0 < τ.1.length := List.length_pos_of_ne_nil τ.2
    omega⟩

omit [LinearOrder U] in
theorem cutLabel_prefix (τ : Label U) (n : ℕ) : (cutLabel τ n).1 <+: τ.1 :=
  List.take_prefix _ _

omit [LinearOrder U] in
theorem cutLabel_length (τ : Label U) (n : ℕ) :
    (cutLabel τ n).1.length = min (n + 1) τ.1.length := by
  simp [cutLabel]

/-- **Finite-prefix detection.**  Nondecreasing words with different non-default prefix sets are
distinguished by a non-default label of length at most `r.length + 1` prefixing exactly one of
them. -/
theorem exists_short_distinguishing_prefix {D : U → Prop} (hD : UpwardClosed D) {r s : List U}
    (hs : s.Pairwise (· ≤ ·)) (hne : ndPrefixes D r ≠ ndPrefixes D s) :
    ∃ τ : Label U, τ.1.length ≤ r.length + 1 ∧ ¬ D τ.last ∧
      ¬ (τ.1 <+: r ↔ τ.1 <+: s) := by
  -- a label in one set and not the other
  have : ∃ τ : Label U, (τ ∈ ndPrefixes D r ∧ τ ∉ ndPrefixes D s) ∨
      (τ ∈ ndPrefixes D s ∧ τ ∉ ndPrefixes D r) := by
    by_contra hcon
    push Not at hcon
    apply hne
    ext τ
    exact ⟨fun h => (hcon τ).1 h, fun h => (hcon τ).2 h⟩
  obtain ⟨τ, ⟨hr, hns⟩ | ⟨hs', hnr⟩⟩ := this
  · -- a non-default prefix of `r` that is not one of `s`: already short
    refine ⟨τ, hr.1.length_le.trans (Nat.le_succ _), hr.2, fun h => hns ⟨h.mp hr.1, hr.2⟩⟩
  · -- a non-default prefix of `s` that is not one of `r`
    by_cases hlen : τ.1.length ≤ r.length + 1
    · exact ⟨τ, hlen, hs'.2, fun h => hnr ⟨h.mpr hs'.1, hs'.2⟩⟩
    · -- too long: cut it to length `r.length + 1`
      push Not at hlen
      refine ⟨cutLabel τ r.length, ?_, ?_, ?_⟩
      · rw [cutLabel_length]; exact min_le_left _ _
      · -- the cut is non-default: its last letter is at most the last letter of `τ`
        intro hDc
        apply hs'.2
        refine hD (last_le_last_of_prefix ?_ (cutLabel_prefix τ r.length) _ τ.2) hDc
        exact hs.sublist hs'.1.sublist
      · -- the cut prefixes `s` (through `τ`) but is too long to prefix `r`
        intro h
        have hcs : (cutLabel τ r.length).1 <+: s := (cutLabel_prefix τ r.length).trans hs'.1
        have hcr := h.mpr hcs
        have := hcr.length_le
        rw [cutLabel_length] at this
        omega

end FiberAssembly

end FirstOrder.Language
