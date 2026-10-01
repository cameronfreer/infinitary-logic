/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Lomega1omega.FiniteQuantification
import InfinitaryLogic.Lomega1omega.QuantifierClass
import InfinitaryLogic.Lomega1omega.QuantifierRank

/-!
# The ordinal-indexed `Σ^in_α` / `Π^in_α` hierarchy of `L_ω₁ω` formulas

Montalbán's classes of infinitary formulas are normal forms: `Σ^in_0 = Π^in_0` are the finitary
quantifier-free formulas; for `α ≥ 1`, `Σ^in_α` consists of the countable disjunctions of
formulas `∃ȳ ψ` with `ψ ∈ Π^in_β` for some `β < α`, and `Π^in_α` dually of the countable
conjunctions of `∀ȳ ψ` with `ψ ∈ Σ^in_β`, `β < α`.

Here they are approximated syntactically, without constructing any normal form, by one
**signed traversal** `inSigned α s φ` with the design of `universalSigned`
(`Lomega1omega/QuantifierClass.lean`): the sign `s` names the class being asked for, an
antecedent flips it, and the mutual dependence of the two classes through negation is
definitional.  A node of the asked kind (`all` or `iInf` at the `Π` sign, `iSup` at the `Σ` sign)
keeps the level and needs `1 ≤ α`; a node of the other kind must lie entirely in the other class
at some level `β` with `1 ≤ β < α`.

## Main declarations

* `inSigned α s φ`: the signed recursion; `IsPiIn α φ := inSigned α true φ` and
  `IsSigmaIn α φ := inSigned α false φ`.
* Constructor equations `inSigned_imp`, `inSigned_all_true`, `inSigned_all_false`,
  `inSigned_iInf_true`, …, and for the derived connectives `inSigned_not`, `inSigned_and`,
  `inSigned_or`, `inSigned_inf`, `inSigned_sup`, `inSigned_ex_true`, `inSigned_ex_false`.
* Order: `inSigned_mono` (`IsSigmaIn.mono`, `IsPiIn.mono`) and `inSigned_of_lt`
  (`IsSigmaIn.isPiIn_add_one`, `IsPiIn.isSigmaIn_add_one`), so `Σ^in_α ∪ Π^in_α` lies in
  `Σ^in_{α+1} ∩ Π^in_{α+1}`; `inSigned_zero_iff` (`Σ^in_0 = Π^in_0`).
* Negation duality: `isSigmaIn_not_iff`, `isPiIn_not_iff`.
* Closure at a level `α ≥ 1`: `isPiIn_all`, `isSigmaIn_ex`, `isPiIn_einf`, `isSigmaIn_esup`
  (with the exact forms `isPiIn_einf_iff`, `isSigmaIn_esup_iff`), finite blocks
  `isPiIn_forallBlock_iff`, `isSigmaIn_existsBlock_iff`; at every level: `isPiIn_imp`,
  `isSigmaIn_imp`, `isPiIn_inf`, `isSigmaIn_sup`; one level up:
  `IsSigmaIn.isPiIn_add_one_all`, `IsPiIn.isSigmaIn_add_one_ex`.
* Invariance under `castLE`, `relabel`, `subst`, `mapFreeVars`, `mapLanguage`.
* Level one against `universalSigned`: the exact characterization `inSigned_one_iff` through
  `connectiveSigned`, the inclusion `universalSigned_of_inSigned_one`, and
  `inSigned_one_toLω_iff_universalSigned`.
* Montalbán's literal normal forms: `NormalFormIn`, `IsSigmaInNF`, `IsPiInNF`, with
  `isSigmaInNF_esup`, `isPiInNF_einf`; a normal form lies in the signed class
  (`NormalFormIn.inSigned`, `IsSigmaInNF.isSigmaIn`, `IsPiInNF.isPiIn`) and has quantifier rank
  at most `ω · α` (`IsSigmaInNF.qrank_le`, `IsPiInNF.qrank_le`).
* Quantifier rank of the signed classes: `qrank_eq_zero_of_inSigned_zero` (level `0` only).

## Interpretation choices

* **Sign convention.** `true` is the `Π` sign and `false` the `Σ` sign, as in `universalSigned`
  (`true` = universal, `∀₁`), so that the level-one comparison reads
  `inSigned 1 s φ → universalSigned s φ` at the *same* sign.
* **Level `0`.** `inSigned 0 s φ` holds exactly when `φ` is built from `falsum`, equality and
  relation atoms by `imp`: no `all`, no `iSup`, no `iInf`, at either sign (`inSigned_zero_iff`).
  In particular `einf`/`esup` are never level `0`, even over a finite index type: the syntax does
  not record finiteness of an index.  Every same-level closure lemma for a quantifier or a
  countable connective therefore carries `1 ≤ α`.
* **`imp` policy.** `imp` is admitted at **every** level, with the antecedent read at the flipped
  sign: `inSigned α s (φ.imp ψ) ↔ inSigned α (!s) φ ∧ inSigned α s ψ`.  Hence each class is closed
  under `and`, `or` (and `not` exchanges the classes), and the traversal is negation-free except
  through the sign.  `imp` is not a constructor of Montalbán's normal forms; the rule is sound up
  to logical equivalence, because a finite disjunction or conjunction of `Π^in_α` formulas is
  equivalent to a `Π^in_α` normal form after merging quantifier blocks and distributing (and
  dually).
* **Closure within a level.** `Π^in_α` is closed under `∀` and countable conjunction, and
  `Σ^in_α` under `∃` and countable disjunction, at the same level, so a quantifier may sit over a
  countable connective of its own kind (`∀x ⋀ᵢ ψᵢ ≡ ⋀ᵢ ∀x ψᵢ`).  A node of the opposite kind drops
  to a strictly smaller level: a countable conjunction of `Σ^in_β` formulas is `Π^in_{β+1}`, and
  not in general `Σ^in_{β+1}` (a conjunction of atoms is `Π^in_1`, hence also `Σ^in_2`).
* **Relation to the normal forms.** `NormalFormIn` is Montalbán's literal syntax: a `Σ^in_α`
  normal form (`α ≥ 1`) is an `iSup` of existential blocks (finite iterations of `ex`) over
  `Π^in_β` normal forms with `β < α`, dually for `Π^in_α` with `iInf` and `all`, and level `0` is
  the finitary quantifier-free formulas.  Every normal form lies in the signed class of the same
  level and sign (`NormalFormIn.inSigned`).  Conversely, by the two equivalences above, each formula
  accepted by the traversal is logically equivalent to a normal form of the same level and kind;
  that converse is **not formalized**; `IsPiIn α` always means membership in the signed-traversal
  class.
* **Finite quantifier blocks.** A block `∀ȳ` is a finite iteration of `all` (`forallBlock`), and
  `∃ȳ` of `ex` (`existsBlock`); there is no separate block constructor, and a block of any finite
  length stays at its level.
* **Relation to `universalSigned`.** The level-one classes are the `∀₁`/`∃₁` classes of
  Harrison-Trainor–Kretschmer's convention cut down by one condition (`inSigned_one_iff`):
  `inSigned 1 s φ ↔ universalSigned s φ ∧ connectiveSigned s φ`, where `connectiveSigned s φ`
  says that no countable connective has the wrong sign (no `iSup` at the `Π` sign, no `iInf` at
  the `Σ` sign), the sign traced through `imp` as in `universalSigned`.  So they are *contained
  in* the `∀₁`/`∃₁` classes (`universalSigned_of_inSigned_one`), *agree* with them on formulas
  without countable connectives (`inSigned_one_toLω_iff_universalSigned`), and differ exactly at
  countable connectives of the wrong sign: `universalSigned` does not count the countable
  connectives and admits them at both signs, whereas `Σ^in_1` admits no `iInf` and `Π^in_1` no
  `iSup`, under a quantifier or not.  A countable conjunction of atoms is `∃₁` but not `Σ^in_1`
  (it is `Π^in_1`), and `∃x ⋀ᵢ ψᵢ` is `∃₁` but only `Σ^in_2`.  `universalSigned` is
  stated over `Language.{0, 0}` and free variables in `Type`, so only this comparison is pinned
  there; everything else is universe-polymorphic.
* **Quantifier rank.** The bound `qrank ≤ ω · α` holds for the normal forms
  (`IsSigmaInNF.qrank_le`, `IsPiInNF.qrank_le`; countable connectives are not counted, as in
  `qrank`), and for the signed classes **fails at every countable level `a ≥ 1`**: the closure of
  `Π^in_1` under `∀` over `⋀` admits `∀x ⋀ₖ ∀y₁ … yₖ ψ` with `ψ` atomic, of rank
  `ω + 1 > ω · 1`, and iterating the two steps gives `Π^in_1 ⊆ Π^in_a` sentences of unboundedly
  large countable rank.  (At levels `a ≥ ω₁` the bound holds trivially: `qrank` takes suprema of
  `ℕ`-indexed families only, so every rank is countable.)  Below `ω₁`, level `0` is the only
  bounded level of the signed classes (`qrank_eq_zero_of_inSigned_zero`).  Nor does the rank bound
  the level: quantifier-free formulas alternating `⋀` and `⋁` have rank `0` and unbounded level.

## References

* A. Montalbán, *A robuster Scott rank*, Proc. Amer. Math. Soc. 143 (2015), 5427–5436.
-/

universe u v u'

namespace FirstOrder.Language

namespace BoundedFormulaω

variable {L : Language.{u, v}} {α β : Type u'}

/-- **The signed `Σ^in`/`Π^in` traversal.**  `inSigned a true φ` says that `φ` lies in the
signed-traversal class `Π^in_a`, and `inSigned a false φ` in the signed-traversal class `Σ^in_a`
(they contain Montalbán's normal forms, `NormalFormIn.inSigned`; they agree with them only up to
logical equivalence, not formalized).  Atoms are in every class; an antecedent flips the sign;
`all` and `iInf` keep the level at the `Π` sign and `iSup` at the `Σ` sign, provided `1 ≤ a`; at
the other sign each of them must lie in the other class at some level `b` with `1 ≤ b < a`. -/
def inSigned : ∀ {n : ℕ}, Ordinal.{0} → Bool → L.BoundedFormulaω α n → Prop
  | _, _, _, .falsum => True
  | _, _, _, .equal _ _ => True
  | _, _, _, .rel _ _ => True
  | _, a, s, .imp φ ψ => inSigned a (!s) φ ∧ inSigned a s ψ
  | _, a, true, .all φ => 1 ≤ a ∧ inSigned a true φ
  | _, a, false, .all φ => ∃ b < a, 1 ≤ b ∧ inSigned b true φ
  | _, a, true, .iInf φs => 1 ≤ a ∧ ∀ i, inSigned a true (φs i)
  | _, a, false, .iInf φs => ∃ b < a, 1 ≤ b ∧ ∀ i, inSigned b true (φs i)
  | _, a, true, .iSup φs => ∃ b < a, 1 ≤ b ∧ ∀ i, inSigned b false (φs i)
  | _, a, false, .iSup φs => 1 ≤ a ∧ ∀ i, inSigned a false (φs i)

/-- `φ` lies in **the signed-traversal class `Π^in_a`** (contains Montalbán's normal forms,
`NormalFormIn.inSigned`; agrees with them only up to logical equivalence, not formalized): the
`true` sign of `inSigned`. -/
abbrev IsPiIn {n : ℕ} (a : Ordinal.{0}) (φ : L.BoundedFormulaω α n) : Prop := inSigned a true φ

/-- `φ` lies in **the signed-traversal class `Σ^in_a`** (contains Montalbán's normal forms,
`NormalFormIn.inSigned`; agrees with them only up to logical equivalence, not formalized): the
`false` sign of `inSigned`. -/
abbrev IsSigmaIn {n : ℕ} (a : Ordinal.{0}) (φ : L.BoundedFormulaω α n) : Prop :=
  inSigned a false φ

variable {n : ℕ} {a b : Ordinal.{0}} {s : Bool}

/-! ## Constructor equations -/

@[simp] theorem inSigned_falsum (a : Ordinal.{0}) (s : Bool) :
    inSigned a s (BoundedFormulaω.falsum : L.BoundedFormulaω α n) := trivial

@[simp] theorem inSigned_bot (a : Ordinal.{0}) (s : Bool) :
    inSigned a s (⊥ : L.BoundedFormulaω α n) := trivial

@[simp] theorem inSigned_equal (a : Ordinal.{0}) (s : Bool) (t₁ t₂ : L.Term (α ⊕ Fin n)) :
    inSigned a s (BoundedFormulaω.equal t₁ t₂) := trivial

@[simp] theorem inSigned_rel {l : ℕ} (a : Ordinal.{0}) (s : Bool) (R : L.Relations l)
    (ts : Fin l → L.Term (α ⊕ Fin n)) :
    inSigned a s (BoundedFormulaω.rel R ts) := trivial

@[simp] theorem inSigned_imp (a : Ordinal.{0}) (s : Bool) (φ ψ : L.BoundedFormulaω α n) :
    inSigned a s (φ.imp ψ) ↔ inSigned a (!s) φ ∧ inSigned a s ψ := Iff.rfl

@[simp] theorem inSigned_all_true (a : Ordinal.{0}) (φ : L.BoundedFormulaω α (n + 1)) :
    inSigned a true φ.all ↔ 1 ≤ a ∧ inSigned a true φ := Iff.rfl

@[simp] theorem inSigned_all_false (a : Ordinal.{0}) (φ : L.BoundedFormulaω α (n + 1)) :
    inSigned a false φ.all ↔ ∃ b < a, 1 ≤ b ∧ inSigned b true φ := Iff.rfl

@[simp] theorem inSigned_iInf_true (a : Ordinal.{0}) (φs : ℕ → L.BoundedFormulaω α n) :
    inSigned a true (BoundedFormulaω.iInf φs) ↔ 1 ≤ a ∧ ∀ i, inSigned a true (φs i) := Iff.rfl

@[simp] theorem inSigned_iInf_false (a : Ordinal.{0}) (φs : ℕ → L.BoundedFormulaω α n) :
    inSigned a false (BoundedFormulaω.iInf φs) ↔
      ∃ b < a, 1 ≤ b ∧ ∀ i, inSigned b true (φs i) := Iff.rfl

@[simp] theorem inSigned_iSup_true (a : Ordinal.{0}) (φs : ℕ → L.BoundedFormulaω α n) :
    inSigned a true (BoundedFormulaω.iSup φs) ↔
      ∃ b < a, 1 ≤ b ∧ ∀ i, inSigned b false (φs i) := Iff.rfl

@[simp] theorem inSigned_iSup_false (a : Ordinal.{0}) (φs : ℕ → L.BoundedFormulaω α n) :
    inSigned a false (BoundedFormulaω.iSup φs) ↔ 1 ≤ a ∧ ∀ i, inSigned a false (φs i) := Iff.rfl

/-! ## The derived connectives -/

/-- Negation **exchanges** the two classes at every level. -/
@[simp] theorem inSigned_not (a : Ordinal.{0}) (s : Bool) (φ : L.BoundedFormulaω α n) :
    inSigned a s φ.not ↔ inSigned a (!s) φ := by
  simp [BoundedFormulaInf.not]

@[simp] theorem inSigned_top (a : Ordinal.{0}) (s : Bool) :
    inSigned a s (⊤ : L.BoundedFormulaω α n) := ⟨trivial, trivial⟩

@[simp] theorem inSigned_and (a : Ordinal.{0}) (s : Bool) (φ ψ : L.BoundedFormulaω α n) :
    inSigned a s (φ.and ψ) ↔ inSigned a s φ ∧ inSigned a s ψ := by
  simp [BoundedFormulaω.and]

@[simp] theorem inSigned_or (a : Ordinal.{0}) (s : Bool) (φ ψ : L.BoundedFormulaω α n) :
    inSigned a s (φ.or ψ) ↔ inSigned a s φ ∧ inSigned a s ψ := by
  simp [BoundedFormulaω.or]

@[simp] theorem inSigned_inf (a : Ordinal.{0}) (s : Bool) (φ ψ : L.BoundedFormulaω α n) :
    inSigned a s (φ ⊓ ψ) ↔ inSigned a s φ ∧ inSigned a s ψ :=
  inSigned_and a s φ ψ

@[simp] theorem inSigned_sup (a : Ordinal.{0}) (s : Bool) (φ ψ : L.BoundedFormulaω α n) :
    inSigned a s (φ ⊔ ψ) ↔ inSigned a s φ ∧ inSigned a s ψ :=
  inSigned_or a s φ ψ

/-- An existential quantifier keeps the `Σ` level: `ex φ = (φ.not.all).not` meets its `all` at
the `Π` sign. -/
@[simp] theorem inSigned_ex_false (a : Ordinal.{0}) (φ : L.BoundedFormulaω α (n + 1)) :
    inSigned a false φ.ex ↔ 1 ≤ a ∧ inSigned a false φ := by
  simp [BoundedFormulaInf.ex]

/-- An existential quantifier is `Π^in_a` only through `Σ^in_b` for some `1 ≤ b < a`. -/
@[simp] theorem inSigned_ex_true (a : Ordinal.{0}) (φ : L.BoundedFormulaω α (n + 1)) :
    inSigned a true φ.ex ↔ ∃ b < a, 1 ≤ b ∧ inSigned b false φ := by
  simp [BoundedFormulaInf.ex]

/-! ## Level `0` -/

/-- **Level `0` is sign-independent**: `Σ^in_0 = Π^in_0`. -/
theorem inSigned_zero_iff (s t : Bool) (φ : L.BoundedFormulaω α n) :
    inSigned 0 s φ ↔ inSigned 0 t φ := by
  induction φ generalizing s t with
  | falsum => exact Iff.rfl
  | equal => exact Iff.rfl
  | rel => exact Iff.rfl
  | imp φ ψ ihφ ihψ => exact and_congr (ihφ _ _) (ihψ _ _)
  | all φ ih => cases s <;> cases t <;> simp
  | iSup φs ih => cases s <;> cases t <;> simp
  | iInf φs ih => cases s <;> cases t <;> simp

/-- A level-`0` formula has quantifier rank `0`. -/
theorem qrank_eq_zero_of_inSigned_zero {φ : L.BoundedFormulaω α n} (h : inSigned 0 s φ) :
    φ.qrank = 0 := by
  induction φ generalizing s with
  | falsum => rfl
  | equal => rfl
  | rel => rfl
  | imp φ ψ ihφ ihψ => simp [ihφ h.1, ihψ h.2]
  | all φ ih => cases s <;> simp at h
  | iSup φs ih => cases s <;> simp at h
  | iInf φs ih => cases s <;> simp at h

/-! ## Monotonicity and the step to the next level -/

/-- **Monotonicity in the level.** -/
theorem inSigned_mono (hab : a ≤ b) {φ : L.BoundedFormulaω α n} (h : inSigned a s φ) :
    inSigned b s φ := by
  induction φ generalizing a b s with
  | falsum => trivial
  | equal => trivial
  | rel => trivial
  | imp φ ψ ihφ ihψ => exact ⟨ihφ hab h.1, ihψ hab h.2⟩
  | all φ ih =>
    cases s
    · obtain ⟨c, hc, h⟩ := h
      exact ⟨c, hc.trans_le hab, h⟩
    · exact ⟨h.1.trans hab, ih hab h.2⟩
  | iSup φs ih =>
    cases s
    · exact ⟨h.1.trans hab, fun i ↦ ih i hab (h.2 i)⟩
    · obtain ⟨c, hc, h⟩ := h
      exact ⟨c, hc.trans_le hab, h⟩
  | iInf φs ih =>
    cases s
    · obtain ⟨c, hc, h⟩ := h
      exact ⟨c, hc.trans_le hab, h⟩
    · exact ⟨h.1.trans hab, fun i ↦ ih i hab (h.2 i)⟩

/-- `Σ^in_a ⊆ Π^in_{a+1}` and `Π^in_a ⊆ Σ^in_{a+1}`, at one stroke. -/
private theorem inSigned_add_one_not {φ : L.BoundedFormulaω α n} (h : inSigned a s φ) :
    inSigned (a + 1) (!s) φ := by
  induction φ generalizing s with
  | falsum => trivial
  | equal => trivial
  | rel => trivial
  | imp φ ψ ihφ ihψ => exact ⟨ihφ h.1, ihψ h.2⟩
  | all φ ih =>
    cases s
    · obtain ⟨c, hca, hc1, hφ⟩ := h
      have hc : c ≤ a + 1 := (hca.trans (lt_add_one a)).le
      exact ⟨hc1.trans hc, inSigned_mono hc hφ⟩
    · exact ⟨a, lt_add_one a, h⟩
  | iSup φs ih =>
    cases s
    · exact ⟨a, lt_add_one a, h⟩
    · obtain ⟨c, hca, hc1, hφ⟩ := h
      have hc : c ≤ a + 1 := (hca.trans (lt_add_one a)).le
      exact ⟨hc1.trans hc, fun i ↦ inSigned_mono hc (hφ i)⟩
  | iInf φs ih =>
    cases s
    · obtain ⟨c, hca, hc1, hφ⟩ := h
      have hc : c ≤ a + 1 := (hca.trans (lt_add_one a)).le
      exact ⟨hc1.trans hc, fun i ↦ inSigned_mono hc (hφ i)⟩
    · exact ⟨a, lt_add_one a, h⟩

/-- **Both classes at a level lie in both classes at every higher level**:
`Σ^in_a ∪ Π^in_a ⊆ Σ^in_b ∩ Π^in_b` for `a < b`. -/
theorem inSigned_of_lt (hab : a < b) (t : Bool) {φ : L.BoundedFormulaω α n}
    (h : inSigned a s φ) : inSigned b t φ := by
  cases s <;> cases t
  · exact inSigned_mono hab.le h
  · exact inSigned_mono (Order.add_one_le_of_lt hab) (inSigned_add_one_not h)
  · exact inSigned_mono (Order.add_one_le_of_lt hab) (inSigned_add_one_not h)
  · exact inSigned_mono hab.le h

/-- Monotonicity of `Σ^in` in the level. -/
theorem IsSigmaIn.mono {φ : L.BoundedFormulaω α n} (hab : a ≤ b) (h : IsSigmaIn a φ) :
    IsSigmaIn b φ :=
  inSigned_mono hab h

/-- Monotonicity of `Π^in` in the level. -/
theorem IsPiIn.mono {φ : L.BoundedFormulaω α n} (hab : a ≤ b) (h : IsPiIn a φ) :
    IsPiIn b φ :=
  inSigned_mono hab h

/-- `Σ^in_a ⊆ Π^in_{a+1}`. -/
theorem IsSigmaIn.isPiIn_add_one {φ : L.BoundedFormulaω α n} (h : IsSigmaIn a φ) :
    IsPiIn (a + 1) φ :=
  inSigned_of_lt (lt_add_one a) true h

/-- `Π^in_a ⊆ Σ^in_{a+1}`. -/
theorem IsPiIn.isSigmaIn_add_one {φ : L.BoundedFormulaω α n} (h : IsPiIn a φ) :
    IsSigmaIn (a + 1) φ :=
  inSigned_of_lt (lt_add_one a) false h

/-! ## Negation duality -/

/-- `¬φ ∈ Σ^in_a ↔ φ ∈ Π^in_a`. -/
theorem isSigmaIn_not_iff {φ : L.BoundedFormulaω α n} : IsSigmaIn a φ.not ↔ IsPiIn a φ :=
  inSigned_not a false φ

/-- `¬φ ∈ Π^in_a ↔ φ ∈ Σ^in_a`. -/
theorem isPiIn_not_iff {φ : L.BoundedFormulaω α n} : IsPiIn a φ.not ↔ IsSigmaIn a φ :=
  inSigned_not a true φ

/-! ## Finite connectives at every level -/

/-- An implication with a `Σ^in_a` antecedent and a `Π^in_a` consequent is `Π^in_a`. -/
theorem isPiIn_imp {φ ψ : L.BoundedFormulaω α n} (hφ : IsSigmaIn a φ) (hψ : IsPiIn a ψ) :
    IsPiIn a (φ.imp ψ) :=
  ⟨hφ, hψ⟩

/-- An implication with a `Π^in_a` antecedent and a `Σ^in_a` consequent is `Σ^in_a`. -/
theorem isSigmaIn_imp {φ ψ : L.BoundedFormulaω α n} (hφ : IsPiIn a φ) (hψ : IsSigmaIn a ψ) :
    IsSigmaIn a (φ.imp ψ) :=
  ⟨hφ, hψ⟩

/-- `Π^in_a` is closed under binary conjunction. -/
theorem isPiIn_inf {φ ψ : L.BoundedFormulaω α n} (hφ : IsPiIn a φ) (hψ : IsPiIn a ψ) :
    IsPiIn a (φ ⊓ ψ) :=
  (inSigned_inf a true φ ψ).2 ⟨hφ, hψ⟩

/-- `Σ^in_a` is closed under binary disjunction. -/
theorem isSigmaIn_sup {φ ψ : L.BoundedFormulaω α n} (hφ : IsSigmaIn a φ) (hψ : IsSigmaIn a ψ) :
    IsSigmaIn a (φ ⊔ ψ) :=
  (inSigned_sup a false φ ψ).2 ⟨hφ, hψ⟩

/-! ## Quantifiers and finite blocks -/

/-- `Π^in_a` is closed under `∀` at every level `a ≥ 1`. -/
theorem isPiIn_all {φ : L.BoundedFormulaω α (n + 1)} (ha : 1 ≤ a) (h : IsPiIn a φ) :
    IsPiIn a φ.all :=
  ⟨ha, h⟩

/-- `Σ^in_a` is closed under `∃` at every level `a ≥ 1`. -/
theorem isSigmaIn_ex {φ : L.BoundedFormulaω α (n + 1)} (ha : 1 ≤ a) (h : IsSigmaIn a φ) :
    IsSigmaIn a φ.ex :=
  (inSigned_ex_false a φ).2 ⟨ha, h⟩

/-- A universal quantifier over a `Σ^in_a` formula is `Π^in_{a+1}`. -/
theorem IsSigmaIn.isPiIn_add_one_all {φ : L.BoundedFormulaω α (n + 1)} (h : IsSigmaIn a φ) :
    IsPiIn (a + 1) φ.all :=
  isPiIn_all le_add_self h.isPiIn_add_one

/-- An existential quantifier over a `Π^in_a` formula is `Σ^in_{a+1}`. -/
theorem IsPiIn.isSigmaIn_add_one_ex {φ : L.BoundedFormulaω α (n + 1)} (h : IsPiIn a φ) :
    IsSigmaIn (a + 1) φ.ex :=
  isSigmaIn_ex le_add_self h.isSigmaIn_add_one

/-- A finite universal block keeps a `Π^in` level `a ≥ 1`. -/
theorem isPiIn_forallBlock_iff (ha : 1 ≤ a) :
    ∀ {k : ℕ} (φ : L.BoundedFormulaω α (n + k)), IsPiIn a (forallBlock φ) ↔ IsPiIn a φ
  | 0, _ => Iff.rfl
  | _ + 1, φ => (isPiIn_forallBlock_iff ha φ.all).trans (and_iff_right ha)

/-- A finite existential block keeps a `Σ^in` level `a ≥ 1`. -/
theorem isSigmaIn_existsBlock_iff (ha : 1 ≤ a) :
    ∀ {k : ℕ} (φ : L.BoundedFormulaω α (n + k)), IsSigmaIn a (existsBlock φ) ↔ IsSigmaIn a φ
  | 0, _ => Iff.rfl
  | _ + 1, φ =>
    (isSigmaIn_existsBlock_iff ha φ.ex).trans ((inSigned_ex_false a φ).trans (and_iff_right ha))

/-! ## Countable connectives over an `Encodable` index -/

/-- `Π^in_a` membership of a countable conjunction, exactly; the `⊤` padding of `einf` is
admitted. -/
@[simp] theorem isPiIn_einf_iff {ι : Type*} [Encodable ι] (φs : ι → L.BoundedFormulaω α n) :
    IsPiIn a (BoundedFormulaω.einf φs) ↔ 1 ≤ a ∧ ∀ i, IsPiIn a (φs i) := by
  rw [BoundedFormulaω.einf, IsPiIn, inSigned_iInf_true]
  refine and_congr_right fun _ ↦ ⟨fun h i ↦ ?_, fun h k ↦ ?_⟩
  · simpa [Encodable.encodek] using h (Encodable.encode i)
  · cases hd : Encodable.decode (α := ι) k with
    | none => exact inSigned_top a true
    | some i => exact h i

/-- `Σ^in_a` membership of a countable disjunction, exactly; the `⊥` padding of `esup` is
admitted. -/
@[simp] theorem isSigmaIn_esup_iff {ι : Type*} [Encodable ι] (φs : ι → L.BoundedFormulaω α n) :
    IsSigmaIn a (BoundedFormulaω.esup φs) ↔ 1 ≤ a ∧ ∀ i, IsSigmaIn a (φs i) := by
  rw [BoundedFormulaω.esup, IsSigmaIn, inSigned_iSup_false]
  refine and_congr_right fun _ ↦ ⟨fun h i ↦ ?_, fun h k ↦ ?_⟩
  · simpa [Encodable.encodek] using h (Encodable.encode i)
  · cases hd : Encodable.decode (α := ι) k with
    | none => exact inSigned_bot a false
    | some i => exact h i

/-- `Π^in_a` is closed under countable conjunction at every level `a ≥ 1`. -/
theorem isPiIn_einf {ι : Type*} [Encodable ι] {φs : ι → L.BoundedFormulaω α n} (ha : 1 ≤ a)
    (h : ∀ i, IsPiIn a (φs i)) : IsPiIn a (BoundedFormulaω.einf φs) :=
  (isPiIn_einf_iff φs).2 ⟨ha, h⟩

/-- `Σ^in_a` is closed under countable disjunction at every level `a ≥ 1`. -/
theorem isSigmaIn_esup {ι : Type*} [Encodable ι] {φs : ι → L.BoundedFormulaω α n} (ha : 1 ≤ a)
    (h : ∀ i, IsSigmaIn a (φs i)) : IsSigmaIn a (BoundedFormulaω.esup φs) :=
  (isSigmaIn_esup_iff φs).2 ⟨ha, h⟩

/-! ## Stability under the variable and symbol operations -/

/-- The classes are invariant under `castLE`. -/
theorem inSigned_castLE {m : ℕ} (h : m ≤ n) (a : Ordinal.{0}) (s : Bool)
    (φ : L.BoundedFormulaω α m) : inSigned a s (φ.castLE h) ↔ inSigned a s φ := by
  induction φ generalizing n a s with
  | falsum => exact Iff.rfl
  | equal => exact Iff.rfl
  | rel => exact Iff.rfl
  | imp φ ψ ihφ ihψ => exact and_congr (ihφ h _ _) (ihψ h _ _)
  | all φ ih =>
    cases s
    · exact exists_congr fun b ↦ and_congr_right fun _ ↦ and_congr_right fun _ ↦ ih _ _ _
    · exact and_congr_right fun _ ↦ ih _ _ _
  | iSup φs ih =>
    cases s
    · exact and_congr_right fun _ ↦ forall_congr' fun i ↦ ih i h _ _
    · exact exists_congr fun b ↦ and_congr_right fun _ ↦ and_congr_right fun _ ↦
        forall_congr' fun i ↦ ih i h _ _
  | iInf φs ih =>
    cases s
    · exact exists_congr fun b ↦ and_congr_right fun _ ↦ and_congr_right fun _ ↦
        forall_congr' fun i ↦ ih i h _ _
    · exact and_congr_right fun _ ↦ forall_congr' fun i ↦ ih i h _ _

/-- The classes are invariant under `relabel`; its `all` case is a `castLE`. -/
theorem inSigned_relabel {p : ℕ} (g : α → β ⊕ Fin p) (a : Ordinal.{0}) (s : Bool)
    (φ : L.BoundedFormulaω α n) : inSigned a s (φ.relabel g) ↔ inSigned a s φ := by
  induction φ generalizing a s with
  | falsum => exact Iff.rfl
  | equal => exact Iff.rfl
  | rel => exact Iff.rfl
  | imp φ ψ ihφ ihψ => exact and_congr (ihφ _ _) (ihψ _ _)
  | all φ ih =>
    cases s
    · show (∃ b < a, 1 ≤ b ∧ inSigned b true (_ : L.BoundedFormulaω β _)) ↔ _
      simp only [inSigned_castLE, ih]
      exact Iff.rfl
    · show 1 ≤ a ∧ inSigned a true (_ : L.BoundedFormulaω β _) ↔ _
      simp only [inSigned_castLE, ih]
      exact Iff.rfl
  | iSup φs ih =>
    cases s
    · exact and_congr_right fun _ ↦ forall_congr' fun i ↦ ih i _ _
    · exact exists_congr fun b ↦ and_congr_right fun _ ↦ and_congr_right fun _ ↦
        forall_congr' fun i ↦ ih i _ _
  | iInf φs ih =>
    cases s
    · exact exists_congr fun b ↦ and_congr_right fun _ ↦ and_congr_right fun _ ↦
        forall_congr' fun i ↦ ih i _ _
    · exact and_congr_right fun _ ↦ forall_congr' fun i ↦ ih i _ _

/-- The classes are invariant under substitution of terms for the free variables. -/
theorem inSigned_subst (tf : α → L.Term β) (a : Ordinal.{0}) (s : Bool)
    (φ : L.BoundedFormulaω α n) : inSigned a s (φ.subst tf) ↔ inSigned a s φ := by
  induction φ generalizing a s with
  | falsum => exact Iff.rfl
  | equal => exact Iff.rfl
  | rel => exact Iff.rfl
  | imp φ ψ ihφ ihψ => exact and_congr (ihφ _ _) (ihψ _ _)
  | all φ ih =>
    cases s
    · exact exists_congr fun b ↦ and_congr_right fun _ ↦ and_congr_right fun _ ↦ ih _ _
    · exact and_congr_right fun _ ↦ ih _ _
  | iSup φs ih =>
    cases s
    · exact and_congr_right fun _ ↦ forall_congr' fun i ↦ ih i _ _
    · exact exists_congr fun b ↦ and_congr_right fun _ ↦ and_congr_right fun _ ↦
        forall_congr' fun i ↦ ih i _ _
  | iInf φs ih =>
    cases s
    · exact exists_congr fun b ↦ and_congr_right fun _ ↦ and_congr_right fun _ ↦
        forall_congr' fun i ↦ ih i _ _
    · exact and_congr_right fun _ ↦ forall_congr' fun i ↦ ih i _ _

/-- The classes are invariant under renaming the free variables. -/
theorem inSigned_mapFreeVars (f : α → β) (a : Ordinal.{0}) (s : Bool)
    (φ : L.BoundedFormulaω α n) : inSigned a s (φ.mapFreeVars f) ↔ inSigned a s φ := by
  induction φ generalizing a s with
  | falsum => exact Iff.rfl
  | equal => exact Iff.rfl
  | rel => exact Iff.rfl
  | imp φ ψ ihφ ihψ => exact and_congr (ihφ _ _) (ihψ _ _)
  | all φ ih =>
    cases s
    · exact exists_congr fun b ↦ and_congr_right fun _ ↦ and_congr_right fun _ ↦ ih _ _
    · exact and_congr_right fun _ ↦ ih _ _
  | iSup φs ih =>
    cases s
    · exact and_congr_right fun _ ↦ forall_congr' fun i ↦ ih i _ _
    · exact exists_congr fun b ↦ and_congr_right fun _ ↦ and_congr_right fun _ ↦
        forall_congr' fun i ↦ ih i _ _
  | iInf φs ih =>
    cases s
    · exact exists_congr fun b ↦ and_congr_right fun _ ↦ and_congr_right fun _ ↦
        forall_congr' fun i ↦ ih i _ _
    · exact and_congr_right fun _ ↦ forall_congr' fun i ↦ ih i _ _

/-- The classes are invariant under language maps: `mapLanguage` rewrites terms and symbols only
and keeps every connective and quantifier node. -/
theorem inSigned_mapLanguage {L' : Language.{u, v}} (g : L →ᴸ L') (a : Ordinal.{0}) (s : Bool)
    (φ : L.BoundedFormulaω α n) : inSigned a s (φ.mapLanguage g) ↔ inSigned a s φ := by
  induction φ generalizing a s with
  | falsum => exact Iff.rfl
  | equal => exact Iff.rfl
  | rel => exact Iff.rfl
  | imp φ ψ ihφ ihψ => exact and_congr (ihφ _ _) (ihψ _ _)
  | all φ ih =>
    cases s
    · exact exists_congr fun b ↦ and_congr_right fun _ ↦ and_congr_right fun _ ↦ ih _ _
    · exact and_congr_right fun _ ↦ ih _ _
  | iSup φs ih =>
    cases s
    · exact and_congr_right fun _ ↦ forall_congr' fun i ↦ ih i _ _
    · exact exists_congr fun b ↦ and_congr_right fun _ ↦ and_congr_right fun _ ↦
        forall_congr' fun i ↦ ih i _ _
  | iInf φs ih =>
    cases s
    · exact exists_congr fun b ↦ and_congr_right fun _ ↦ and_congr_right fun _ ↦
        forall_congr' fun i ↦ ih i _ _
    · exact and_congr_right fun _ ↦ forall_congr' fun i ↦ ih i _ _

/-! ## Montalbán's normal forms

The literal classes, as an inductive predicate.  They are not closed under the operations above
(not even under monotonicity: a quantifier-free formula is a `Σ^in_0` normal form but not a
`Σ^in_1` one), which is why the signed traversal is the working notion; what they add is the
quantifier-rank bound, which fails for the signed classes. -/

/-- **Montalbán's normal forms.**  `NormalFormIn a s false φ` says that `φ` is literally a
`Π^in_a` normal form (`s = true`) or a `Σ^in_a` normal form (`s = false`); `NormalFormIn a s true φ`
says that `φ` is a finite block of quantifiers of the kind of `s` (`∀` for `true`, `∃` for
`false`) over a normal form of the other kind at a level `b < a`. -/
inductive NormalFormIn : Ordinal.{0} → Bool → Bool → ∀ {n : ℕ}, L.BoundedFormulaω α n → Prop
  /-- Level `0`: the finitary quantifier-free formulas, at either sign. -/
  | zero {s : Bool} {n : ℕ} {φ : L.BoundedFormulaω α n} (h : inSigned 0 true φ) :
      NormalFormIn 0 s false φ
  /-- The empty block: a normal form of the other kind at a lower level. -/
  | base {a b : Ordinal.{0}} {s : Bool} {n : ℕ} {φ : L.BoundedFormulaω α n} (hb : b < a)
      (h : NormalFormIn b (!s) false φ) : NormalFormIn a s true φ
  /-- One more `∃` on an existential block. -/
  | ex {a : Ordinal.{0}} {n : ℕ} {φ : L.BoundedFormulaω α (n + 1)}
      (h : NormalFormIn a false true φ) : NormalFormIn a false true φ.ex
  /-- One more `∀` on a universal block. -/
  | all {a : Ordinal.{0}} {n : ℕ} {φ : L.BoundedFormulaω α (n + 1)}
      (h : NormalFormIn a true true φ) : NormalFormIn a true true φ.all
  /-- A countable disjunction of existential blocks. -/
  | iSup {a : Ordinal.{0}} {n : ℕ} {φs : ℕ → L.BoundedFormulaω α n}
      (h : ∀ i, NormalFormIn a false true (φs i)) : NormalFormIn a false false (iSup φs)
  /-- A countable conjunction of universal blocks. -/
  | iInf {a : Ordinal.{0}} {n : ℕ} {φs : ℕ → L.BoundedFormulaω α n}
      (h : ∀ i, NormalFormIn a true true (φs i)) : NormalFormIn a true false (iInf φs)

/-- `φ` is literally a **`Σ^in_a` normal form**: a countable disjunction of existential blocks
over `Π^in_b` normal forms, `b < a` (for `a = 0`: finitary quantifier-free). -/
abbrev IsSigmaInNF (a : Ordinal.{0}) (φ : L.BoundedFormulaω α n) : Prop :=
  NormalFormIn a false false φ

/-- `φ` is literally a **`Π^in_a` normal form**: a countable conjunction of universal blocks over
`Σ^in_b` normal forms, `b < a` (for `a = 0`: finitary quantifier-free). -/
abbrev IsPiInNF (a : Ordinal.{0}) (φ : L.BoundedFormulaω α n) : Prop :=
  NormalFormIn a true false φ

private theorem NormalFormIn.inSigned_aux {blk : Bool} {φ : L.BoundedFormulaω α n}
    (h : NormalFormIn a s blk φ) : inSigned a s φ ∧ (blk = true → 1 ≤ a) := by
  induction h with
  | zero h => exact ⟨(inSigned_zero_iff _ _ _).1 h, fun h ↦ (nomatch h)⟩
  | base hb _ ih =>
    have ha : (1 : Ordinal.{0}) ≤ _ := Order.one_le_iff_pos.2 (pos_of_gt hb)
    exact ⟨inSigned_of_lt hb _ ih.1, fun _ ↦ ha⟩
  | ex _ ih =>
    have ha := ih.2 rfl
    exact ⟨isSigmaIn_ex ha ih.1, fun _ ↦ ha⟩
  | all _ ih =>
    have ha := ih.2 rfl
    exact ⟨isPiIn_all ha ih.1, fun _ ↦ ha⟩
  | iSup _ ih =>
    exact ⟨⟨(ih 0).2 rfl, fun i ↦ (ih i).1⟩, fun h ↦ (nomatch h)⟩
  | iInf _ ih =>
    exact ⟨⟨(ih 0).2 rfl, fun i ↦ (ih i).1⟩, fun h ↦ (nomatch h)⟩

/-- **A normal form lies in the signed class** of the same level and sign; so does a block. -/
theorem NormalFormIn.inSigned {blk : Bool} {φ : L.BoundedFormulaω α n}
    (h : NormalFormIn a s blk φ) : inSigned a s φ :=
  h.inSigned_aux.1

open Ordinal in
private theorem NormalFormIn.qrank_aux {blk : Bool} {φ : L.BoundedFormulaω α n}
    (h : NormalFormIn a s blk φ) :
    (blk = false → φ.qrank ≤ ω * a) ∧ (blk = true → φ.qrank < ω * a) := by
  induction h with
  | zero h =>
    exact ⟨fun _ ↦ (qrank_eq_zero_of_inSigned_zero h).trans_le (zero_le), fun h ↦ (nomatch h)⟩
  | @base a b _ _ _ hb _ ih =>
    refine ⟨fun h ↦ (nomatch h), fun _ ↦ ?_⟩
    calc _ ≤ ω * b := ih.1 rfl
      _ < ω * b + ω := lt_add_of_pos_right _ omega0_pos
      _ = ω * (b + 1) := (mul_add_one _ _).symm
      _ ≤ ω * a := mul_le_mul_right (Order.add_one_le_of_lt hb) _
  | @ex a _ _ hφ ih =>
    refine ⟨fun h ↦ (nomatch h), fun _ ↦ ?_⟩
    have ha : 0 < a := Order.one_le_iff_pos.1 (hφ.inSigned_aux.2 rfl)
    rw [qrank_ex]
    exact (isSuccLimit_mul_left isSuccLimit_omega0 ha).add_one_lt (ih.2 rfl)
  | @all a _ _ hφ ih =>
    refine ⟨fun h ↦ (nomatch h), fun _ ↦ ?_⟩
    have ha : 0 < a := Order.one_le_iff_pos.1 (hφ.inSigned_aux.2 rfl)
    rw [qrank_all]
    exact (isSuccLimit_mul_left isSuccLimit_omega0 ha).add_one_lt (ih.2 rfl)
  | iSup _ ih =>
    exact ⟨fun _ ↦ by rw [qrank_iSup]; exact Ordinal.iSup_le fun i ↦ ((ih i).2 rfl).le,
      fun h ↦ (nomatch h)⟩
  | iInf _ ih =>
    exact ⟨fun _ ↦ by rw [qrank_iInf]; exact Ordinal.iSup_le fun i ↦ ((ih i).2 rfl).le,
      fun h ↦ (nomatch h)⟩

/-- A `Σ^in_a` normal form lies in `Σ^in_a`. -/
theorem IsSigmaInNF.isSigmaIn {φ : L.BoundedFormulaω α n} (h : IsSigmaInNF a φ) :
    IsSigmaIn a φ :=
  NormalFormIn.inSigned h

/-- A `Π^in_a` normal form lies in `Π^in_a`. -/
theorem IsPiInNF.isPiIn {φ : L.BoundedFormulaω α n} (h : IsPiInNF a φ) : IsPiIn a φ :=
  NormalFormIn.inSigned h

/-- **A `Σ^in_a` normal form has quantifier rank at most `ω · a`** (countable connectives are not
counted). -/
theorem IsSigmaInNF.qrank_le {φ : L.BoundedFormulaω α n} (h : IsSigmaInNF a φ) :
    φ.qrank ≤ Ordinal.omega0 * a :=
  (NormalFormIn.qrank_aux h).1 rfl

/-- **A `Π^in_a` normal form has quantifier rank at most `ω · a`** (countable connectives are not
counted). -/
theorem IsPiInNF.qrank_le {φ : L.BoundedFormulaω α n} (h : IsPiInNF a φ) :
    φ.qrank ≤ Ordinal.omega0 * a :=
  (NormalFormIn.qrank_aux h).1 rfl

/-- A countable disjunction, over an `Encodable` index, of existential blocks at a level `a ≥ 1`
is a `Σ^in_a` normal form; the `⊥` padding of `esup` is a level-`0` block. -/
theorem isSigmaInNF_esup {ι : Type*} [Encodable ι] {φs : ι → L.BoundedFormulaω α n}
    (ha : 1 ≤ a) (h : ∀ i, NormalFormIn a false true (φs i)) : IsSigmaInNF a (esup φs) := by
  refine NormalFormIn.iSup fun k ↦ ?_
  cases hd : Encodable.decode (α := ι) k with
  | none => exact .base (b := 0) (Order.one_le_iff_pos.1 ha) (.zero trivial)
  | some i => exact h i

/-- A countable conjunction, over an `Encodable` index, of universal blocks at a level `a ≥ 1` is
a `Π^in_a` normal form; the `⊤` padding of `einf` is a level-`0` block. -/
theorem isPiInNF_einf {ι : Type*} [Encodable ι] {φs : ι → L.BoundedFormulaω α n}
    (ha : 1 ≤ a) (h : ∀ i, NormalFormIn a true true (φs i)) : IsPiInNF a (einf φs) := by
  refine NormalFormIn.iInf fun k ↦ ?_
  cases hd : Encodable.decode (α := ι) k with
  | none => exact .base (b := 0) (Order.one_le_iff_pos.1 ha) (.zero ⟨trivial, trivial⟩)
  | some i => exact h i

/-! ## Level one against the `∀₁`/`∃₁` classes

`universalSigned` lives over `Language.{0, 0}` and free variables in `Type`, so the comparison
section `LevelOne`, and only it, is stated there. -/

/-- **No countable connective of the wrong sign**: `connectiveSigned true φ` says that `φ` has no
`iSup` at the `Π` sign and `connectiveSigned false φ` no `iInf` at the `Σ` sign, the sign traced
through `imp` as in `universalSigned`; quantifiers are not constrained. -/
def connectiveSigned : ∀ {n : ℕ}, Bool → L.BoundedFormulaω α n → Prop
  | _, _, .falsum => True
  | _, _, .equal _ _ => True
  | _, _, .rel _ _ => True
  | _, s, .imp φ ψ => connectiveSigned (!s) φ ∧ connectiveSigned s ψ
  | _, s, .all φ => connectiveSigned s φ
  | _, s, .iSup φs => s = false ∧ ∀ i, connectiveSigned s (φs i)
  | _, s, .iInf φs => s = true ∧ ∀ i, connectiveSigned s (φs i)

section LevelOne

variable {L : Language.{0, 0}} {α : Type}

private theorem not_exists_lt_one {P : Ordinal.{0} → Prop} :
    ¬ ∃ b < (1 : Ordinal.{0}), 1 ≤ b ∧ P b :=
  fun ⟨_, hb, hb1, _⟩ ↦ (hb1.trans_lt hb).false

/-- **Level one is `∀₁`/`∃₁` without wrong-sign countable connectives**: `Π^in_1` is exactly the
`∀₁` formulas with no `iSup` at the `Π` sign, and `Σ^in_1` the `∃₁` formulas with no `iInf` at the
`Σ` sign, the sign traced through `imp`. -/
theorem inSigned_one_iff (s : Bool) (φ : L.BoundedFormulaω α n) :
    inSigned 1 s φ ↔ universalSigned s φ ∧ connectiveSigned s φ := by
  induction φ generalizing s with
  | falsum => exact iff_of_true trivial ⟨trivial, trivial⟩
  | equal => exact iff_of_true trivial ⟨trivial, trivial⟩
  | rel => exact iff_of_true trivial ⟨trivial, trivial⟩
  | imp φ ψ ihφ ihψ => exact (and_congr (ihφ _) (ihψ _)).trans and_and_and_comm
  | all φ ih => cases s <;> simp [connectiveSigned, ih]
  | iSup φs ih => cases s <;> simp [connectiveSigned, ih, forall_and]
  | iInf φs ih => cases s <;> simp [connectiveSigned, ih, forall_and]

/-- **`Σ^in_1 ⊆ ∃₁` and `Π^in_1 ⊆ ∀₁`**, at the same sign.  The inclusion is strict: the
countable connectives of the wrong sign, which `universalSigned` admits, are excluded here
(`inSigned_one_iff`). -/
theorem universalSigned_of_inSigned_one {φ : L.BoundedFormulaω α n} (h : inSigned 1 s φ) :
    universalSigned s φ :=
  ((inSigned_one_iff s φ).1 h).1

/-- **On formulas without countable connectives the level-one classes are `∀₁`/`∃₁`**: for the
image of a first-order formula, `Σ^in_1` is exactly `∃₁` and `Π^in_1` exactly `∀₁`.  In
particular a finitary existential formula is `Σ^in_1` after `toLω`. -/
theorem inSigned_one_toLω_iff_universalSigned (s : Bool) (φ : L.BoundedFormula α n) :
    inSigned 1 s φ.toLω ↔ universalSigned s φ.toLω := by
  induction φ generalizing s with
  | falsum => exact Iff.rfl
  | equal => exact Iff.rfl
  | rel => exact Iff.rfl
  | imp φ ψ ihφ ihψ => exact and_congr (ihφ _) (ihψ _)
  | all φ ih =>
    cases s
    · exact iff_of_false not_exists_lt_one fun h ↦ Bool.false_ne_true h.1
    · exact and_congr (iff_of_true le_rfl rfl) (ih true)

end LevelOne

end BoundedFormulaω

end FirstOrder.Language
