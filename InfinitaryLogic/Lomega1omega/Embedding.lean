/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Linf.Countability
import InfinitaryLogic.Lomega1omega.Operations

/-!
# Embeddings between Lω₁ω and L∞ω

This file defines embeddings between Lω₁ω (countable infinitary logic) and L∞ω (arbitrary
infinitary logic).

## Main Definitions

- `BoundedFormulaω.toLinf`: Embeds Lω₁ω into L∞ω (uses ℕ as index type)
- `BoundedFormulaInf.ofCountable`: Converts countable L∞ω back to Lω₁ω via Encodable

## Main Results

- `realize_toLinf`: Semantics preserved by toLinf embedding
- `realize_ofCountable`: Semantics preserved by ofCountable conversion
-/

universe u v u' w uι

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}} {α : Type u'} {n : ℕ}

namespace BoundedFormulaω

/-- Embeds a Lω₁ω formula into L∞ω **at an arbitrary target index universe** `uι`.

The Lω₁ω infinitary nodes branch over `ℕ : Type 0`, so hitting a target in `Type uι` requires a
branch type in that universe: `ULift.{uι} ℕ`.  Writing the target as `L.BoundedFormulaInf α n` and
branching on `ℕ` directly — as this definition used to — silently forces `uι = 0`, which is exactly
the restriction Karp's backward direction cannot live with. -/
def toLinf : ∀ {n}, L.BoundedFormulaω α n → L.BoundedFormulaInf.{u, v, u', uι} α n
  | _, falsum => .falsum
  | _, equal t₁ t₂ => .equal t₁ t₂
  | _, rel R ts => .rel R ts
  | _, imp φ ψ => .imp (toLinf φ) (toLinf ψ)
  | _, all φ => .all (toLinf φ)
  | _, iSup φs => .iSup (fun i : ULift.{uι} ℕ => toLinf (φs i.down))
  | _, iInf φs => .iInf (fun i : ULift.{uι} ℕ => toLinf (φs i.down))

/-! ### Constructor equations

The infinitary equations are the ones with content: they name `ULift.{uι} ℕ` as the branch type, so
a downstream `simp` can see through the embedding at a nonzero target universe. -/

@[simp] theorem toLinf_falsum :
    (falsum : L.BoundedFormulaω α n).toLinf = (.falsum : L.BoundedFormulaInf.{u, v, u', uι} α n) :=
  rfl

@[simp] theorem toLinf_imp (φ ψ : L.BoundedFormulaω α n) :
    (φ.imp ψ).toLinf = (.imp φ.toLinf ψ.toLinf : L.BoundedFormulaInf.{u, v, u', uι} α n) := rfl

@[simp] theorem toLinf_all (φ : L.BoundedFormulaω α (n + 1)) :
    φ.all.toLinf = (.all φ.toLinf : L.BoundedFormulaInf.{u, v, u', uι} α n) := rfl

@[simp] theorem toLinf_iSup (φs : ℕ → L.BoundedFormulaω α n) :
    (BoundedFormulaω.iSup φs).toLinf
      = (.iSup fun i : ULift.{uι} ℕ => (φs i.down).toLinf :
          L.BoundedFormulaInf.{u, v, u', uι} α n) := rfl

@[simp] theorem toLinf_iInf (φs : ℕ → L.BoundedFormulaω α n) :
    (BoundedFormulaω.iInf φs).toLinf
      = (.iInf fun i : ULift.{uι} ℕ => (φs i.down).toLinf :
          L.BoundedFormulaInf.{u, v, u', uι} α n) := rfl

variable {M : Type w} [L.Structure M] {v : α → M} {xs : Fin n → M}

/-- Realization is preserved at **every** target index universe.  The infinitary cases are no longer
an index-preserving `exists_congr`/`forall_congr'`: the quantifier on the left ranges over
`ULift.{uι} ℕ` and on the right over `ℕ`, so the witness must be transported across the lift. -/
@[simp]
theorem realize_toLinf (φ : L.BoundedFormulaω α n) :
    (toLinf.{u, v, u', uι} φ).Realize v xs ↔ φ.Realize v xs := by
  induction φ with
  | falsum => rfl
  | equal => rfl
  | rel => rfl
  | imp φ ψ ih₁ ih₂ =>
    simp only [toLinf, BoundedFormulaInf.realize_imp, BoundedFormulaω.realize_imp, ih₁, ih₂]
  | all φ ih =>
    simp only [toLinf, BoundedFormulaInf.realize_all, BoundedFormulaω.realize_all]
    exact forall_congr' fun x => ih
  | iSup φs ih =>
    simp only [toLinf, BoundedFormulaInf.realize_iSup, BoundedFormulaω.realize_iSup, ULift.exists]
    exact exists_congr fun i => ih i
  | iInf φs ih =>
    simp only [toLinf, BoundedFormulaInf.realize_iInf, BoundedFormulaω.realize_iInf, ULift.forall]
    exact forall_congr' fun i => ih i

/-- `toLinf` preserves the countable property.

**Explicitly at `uι = 0`.**  `IsCountable` is itself pinned to index universe zero — its `iSup`/`iInf`
constructors take `ι : Type` — so this statement cannot be generalized along with `toLinf` until that
predicate is redesigned.  That redesign is deliberately out of scope here. -/
theorem toLinf_isCountable (φ : L.BoundedFormulaω α n) : (toLinf.{u, v, u', 0} φ).IsCountable := by
  induction φ with
  | falsum => exact .falsum
  | equal t₁ t₂ => exact .equal t₁ t₂
  | rel R ts => exact .rel R ts
  | imp _ _ ih₁ ih₂ => exact .imp ih₁ ih₂
  | all _ ih => exact .all ih
  -- the branch type is now `ULift.{0} ℕ`, so the induction hypothesis is reindexed through `down`
  | iSup φs ih => exact .iSup fun i => ih i.down
  | iInf φs ih => exact .iInf fun i => ih i.down

end BoundedFormulaω

namespace Formulaω

/-- Embeds a Lω₁ω formula into L∞ω at an arbitrary target index universe. -/
def toLinf (φ : L.Formulaω α) : L.FormulaInf.{u, v, u', uι} α := BoundedFormulaω.toLinf φ

@[simp]
theorem realize_toLinf {M : Type w} [L.Structure M] {v : α → M} (φ : L.Formulaω α) :
    FormulaInf.Realize (toLinf.{u, v, u', uι} φ) v ↔ Formulaω.Realize φ v :=
  BoundedFormulaω.realize_toLinf φ

end Formulaω

namespace Sentenceω

/-- Embeds a Lω₁ω sentence into L∞ω at an arbitrary target index universe. -/
def toLinf (φ : L.Sentenceω) : L.SentenceInf.{u, v, uι} := Formulaω.toLinf φ

@[simp]
theorem realize_toLinf {M : Type w} [L.Structure M] (φ : L.Sentenceω) :
    SentenceInf.Realize (toLinf.{u, v, uι} φ) M ↔ Sentenceω.Realize φ M := by
  simp only [SentenceInf.Realize, Sentenceω.Realize, toLinf, Formulaω.toLinf]
  exact BoundedFormulaω.realize_toLinf φ

end Sentenceω

/-! ## The embedding triangle

A first-order formula reaches L∞ω two ways: directly by `BoundedFormula.toLinf`, or through Lω₁ω by
`BoundedFormula.toLω` followed by `BoundedFormulaω.toLinf`.  They agree, **at every target index
universe** — and the agreement is syntactic, not merely semantic, because a finitary formula has no
infinitary node for the two routes to disagree at.  `BoundedFormula.toLinf` was already
universe-polymorphic for that same reason: with no `iSup`/`iInf` clause, nothing pinned its target. -/

namespace BoundedFormula

@[simp]
theorem toLω_toLinf (φ : L.BoundedFormula α n) :
    (φ.toLω.toLinf : L.BoundedFormulaInf.{u, v, u', uι} α n) = φ.toLinf := by
  induction φ with
  | falsum => rfl
  | equal => rfl
  | rel => rfl
  | imp _ _ ih₁ ih₂ => simp only [toLω, BoundedFormulaω.toLinf, toLinf, ih₁, ih₂]
  | all _ ih => simp only [toLω, BoundedFormulaω.toLinf, toLinf, ih]

end BoundedFormula

namespace Formula

@[simp]
theorem toLω_toLinf (φ : L.Formula α) :
    (φ.toLω.toLinf : L.FormulaInf.{u, v, u', uι} α) = φ.toLinf :=
  BoundedFormula.toLω_toLinf φ

end Formula

namespace Sentence

@[simp]
theorem toLω_toLinf (φ : L.Sentence) :
    (φ.toLω.toLinf : L.SentenceInf.{u, v, uι}) = φ.toLinf :=
  BoundedFormula.toLω_toLinf φ

end Sentence

/-! ## Nonzero-universe acceptance probes

Permanent regressions for the target-universe generalization, at a *literal* `Type 1`.  They belong
in this file rather than a scratch file for two reasons: a scratch file is not built by any target,
and — more sharply — elaborating a probe against stale `.olean`s silently reports the *pre-edit*
behaviour, so a probe that lives outside the changed module can pass while testing nothing. -/

section Probes

variable {M : Type w} [L.Structure M] {v : α → M} {xs : Fin n → M}

/-- The triangle at a nonzero target universe.  Starts from a *finitary* formula, so it never visits
an infinitary node. -/
example (φ : L.BoundedFormula α n) :
    (φ.toLω.toLinf : L.BoundedFormulaInf.{u, v, u', 1} α n) = φ.toLinf :=
  BoundedFormula.toLω_toLinf φ

/-- The case the triangle cannot reach: an *infinitary* Lω₁ω formula translated at a nonzero target
universe.  This is what exercises the `ULift.{1} ℕ` branch type. -/
example (φ : L.BoundedFormulaω α n) :
    (BoundedFormulaω.toLinf.{u, v, u', 1} φ).Realize v xs ↔ φ.Realize v xs :=
  BoundedFormulaω.realize_toLinf φ

/-- The constructor equation at that target, naming the lifted branch type explicitly. -/
example (φs : ℕ → L.BoundedFormulaω α n) :
    (BoundedFormulaω.iSup φs).toLinf
      = (.iSup fun i : ULift.{1} ℕ => (φs i.down).toLinf :
          L.BoundedFormulaInf.{u, v, u', 1} α n) :=
  BoundedFormulaω.toLinf_iSup φs

/-- Karp-shaped: the branch type is a structure's own carrier universe, which is the reason the
target universe had to become a parameter at all. -/
example (φs : M → L.BoundedFormulaInf.{u, v, u', w} α n) :
    L.BoundedFormulaInf.{u, v, u', w} α n :=
  .iInf φs

end Probes

namespace BoundedFormulaInf

namespace IsCountable

/-- Extract the IsCountable proofs from an imp proof. -/
theorem imp_left {φ ψ : L.BoundedFormulaInf α n} (h : (φ.imp ψ).IsCountable) :
    φ.IsCountable := by
  cases h with
  | imp hφ _ => exact hφ

/-- Extract the IsCountable proofs from an imp proof. -/
theorem imp_right {φ ψ : L.BoundedFormulaInf α n} (h : (φ.imp ψ).IsCountable) :
    ψ.IsCountable := by
  cases h with
  | imp _ hψ => exact hψ

/-- Extract the IsCountable proof from an all proof. -/
theorem all_inner {φ : L.BoundedFormulaInf α (n + 1)} (h : φ.all.IsCountable) :
    φ.IsCountable := by
  cases h with
  | all hφ => exact hφ

/-- Extract Countable instance from an iSup IsCountable proof. -/
theorem iSup_countable {ι : Type} {φs : ι → L.BoundedFormulaInf α n}
    (h : (BoundedFormulaInf.iSup φs).IsCountable) : Countable ι := by
  cases h with
  | iSup _ => assumption

/-- Extract the IsCountable proofs from an iSup proof. -/
theorem iSup_forall {ι : Type} {φs : ι → L.BoundedFormulaInf α n}
    (h : (BoundedFormulaInf.iSup φs).IsCountable) : ∀ i, (φs i).IsCountable := by
  cases h with
  | iSup hφs => exact hφs

/-- Extract Countable instance from an iInf IsCountable proof. -/
theorem iInf_countable {ι : Type} {φs : ι → L.BoundedFormulaInf α n}
    (h : (BoundedFormulaInf.iInf φs).IsCountable) : Countable ι := by
  cases h with
  | iInf _ => assumption

/-- Extract the IsCountable proofs from an iInf proof. -/
theorem iInf_forall {ι : Type} {φs : ι → L.BoundedFormulaInf α n}
    (h : (BoundedFormulaInf.iInf φs).IsCountable) : ∀ i, (φs i).IsCountable := by
  cases h with
  | iInf hφs => exact hφs

end IsCountable

/-- Converts a countable L∞ω formula back to Lω₁ω.
Recurses on the IsCountable proof to extract Countable instances at iSup/iInf nodes.

**Index universe zero.**  Unlike the forward `toLinf`, this reverse direction is *not* generalized:
its argument carries an `IsCountable` proof, and that predicate pins `uι = 0` (its `iSup`/`iInf`
constructors take `ι : Type`).  The pinning is therefore forced by the signature rather than chosen
here.  Generalizing it means redesigning `IsCountable`, which is out of scope. -/
noncomputable def ofCountable : ∀ {n} {φ : L.BoundedFormulaInf α n}, φ.IsCountable → L.BoundedFormulaω α n
  | _, .falsum, _ => .falsum
  | _, .equal t₁ t₂, _ => .equal t₁ t₂
  | _, .rel R ts, _ => .rel R ts
  | _, .imp _ _, h => .imp (ofCountable h.imp_left) (ofCountable h.imp_right)
  | _, .all _, h => .all (ofCountable h.all_inner)
  | _, @BoundedFormulaInf.iSup _ _ _ ι _, h =>
    haveI : Countable ι := h.iSup_countable
    haveI : Encodable ι := Encodable.ofCountable ι
    BoundedFormulaω.esup (fun i => ofCountable (h.iSup_forall i))
  | _, @BoundedFormulaInf.iInf _ _ _ ι _, h =>
    haveI : Countable ι := h.iInf_countable
    haveI : Encodable ι := Encodable.ofCountable ι
    BoundedFormulaω.einf (fun i => ofCountable (h.iInf_forall i))

variable {M : Type w} [L.Structure M] {v : α → M} {xs : Fin n → M}

/-- Semantics is preserved by ofCountable conversion. -/
@[simp]
theorem realize_ofCountable {φ : L.BoundedFormulaInf α n} (h : φ.IsCountable) :
    (ofCountable h).Realize v xs ↔ φ.Realize v xs := by
  induction h with
  | falsum => rfl
  | equal => rfl
  | rel => rfl
  | imp _ _ ih₁ ih₂ =>
    simp only [ofCountable, BoundedFormulaω.realize_imp, realize_imp, ih₁, ih₂]
  | all _ ih =>
    simp only [ofCountable, BoundedFormulaω.realize_all, realize_all]
    exact forall_congr' fun x => ih
  | iSup hφs ih =>
    simp only [ofCountable, BoundedFormulaω.realize_esup, realize_iSup]
    exact exists_congr fun i => ih i
  | iInf hφs ih =>
    simp only [ofCountable, BoundedFormulaω.realize_einf, realize_iInf]
    exact forall_congr' fun i => ih i

/-- Encoding independence: different `IsCountable` proofs for the same formula
yield semantically equivalent Lω₁ω formulas. The `ofCountable` function uses
`Encodable.ofCountable` (a choice function) at each `iSup`/`iInf` node, so different
proofs may produce syntactically different formulas, but their realizations agree. -/
theorem realize_ofCountable_irrel {φ : L.BoundedFormulaInf α n}
    (h₁ h₂ : φ.IsCountable) (v : α → M) (xs : Fin n → M) :
    (ofCountable h₁).Realize v xs ↔ (ofCountable h₂).Realize v xs :=
  (realize_ofCountable h₁).trans (realize_ofCountable h₂).symm

end BoundedFormulaInf

namespace FormulaInf

/-- Converts a countable L∞ω formula to Lω₁ω. -/
noncomputable def ofCountable {φ : L.FormulaInf α} (h : φ.IsCountable) : L.Formulaω α :=
  BoundedFormulaInf.ofCountable h

@[simp]
theorem realize_ofCountable {M : Type w} [L.Structure M] {v : α → M}
    {φ : L.FormulaInf α} (h : φ.IsCountable) :
    Formulaω.Realize (ofCountable h) v ↔ FormulaInf.Realize φ v :=
  BoundedFormulaInf.realize_ofCountable h

end FormulaInf

namespace SentenceInf

/-- Converts a countable L∞ω sentence to Lω₁ω. -/
noncomputable def ofCountable {φ : L.SentenceInf} (h : φ.IsCountable) : L.Sentenceω :=
  FormulaInf.ofCountable h

@[simp]
theorem realize_ofCountable {M : Type w} [L.Structure M]
    {φ : L.SentenceInf} (h : φ.IsCountable) :
    Sentenceω.Realize (ofCountable h) M ↔ SentenceInf.Realize φ M := by
  simp only [Sentenceω.Realize, SentenceInf.Realize, ofCountable, FormulaInf.ofCountable]
  exact BoundedFormulaInf.realize_ofCountable h

/-- Encoding independence at the sentence level. -/
theorem realize_ofCountable_irrel {φ : L.SentenceInf}
    (h₁ h₂ : φ.IsCountable) (M : Type w) [L.Structure M] :
    Sentenceω.Realize (ofCountable h₁) M ↔ Sentenceω.Realize (ofCountable h₂) M := by
  simp [realize_ofCountable]

end SentenceInf

end Language

end FirstOrder
