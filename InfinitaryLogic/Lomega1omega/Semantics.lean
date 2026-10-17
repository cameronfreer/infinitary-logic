/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Lomega1omega.Syntax
import TauCeti.ModelTheory.Infinitary.Semantics

/-!
# Lω₁ω Semantics — compatibility facade over the fixed-carrier semantics

The three realization *definitions* are no longer given here. They come from
`TauCeti.ModelTheory.Infinitary.Semantics`, whose `BoundedFormulaInf.Realize` is the single
structural recursion serving every index carrier. This file re-exports that semantics under the
qualified names the project already uses, and keeps only what TauCeti does not provide.

TauCeti does not expose the bodies of `Realize`, `FormulaInf.Realize` or `SentenceInf.Realize`:
reason about them through the realization lemmas (`realize_imp`, `realize_all`, …) and the
bridges `FormulaInf.realize_def`/`SentenceInf.realize_def` (simp lemmas there), or
`Formulaω.realize_def`/`Sentenceω.realize_def` below, not by unfolding. No `show` or `change`
step in this repository crosses these bodies. Other definitional uses remain (term-mode proofs
across the formula/bounded levels, `intro`/`rcases` through a connective, `Iff.rfl`); they
compile only because this project's files are not `module`s.

## Why the definitions had to be adopted, not merely paralleled

`Lomega1omega/Syntax.lean` already identifies `BoundedFormulaω` with `BoundedFormulaInf ℕ`
definitionally. Keeping a *separate* recursive `Realize` here would leave two definitionally
distinct semantics for one and the same formula type: dot-notation `φ.Realize` resolves through
the head symbol to `BoundedFormulaInf.Realize`, while the qualified `BoundedFormulaω.Realize`
would name the other one. Every later operation would then have to pick, and would pick wrong.

## What this file still owns

- the qualified `Realize` names, as **reducible aliases** — 100-odd files name
  `BoundedFormulaω.Realize` / `Formulaω.Realize` / `Sentenceω.Realize` explicitly, many in
  `@`-applied form, so the aliases reproduce TauCeti's semantics at the project's historical
  argument order;
- compatibility wrappers carrying the project's realization theorem names, with the project's
  **explicit** argument convention (TauCeti states these with implicit arguments);
- realization for the connectives TauCeti does not name: `and`/`or` and the
  `Encodable`-indexed `einf`/`esup` with their explicit-encoding forms;
- the `⊨ω` notation;
- the atomic cases of transport along an embedding (`Embedding.realize_equal_comp`,
  `Embedding.realize_rel_comp`), shared by every induction that moves realization along one;
- isomorphism invariance of realization (`BoundedFormulaω.realize_equiv`), the induction built on
  those atomic cases.

The gates at the end certify by `Iff.rfl` — no rewriting, no casts — that each alias *is* the
TauCeti semantics, and that the historical `Fin.elim0` spellings of the arity-0 cases still
agree with TauCeti's `default`.
-/

universe u v w w' u'

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}}
variable {M : Type w} [L.Structure M]
variable {α : Type u'} {n : ℕ}

open FirstOrder Structure Fin

namespace BoundedFormulaω

/-- Realization of a bounded Lω₁ω formula, as a qualified name.
TauCeti's `BoundedFormulaInf.Realize` is the definition; this alias is `@[reducible]` and
reproduces the project's historical argument order `L M inst α n φ v xs`. -/
abbrev Realize (φ : L.BoundedFormulaω α n) (v : α → M) (xs : Fin n → M) : Prop :=
  BoundedFormulaInf.Realize φ v xs

variable {v : α → M} {xs : Fin n → M}

/-! ### Primitive connectives

TauCeti states each of these with implicit arguments; the project's consumers supply them
explicitly (`realize_rel R ts`, `realize_imp φ ψ`, …), so the wrappers keep that convention. -/

@[simp]
theorem realize_falsum : (falsum : L.BoundedFormulaω α n).Realize v xs ↔ False :=
  BoundedFormulaInf.realize_falsum

@[simp]
theorem realize_bot : (⊥ : L.BoundedFormulaω α n).Realize v xs ↔ False :=
  BoundedFormulaInf.realize_bot

@[simp]
theorem realize_equal (t₁ t₂ : L.Term (α ⊕ Fin n)) :
    (equal t₁ t₂ : L.BoundedFormulaω α n).Realize v xs ↔
      t₁.realize (Sum.elim v xs) = t₂.realize (Sum.elim v xs) :=
  BoundedFormulaInf.realize_equal

@[simp]
theorem realize_rel {l : ℕ} (R : L.Relations l) (ts : Fin l → L.Term (α ⊕ Fin n)) :
    (rel R ts : L.BoundedFormulaω α n).Realize v xs ↔
      RelMap R fun i => (ts i).realize (Sum.elim v xs) :=
  BoundedFormulaInf.realize_rel

@[simp]
theorem realize_imp (φ ψ : L.BoundedFormulaω α n) :
    (imp φ ψ).Realize v xs ↔ (φ.Realize v xs → ψ.Realize v xs) :=
  BoundedFormulaInf.realize_imp

@[simp]
theorem realize_all (φ : L.BoundedFormulaω α (n + 1)) :
    (all φ).Realize v xs ↔ ∀ x : M, φ.Realize v (snoc xs x) :=
  BoundedFormulaInf.realize_all

@[simp]
theorem realize_iSup (φs : ℕ → L.BoundedFormulaω α n) :
    (iSup φs).Realize v xs ↔ ∃ i, (φs i).Realize v xs :=
  BoundedFormulaInf.realize_iSup

@[simp]
theorem realize_iInf (φs : ℕ → L.BoundedFormulaω α n) :
    (iInf φs).Realize v xs ↔ ∀ i, (φs i).Realize v xs :=
  BoundedFormulaInf.realize_iInf

@[simp]
theorem realize_top : (⊤ : L.BoundedFormulaω α n).Realize v xs ↔ True :=
  BoundedFormulaInf.realize_top

@[simp]
theorem realize_not (φ : L.BoundedFormulaω α n) :
    φ.not.Realize v xs ↔ ¬φ.Realize v xs :=
  BoundedFormulaInf.realize_not

@[simp]
theorem realize_ex (φ : L.BoundedFormulaω α (n + 1)) :
    φ.ex.Realize v xs ↔ ∃ x : M, φ.Realize v (snoc xs x) :=
  BoundedFormulaInf.realize_ex

/-! ### Connectives the project owns -/

@[simp]
theorem realize_and (φ ψ : L.BoundedFormulaω α n) :
    (φ.and ψ).Realize v xs ↔ φ.Realize v xs ∧ ψ.Realize v xs := by
  simp only [BoundedFormulaω.and, realize_not, realize_imp]
  tauto

@[simp]
theorem realize_inf (φ ψ : L.BoundedFormulaω α n) :
    (φ ⊓ ψ).Realize v xs ↔ φ.Realize v xs ∧ ψ.Realize v xs :=
  BoundedFormulaInf.realize_inf

@[simp]
theorem realize_or (φ ψ : L.BoundedFormulaω α n) :
    (φ.or ψ).Realize v xs ↔ φ.Realize v xs ∨ ψ.Realize v xs := by
  simp only [BoundedFormulaω.or, realize_not, realize_imp]
  tauto

@[simp]
theorem realize_sup (φ ψ : L.BoundedFormulaω α n) :
    (φ ⊔ ψ).Realize v xs ↔ φ.Realize v xs ∨ ψ.Realize v xs :=
  BoundedFormulaInf.realize_sup

@[simp]
theorem realize_iff (φ ψ : L.BoundedFormulaω α n) :
    (φ.iff ψ).Realize v xs ↔ (φ.Realize v xs ↔ ψ.Realize v xs) :=
  BoundedFormulaInf.realize_iff

@[simp]
theorem realize_einf {ι : Type*} [Encodable ι] (φs : ι → L.BoundedFormulaω α n) :
    (einf φs).Realize v xs ↔ ∀ i, (φs i).Realize v xs := by
  simp only [einf, realize_iInf]
  constructor
  · intro h i
    simpa only [Encodable.encodek] using h (Encodable.encode i)
  · intro h k
    cases hd : Encodable.decode (α := ι) k with
    | none => simp only [realize_top]
    | some i => exact h i

@[simp]
theorem realize_esup {ι : Type*} [Encodable ι] (φs : ι → L.BoundedFormulaω α n) :
    (esup φs).Realize v xs ↔ ∃ i, (φs i).Realize v xs := by
  simp only [esup, realize_iSup]
  constructor
  · rintro ⟨k, hk⟩
    cases hd : Encodable.decode (α := ι) k with
    | none => simp only [hd, realize_bot] at hk
    | some i =>
      exact ⟨i, by simpa only [hd] using hk⟩
  · rintro ⟨i, hi⟩
    use Encodable.encode i
    simp only [Encodable.encodek, hi]

/-- Realization of `einfWith`: the supplied encoding does not affect the semantics. -/
@[simp] theorem realize_einfWith {ι : Type*} (e : Encodable ι) (φs : ι → L.BoundedFormulaω α n) :
    (einfWith e φs).Realize v xs ↔ ∀ i, (φs i).Realize v xs :=
  @realize_einf L M _ α n v xs ι e φs

/-- Realization of `esupWith`. -/
@[simp] theorem realize_esupWith {ι : Type*} (e : Encodable ι) (φs : ι → L.BoundedFormulaω α n) :
    (esupWith e φs).Realize v xs ↔ ∃ i, (φs i).Realize v xs :=
  @realize_esup L M _ α n v xs ι e φs

end BoundedFormulaω

/-! ### Atomic formulas along embeddings

An embedding preserves and reflects atomic formulas: realizing one at the image valuations
`⇑f ∘ v`, `⇑f ∘ xs` is the same as realizing it at `v`, `xs`. These are the base cases of every
induction that transports realization along an embedding. -/

namespace Embedding

variable {N : Type w'} [L.Structure N] (f : M ↪[L] N) {v : α → M} {xs : Fin n → M}

/-- An embedding preserves and reflects the atomic formula `t₁ = t₂`. -/
theorem realize_equal_comp (t₁ t₂ : L.Term (α ⊕ Fin n)) :
    (BoundedFormulaω.equal t₁ t₂).Realize (⇑f ∘ v) (⇑f ∘ xs) ↔
      (BoundedFormulaω.equal t₁ t₂).Realize v xs := by
  simp only [BoundedFormulaω.realize_equal, ← Sum.comp_elim, HomClass.realize_term]
  exact f.injective.eq_iff

/-- An embedding preserves and reflects the atomic formula `R ts`. -/
theorem realize_rel_comp {l : ℕ} (R : L.Relations l) (ts : Fin l → L.Term (α ⊕ Fin n)) :
    (BoundedFormulaω.rel R ts).Realize (⇑f ∘ v) (⇑f ∘ xs) ↔
      (BoundedFormulaω.rel R ts).Realize v xs := by
  simp only [BoundedFormulaω.realize_rel, ← Sum.comp_elim, HomClass.realize_term]
  exact f.map_rel R _

end Embedding

/-! ### Isomorphism invariance of realization -/

-- The explicit list `.{u_1}`, with `u, v, w` declared at the top of this file, pins the universe
-- parameters to `[u, v, w, u_1]`: the order this theorem had in `Lomega1omega/Theory.lean`.
/-- Realization of Lω₁ω formulas is preserved by language isomorphisms.

Given an isomorphism `e : M ≃[L] N`, a formula realized in M with variable assignments
`v` and `xs` is also realized in N with the transported assignments `e ∘ v` and `e ∘ xs`. -/
theorem BoundedFormulaω.realize_equiv.{u_1} {M N : Type w} [L.Structure M] [L.Structure N]
    (e : M ≃[L] N) {α : Type u_1} {n : ℕ} (φ : L.BoundedFormulaω α n)
    (v : α → M) (xs : Fin n → M) :
    φ.Realize v xs ↔ φ.Realize (e ∘ v) (e ∘ xs) := by
  induction φ with
  | falsum => simp
  | equal t₁ t₂ => exact (e.toEmbedding.realize_equal_comp t₁ t₂).symm
  | rel R ts => exact (e.toEmbedding.realize_rel_comp R ts).symm
  | imp φ ψ ihφ ihψ =>
    simp only [BoundedFormulaInf.realize_imp]
    exact Iff.imp (ihφ xs) (ihψ xs)
  | all φ ih =>
    simp only [BoundedFormulaInf.realize_all]
    constructor
    · intro h y
      have h1 := (ih (Fin.snoc xs (e.symm y))).mp (h (e.symm y))
      rwa [Fin.comp_snoc, e.apply_symm_apply] at h1
    · intro h x
      have h1 := h (e x)
      rw [← Fin.comp_snoc] at h1
      exact (ih (Fin.snoc xs x)).mpr h1
  | iSup φs ih =>
    simp only [BoundedFormulaInf.realize_iSup]
    exact exists_congr fun i => ih i xs
  | iInf φs ih =>
    simp only [BoundedFormulaInf.realize_iInf]
    exact forall_congr' fun i => ih i xs

namespace Formulaω

/-- Realization of an Lω₁ω formula, as a qualified name. TauCeti's `FormulaInf.Realize` is the
definition; it fills the arity-0 valuation with `default`, which is the project's historical
`Fin.elim0` (gated below). -/
abbrev Realize (φ : L.Formulaω α) (v : α → M) : Prop :=
  FormulaInf.Realize φ v

variable {φ : L.Formulaω α} {v : α → M}

/-! #### Simp normal form at the formula level

TauCeti's `FormulaInf.realize_def` is a `@[simp]` lemma, so a plain `simp` rewrites
`Formulaω.Realize φ v` for an opaque `φ` to `BoundedFormulaInf.Realize φ v default`; likewise
`SentenceInf.realize_def` for `Sentenceω.Realize`. The project's formula-level normal form is kept
only for the 17 lemmas tagged `@[simp high]`: the eight below, and nine in
`Lomega1omega/Operations.lean`, `Lomega1omega/InfiniteAxiom.lean`,
`Scott/MontalbanSentence.lean` and `Scott/OrbitParameters.lean`. A formula-level lemma at
default priority, or a formula-level hypothesis `h` in `simp [h]`, loses to the bridge; apply it
with `rw` or `simp only` before a full `simp`. -/

/-- The level-crossing lemma: formula realization *is* bounded-formula realization at the empty
tuple.

`FormulaInf.Realize` is a plain definition in TauCeti, not a reducible abbreviation (matching the
finitary `Formula.Realize`), and its body is not exposed, so neither `rw` nor `simp` can see a
`BoundedFormulaω` realization lemma through it. Supply this lemma explicitly —
`simp only [Formulaω.realize_def, realize_not]` — in place of unfolding `Formulaω.Realize`.
Deliberately not `@[simp]`: the formula-level lemmas below are the normal interface, and this
escape hatch should be visible where it is used. (TauCeti's own bridge `FormulaInf.realize_def`
*is* a simp lemma, stated at `default` rather than `Fin.elim0`.) -/
theorem realize_def (φ : L.Formulaω α) (v : α → M) :
    Realize φ v ↔ BoundedFormulaω.Realize φ v Fin.elim0 :=
  (FormulaInf.realize_def φ v).trans
    (iff_of_eq (congrArg (BoundedFormulaInf.Realize φ v) (Subsingleton.elim _ _)))

@[simp high] -- outranks TauCeti's simp `FormulaInf.realize_def`, which would pre-empt it
theorem realize_not : Realize φ.not v ↔ ¬Realize φ v := BoundedFormulaω.realize_not φ

@[simp high] -- outranks TauCeti's simp `FormulaInf.realize_def`, which would pre-empt it
theorem realize_bot : Realize (⊥ : L.Formulaω α) v ↔ False := BoundedFormulaω.realize_bot

@[simp high] -- outranks TauCeti's simp `FormulaInf.realize_def`, which would pre-empt it
theorem realize_top : Realize (⊤ : L.Formulaω α) v ↔ True := BoundedFormulaω.realize_top

@[simp high] -- outranks TauCeti's simp `FormulaInf.realize_def`, which would pre-empt it
theorem realize_imp (φ ψ : L.Formulaω α) :
    Realize (φ.imp ψ) v ↔ (Realize φ v → Realize ψ v) := BoundedFormulaω.realize_imp φ ψ

@[simp high] -- outranks TauCeti's simp `FormulaInf.realize_def`, which would pre-empt it
theorem realize_inf (φ ψ : L.Formulaω α) :
    Realize (φ ⊓ ψ) v ↔ Realize φ v ∧ Realize ψ v := BoundedFormulaω.realize_inf φ ψ

@[simp high] -- outranks TauCeti's simp `FormulaInf.realize_def`, which would pre-empt it
theorem realize_sup (φ ψ : L.Formulaω α) :
    Realize (φ ⊔ ψ) v ↔ Realize φ v ∨ Realize ψ v := BoundedFormulaω.realize_sup φ ψ

@[simp high] -- outranks TauCeti's simp `FormulaInf.realize_def`, which would pre-empt it
theorem realize_einf {ι : Type*} [Encodable ι] (φs : ι → L.Formulaω α) :
    Realize (BoundedFormulaω.einf φs) v ↔ ∀ i, Realize (φs i) v := BoundedFormulaω.realize_einf φs

@[simp high] -- outranks TauCeti's simp `FormulaInf.realize_def`, which would pre-empt it
theorem realize_esup {ι : Type*} [Encodable ι] (φs : ι → L.Formulaω α) :
    Realize (BoundedFormulaω.esup φs) v ↔ ∃ i, Realize (φs i) v := BoundedFormulaω.realize_esup φs

end Formulaω

namespace Sentenceω

/-- Truth of an Lω₁ω sentence in a structure, as a qualified name. TauCeti's
`SentenceInf.Realize` is the definition. -/
abbrev Realize (φ : L.Sentenceω) (M : Type w) [L.Structure M] : Prop :=
  SentenceInf.Realize φ M

/-- The level-crossing lemma: sentence truth *is* bounded-formula realization at the empty
valuation and the empty tuple. See `Formulaω.realize_def` for why this is needed and why it is
not a `simp` lemma. -/
theorem realize_def (φ : L.Sentenceω) (M : Type w) [L.Structure M] :
    Realize φ M ↔ BoundedFormulaω.Realize φ (Empty.elim : Empty → M) Fin.elim0 :=
  (SentenceInf.realize_def φ M).trans <| (FormulaInf.realize_def (M := M) φ Empty.elim).trans
    (iff_of_eq (congrArg (BoundedFormulaInf.Realize φ Empty.elim) (Subsingleton.elim _ _)))

/-- Notation for a structure satisfying a sentence. -/
scoped notation:51 M " ⊨ω " φ:51 => Sentenceω.Realize φ M

end Sentenceω

/-! ## Facade semantics gates

Each must close by `Iff.rfl` — no `change`, no rewriting, no explicit cast. That is what
certifies that the qualified ω names *are* TauCeti's semantics rather than a parallel copy of
it, and that the arity-0 spellings the project has used throughout (`Fin.elim0`, `Empty.elim`)
still agree with TauCeti's `default`.

The two arity-0 spelling gates see through `FormulaInf.Realize`/`SentenceInf.Realize`, whose
bodies TauCeti does not expose. They hold because this project's files are not `module`s: a
non-module file imports every dependency in full, hidden bodies included. They are kept as
canaries for the definitional uses of these bodies that remain elsewhere (see the module
docstring); no `show` or `change` step relies on them. -/

section Gates

variable {v : α → M} {xs : Fin n → M}

/-- The bounded alias is TauCeti's realization. -/
example (φ : L.BoundedFormulaω α n) :
    BoundedFormulaω.Realize φ v xs ↔ BoundedFormulaInf.Realize φ v xs := Iff.rfl

/-- The formula alias is TauCeti's realization. -/
example (φ : L.Formulaω α) : Formulaω.Realize φ v ↔ FormulaInf.Realize φ v := Iff.rfl

/-- The sentence alias is TauCeti's realization. -/
example (φ : L.Sentenceω) : Sentenceω.Realize φ M ↔ SentenceInf.Realize φ M := Iff.rfl

/-- Dot-notation, which resolves through the head symbol `BoundedFormulaInf`, agrees with the
qualified alias. -/
example (φ : L.BoundedFormulaω α n) : φ.Realize v xs ↔ BoundedFormulaω.Realize φ v xs := Iff.rfl

/-- The historical arity-0 spelling: TauCeti's `default : Fin 0 → M` is `Fin.elim0`. -/
example (φ : L.Formulaω α) :
    Formulaω.Realize φ v ↔ BoundedFormulaω.Realize φ v Fin.elim0 := Iff.rfl

/-- The historical sentence spelling, stated as an equation by `Sentenceω.realize_def`. -/
example (φ : L.Sentenceω) :
    Sentenceω.Realize φ M ↔
      BoundedFormulaω.Realize φ (Empty.elim : Empty → M) Fin.elim0 := Iff.rfl

/-- The `@`-applied argument order used by 40-odd consumer sites is unchanged:
`L`, `M`, the instance, `α`, `n`, then the formula and both valuations. -/
example (inst : L.Structure M) (φ : L.BoundedFormulaω α n) (v : α → M) (xs : Fin n → M) :
    @BoundedFormulaω.Realize L M inst α n φ v xs ↔
      @BoundedFormulaInf.Realize L ℕ α M inst n φ v xs := Iff.rfl

end Gates

end Language

end FirstOrder
