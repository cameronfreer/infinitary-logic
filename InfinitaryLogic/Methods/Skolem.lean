/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Lomega1omega.Semantics

/-!
# L_{ω₁ω} Skolem functions

Infinitary analogue of Mathlib's `Language.skolem₁`: a Skolem function symbol for each L_{ω₁ω}
formula `ψ(x₀, …, x_{n-1}, x_n)`, interpreted by Hilbert choice to witness `∃ x_n, ψ`. This is the
ambient one-layer Skolem language iterated by the `skolemStage`/`skolemColim` tower
(`SkolemColimit.lean`) and consumed by the Ehrenfeucht–Mostowski term model (`EMTermModel.lean`),
whose Skolem-witness transport (`skWitness_universal`) is powered by `skolem₁ω_funMap_spec`.
Note `skolem₁ω L` is **uncountable** (a symbol per `BoundedFormulaω`); the countable
*family-restricted* variant is `localSkolem` (`LocalSkolem.lean`), which adjoins symbols only for
a countable family `Γ` and is the basis of the `Llocal`/`Γlocal` re-base.

**Only `∃` is Skolemized here.** The countable connectives `⋁`/`⋀` are *not* given object-language
selectors — witnessing them is external (the EM term model's `OmegaComplete` mixin). So this layer
adds function symbols only; `iSup`/`iInf` are untouched.

## Main definitions

* `skolem₁ω L` — the Skolem language (arity-`n` symbol per `L.BoundedFormulaω Empty (n+1)`).
* `skolem₁ωStructure` — the Hilbert-choice interpretation on any `L`-structure.
* `skolemTerm ψ ts` — the Skolem witness term in `L.sum (skolem₁ω L)`.

## Main result

* `skolem₁ω_funMap_spec` — the **Skolem axiom schema** (semantic form): if `∃ a, ψ(x, a)` then
  `ψ` holds at `x` extended by the Skolem value. Consumed by the EM term model's
  `skWitness_universal` (the `all`-case Skolem input of `truthLemmaStage`).
-/

universe u v u' w

namespace FirstOrder.Language

variable (L : Language.{u, v})

/-- The **L_{ω₁ω} Skolem language**: an arity-`n` function symbol for every formula
`ψ : L.BoundedFormulaω Empty (n+1)` (to witness the last variable `x_n`), and no relation symbols.
Infinitary analogue of `Language.skolem₁`. -/
def skolem₁ω : Language :=
  ⟨fun n => L.BoundedFormulaω Empty (n + 1), fun _ => Empty⟩

variable {L} {M : Type w} [L.Structure M] [Nonempty M]

/-- The Skolem structure on `M`: each Skolem symbol `ψ` is interpreted as a Hilbert-choice witness
for `∃ x_n, ψ(x, x_n)` (junk choice when no witness exists). -/
noncomputable instance skolem₁ωStructure : (skolem₁ω L).Structure M where
  funMap {_} ψ x := Classical.epsilon fun a => ψ.Realize (Empty.elim : Empty → M) (Fin.snoc x a)
  RelMap {_} r := r.elim

/-- The **Skolem witness term** for `∃ x_n, ψ(ts, x_n)`: the Skolem function symbol `ψ` (in the
`skolem₁ω` summand) applied to the argument terms `ts`, as a term of `L.sum (skolem₁ω L)`. -/
def skolemTerm {γ : Type u'} {n : ℕ} (ψ : L.BoundedFormulaω Empty (n + 1))
    (ts : Fin n → (L.sum (skolem₁ω L)).Term γ) : (L.sum (skolem₁ω L)).Term γ :=
  Term.func (Sum.inr ψ : (L.sum (skolem₁ω L)).Functions n) ts

/-- **Skolem axiom schema** (semantic form). If `∃ a, ψ(x, a)` holds in `M`, then `ψ` holds at `x`
extended by the Skolem value `funMap ψ x`. This is `Classical.epsilon_spec`; it is exactly what
lets the `C7` quantifier-witness rule be discharged by a `skolemTerm`. -/
theorem skolem₁ω_funMap_spec {n : ℕ} (ψ : L.BoundedFormulaω Empty (n + 1)) (x : Fin n → M)
    (h : ∃ a, ψ.Realize (Empty.elim : Empty → M) (Fin.snoc x a)) :
    ψ.Realize (Empty.elim : Empty → M)
      (Fin.snoc x (Structure.funMap (L := skolem₁ω L) ψ x)) := by
  show ψ.Realize (Empty.elim : Empty → M)
    (Fin.snoc x (Classical.epsilon fun a => ψ.Realize (Empty.elim : Empty → M) (Fin.snoc x a)))
  exact Classical.epsilon_spec h

/-! ### Syntactic-to-semantic bridge: the Skolem term realizes to the chosen witness

These connect the *syntactic* `skolemTerm` to the *semantic* Skolem function of
`skolem₁ωStructure`. **Currently unused API**: the envisioned consistency-property consumer (a
`C7` quantifier-witness discharge) never materialized — the live consumer of this file is the EM
term model, which uses `skolem₁ω_funMap_spec` directly. Kept as the natural entry points for any
future syntactic Skolemization. -/

/-- The syntactic Skolem term evaluates to the semantic Skolem function value: realizing
`skolemTerm ψ ts` under `v` is `funMap ψ` applied to the realized arguments. Definitional, via
`Term.realize_func` and `funMap_sumInr`. -/
theorem realize_skolemTerm {γ : Type u'} {n : ℕ} (ψ : L.BoundedFormulaω Empty (n + 1))
    (ts : Fin n → (L.sum (skolem₁ω L)).Term γ) (v : γ → M) :
    (skolemTerm ψ ts).realize v
      = Structure.funMap (L := skolem₁ω L) ψ (fun i => (ts i).realize v) := by
  simp only [skolemTerm, Term.realize_func]
  rfl

/-- **Skolem witness lemma** (currently unused). If, under the assignment given by `ts`, the
formula `ψ` has a witness for its last variable, then the Skolem term `skolemTerm ψ ts` *is* such
a witness: `ψ` holds at the realized arguments extended by the realized Skolem term. -/
theorem exists_witness_skolemTerm {γ : Type u'} {n : ℕ} (ψ : L.BoundedFormulaω Empty (n + 1))
    (ts : Fin n → (L.sum (skolem₁ω L)).Term γ) (v : γ → M)
    (h : ∃ a, ψ.Realize (Empty.elim : Empty → M) (Fin.snoc (fun i => (ts i).realize v) a)) :
    ψ.Realize (Empty.elim : Empty → M)
      (Fin.snoc (fun i => (ts i).realize v) ((skolemTerm ψ ts).realize v)) := by
  rw [realize_skolemTerm]
  exact skolem₁ω_funMap_spec ψ (fun i => (ts i).realize v) h

end FirstOrder.Language
