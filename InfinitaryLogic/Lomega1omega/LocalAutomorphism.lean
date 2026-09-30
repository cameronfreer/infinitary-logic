/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Lomega1omega.Theory

/-!
# Local automorphisms preserve infinitary truth on finite tuples

A map `f : M → M` **agrees locally with automorphisms** if on every finite tuple it agrees with
some automorphism of `M`:
`∀ (n : ℕ) (a : Fin n → M), ∃ e : M ≃[L] M, ⇑e ∘ a = f ∘ a`.
Such a map preserves the truth of every `Lω₁ω` formula on finite tuples: choose the automorphism
for the tuple and apply the isomorphism invariance `BoundedFormulaω.realize_equiv`.  There is no
induction on the formula.

## Main declarations

* `BoundedFormulaω.realize_comp_of_localAutomorphisms`: for `φ : L.BoundedFormulaω Empty n`,
  `φ.Realize Empty.elim (f ∘ a) ↔ φ.Realize Empty.elim a`.
* `BoundedFormulaω.realize_embedding_comp_of_localAutomorphisms`: the same for a
  self-embedding `g : M ↪[L] M` agreeing locally with automorphisms.
* `BoundedFormulaω.realize_comp_append_of_localAutomorphisms`: the simultaneous-valuation form,
  for finitely many free variables `v : Fin m → M` and bound variables `a : Fin n → M`, with one
  automorphism chosen for the combined tuple `Fin.append v a`.

## Interpretation notes

* **A property of a function.**  The hypothesis is only the displayed local agreement, and no
  homogeneity of `M` is assumed.  Injectivity and the embedding property are consequences, not
  premises: apply the hypothesis to `![x, y]`, to `Fin.snoc xs (funMap F xs)` and to `xs`.
  Surjectivity is not implied (the successor on the pure set `ℕ` agrees with a permutation on
  every finite tuple).  The embedding form is a restatement for callers holding `g : M ↪[L] M`.
  Establishing the local agreement for a particular map is left to the caller.
* **No further premises.**  Any language (function symbols allowed), any carrier universe, no
  relationality, countability, infinitude or nonemptiness.
* **Finitely many assigned variables.**  The simultaneous form assigns finitely many free
  variables, all moved by the same automorphism as the bound tuple.  Infinitely many assigned
  free variables would need a stronger agreement premise and are not covered.
-/

universe u v w

namespace FirstOrder.Language

namespace BoundedFormulaω

variable {L : Language.{u, v}} {M : Type w} [L.Structure M] {f : M → M}

/-- **Local automorphisms preserve infinitary truth on finite tuples.**  If `f : M → M` agrees
on every finite tuple with some automorphism of `M`, then every `Lω₁ω` formula without free
variables holds of `f ∘ a` iff it holds of `a`. -/
theorem realize_comp_of_localAutomorphisms
    (hf : ∀ (n : ℕ) (a : Fin n → M), ∃ e : M ≃[L] M, ⇑e ∘ a = f ∘ a)
    {n : ℕ} (φ : L.BoundedFormulaω Empty n) (a : Fin n → M) :
    φ.Realize Empty.elim (f ∘ a) ↔ φ.Realize Empty.elim a := by
  obtain ⟨e, he⟩ := hf n a
  rw [realize_equiv e φ Empty.elim a, comp_empty_elim, he]

/-- **Self-embeddings agreeing locally with automorphisms preserve infinitary truth** on finite
tuples: the case `f = ⇑g` of `realize_comp_of_localAutomorphisms`. -/
theorem realize_embedding_comp_of_localAutomorphisms (g : M ↪[L] M)
    (hg : ∀ (n : ℕ) (a : Fin n → M), ∃ e : M ≃[L] M, ⇑e ∘ a = ⇑g ∘ a)
    {n : ℕ} (φ : L.BoundedFormulaω Empty n) (a : Fin n → M) :
    φ.Realize Empty.elim (⇑g ∘ a) ↔ φ.Realize Empty.elim a :=
  realize_comp_of_localAutomorphisms hg φ a

/-- **Simultaneous valuations.**  If `f : M → M` agrees on every finite tuple with some
automorphism of `M`, then an `Lω₁ω` formula with free variables `Fin m` holds of `f ∘ v` and
`f ∘ a` iff it holds of `v` and `a`.  One automorphism, chosen for `Fin.append v a`, moves both. -/
theorem realize_comp_append_of_localAutomorphisms
    (hf : ∀ (n : ℕ) (a : Fin n → M), ∃ e : M ≃[L] M, ⇑e ∘ a = f ∘ a)
    {m n : ℕ} (φ : L.BoundedFormulaω (Fin m) n) (v : Fin m → M) (a : Fin n → M) :
    φ.Realize (f ∘ v) (f ∘ a) ↔ φ.Realize v a := by
  obtain ⟨e, he⟩ := hf (m + n) (Fin.append v a)
  have hv : ⇑e ∘ v = f ∘ v := funext fun i ↦ by
    simpa only [Function.comp_apply, Fin.append_left] using congrFun he (Fin.castAdd n i)
  have ha : ⇑e ∘ a = f ∘ a := funext fun i ↦ by
    simpa only [Function.comp_apply, Fin.append_right] using congrFun he (Fin.natAdd m i)
  rw [realize_equiv e φ v a, hv, ha]

end BoundedFormulaω

end FirstOrder.Language
