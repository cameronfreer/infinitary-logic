/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Scott.MontalbanSentence
import InfinitaryLogic.Scott.QuantifierRank

/-!
# Eliminating orbit parameters

Let `M` be an `L`-structure, `c₀ : Fin k → M` a parameter tuple and `a : Fin n → M` a tuple.
Suppose `θ : L.Formulaω (Fin k)` defines the automorphism orbit of `c₀`, and
`ψ : L.Formulaω (Fin (k + n))`, read at `c₀⌢b`, defines the orbit of `a` under the automorphisms
of `M` fixing `c₀` pointwise.  Then the formula

```
φ(x̄) := ∃z̄ (θ(z̄) ∧ ψ(z̄, x̄)),   the syntax `existsOrbitParams θ ψ : L.Formulaω (Fin n)`,
```

defines the full automorphism orbit of `a` (`realize_existsOrbitParams_iff_orbit`), and its
quantifier rank is exactly `max θ.qrank ψ.qrank + k`, with `k` added on the right
(`qrank_existsOrbitParams`).

## Main declarations

* `existsOrbitParams θ ψ`: the explicit formula, with `realize_existsOrbitParams` (`@[simp]`):
  it holds of `b` iff some `c` satisfies `θ` and `ψ` holds of `c⌢b`.
* `qrank_existsOrbitParams`: its rank is `max θ.qrank ψ.qrank + k`; and
  `qrank_existsOrbitParams_le`, the bound `α + k` from `θ.qrank ≤ α` and `ψ.qrank ≤ α`.
* `realize_existsOrbitParams_iff_orbit`: the orbit theorem, with the relative hypothesis in the
  pointwise form `∀ i, f (c₀ i) = c₀ i`; `realize_existsOrbitParams_iff_orbit'`, the same with
  `⇑f ∘ c₀ = c₀`; and `realize_existsOrbitParams_of_isOrbitFormulaFamilyPointed`, which feeds a
  pointed orbit-formula family `IsOrbitFormulaFamilyPointed c₀ Φ` in directly.
* The tuple-block rank family `qrank_existsTupleFrom`, `qrank_forallTupleFrom`,
  `qrank_existsTuple`, `qrank_forallTuple`: each block of `n` quantifiers adds `n` on the right.
* `Fin.append_comp_finAddFlip`, `Fin.append_comp_natAdd`: the two coordinate identities that
  read the block back in the parameters-first layout.

## Interpretation choices

* **The layout and the permutation.**  `ψ` takes the parameters first, `Fin (k + n)` read at
  `Fin.append c b`: the layout of the pointed sentence and of `IsOrbitFormulaFamilyPointed`
  (`Scott/MontalbanSentence.lean`).  Every block constructor of this library binds the *last*
  free variables (it iterates `existsLastVar` or `forallLastVar`), so the variables that stay
  free must form an initial segment, and closing the parameters requires moving them to the
  end.  Inside the block the formula lives in `Fin (n + k)`: the first `n` positions are the free
  tuple `x̄`, the last `k` the bound parameters `z̄`.  `θ` is moved by `Fin.natAdd n`
  (`j ↦ n + j`, an order-preserving embedding) and `ψ` by Mathlib's
  `finAddFlip : Fin (k + n) ≃ Fin (n + k)`, which swaps the two blocks and keeps the order inside
  each.  The renaming is `mapFreeVars`, which leaves the bound structure, so it costs no rank
  (`BoundedFormulaω.qrank_mapFreeVars`); the conjunction is `⊓`; the block is
  `existsTupleFrom n k`.
* **The relative hypothesis is used only at `c₀`.**  `ψ` is assumed to define the relative orbit
  of `a` over the one tuple `c₀`; no family of formulas, equivariant or not, is asked for at the
  other parameter tuples.  A witness `c` of `θ` is carried back to `c₀` by the inverse of an
  automorphism `e` with `⇑e ∘ c₀ = c`, the relative orbit property applies there, and the two
  automorphisms compose.  The converse is invariance of satisfaction under automorphisms.
* **Satisfaction invariance, not back-and-forth.**  The semantic theorems are proved from
  `BoundedFormulaω.realize_equiv` alone; neither Karp's theorem nor any rank comparison enters.
  The rank identity is a separate syntactic computation.
* **Proof terms versus imports.**  Freedom from Karp is a property of the *proof terms* of the
  semantic theorems, not of this module's import closure.  The closure does contain
  `Karp/CarrierTheorem`, through `Scott/QuantifierRank`, which the rank lemmas need.  The two are
  audited separately: `scripts/check_orbit_parameters_regressions.lean` asserts the exact import
  closure as it is, and `scripts/check_orbit_parameters_deps.lean` asserts that the proof-term
  cones of the semantic theorems contain `realize_equiv` and no constant from a Karp module and
  no `qrank` declaration.
* **Hypotheses deliberately absent.**  No countability (of `M` or of the symbols), no
  `[L.IsRelational]` (function symbols are handled by `realize_equiv`), no `Nonempty M`, and no
  injectivity of `c₀` or `a`.  The language and carrier universes are independent.
* **Owned helpers.**  The tuple-block rank lemmas live here because `Scott/QuantifierRank.lean`
  does not import `Scott/MontalbanSentence.lean`, and adding that import would widen the cone of
  every module downstream of the quantifier-rank file; they are stated for the blocks of
  `Scott/MontalbanSentence.lean` in general, not only for this construction.

## What is not claimed

* No optimal rank: `max θ.qrank ψ.qrank + k` is the rank of this formula, not the least rank of
  a formula defining the orbit.
* No Scott-rank equality, or comparison with any Scott-rank notion.
* The rank identity holds for this explicit syntax only, not up to logical equivalence.
* This is not the parameter forgetting of `Scott/ForgetParameters.lean`, which closes the
  parameters of a *sentence* characterizing `(M, c)`; here the parameters of *orbit formulas*
  are eliminated, and the free tuple `x̄` stays free.
-/

universe u v w

namespace Fin

/-- Reading the parameters-last layout `Fin (n + k)` through `finAddFlip` gives the
parameters-first layout `Fin (k + n)`. -/
theorem append_comp_finAddFlip {α : Sort*} {k n : ℕ} (c : Fin k → α) (b : Fin n → α) :
    append b c ∘ (finAddFlip : Fin (k + n) ≃ Fin (n + k)) = append c b := by
  funext i
  refine addCases (fun j ↦ ?_) (fun j ↦ ?_) i <;> simp

/-- The last `k` coordinates of `b⌢c` are `c`. -/
theorem append_comp_natAdd {α : Sort*} {k n : ℕ} (c : Fin k → α) (b : Fin n → α) :
    append b c ∘ natAdd n = c := by
  funext i
  simp

end Fin

namespace FirstOrder.Language

open Structure BoundedFormulaω

variable {L : Language.{u, v}}

/-! ### The tuple-block rank family -/

section TupleRank

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

end TupleRank

/-! ### The syntax -/

/-- `∃z̄ (θ(z̄) ∧ ψ(z̄, x̄))`, free in the `n` variables `x̄`.  `ψ` takes the `k` parameters
first; inside the block the variables are laid out `x̄` first and `z̄` last, so `θ` is moved by
`Fin.natAdd n` and `ψ` by `finAddFlip`. -/
def existsOrbitParams {k n : ℕ} (θ : L.Formulaω (Fin k)) (ψ : L.Formulaω (Fin (k + n))) :
    L.Formulaω (Fin n) :=
  existsTupleFrom n k
    (θ.mapFreeVars (Fin.natAdd n) ⊓ ψ.mapFreeVars (finAddFlip : Fin (k + n) ≃ Fin (n + k)))

/-- `existsOrbitParams θ ψ` holds of `b` iff some `c` satisfies `θ` and `ψ` holds of `c⌢b`. -/
@[simp]
theorem realize_existsOrbitParams {M : Type w} [L.Structure M] {k n : ℕ}
    (θ : L.Formulaω (Fin k)) (ψ : L.Formulaω (Fin (k + n))) (b : Fin n → M) :
    (existsOrbitParams θ ψ).Realize b ↔
      ∃ c : Fin k → M, θ.Realize c ∧ ψ.Realize (Fin.append c b) := by
  simp only [existsOrbitParams, realize_existsTupleFrom, Formulaω.realize_inf,
    Formulaω.realize_mapFreeVars, Fin.append_comp_finAddFlip, Fin.append_comp_natAdd]

/-- **The rank of the explicit syntax**: `max θ.qrank ψ.qrank + k`, the `k` parameter
quantifiers added on the right.  This is the rank of this formula, not of its logical
equivalence class. -/
theorem qrank_existsOrbitParams {k n : ℕ} (θ : L.Formulaω (Fin k))
    (ψ : L.Formulaω (Fin (k + n))) :
    (existsOrbitParams θ ψ).qrank = max θ.qrank ψ.qrank + k := by
  rw [existsOrbitParams, qrank_existsTupleFrom, Formulaω.qrank, qrank_inf, qrank_mapFreeVars,
    qrank_mapFreeVars]

/-- The rank bound: from `θ.qrank ≤ α` and `ψ.qrank ≤ α`, the rank is at most `α + k`. -/
theorem qrank_existsOrbitParams_le {k n : ℕ} {θ : L.Formulaω (Fin k)}
    {ψ : L.Formulaω (Fin (k + n))} {α : Ordinal.{0}} (hθ : θ.qrank ≤ α) (hψ : ψ.qrank ≤ α) :
    (existsOrbitParams θ ψ).qrank ≤ α + k := by
  rw [qrank_existsOrbitParams]
  exact add_le_add_left (max_le hθ hψ) _

/-! ### The orbit theorem -/

section Orbit

variable {M : Type w} [L.Structure M]

/-- Composition commutes with appending. -/
private theorem comp_append {α β : Type*} {k n : ℕ} (g : α → β) (c : Fin k → α)
    (b : Fin n → α) : g ∘ Fin.append c b = Fin.append (g ∘ c) (g ∘ b) := by
  funext i
  refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i <;> simp

/-- Transport of `Formulaω` truth along an automorphism. -/
private theorem realize_comp_aut (e : M ≃[L] M) {β : Type*} (φ : L.Formulaω β) (v : β → M) :
    φ.Realize v ↔ φ.Realize (⇑e ∘ v) := by
  simpa only [Formulaω.realize_def, comp_fin_elim0] using
    BoundedFormulaω.realize_equiv e φ v Fin.elim0

/-- **Eliminating orbit parameters.**  If `θ` defines the automorphism orbit of `c₀`, and `ψ`,
read at `c₀⌢b`, defines the orbit of `a` under the automorphisms fixing `c₀` pointwise, then
`existsOrbitParams θ ψ = ∃z̄ (θ(z̄) ∧ ψ(z̄, x̄))` defines the automorphism orbit of `a`.

`ψ` takes the parameters first (`Fin (k + n)`, read at `Fin.append c b`); `existsOrbitParams`
moves them to the end of the block with `finAddFlip`, because the block binds the last
variables.  The relative hypothesis `hψ` is assumed and used at `c₀` only: nothing is asked of
`ψ` at other parameter tuples.  The proof is satisfaction invariance under automorphisms
(`BoundedFormulaω.realize_equiv`), not Karp's theorem or a rank comparison.  No countability, no
relationality (function symbols are allowed), no nonempty carrier and no injectivity of `c₀` or
`a` is assumed.  Nothing is claimed about optimal rank or Scott rank; for the rank of this
syntax see `qrank_existsOrbitParams`. -/
theorem realize_existsOrbitParams_iff_orbit {k n : ℕ} {θ : L.Formulaω (Fin k)}
    {ψ : L.Formulaω (Fin (k + n))} {c₀ : Fin k → M} {a : Fin n → M}
    (hθ : ∀ c, θ.Realize c ↔ ∃ e : M ≃[L] M, ⇑e ∘ c₀ = c)
    (hψ : ∀ b, ψ.Realize (Fin.append c₀ b) ↔
      ∃ f : M ≃[L] M, (∀ i, f (c₀ i) = c₀ i) ∧ ⇑f ∘ a = b) :
    ∀ b, (existsOrbitParams θ ψ).Realize b ↔ ∃ g : M ≃[L] M, ⇑g ∘ a = b := by
  intro b
  rw [realize_existsOrbitParams]
  constructor
  · rintro ⟨c, hc, hcb⟩
    obtain ⟨e, rfl⟩ := (hθ c).1 hc
    have h' := (realize_comp_aut e.symm ψ _).1 hcb
    rw [comp_append, ← Function.comp_assoc] at h'
    have hsym : ⇑e.symm ∘ ⇑e = id := funext fun x ↦ e.symm_apply_apply x
    rw [hsym, Function.id_comp] at h'
    obtain ⟨f, -, hfa⟩ := (hψ _).1 h'
    refine ⟨e.comp f, funext fun i ↦ ?_⟩
    have := congrFun hfa i
    simp only [Function.comp_apply] at this ⊢
    rw [Language.Equiv.comp_apply, this, e.apply_symm_apply]
  · rintro ⟨g, rfl⟩
    refine ⟨⇑g ∘ c₀, (hθ _).2 ⟨g, rfl⟩, ?_⟩
    rw [← comp_append]
    exact (realize_comp_aut g ψ _).1 ((hψ a).2 ⟨Language.Equiv.refl L M, fun _ ↦ rfl, rfl⟩)

/-- `realize_existsOrbitParams_iff_orbit` with the relative hypothesis in the composite form
`⇑f ∘ c₀ = c₀`, the form of `IsOrbitFormulaFamilyPointed`. -/
theorem realize_existsOrbitParams_iff_orbit' {k n : ℕ} {θ : L.Formulaω (Fin k)}
    {ψ : L.Formulaω (Fin (k + n))} {c₀ : Fin k → M} {a : Fin n → M}
    (hθ : ∀ c, θ.Realize c ↔ ∃ e : M ≃[L] M, ⇑e ∘ c₀ = c)
    (hψ : ∀ b, ψ.Realize (Fin.append c₀ b) ↔ ∃ f : M ≃[L] M, ⇑f ∘ c₀ = c₀ ∧ ⇑f ∘ a = b) :
    ∀ b, (existsOrbitParams θ ψ).Realize b ↔ ∃ g : M ≃[L] M, ⇑g ∘ a = b :=
  realize_existsOrbitParams_iff_orbit hθ fun b ↦ (hψ b).trans <|
    exists_congr fun _ ↦ and_congr_left' funext_iff

/-- A pointed orbit-formula family over `c₀` and an orbit formula `θ` of `c₀` give an orbit
formula of every tuple: `existsOrbitParams θ (Φ n a)` defines the automorphism orbit of `a`.
No countability is assumed. -/
theorem realize_existsOrbitParams_of_isOrbitFormulaFamilyPointed {k : ℕ} {c₀ : Fin k → M}
    {θ : L.Formulaω (Fin k)} {Φ : ∀ n, (Fin n → M) → L.Formulaω (Fin (k + n))}
    (hθ : ∀ c, θ.Realize c ↔ ∃ e : M ≃[L] M, ⇑e ∘ c₀ = c)
    (hΦ : IsOrbitFormulaFamilyPointed c₀ Φ) (n : ℕ) (a b : Fin n → M) :
    (existsOrbitParams θ (Φ n a)).Realize b ↔ ∃ g : M ≃[L] M, ⇑g ∘ a = b :=
  realize_existsOrbitParams_iff_orbit' hθ (hΦ n a) b

end Orbit

end FirstOrder.Language
