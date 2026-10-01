/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Scott.MontalbanComplexity

/-!
# Forgetting finitely many parameters

Let `c : Fin k → M` be a parameter tuple and `φ : L.Formulaω (Fin k)` a formula that
characterizes the pointed structure `(M, c)`: it holds of `c` in `M`, and any countable `N` with a
tuple `d` satisfying it is isomorphic to `M`.  Then the existential closure `∃x̄ φ(x̄)`, the
sentence `existsTuple k φ`, is a Scott sentence of `M` among countable structures
(`existsTuple_isScott`).  If `φ` is `Π^in_{α+1}`, the closure is `Σ^in_{α+2}`
(`isSigmaIn_existsTuple_of_isPiIn`).  Composed with the bound on Montalbán's pointed sentence
(`Scott/MontalbanComplexity.lean`), a countable structure in a countable relational language
whose automorphism orbits over some finite tuple of parameters are `Σ^in_α`-definable over those
parameters, `1 ≤ α`, has a `Σ^in_{α+2}` Scott sentence
(`exists_isSigmaIn_scottSentence_of_sigmaIn_orbits_over`), and `Σ^in_1`-definable orbits over
parameters give a `Σ^in_3` Scott sentence
(`exists_isSigmaIn_three_scottSentence_of_sigmaIn_one_orbits_over`).

The module has three layers, kept apart:

1. **Semantic closure** (`existsTuple_isScott`, `existsTuple_isScott_of_pointed`): no syntactic
   class, no relationality, no orbit hypothesis.
2. **Syntactic closure** (`isSigmaIn_existsTuple_iff`, `isSigmaIn_existsTuple_of_isPiIn`): the
   existential block over the parameters keeps the class `Σ^in_α` for `1 ≤ α`, read off the
   formula by iterating `isSigmaIn_existsLastVar_iff`; no semantics.
3. **Composition** with the pointed bound and the pointed characterization of
   `Scott/MontalbanComplexity.lean` (`exists_isPiIn_pointed_of_sigmaIn_orbits`).

## Main declarations

* `existsTuple_isScott`: the existential closure of a formula true of `c`, whose realizations
  in a countable `N` force `N ≅ M`, is a Scott sentence of `M` among countable structures.
* `existsTuple_isScott_of_pointed`: the same from the pointed characterization
  `φ.Realize d ↔ ∃ e : M ≃[L] N, ⇑e ∘ c = d`, for countable `M`.
* `isSigmaIn_existsTuple_iff`: `existsTuple k φ` is `Σ^in_α` iff `φ` is, for `1 ≤ α`, every
  `k` including `0`.
* `isSigmaIn_existsTuple_of_isPiIn`: a `Π^in_{α+1}` formula closes to a `Σ^in_{α+2}` sentence.
* `exists_isSigmaIn_scottSentence_of_sigmaIn_orbits_over`: `Σ^in_α` orbits over parameters,
  `1 ≤ α`, give a `Σ^in_{α+2}` Scott sentence.
* `exists_isSigmaIn_three_scottSentence_of_sigmaIn_one_orbits_over`: `Σ^in_1` orbits over
  parameters give a `Σ^in_3` Scott sentence.

## Interpretation choices

* **Three layers.**  The semantic closure assumes only the characterization of `(M, c)`; the
  syntactic closure assumes only the class of `φ`; only the composition assumes what the pointed
  sentence needs (`[L.IsRelational]`, countably many relation symbols, countable `M`) and the
  orbit hypothesis.
* **A formula over `Fin k`, not a constants language.**  The parameters are the `k` free
  variables of `φ`, as in the pointed sentence of `Scott/MontalbanSentence.lean`; `φ` is a
  formula of `L`, not a sentence of `L` expanded by `k` constant symbols.  The constants
  formulation through `L.withConstants` (an expansion `L[[Fin k]]` with `IsExpansionOn`) is
  deferred: it would need a translation of `L[[Fin k]]`-sentences into `L`-formulas over
  `Fin k`, with its own complexity lemma, and is not used here.
* **The countable-model comparison boundary.**  The characterization hypothesis and the
  conclusion quantify over countable structures `N` in `M`'s carrier universe `Type w` only, the
  boundary of `nonempty_equiv_of_realize_montalbanSentence` and
  `exists_equiv_of_realize_montalbanSentencePointed`.  Nothing is said about uncountable models
  of the sentence, nor about models in other carrier universes.
* **The weak hypothesis.**  `existsTuple_isScott` asks of a realizing tuple `d` only for *some*
  isomorphism `M ≃[L] N`, not one carrying `c` to `d`: the weaker form is all the closure uses,
  so the theorem is more general than the pointed characterization.
  `existsTuple_isScott_of_pointed` passes from the pointed characterization (the form produced
  by `exists_isPiIn_pointed_of_sigmaIn_orbits`) to the weak form; it is the only closure lemma
  that assumes `[Countable M]`, which it uses to read `φ.Realize c` off the characterization at
  `N = M`.
* **No relationality and no orbit hypothesis on the closure lemmas.**  Neither the semantic nor
  the syntactic closure mentions `[L.IsRelational]`, countability of the language, or orbit
  formulas.  No `Nonempty` is assumed: an empty `M` admits only `k = 0`, where the closure is
  `φ` itself.
* **The empty block.**  `existsTuple 0 φ` is `φ` by definition, so at `k = 0` both layers
  are statements about `φ` itself, and the bound `Π^in_{α+1} → Σ^in_{α+2}` is
  `IsPiIn.isSigmaIn_add_one`.  `isSigmaIn_existsTuple_iff` covers every `k` by recursion on the
  block, with no normalization of the formula and no appeal to logical equivalence.
* **The signed class.**  `IsSigmaIn` and `IsPiIn` are the signed-traversal classes of
  `Lomega1omega/InHierarchy.lean`.  They contain Montalbán's normal forms and agree with them only
  up to logical equivalence, which is not formalized; "`Σ^in_{α+2}`" means membership of this
  sentence in the signed class, not that it is literally in normal form.
* **`1 ≤ α`.**  The block lemma needs `1 ≤ α`: at level `0` no quantifier is admitted.  The
  composite bound needs no hypothesis on `α`, since its block sits at level `α + 2 ≥ 1`.  The
  composition with the pointed sentence needs `1 ≤ α` as that bound does; level-`0` orbit
  formulas are promoted to level `1` by `IsSigmaIn.mono` and give `Σ^in_3`, not `Σ^in_2`.
  **Non-claims:** no lower bound is proved: neither that a `Σ^in_{α+2}` Scott sentence is
  optimal for a given structure, nor the converse direction (that a `Σ^in_{α+2}` Scott sentence
  yields parameters over which the orbits are `Σ^in_α`-definable).

## References

* A. Montalbán, *A robuster Scott rank*, Proc. Amer. Math. Soc. 143 (2015).
* A. Montalbán, *Computable Structure Theory: Beyond the Arithmetic*, draft, Chapter II, §II.5,
  Proposition II.26 (the step from a description over finitely many parameters to a Scott
  sentence).
* M. Harrison-Trainor and M.-C. Ho, *On optimal Scott sentences of finitely generated
  algebraic structures*, Proc. Amer. Math. Soc. 146 (2018) (forgetting finitely many
  constants).
-/

universe u v w

namespace FirstOrder.Language

open Structure BoundedFormulaω

variable {L : Language.{u, v}}

/-! ### The semantic closure -/

section Semantic

variable {M : Type w} [L.Structure M]

/-- **Forgetting the parameters, semantically.**  If `φ` holds of `c` in `M`, and every countable
`N` (in `M`'s carrier universe) with a tuple satisfying `φ` is isomorphic to `M`, then the
existential closure `∃x̄ φ(x̄)` holds in `M` and is a Scott sentence of `M` among countable
structures.  No syntactic class, relationality, countability of `M` or orbit hypothesis is
assumed; `k = 0` is allowed. -/
theorem existsTuple_isScott {k : ℕ} (c : Fin k → M) (φ : L.Formulaω (Fin k))
    (hM : φ.Realize c)
    (hScott : ∀ (N : Type w) [L.Structure N] [Countable N] (d : Fin k → N),
      φ.Realize d → Nonempty (M ≃[L] N)) :
    (existsTuple k φ).realize_as_sentence M ∧
      ∀ (N : Type w) [L.Structure N] [Countable N],
        (existsTuple k φ).realize_as_sentence N ↔ Nonempty (M ≃[L] N) := by
  refine ⟨(realize_existsTuple k φ _).2 ⟨c, hM⟩, fun N _ _ ↦ ⟨fun h ↦ ?_, fun ⟨e⟩ ↦ ?_⟩⟩
  · obtain ⟨d, hd⟩ := (realize_existsTuple k φ _).1 h
    exact hScott N d hd
  · refine (realize_existsTuple k φ _).2 ⟨⇑e ∘ c, ?_⟩
    simpa only [Formulaω.realize_def, comp_fin_elim0] using
      (BoundedFormulaω.realize_equiv e φ c Fin.elim0).1 hM

/-- **Forgetting the parameters, from the pointed characterization.**  For countable `M`, if `φ`
holds of `d` in a countable `N` exactly when some isomorphism `M ≃[L] N` carries `c` to `d` (the
form of `exists_isPiIn_pointed_of_sigmaIn_orbits`), then `∃x̄ φ(x̄)` holds in `M` and is a Scott
sentence of `M` among countable structures.  The pointed characterization gives the hypotheses
of `existsTuple_isScott`: `φ.Realize c` at `N = M` through the identity, and the weak form by
forgetting that the isomorphism carries `c` to `d`. -/
theorem existsTuple_isScott_of_pointed [Countable M] {k : ℕ} (c : Fin k → M)
    (φ : L.Formulaω (Fin k))
    (h : ∀ (N : Type w) [L.Structure N] [Countable N] (d : Fin k → N),
      φ.Realize d ↔ ∃ e : M ≃[L] N, ⇑e ∘ c = d) :
    (existsTuple k φ).realize_as_sentence M ∧
      ∀ (N : Type w) [L.Structure N] [Countable N],
        (existsTuple k φ).realize_as_sentence N ↔ Nonempty (M ≃[L] N) :=
  existsTuple_isScott c φ ((h M c).2 ⟨Language.Equiv.refl L M, rfl⟩)
    fun N _ _ d hd ↦ ((h N d).1 hd).elim fun e _ ↦ ⟨e⟩

end Semantic

/-! ### The syntactic closure -/

section Syntactic

variable {α : Ordinal.{0}}

/-- **The existential block keeps the class `Σ^in_α`**, `1 ≤ α`: `existsTuple k φ` is `Σ^in_α`
iff `φ` is.  At `k = 0` the block is empty and `existsTuple 0 φ` is `φ` by definition; each
further variable is one `existsLastVar` step (`isSigmaIn_existsLastVar_iff`). -/
theorem isSigmaIn_existsTuple_iff (hα : 1 ≤ α) :
    ∀ (k : ℕ) (φ : L.Formulaω (Fin k)), IsSigmaIn α (existsTuple k φ) ↔ IsSigmaIn α φ
  | 0, _ => Iff.rfl
  | k + 1, _ => (isSigmaIn_existsTuple_iff hα k _).trans (isSigmaIn_existsLastVar_iff hα)

/-- **Forgetting the parameters, syntactically.**  The existential closure of a `Π^in_{α+1}`
formula is `Σ^in_{α+2}`: the formula is `Σ^in_{α+2}` (`IsPiIn.isSigmaIn_add_one`), and the
block keeps that class (`isSigmaIn_existsTuple_iff` at `1 ≤ α + 2`).  No hypothesis on `α`;
`k = 0` is allowed. -/
theorem isSigmaIn_existsTuple_of_isPiIn {k : ℕ} {φ : L.Formulaω (Fin k)}
    (hφ : IsPiIn (α + 1) φ) : IsSigmaIn (α + 2) (existsTuple k φ) := by
  have hlev : α + 1 + 1 = α + 2 := by rw [add_assoc, one_add_one_eq_two]
  rw [← hlev]
  exact (isSigmaIn_existsTuple_iff le_add_self k φ).2 hφ.isSigmaIn_add_one

end Syntactic

/-! ### Composition with the pointed sentence -/

section Composition

variable [Countable (Σ l, L.Relations l)] [L.IsRelational] {M : Type w} [L.Structure M]
  [Countable M] {α : Ordinal.{0}}

/-- **A `Σ^in_{α+2}` Scott sentence from `Σ^in_α` orbits over parameters.**  If `1 ≤ α` and,
for some parameter tuple `c`, the orbits of tuples under the automorphisms of `M` fixing `c` are
defined over `c` by `Σ^in_α` formulas, then `M` has a `Σ^in_{α+2}` Scott sentence: a countable
structure in `M`'s carrier universe satisfies it iff it is isomorphic to `M`.  The sentence is the
existential closure of Montalbán's pointed sentence of the chosen orbit formulas. -/
theorem exists_isSigmaIn_scottSentence_of_sigmaIn_orbits_over (hα : 1 ≤ α) {k : ℕ} (c : Fin k → M)
    (h : ∀ n (a : Fin n → M), ∃ φ : L.Formulaω (Fin (k + n)), IsSigmaIn α φ ∧
      ∀ b, φ.Realize (Fin.append c b) ↔ ∃ e : M ≃[L] M, ⇑e ∘ c = c ∧ ⇑e ∘ a = b) :
    ∃ σ : L.Formulaω (Fin 0), IsSigmaIn (α + 2) σ ∧
      ∀ (N : Type w) [L.Structure N] [Countable N],
        σ.realize_as_sentence N ↔ Nonempty (M ≃[L] N) := by
  obtain ⟨φ, hφ, hchar⟩ := exists_isPiIn_pointed_of_sigmaIn_orbits hα c h
  exact ⟨existsTuple k φ, isSigmaIn_existsTuple_of_isPiIn hφ,
    (existsTuple_isScott_of_pointed c φ hchar).2⟩

/-- **`Σ^in_1` orbits over parameters give a `Σ^in_3` Scott sentence**: the case `α = 1` of
`exists_isSigmaIn_scottSentence_of_sigmaIn_orbits_over`.  Quantifier-free (level-`0`) orbit
formulas are promoted to level `1` by `IsSigmaIn.mono` and give `Σ^in_3` as well; level `0` is not
a case of the general theorem, since the forth clauses of the pointed sentence quantify
existentially. -/
theorem exists_isSigmaIn_three_scottSentence_of_sigmaIn_one_orbits_over {k : ℕ} (c : Fin k → M)
    (h : ∀ n (a : Fin n → M), ∃ φ : L.Formulaω (Fin (k + n)), IsSigmaIn 1 φ ∧
      ∀ b, φ.Realize (Fin.append c b) ↔ ∃ e : M ≃[L] M, ⇑e ∘ c = c ∧ ⇑e ∘ a = b) :
    ∃ σ : L.Formulaω (Fin 0), IsSigmaIn 3 σ ∧
      ∀ (N : Type w) [L.Structure N] [Countable N],
        σ.realize_as_sentence N ↔ Nonempty (M ≃[L] N) := by
  have h3 : (1 : Ordinal.{0}) + 2 = 3 := by
    rw [← one_add_one_eq_two, ← add_assoc, one_add_one_eq_two, two_add_one_eq_three]
  simpa only [h3] using exists_isSigmaIn_scottSentence_of_sigmaIn_orbits_over le_rfl c h

end Composition

end FirstOrder.Language
