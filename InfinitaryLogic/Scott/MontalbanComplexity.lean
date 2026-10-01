/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Scott.MontalbanSentence
import InfinitaryLogic.Lomega1omega.InHierarchy

/-!
# The complexity of Montalbán's explicit Scott sentence

If every formula of a family `Φ` lies in the signed class `Σ^in_α` with `1 ≤ α`, then
Montalbán's sentence of the family (`Scott/MontalbanSentence.lean`) lies in the signed class
`Π^in_{α+1}` (`isPiIn_montalbanSentence`), and so does the pointed sentence over any parameter
tuple (`isPiIn_montalbanSentencePointed`).  The bound assumes nothing about the family beyond
its class: not that it defines orbits.  Combined with the characterization of
`Scott/MontalbanSentence.lean` (`montalbanSentence_characterizes`), a countable structure in a
countable relational language whose automorphism orbits are `Σ^in_α`-definable without
parameters has a `Π^in_{α+1}` Scott sentence
(`exists_isPiIn_scottSentence_of_sigmaIn_orbits`), and dually over parameters
(`exists_isPiIn_pointed_of_sigmaIn_orbits`).

The classification is the sentence read node by node: the seed `Φ 0 ⟨⟩` is `Σ^in_α`, hence
`Π^in_{α+1}`; in each clause body `θ → D ∧ ⋀_m ∃y ψ m ∧ ∀y ⋁_m ψ m` the antecedent `θ` is
`Σ^in_α ⊆ Σ^in_{α+1}`, the atomic diagram `D` is a countable conjunction of literals (`Π^in_1`),
each `∃y ψ m` is `Σ^in_α`, hence `Π^in_{α+1}`, and `⋁_m ψ m` is `Σ^in_α`, hence `Π^in_{α+1}`
under the `∀y`; the universal closure of the free variables and the outer countable conjunction
keep the level `α + 1 ≥ 1`.

## Main declarations

* `isPiIn_atomicDiagram`: the atomic diagram of a tuple is `Π^in_α` at every level `α ≥ 1`.
* `isPiIn_forallLastVar_iff`, `isSigmaIn_existsLastVar_iff`, `isPiIn_forallTuple_iff`,
  `isPiIn_forallTupleFrom_iff`: the quantifier steps of the Scott formulas keep their class at
  every level `α ≥ 1`.
* `isPiIn_montalbanClauseBody`: the clause body shared by both forms is `Π^in_{α+1}`.
* `isPiIn_montalbanSentencePointed`, `isPiIn_montalbanSentence`: the two sentences are
  `Π^in_{α+1}` when the family is `Σ^in_α` and `1 ≤ α`.
* `exists_isPiIn_scottSentence_of_sigmaIn_orbits`,
  `exists_isPiIn_pointed_of_sigmaIn_orbits`: a `Π^in_{α+1}` Scott sentence (pointed: formula)
  from `Σ^in_α` orbit formulas, `1 ≤ α`.
* `exists_isPiIn_two_scottSentence_of_sigmaIn_zero_orbits`: the case of quantifier-free
  (level `0`) orbit formulas, which gives `Π^in_2`.

## Interpretation choices

* **The signed class.**  `IsPiIn` and `IsSigmaIn` are the signed-traversal classes of
  `Lomega1omega/InHierarchy.lean`: syntactic membership, with `imp` admitted at every level and
  its antecedent read at the opposite sign.  They contain Montalbán's normal forms and agree with
  them only up to logical equivalence, which is not formalized.  So "`Π^in_{α+1}`" here means
  membership of this particular sentence in the signed class; no claim is made that the
  sentence is literally in Montalbán's normal form `⋀ ∀ȳ ψ`, nor that a normal form equivalent
  to it has been constructed.
* **`1 ≤ α` is assumed and necessary.**  At level `0` the signed classes are the finitary
  quantifier-free formulas: no quantifier and no countable connective.  The forth clause
  `∃y Φ (n+1) (a⌢m)` is therefore `Σ^in_1` at best even when the family is quantifier-free, and
  the sentence is `Π^in_2`, not `Π^in_1`.  Quantifier-free orbit formulas are handled by
  monotonicity to level `1` (`exists_isPiIn_two_scottSentence_of_sigmaIn_zero_orbits`).
  **Non-claim:** that `Π^in_1` cannot be reached in general is not proved here.  The reason is
  that `Π^in_1` sentences pass to substructures, so the infinite pure set, whose orbits are
  quantifier-free definable, has no `Π^in_1` Scott sentence: its finite substructures would
  satisfy it.
* **The atomic diagram.**  `atomicDiagram` is a countable conjunction (`einf`) over all atomic
  indices, never level `0` (even in a finite language: the syntax does not record finiteness of
  an index), and `Π^in_1`; it is absorbed into `Π^in_{α+1}` because `α + 1 ≥ 1`.  In Montalbán's
  source the diagram is a finitary quantifier-free formula; the bound is the same.
* **Pointed and unpointed: two routes.**  `IsPiIn` is syntactic, so the semantic `k = 0`
  lemma `realize_montalbanSentence_iff_pointed` cannot transfer it.  Both constructions are
  classified directly through the shared clause-body lemma `isPiIn_montalbanClauseBody` (with the
  block lemmas `isPiIn_forallTuple_iff` and `isPiIn_forallTupleFrom_iff`); the syntactic
  equation `montalbanSentence_eq_pointed_elim0` of `Scott/MontalbanSentence.lean` (transport
  along `0 + n = n`) gives a second route, exercised in the guard.
* **Hypotheses.**  The complexity theorems assume only the class of the family and `1 ≤ α`;
  they need neither `[L.IsRelational]` nor any orbit property, and are universe-polymorphic in the
  language and the carrier.  The Scott-sentence corollaries add what `montalbanSentence_self` and
  `nonempty_equiv_of_realize_montalbanSentence` (and their pointed forms) need:
  `[L.IsRelational]`, and countable structures in `M`'s carrier universe.

## References

* A. Montalbán, *A robuster Scott rank*, Proc. Amer. Math. Soc. 143 (2015).
* A. Montalbán, *Computable Structure Theory: Beyond the Arithmetic*, draft, Chapter II,
  Observation II.11 (the explicit sentence is `Π^in_{α+1}` for `Σ^in_α` orbit formulas).
-/

universe u v w

namespace FirstOrder.Language

open Structure BoundedFormulaω

variable {L : Language.{u, v}} {α : Ordinal.{0}}

/-! ### Components -/

section Components

/-- The atomic diagram of a tuple is `Π^in_α` at every level `α ≥ 1`: a countable conjunction of
atoms and negated atoms. -/
theorem isPiIn_atomicDiagram [Countable (Σ l, L.Relations l)] {M : Type w} [L.Structure M]
    {n : ℕ} (hα : 1 ≤ α) (a : Fin n → M) : IsPiIn α (atomicDiagram (L := L) a) := by
  let _ : Encodable (L.AtomicIdx n) := Encodable.ofCountable _
  unfold atomicDiagram
  refine isPiIn_einf hα fun idx ↦ ?_
  have hlit : ∀ s, inSigned α s (atomicFormulaω (L := L) idx) := fun s ↦ by
    cases idx <;> exact trivial
  split
  · exact hlit true
  · exact (inSigned_not α true _).2 (hlit false)

/-- `∀y φ` over the last free variable keeps the class `Π^in_α`, `α ≥ 1`. -/
theorem isPiIn_forallLastVar_iff {n : ℕ} (hα : 1 ≤ α) {φ : L.Formulaω (Fin (n + 1))} :
    IsPiIn α (forallLastVar φ) ↔ IsPiIn α φ :=
  (and_iff_right hα).trans (inSigned_relabel _ α true φ)

/-- `∃y φ` over the last free variable keeps the class `Σ^in_α`, `α ≥ 1`. -/
theorem isSigmaIn_existsLastVar_iff {n : ℕ} (hα : 1 ≤ α) {φ : L.Formulaω (Fin (n + 1))} :
    IsSigmaIn α (existsLastVar φ) ↔ IsSigmaIn α φ :=
  ((inSigned_ex_false α _).trans (and_iff_right hα)).trans (inSigned_relabel _ α false φ)

/-- The universal closure `forallTuple n φ` keeps the class `Π^in_α`, `α ≥ 1`. -/
theorem isPiIn_forallTuple_iff (hα : 1 ≤ α) :
    ∀ (n : ℕ) (φ : L.Formulaω (Fin n)), IsPiIn α (forallTuple n φ) ↔ IsPiIn α φ
  | 0, _ => Iff.rfl
  | n + 1, _ => (isPiIn_forallTuple_iff hα n _).trans (isPiIn_forallLastVar_iff hα)

/-- The universal closure `forallTupleFrom k n φ` of the last `n` variables keeps the class
`Π^in_α`, `α ≥ 1`. -/
theorem isPiIn_forallTupleFrom_iff (hα : 1 ≤ α) (k : ℕ) :
    ∀ (n : ℕ) (φ : L.Formulaω (Fin (k + n))), IsPiIn α (forallTupleFrom k n φ) ↔ IsPiIn α φ
  | 0, _ => Iff.rfl
  | n + 1, _ => (isPiIn_forallTupleFrom_iff hα k n _).trans (isPiIn_forallLastVar_iff hα)

/-- **The clause body is `Π^in_{α+1}`.**  In `θ → D ∧ ⋀_m ∃y ψ m ∧ ∀y ⋁_m ψ m`, a `Σ^in_{α+1}`
antecedent, a `Π^in_{α+1}` diagram and `Σ^in_α` successors give `Π^in_{α+1}`, for `1 ≤ α`:
`⋀_m ∃y ψ m` is a countable conjunction of `Σ^in_α ⊆ Π^in_{α+1}` formulas, and `∀y ⋁_m ψ m` a
universal quantifier over a `Σ^in_α ⊆ Π^in_{α+1}` formula. -/
theorem isPiIn_montalbanClauseBody {M : Type w} [Countable M] {j : ℕ} (hα : 1 ≤ α)
    {θ D : L.Formulaω (Fin j)} {ψ : M → L.Formulaω (Fin (j + 1))} (hθ : IsSigmaIn (α + 1) θ)
    (hD : IsPiIn (α + 1) D) (hψ : ∀ m, IsSigmaIn α (ψ m)) :
    IsPiIn (α + 1) (montalbanClauseBody θ D ψ) := by
  have h1 : (1 : Ordinal.{0}) ≤ α + 1 := le_add_self
  let _ : Encodable M := Encodable.ofCountable M
  refine isPiIn_imp hθ ?_
  refine isPiIn_inf (isPiIn_inf hD (isPiIn_einf h1 fun m ↦ ?_)) ?_
  · exact ((isSigmaIn_existsLastVar_iff hα).2 (hψ m)).isPiIn_add_one
  · exact (isPiIn_forallLastVar_iff h1).2 (isSigmaIn_esup hα hψ).isPiIn_add_one

end Components

/-! ### The two sentences -/

section Sentences

variable [Countable (Σ l, L.Relations l)] {M : Type w} [L.Structure M] [Countable M]

/-- **Complexity of the pointed sentence.**  If every formula of the family is `Σ^in_α` with
`1 ≤ α`, the pointed sentence over any parameter tuple is `Π^in_{α+1}`.  No orbit property is
assumed. -/
theorem isPiIn_montalbanSentencePointed (hα : 1 ≤ α) {k : ℕ} (c : Fin k → M)
    {Φ : ∀ n, (Fin n → M) → L.Formulaω (Fin (k + n))} (hΦ : ∀ n a, IsSigmaIn α (Φ n a)) :
    IsPiIn (α + 1) (montalbanSentencePointed c Φ) := by
  have h1 : (1 : Ordinal.{0}) ≤ α + 1 := le_add_self
  let _ : Encodable (Σ n, Fin n → M) := Encodable.ofCountable _
  refine isPiIn_inf (hΦ 0 _).isPiIn_add_one (isPiIn_einf h1 fun p ↦ ?_)
  exact (isPiIn_forallTupleFrom_iff h1 k p.1 _).2 <| isPiIn_montalbanClauseBody hα
    ((hΦ _ _).mono le_self_add) (isPiIn_atomicDiagram h1 _) fun _ ↦ hΦ _ _

/-- **Complexity of the sentence.**  If every formula of the family is `Σ^in_α` with `1 ≤ α`,
Montalbán's sentence of the family is `Π^in_{α+1}`.  No orbit property is assumed.  The
hypothesis `1 ≤ α` cannot be dropped (see the module docstring).  The same bound also follows
from `isPiIn_montalbanSentencePointed` through `montalbanSentence_eq_pointed_elim0`. -/
theorem isPiIn_montalbanSentence (hα : 1 ≤ α) {Φ : ∀ n, (Fin n → M) → L.Formulaω (Fin n)}
    (hΦ : ∀ n a, IsSigmaIn α (Φ n a)) : IsPiIn (α + 1) (montalbanSentence Φ) := by
  have h1 : (1 : Ordinal.{0}) ≤ α + 1 := le_add_self
  let _ : Encodable (Σ n, Fin n → M) := Encodable.ofCountable _
  refine isPiIn_inf (hΦ 0 _).isPiIn_add_one (isPiIn_einf h1 fun p ↦ ?_)
  exact (isPiIn_forallTuple_iff h1 p.1 _).2 <| isPiIn_montalbanClauseBody hα
    ((hΦ _ _).mono le_self_add) (isPiIn_atomicDiagram h1 _) fun _ ↦ hΦ _ _

end Sentences

/-! ### Scott sentences from `Σ^in_α` orbit formulas -/

section Scott

variable [Countable (Σ l, L.Relations l)] [L.IsRelational] {M : Type w} [L.Structure M]
  [Countable M]

/-- **A `Π^in_{α+1}` Scott sentence from `Σ^in_α` orbit formulas.**  If `1 ≤ α` and the
automorphism orbit of every tuple of `M` is defined, without parameters, by a `Σ^in_α`
formula, then `M` has a `Π^in_{α+1}` Scott sentence: a countable structure in `M`'s carrier
universe satisfies it iff it is isomorphic to `M` (in particular `M` satisfies it).  The
sentence is Montalbán's sentence of the chosen orbit formulas. -/
theorem exists_isPiIn_scottSentence_of_sigmaIn_orbits (hα : 1 ≤ α)
    (h : ∀ n (a : Fin n → M), ∃ φ : L.Formulaω (Fin n),
      IsSigmaIn α φ ∧ ∀ b, φ.Realize b ↔ ∃ e : M ≃[L] M, ⇑e ∘ a = b) :
    ∃ σ : L.Formulaω (Fin 0), IsPiIn (α + 1) σ ∧
      ∀ (N : Type w) [L.Structure N] [Countable N],
        σ.realize_as_sentence N ↔ Nonempty (M ≃[L] N) := by
  choose Φ hSig hΦ using h
  exact ⟨montalbanSentence Φ, isPiIn_montalbanSentence hα hSig,
    fun N _ _ ↦ montalbanSentence_characterizes (fun n a b ↦ hΦ n a b) N⟩

/-- **The pointed form.**  If `1 ≤ α` and the orbits of tuples under the automorphisms fixing
`c` are defined over `c` by `Σ^in_α` formulas, then there is a `Π^in_{α+1}` formula in `k` free
variables that holds of `d` in a countable `N` (in `M`'s carrier universe) iff some isomorphism
`M ≃[L] N` carries `c` to `d`. -/
theorem exists_isPiIn_pointed_of_sigmaIn_orbits (hα : 1 ≤ α) {k : ℕ} (c : Fin k → M)
    (h : ∀ n (a : Fin n → M), ∃ φ : L.Formulaω (Fin (k + n)), IsSigmaIn α φ ∧
      ∀ b, φ.Realize (Fin.append c b) ↔ ∃ e : M ≃[L] M, ⇑e ∘ c = c ∧ ⇑e ∘ a = b) :
    ∃ σ : L.Formulaω (Fin k), IsPiIn (α + 1) σ ∧
      ∀ (N : Type w) [L.Structure N] [Countable N] (d : Fin k → N),
        σ.Realize d ↔ ∃ e : M ≃[L] N, ⇑e ∘ c = d := by
  choose Φ hSig hΦ using h
  exact ⟨montalbanSentencePointed c Φ, isPiIn_montalbanSentencePointed hα c hSig,
    fun N _ _ ↦ montalbanSentencePointed_characterizes (fun n a b ↦ hΦ n a b) N⟩

/-- **Quantifier-free orbit formulas give `Π^in_2`.**  If the orbit of every tuple of `M` is
defined by a level-`0` (finitary quantifier-free) formula, then `M` has a `Π^in_2` Scott
sentence, by monotonicity to level `1`.  Level `0` does not give `Π^in_1`: the forth clause
quantifies existentially.  That no `Π^in_1` Scott sentence exists in general (the infinite pure
set) is a non-claim, not proved here. -/
theorem exists_isPiIn_two_scottSentence_of_sigmaIn_zero_orbits
    (h : ∀ n (a : Fin n → M), ∃ φ : L.Formulaω (Fin n),
      IsSigmaIn 0 φ ∧ ∀ b, φ.Realize b ↔ ∃ e : M ≃[L] M, ⇑e ∘ a = b) :
    ∃ σ : L.Formulaω (Fin 0), IsPiIn 2 σ ∧
      ∀ (N : Type w) [L.Structure N] [Countable N],
        σ.realize_as_sentence N ↔ Nonempty (M ≃[L] N) := by
  have := exists_isPiIn_scottSentence_of_sigmaIn_orbits (α := 1) le_rfl fun n a ↦
    (h n a).imp fun _ hφ ↦ ⟨hφ.1.mono zero_le_one, hφ.2⟩
  rwa [one_add_one_eq_two] at this

end Scott

end FirstOrder.Language
