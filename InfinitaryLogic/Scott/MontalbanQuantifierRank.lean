/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Scott.MontalbanSentence
import InfinitaryLogic.Scott.QuantifierRank

/-!
# Quantifier rank of Montalbán's explicit Scott sentence

The quantifier rank (`BoundedFormulaω.qrank`) of the sentences of
`Scott/MontalbanSentence.lean`: if every formula `Φ n a` of a family has rank at most `α`, then
Montalbán's sentence of the family has rank at most `α + ω` (`qrank_montalbanSentence_le`),
and so does the pointed sentence over any parameter tuple, uniformly in the number of
parameters (`qrank_montalbanSentencePointed_le`).

**Tuple blocks.**  The tuple quantifiers iterate `existsLastVar` and `forallLastVar`, each of
which adds `1` to the quantifier rank (`qrank_existsLastVar`, `qrank_forallLastVar`).  A block of
`n` quantifiers therefore adds `n`, **on the right**:
`(existsTupleFrom k n φ).qrank = φ.qrank + n`, and likewise for `forallTupleFrom`, `existsTuple`
and `forallTuple`.  For ordinals the side matters at limits: `ω + 1 ≠ 1 + ω`.

**Clauses.**  The clause body `θ → D ∧ ⋀_m ∃y ψ m ∧ ∀y ⋁_m ψ m` has rank
`max θ.qrank (max (max D.qrank (⨆ m, (ψ m).qrank + 1)) ((⨆ m, (ψ m).qrank) + 1))`
(`qrank_montalbanClauseBody`): countable conjunctions and disjunctions take the supremum
without adding `1`, each quantifier adds `1`.  The atomic diagram `D_a` has rank `0`
(`atomicDiagram_qrank_eq_zero`), so it does not affect the rank.  With every `Φ` of rank at most
`α`, the body has rank at most `α + 1` and the clause at a tuple of length `n`, which closes the
`n` tuple variables, rank at most `α + 1 + n = α + (n + 1)`.

**The sentence.**  Each clause has rank at most `α + (n + 1)`; the `+ ω` comes only from the
supremum over the tuple lengths `n`.  The bound is sharp: on a nonempty carrier, if every
`Φ (n + 1) a` has rank exactly `α`, the rank is exactly `max (Φ 0 ⟨⟩).qrank (α + ω)`
(`qrank_montalbanSentence_eq_max`, `qrank_montalbanSentencePointed_eq_max`), so exactly `α + ω`
when the seed also has rank at most `α` (`qrank_montalbanSentence_eq_add_omega0`,
`qrank_montalbanSentencePointed_eq_add_omega0`).
On an empty carrier only the clause at the empty tuple exists, and the rank is exactly
`max (Φ 0 ⟨⟩).qrank 1` (`qrank_montalbanSentence_of_isEmpty`): the back conjunct `∀y ⋁_m`
contributes `1` even when the disjunction is empty.

## Main declarations

* `qrank_existsTupleFrom`, `qrank_forallTupleFrom`: closing the last `n` of `k + n` free
  variables adds `n`.
* `qrank_existsTuple`, `qrank_forallTuple`: closing all `n` free variables adds `n`.
* `qrank_montalbanClauseBody`, `qrank_montalbanClauseBody_le`: the exact rank of the clause
  body, and the bound `α + 1`.
* `qrank_montalbanSentencePointed`, `qrank_montalbanSentence`: the exact rank of the two
  sentences, clause by clause.
* `qrank_montalbanSentencePointed_le`, `qrank_montalbanSentence_le`: the bound `α + ω`.
* `qrank_montalbanSentencePointed_eq_max`, `qrank_montalbanSentence_eq_max`: the exact rank
  `max (Φ 0 ⟨⟩).qrank (α + ω)` on a nonempty carrier when the family has rank exactly `α` at
  positive lengths.
* `qrank_montalbanSentencePointed_eq_add_omega0`, `qrank_montalbanSentence_eq_add_omega0`: the
  bound `α + ω` is attained when, in addition, the seed has rank at most `α`.
* `qrank_montalbanSentence_of_isEmpty`: the exact rank on an empty carrier.

## Interpretation choices

* **Hypotheses.**  The bounds assume only the rank of the family and the countability instances
  the definitions carry (`[Countable M]`, `[Countable (Σ l, L.Relations l)]`).  There is no
  hypothesis `1 ≤ α`, no `[L.IsRelational]`, and no orbit property: the family is arbitrary.
* **Not the signed classes.**  This is a quantifier-rank estimate.  It is distinct from the
  signed `Σ^in`/`Π^in` classification of `Scott/MontalbanComplexity.lean`
  (`isPiIn_montalbanSentence`), which needs `1 ≤ α`; no conversion between the two is stated or
  used.
* **No rank comparison here.**  The bounds are statements about the syntax of the sentence of
  a given family.  No comparison between the Scott ranks of the library (`scottHeight`,
  `stabilizationOrdinal`, `orbitRank`, `internalScottRank`, …) is made here; the comparisons,
  including the `+ ω` bounds that apply `qrank_montalbanSentence_le` to the Scott formulas at a
  uniform level, are in `Scott/InternalRankBounds.lean`.
* **Pointed and unpointed.**  The pointed bound is proved through the exact clause-by-clause
  rank.  The unpointed bound is derived from it through the syntactic equation
  `montalbanSentence_eq_pointed_elim0` and `BoundedFormulaω.qrank_mapFreeVars`, and so is the
  unpointed exact value.  The parameters are not closed in the pointed sentence, so the bound
  `α + ω` is uniform in their number `k`.

## Implementation notes

This is a separate module so that `Scott/QuantifierRank.lean` need not import
`Scott/MontalbanSentence.lean`: that import would widen the cone of every module downstream of
the quantifier-rank file.  The import closure of this module is that of its two imports.
-/

universe u v w

namespace FirstOrder.Language

open BoundedFormulaω

variable {L : Language.{u, v}}

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

/-! ### The clause body -/

/-- **Exact rank of the clause body** `θ → D ∧ ⋀_m ∃y ψ m ∧ ∀y ⋁_m ψ m`: the countable
conjunction and disjunction take the supremum, each of the two quantifiers adds `1`. -/
theorem qrank_montalbanClauseBody {M : Type w} [Countable M] {j : ℕ}
    (θ D : L.Formulaω (Fin j)) (ψ : M → L.Formulaω (Fin (j + 1))) :
    (montalbanClauseBody θ D ψ).qrank =
      max θ.qrank (max (max D.qrank (⨆ m, (ψ m).qrank + 1)) ((⨆ m, (ψ m).qrank) + 1)) := by
  unfold montalbanClauseBody
  simp only [qrank_imp, qrank_inf, qrank_einf, qrank_esup, qrank_existsLastVar,
    qrank_forallLastVar]

/-- The clause body has rank at most `α + 1` when `θ` and `D` do and every `ψ m` has rank at
most `α`. -/
theorem qrank_montalbanClauseBody_le {M : Type w} [Countable M] {j : ℕ}
    {θ D : L.Formulaω (Fin j)} {ψ : M → L.Formulaω (Fin (j + 1))} {α : Ordinal.{0}}
    (hθ : θ.qrank ≤ α + 1) (hD : D.qrank ≤ α + 1) (hψ : ∀ m, (ψ m).qrank ≤ α) :
    (montalbanClauseBody θ D ψ).qrank ≤ α + 1 := by
  rw [qrank_montalbanClauseBody]
  exact max_le hθ (max_le (max_le hD (Ordinal.iSup_le fun m ↦ add_le_add_left (hψ m) 1))
    (add_le_add_left (Ordinal.iSup_le hψ) 1))

/-! ### The pointed sentence -/

section Pointed

variable [Countable (Σ l, L.Relations l)] {M : Type w} [L.Structure M] [Countable M]

/-- **Exact rank of the pointed sentence**, clause by clause: the seed, and for each tuple `a`
of length `n` the rank of its clause body plus `n` (on the right) for the tuple block.  The `k`
parameters are not closed. -/
theorem qrank_montalbanSentencePointed {k : ℕ} (c : Fin k → M)
    (Φ : ∀ n, (Fin n → M) → L.Formulaω (Fin (k + n))) :
    (montalbanSentencePointed c Φ).qrank =
      max (Φ 0 Fin.elim0).qrank (⨆ p : Σ n, Fin n → M,
        (montalbanClauseBody (Φ p.1 p.2) (atomicDiagram (L := L) (Fin.append c p.2))
          fun m ↦ Φ (p.1 + 1) (Fin.snoc p.2 m)).qrank + p.1) := by
  unfold montalbanSentencePointed
  simp only [qrank_inf, qrank_einf, montalbanClausePointed, qrank_forallTupleFrom]

/-- **Quantifier rank of the pointed sentence.**  If every `Φ n a` has rank at most `α`, the
pointed sentence has rank at most `α + ω`, whatever the number `k` of parameters.  The clause at
a tuple of length `n` has rank at most `α + (n + 1)`; the `+ ω` comes only from the supremum
over `n`.  No `1 ≤ α` is needed, unlike the signed classification
`isPiIn_montalbanSentencePointed`, and the two estimates are not converted into each other. -/
theorem qrank_montalbanSentencePointed_le {k : ℕ} (c : Fin k → M)
    {Φ : ∀ n, (Fin n → M) → L.Formulaω (Fin (k + n))} {α : Ordinal.{0}}
    (hΦ : ∀ n a, (Φ n a).qrank ≤ α) :
    (montalbanSentencePointed c Φ).qrank ≤ α + Ordinal.omega0 := by
  rw [qrank_montalbanSentencePointed]
  refine max_le ((hΦ 0 _).trans le_self_add) (Ordinal.iSup_le fun p ↦ ?_)
  have hb := qrank_montalbanClauseBody_le (M := M) (α := α) ((hΦ p.1 p.2).trans le_self_add)
    ((atomicDiagram_qrank_eq_zero (L := L) (Fin.append c p.2)).trans_le zero_le)
    (fun m ↦ hΦ (p.1 + 1) (Fin.snoc p.2 m))
  calc _ ≤ α + 1 + (p.1 : Ordinal) := add_le_add_left hb _
    _ = α + ((p.1 + 1 : ℕ) : Ordinal) := by rw [add_assoc, one_add_natCast]
    _ ≤ α + Ordinal.omega0 := add_le_add_right (Ordinal.natCast_lt_omega0 _).le _

/-- **Exact rank on a nonempty carrier**: if every `Φ (n + 1) a` has rank exactly `α`, the
pointed sentence has rank exactly `max (Φ 0 ⟨⟩).qrank (α + ω)`, whatever `k` and `c` are.  The
clause at the empty tuple contributes `max (Φ 0 ⟨⟩).qrank (α + 1)`, the clauses at length
`n + 1` contribute `α + (n + 2)`, and some tuple of every length exists. -/
theorem qrank_montalbanSentencePointed_eq_max [Nonempty M] {k : ℕ} (c : Fin k → M)
    {Φ : ∀ n, (Fin n → M) → L.Formulaω (Fin (k + n))} {α : Ordinal.{0}}
    (hΦ' : ∀ n a, (Φ (n + 1) a).qrank = α) :
    (montalbanSentencePointed c Φ).qrank = max (Φ 0 Fin.elim0).qrank (α + Ordinal.omega0) := by
  rw [qrank_montalbanSentencePointed]
  refine le_antisymm (max_le (le_max_left _ _) (Ordinal.iSup_le fun ⟨n, a⟩ ↦ ?_))
    (max_le_max le_rfl ?_)
  · rw [qrank_montalbanClauseBody]
    simp only [hΦ', ciSup_const, atomicDiagram_qrank_eq_zero]
    rw [max_eq_right zero_le, max_self]
    cases n with
    | zero =>
      rw [Subsingleton.elim a Fin.elim0, Nat.cast_zero, add_zero]
      exact max_le_max le_rfl (add_le_add_right Ordinal.one_lt_omega0.le _)
    | succ n =>
      rw [hΦ', max_eq_right le_self_add, add_assoc, one_add_natCast]
      exact le_max_of_le_right (add_le_add_right (Ordinal.natCast_lt_omega0 _).le _)
  · rw [← Ordinal.iSup_add_natCast]
    refine Ordinal.iSup_le fun n ↦ ?_
    obtain ⟨x⟩ := ‹Nonempty M›
    refine le_trans ?_ (Ordinal.le_iSup _ ⟨n, fun _ ↦ x⟩)
    rw [qrank_montalbanClauseBody]
    simp only [hΦ', ciSup_const]
    calc α + (n : Ordinal) ≤ α + 1 + n := add_le_add_left le_self_add _
      _ ≤ _ := add_le_add_left (le_max_of_le_right (le_max_right _ _)) _

/-- **The bound `α + ω` is attained**: on a nonempty carrier, if the seed `Φ 0 ⟨⟩` has rank at
most `α` and every `Φ (n + 1) a` has rank exactly `α`, the pointed sentence has rank exactly
`α + ω`, whatever `k` and `c` are.  A seed of larger rank can dominate
(`qrank_montalbanSentencePointed_eq_max`). -/
theorem qrank_montalbanSentencePointed_eq_add_omega0 [Nonempty M] {k : ℕ} (c : Fin k → M)
    {Φ : ∀ n, (Fin n → M) → L.Formulaω (Fin (k + n))} {α : Ordinal.{0}}
    (h0 : (Φ 0 Fin.elim0).qrank ≤ α) (hΦ' : ∀ n a, (Φ (n + 1) a).qrank = α) :
    (montalbanSentencePointed c Φ).qrank = α + Ordinal.omega0 := by
  rw [qrank_montalbanSentencePointed_eq_max c hΦ', max_eq_right (h0.trans le_self_add)]

end Pointed

/-! ### The unpointed sentence -/

section Unpointed

variable [Countable (Σ l, L.Relations l)] {M : Type w} [L.Structure M] [Countable M]

/-- **Exact rank of Montalbán's sentence**, clause by clause: the seed, and for each tuple `a`
of length `n` the rank of its clause body plus `n` (on the right) for the universal closure. -/
theorem qrank_montalbanSentence (Φ : ∀ n, (Fin n → M) → L.Formulaω (Fin n)) :
    (montalbanSentence Φ).qrank =
      max (Φ 0 Fin.elim0).qrank (⨆ p : Σ n, Fin n → M,
        (montalbanClauseBody (Φ p.1 p.2) (atomicDiagram (L := L) p.2)
          fun m ↦ Φ (p.1 + 1) (Fin.snoc p.2 m)).qrank + p.1) := by
  unfold montalbanSentence
  simp only [qrank_inf, qrank_einf, montalbanClause, qrank_forallTuple]

/-- **Quantifier rank of Montalbán's sentence.**  If every `Φ n a` has rank at most `α`, the
sentence has rank at most `α + ω`.  The clause at a tuple of length `n` has rank at most
`α + (n + 1)`; the `+ ω` comes only from the supremum over `n`.  No `1 ≤ α` is needed, unlike
the signed classification `isPiIn_montalbanSentence`, and the two estimates are not converted
into each other.  Derived from the pointed bound `qrank_montalbanSentencePointed_le` through
`montalbanSentence_eq_pointed_elim0` and `BoundedFormulaω.qrank_mapFreeVars`. -/
theorem qrank_montalbanSentence_le {Φ : ∀ n, (Fin n → M) → L.Formulaω (Fin n)}
    {α : Ordinal.{0}} (hΦ : ∀ n a, (Φ n a).qrank ≤ α) :
    (montalbanSentence Φ).qrank ≤ α + Ordinal.omega0 := by
  rw [montalbanSentence_eq_pointed_elim0]
  exact qrank_montalbanSentencePointed_le _ fun n a ↦
    (BoundedFormulaω.qrank_mapFreeVars _ (Φ n a)).trans_le (hΦ n a)

/-- **Exact rank on a nonempty carrier**: if every `Φ (n + 1) a` has rank exactly `α`,
Montalbán's sentence has rank exactly `max (Φ 0 ⟨⟩).qrank (α + ω)`.  Derived from
`qrank_montalbanSentencePointed_eq_max` through `montalbanSentence_eq_pointed_elim0`. -/
theorem qrank_montalbanSentence_eq_max [Nonempty M]
    {Φ : ∀ n, (Fin n → M) → L.Formulaω (Fin n)} {α : Ordinal.{0}}
    (hΦ' : ∀ n a, (Φ (n + 1) a).qrank = α) :
    (montalbanSentence Φ).qrank = max (Φ 0 Fin.elim0).qrank (α + Ordinal.omega0) := by
  rw [montalbanSentence_eq_pointed_elim0, qrank_montalbanSentencePointed_eq_max _
    fun n a ↦ (BoundedFormulaω.qrank_mapFreeVars _ (Φ (n + 1) a)).trans (hΦ' n a)]
  exact congrArg (max · _) (BoundedFormulaω.qrank_mapFreeVars _ (Φ 0 Fin.elim0))

/-- **The bound `α + ω` is attained**: on a nonempty carrier, if the seed `Φ 0 ⟨⟩` has rank at
most `α` and every `Φ (n + 1) a` has rank exactly `α`, Montalbán's sentence has rank exactly
`α + ω`.  A seed of larger rank can dominate (`qrank_montalbanSentence_eq_max`). -/
theorem qrank_montalbanSentence_eq_add_omega0 [Nonempty M]
    {Φ : ∀ n, (Fin n → M) → L.Formulaω (Fin n)} {α : Ordinal.{0}}
    (h0 : (Φ 0 Fin.elim0).qrank ≤ α) (hΦ' : ∀ n a, (Φ (n + 1) a).qrank = α) :
    (montalbanSentence Φ).qrank = α + Ordinal.omega0 := by
  rw [qrank_montalbanSentence_eq_max hΦ', max_eq_right (h0.trans le_self_add)]

/-- **Empty carrier**: the only clause is at the empty tuple, and its back conjunct `∀y ⋁_m`
contributes `1` although the disjunction is empty, so the rank is exactly
`max (Φ 0 ⟨⟩).qrank 1`. -/
theorem qrank_montalbanSentence_of_isEmpty [IsEmpty M]
    (Φ : ∀ n, (Fin n → M) → L.Formulaω (Fin n)) :
    (montalbanSentence Φ).qrank = max (Φ 0 Fin.elim0).qrank 1 := by
  have hp : ∀ p : Σ n, Fin n → M, p = ⟨0, Fin.elim0⟩ := fun ⟨n, a⟩ ↦ by
    cases n with
    | zero => exact Sigma.ext rfl (heq_of_eq (funext fun i ↦ i.elim0))
    | succ n => exact isEmptyElim (a 0)
  rw [qrank_montalbanSentence,
    le_antisymm (Ordinal.iSup_le fun p ↦ by rw [hp p]) (Ordinal.le_iSup _ ⟨0, Fin.elim0⟩),
    qrank_montalbanClauseBody]
  simp only [atomicDiagram_qrank_eq_zero, Nat.cast_zero, add_zero, zero_le, max_eq_right,
    ciSup_of_empty, Ordinal.bot_eq_zero, zero_add]
  rw [← max_assoc, max_self]

end Unpointed

end FirstOrder.Language
