/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Scott.Sentence
import InfinitaryLogic.Scott.OrbitRank
import InfinitaryLogic.Lomega1omega.Theory

/-!
# Montalbán's explicit Scott sentence from a family of orbit formulas

Let `M` be a countable structure in a language with countably many relation symbols, and let
`Φ n a : L.Formulaω (Fin n)` be a formula for every tuple `a : Fin n → M`.  **Montalbán's
sentence** of the family is

```
Φ 0 ⟨⟩ ∧ ⋀_{(n, a)} ∀x̄ (Φ n a (x̄) → D_a(x̄) ∧ ⋀_{m ∈ M} ∃y Φ (n+1) (a⌢m) (x̄, y)
                                          ∧ ∀y ⋁_{m ∈ M} Φ (n+1) (a⌢m) (x̄, y)),
```

where `D_a` is the atomic diagram of `a` (a countable conjunction of atoms; see the
interpretation choices below).  If `Φ n a` defines the automorphism orbit of `a` for
every tuple, the sentence holds in `M` (`montalbanSentence_self`).  For **every** family, a
countable structure satisfying the sentence is isomorphic to `M`
(`nonempty_equiv_of_realize_montalbanSentence`): in `N`, the relation
`R n a b := (Φ n a).Realize b` is a back-and-forth system, so `N ≅ M`.  Together, the sentence of
an orbit-formula family characterizes `M` up to isomorphism among countable structures
(`montalbanSentence_characterizes`).

The **pointed** form names a parameter tuple `c : Fin k → M`: the formulas
`Φ n a : L.Formulaω (Fin (k + n))` take the parameters as their first `k` free variables and
define the orbits of `a` under the automorphisms fixing `c`.  The pointed sentence
`montalbanSentencePointed c Φ : L.Formulaω (Fin k)` holds of `c` in `M`, and a countable
`N` satisfies it at `d : Fin k → N` exactly when some isomorphism `M ≃[L] N` carries `c` to `d`.
The two forms share their machinery: the clause body `montalbanClauseBody`, and the theorems,
which are proved once for the pointed form; the unpointed theorems are its case `k = 0`, through
the compatibility lemma `realize_montalbanSentence_iff_pointed`.

## Main declarations

* `forallTuple`, `existsTuple`, `forallTupleFrom`: universal and existential closure of all free
  variables of a formula, and of the last `n` of `k + n`, with their realization lemmas.
* `montalbanClauseBody`: the body `θ → D ∧ ⋀_m ∃y ψ m ∧ ∀y ⋁_m ψ m` shared by both forms.
* `montalbanClause`, `montalbanSentence`, `IsOrbitFormulaFamily`: the unpointed sentence and
  the orbit hypothesis.
* `montalbanSentence_self` (B1), `nonempty_equiv_of_realize_montalbanSentence` (B2),
  `montalbanSentence_characterizes`.
* `montalbanClausePointed`, `montalbanSentencePointed`, `IsOrbitFormulaFamilyPointed`,
  `montalbanSentencePointed_self`, `exists_equiv_of_realize_montalbanSentencePointed`,
  `montalbanSentencePointed_characterizes`: the pointed form.
* `realize_montalbanSentence`, `realize_montalbanSentencePointed`: the two sentences clause by
  clause, for any family; the form in which to verify a sentence in a given structure.
* `realize_montalbanSentence_iff_pointed`: the unpointed sentence is the pointed sentence with
  no parameters, up to the transport of each `Φ n a` from `Fin n` to `Fin (0 + n)`.

## Interpretation choices

* **All tuples.**  The family and the outer conjunction range over all tuples
  `Σ n, Fin n → M`, a countable index.  One representative per orbit would suffice
  mathematically; indexing over all tuples is simpler, the extra conjuncts hold in `M`, and the
  characterization holds for any family.  A family on representatives becomes a total family by
  composing with a choice of representative.
* **The atomic-diagram conjunct.**  Each clause asserts `D_a(x̄)`, the atomic diagram of `a`
  (`atomicDiagram`): equality atoms between all coordinates and relation atoms of every arity,
  nullary relations included.  Without it the sentence is not a Scott sentence: on a one-point
  structure with a unary predicate, the family of formulas `⊤` defines every orbit, and the
  clauses without `D_a` hold equally in the one-point structure where the predicate fails.  This
  conjunct is why `[Countable (Σ l, L.Relations l)]` is assumed; with uncountably many unary
  predicates no single `Lω₁ω` sentence pins down a one-point structure up to isomorphism, since
  a sentence mentions only countably many symbols.
* **`D_a` differs from the source.**  In §II.2, `D(x̄) = D^A(ā)` is a finitary quantifier-free
  formula over the finite sub-vocabulary `τ_{|ā|}`.  Here `atomicDiagram` is a countable
  conjunction over all atomic indices, so it is `Π^in_1` rather than finitary, and stronger
  clause by clause.  B1 and B2 are unaffected: both read `D_a(b)` only as full atomic agreement
  of `a` and `b` (`sameAtomicType_iff_realize_atomicDiagram`), which `M` has at its own tuples
  (B1) and which is what each stage of a `PotentialIso` requires (B2).  The difference matters
  once the complexity of the sentence is bounded (B3), which this module does not do.
* **The empty-tuple seed.**  The first conjunct is `Φ 0 Fin.elim0`, the orbit formula of the
  empty tuple; it starts the back-and-forth system.  The sentence of an empty `M` holds in
  exactly the empty structures with the same nullary facts (the back clause at `⟨⟩` is `∀y ⊥`,
  and `D_⟨⟩` records the nullary relations).
* **Minimal hypotheses for B2.**  `nonempty_equiv_of_realize_montalbanSentence` assumes nothing
  about the family: neither the orbit property nor any syntactic class.  It needs
  `[L.IsRelational]` (for `PotentialIso`), countable `M` and `N`, and `M` and `N` in one carrier
  universe, which `PotentialIso.countable_toEquiv` requires.  No `Nonempty` is assumed anywhere:
  empty structures are covered.  The orbit property is used only for B1.
* **Pointed form.**  Parameters are the first `k` free variables, `Fin (k + n)`, joined to the
  tuple by `Fin.append`.  This keeps the quantifier steps `forallLastVar`/`existsLastVar` of the
  Scott formulas (`k + (n + 1)` is definitionally `(k + n) + 1`), where `Fin k ⊕ Fin n` would
  need new binder machinery.  The price is that `Fin (0 + n)` is not definitionally `Fin n`, so
  the unpointed sentence is a separate definition and the case `k = 0` is a semantic
  compatibility lemma.  The pointed B2 reads the image of each parameter off the isomorphism
  graph of `PotentialIso.countable_toEquiv_graph`, through the equality atoms between parameter
  and tuple coordinates in the atomic-diagram conjunct.
* **What is not claimed.**  No complexity statement is made here: the syntactic class of the
  family is unconstrained, and no class of the sentence is asserted.  For an orbit-formula
  family, the sentence is *a* Scott sentence of `M`, not the canonical `scottSentence M`: both
  characterize `M` among countable structures of its carrier universe, so they agree there, but
  they are not syntactically equal, and no comparison lemma is stated here.  Constants named
  through `L.withConstants` are not used: the pointed form replaces them.

## References

* A. Montalbán, *A robuster Scott rank*, Proc. Amer. Math. Soc. 143 (2015).
* A. Montalbán, *Computable Structure Theory: Beyond the Arithmetic*, draft, Chapter II,
  §II.2 and Observation II.11 (the explicit sentence, with its atomic-diagram clause).
-/

universe u v w w'

namespace FirstOrder.Language

open Structure BoundedFormulaω

/-! ### Tuple quantifiers -/

section TupleQuantifiers

variable {L : Language.{u, v}}

/-- `∀x₀ … x_{n-1}`: universally close all `n` free variables of a formula, the last one
innermost, by iterating `forallLastVar`. -/
def forallTuple : ∀ n : ℕ, L.Formulaω (Fin n) → L.Formulaω (Fin 0)
  | 0, φ => φ
  | n + 1, φ => forallTuple n (forallLastVar φ)

/-- `∃x₀ … x_{n-1}`: existentially close all `n` free variables of a formula, by iterating
`existsLastVar`. -/
def existsTuple : ∀ n : ℕ, L.Formulaω (Fin n) → L.Formulaω (Fin 0)
  | 0, φ => φ
  | n + 1, φ => existsTuple n (existsLastVar φ)

/-- Universally close the last `n` of the `k + n` free variables of a formula, keeping the first
`k` free (the parameters). -/
def forallTupleFrom (k : ℕ) : ∀ n : ℕ, L.Formulaω (Fin (k + n)) → L.Formulaω (Fin k)
  | 0, φ => φ
  | n + 1, φ => forallTupleFrom k n (forallLastVar φ)

variable {N : Type w'} [L.Structure N]

/-- A tuple of length `n + 1` quantified as its initial segment and its last entry. -/
private theorem forall_snoc_iff {n : ℕ} {P : (Fin (n + 1) → N) → Prop} :
    (∀ b : Fin n → N, ∀ y : N, P (Fin.snoc b y)) ↔ ∀ b : Fin (n + 1) → N, P b :=
  ⟨fun h b ↦ by simpa only [Fin.snoc_init_self] using h (Fin.init b) (b (Fin.last n)),
    fun h _ _ ↦ h _⟩

/-- A tuple of length `n + 1` found as its initial segment and its last entry. -/
private theorem exists_snoc_iff {n : ℕ} {P : (Fin (n + 1) → N) → Prop} :
    (∃ b : Fin n → N, ∃ y : N, P (Fin.snoc b y)) ↔ ∃ b : Fin (n + 1) → N, P b :=
  ⟨fun ⟨_, _, h⟩ ↦ ⟨_, h⟩,
    fun ⟨b, h⟩ ↦ ⟨Fin.init b, b (Fin.last n), by simpa only [Fin.snoc_init_self] using h⟩⟩

/-- `forallTuple n φ` holds iff `φ` holds of every `n`-tuple. -/
@[simp]
theorem realize_forallTuple :
    ∀ (n : ℕ) (φ : L.Formulaω (Fin n)) (v : Fin 0 → N),
      (forallTuple n φ).Realize v ↔ ∀ b : Fin n → N, φ.Realize b
  | 0, φ, v => ⟨fun h b ↦ by rwa [Subsingleton.elim b v], fun h ↦ h v⟩
  | n + 1, φ, v => by
    simp only [forallTuple, realize_forallTuple n, realize_forallLastVar]
    exact forall_snoc_iff

/-- `existsTuple n φ` holds iff `φ` holds of some `n`-tuple. -/
@[simp]
theorem realize_existsTuple :
    ∀ (n : ℕ) (φ : L.Formulaω (Fin n)) (v : Fin 0 → N),
      (existsTuple n φ).Realize v ↔ ∃ b : Fin n → N, φ.Realize b
  | 0, φ, v => ⟨fun h ↦ ⟨v, h⟩, fun ⟨b, h⟩ ↦ by rwa [Subsingleton.elim b v] at h⟩
  | n + 1, φ, v => by
    simp only [existsTuple, realize_existsTuple n, realize_existsLastVar]
    exact exists_snoc_iff

/-- `forallTupleFrom k n φ` holds of the parameters `d` iff `φ` holds of `d` followed by every
`n`-tuple. -/
@[simp]
theorem realize_forallTupleFrom (k : ℕ) :
    ∀ (n : ℕ) (φ : L.Formulaω (Fin (k + n))) (d : Fin k → N),
      (forallTupleFrom k n φ).Realize d ↔ ∀ b : Fin n → N, φ.Realize (Fin.append d b)
  | 0, φ, d => ⟨fun h b ↦ by simpa [forallTupleFrom, Subsingleton.elim b Fin.elim0] using h,
      fun h ↦ by simpa [forallTupleFrom] using h Fin.elim0⟩
  | n + 1, φ, d => by
    simp only [forallTupleFrom, realize_forallTupleFrom k n, realize_forallLastVar,
      ← Fin.append_snoc]
    exact forall_snoc_iff (P := fun b ↦ φ.Realize (Fin.append d b))

end TupleQuantifiers

/-! ### The shared clause body -/

section Body

variable {L : Language.{u, v}} {M : Type w} [Countable M]

/-- The body shared by the clauses of the unpointed and the pointed sentence:
`θ → D ∧ ⋀_{m ∈ M} ∃y ψ m ∧ ∀y ⋁_{m ∈ M} ψ m`, where `y` is a new last free variable.  In a
clause, `θ` is the orbit formula of a tuple `a`, `D` its atomic diagram and `ψ m` the orbit
formula of `a⌢m`. -/
noncomputable def montalbanClauseBody {j : ℕ} (θ D : L.Formulaω (Fin j))
    (ψ : M → L.Formulaω (Fin (j + 1))) : L.Formulaω (Fin j) :=
  haveI : Encodable M := Encodable.ofCountable M
  θ.imp (D ⊓ einf (fun m ↦ existsLastVar (ψ m)) ⊓ forallLastVar (esup ψ))

/-- Realization of the clause body: forth for every `m ∈ M` and back for every `y`. -/
@[simp]
theorem realize_montalbanClauseBody {N : Type w'} [L.Structure N] {j : ℕ}
    (θ D : L.Formulaω (Fin j)) (ψ : M → L.Formulaω (Fin (j + 1))) (v : Fin j → N) :
    (montalbanClauseBody θ D ψ).Realize v ↔
      (θ.Realize v → D.Realize v ∧ (∀ m, ∃ y, (ψ m).Realize (Fin.snoc v y)) ∧
        ∀ y, ∃ m, (ψ m).Realize (Fin.snoc v y)) := by
  simp only [montalbanClauseBody, Formulaω.realize_imp, Formulaω.realize_inf,
    Formulaω.realize_einf, realize_existsLastVar, realize_forallLastVar, Formulaω.realize_esup,
    and_assoc]

end Body

/-! ### The pointed sentence -/

section Pointed

variable {L : Language.{u, v}} [Countable (Σ l, L.Relations l)]
variable {M : Type w} [L.Structure M] [Countable M]

/-- The clause of the pointed sentence at a tuple `a`:
`∀x̄ (Φ n a (z̄, x̄) → D_{c⌢a}(z̄, x̄) ∧ ⋀_m ∃y Φ (n+1) (a⌢m) (z̄, x̄, y) ∧ ∀y ⋁_m …)`,
with the parameters `z̄` free. -/
noncomputable def montalbanClausePointed {k : ℕ} (c : Fin k → M)
    (Φ : ∀ n, (Fin n → M) → L.Formulaω (Fin (k + n))) (n : ℕ) (a : Fin n → M) :
    L.Formulaω (Fin k) :=
  forallTupleFrom k n <| montalbanClauseBody (Φ n a) (atomicDiagram (L := L) (Fin.append c a))
    fun m ↦ Φ (n + 1) (Fin.snoc a m)

/-- **Montalbán's pointed sentence** of a family over the parameters `c : Fin k → M`: the
formula `Φ 0 ⟨⟩ ∧ ⋀_{(n, a)} montalbanClausePointed c Φ n a` in the `k` parameter variables.
For the empty tuple `c` it is the unpointed sentence (`realize_montalbanSentence_iff_pointed`). -/
noncomputable def montalbanSentencePointed {k : ℕ} (c : Fin k → M)
    (Φ : ∀ n, (Fin n → M) → L.Formulaω (Fin (k + n))) : L.Formulaω (Fin k) :=
  haveI : Encodable (Σ n, Fin n → M) := Encodable.ofCountable _
  Φ 0 Fin.elim0 ⊓ einf fun p : Σ n, Fin n → M ↦ montalbanClausePointed c Φ p.1 p.2

omit [Countable (Σ l, L.Relations l)] [Countable M] in
/-- `Φ` defines, over the parameters `c`, the orbits of tuples under the automorphisms of `M`
fixing `c`: `Φ n a` holds of `c⌢b` iff an automorphism fixing `c` carries `a` to `b`. -/
def IsOrbitFormulaFamilyPointed {k : ℕ} (c : Fin k → M)
    (Φ : ∀ n, (Fin n → M) → L.Formulaω (Fin (k + n))) : Prop :=
  ∀ n (a b : Fin n → M),
    (Φ n a).Realize (Fin.append c b) ↔ ∃ e : M ≃[L] M, ⇑e ∘ c = c ∧ ⇑e ∘ a = b

/-- **The pointed sentence, clause by clause.**  The pointed sentence holds of `d` in `N` iff the
seed `Φ 0 ⟨⟩` holds of `d` and, whenever `Φ n a` holds of `d⌢b`, the tuples `c⌢a` and `d⌢b`
satisfy the same atomic formulas (the diagram conjunct), every `m ∈ M` has a witness `y` with
`Φ (n+1) (a⌢m)` true of `d⌢b⌢y` (forth), and every `y ∈ N` is matched by some `m ∈ M` (back).
No hypothesis on `Φ`: this is the form in which to verify the sentence in a given structure.
Not `@[simp]`, as the right-hand side is large. -/
theorem realize_montalbanSentencePointed {N : Type w'} [L.Structure N] {k : ℕ}
    (c : Fin k → M) (Φ : ∀ n, (Fin n → M) → L.Formulaω (Fin (k + n))) (d : Fin k → N) :
    (montalbanSentencePointed c Φ).Realize d ↔
      (Φ 0 Fin.elim0).Realize d ∧ ∀ (n : ℕ) (a : Fin n → M) (b : Fin n → N),
        (Φ n a).Realize (Fin.append d b) →
          SameAtomicType (L := L) (Fin.append c a) (Fin.append d b) ∧
          (∀ m, ∃ y, (Φ (n + 1) (Fin.snoc a m)).Realize (Fin.append d (Fin.snoc b y))) ∧
          ∀ y, ∃ m, (Φ (n + 1) (Fin.snoc a m)).Realize (Fin.append d (Fin.snoc b y)) := by
  simp only [montalbanSentencePointed, montalbanClausePointed, Formulaω.realize_inf,
    Formulaω.realize_einf, realize_forallTupleFrom, realize_montalbanClauseBody,
    ← sameAtomicType_iff_realize_atomicDiagram, Fin.append_snoc, Sigma.forall]

/-- **B1, pointed.**  If `Φ` defines the orbits over `c`, then `c` satisfies the pointed
sentence in `M`. -/
theorem montalbanSentencePointed_self {k : ℕ} {c : Fin k → M}
    {Φ : ∀ n, (Fin n → M) → L.Formulaω (Fin (k + n))} (hΦ : IsOrbitFormulaFamilyPointed c Φ) :
    (montalbanSentencePointed c Φ).Realize c := by
  rw [realize_montalbanSentencePointed]
  refine ⟨?_, fun n a b hb ↦ ?_⟩
  · have h := (hΦ 0 Fin.elim0 Fin.elim0).2 ⟨Equiv.refl L M, rfl, rfl⟩
    simpa using h
  obtain ⟨e, hec, rfl⟩ := (hΦ n a b).1 hb
  have happ : Fin.append c (⇑e ∘ a) = ⇑e ∘ Fin.append c a := by
    funext i
    refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i
    · simp only [Fin.append_left, Function.comp_apply]
      exact (congrFun hec j).symm
    · simp only [Fin.append_right, Function.comp_apply]
  refine ⟨?_, fun m ↦ ⟨e m, ?_⟩, fun y ↦ ⟨e.symm y, ?_⟩⟩
  · rw [happ]
    exact (SameAtomicType.map_equiv (Language.Equiv.refl L M) e).2 (SameAtomicType.refl _)
  · exact (hΦ _ _ _).2 ⟨e, hec, Fin.comp_snoc _ _ _⟩
  · refine (hΦ _ _ _).2 ⟨e, hec, ?_⟩
    rw [Fin.comp_snoc, Equiv.apply_symm_apply]

/-- **B2, pointed.**  For any family `Φ`, if a countable `N` satisfies the pointed sentence at
`d`, then some isomorphism `M ≃[L] N` carries `c` to `d`.  The relation
`R n a b := (Φ n a).Realize (d⌢b)` is a back-and-forth system; the isomorphism it produces
carries each `c j` to `d j` because of the equality atoms between parameter and tuple
coordinates in the clauses. -/
theorem exists_equiv_of_realize_montalbanSentencePointed [L.IsRelational] {k : ℕ}
    (c : Fin k → M) (Φ : ∀ n, (Fin n → M) → L.Formulaω (Fin (k + n)))
    (N : Type w) [L.Structure N] [Countable N] (d : Fin k → N)
    (h : (montalbanSentencePointed c Φ).Realize d) : ∃ e : M ≃[L] N, ⇑e ∘ c = d := by
  obtain ⟨h0, hcl⟩ := (realize_montalbanSentencePointed c Φ d).1 h
  let R : ∀ n, (Fin n → M) → (Fin n → N) → Prop := fun n a b ↦ (Φ n a).Realize (Fin.append d b)
  have hsat : ∀ {n a b}, R n a b → SameAtomicType (L := L) (Fin.append c a) (Fin.append d b) :=
    fun hR ↦ (hcl _ _ _ hR).1
  let P : PotentialIso L M N := PotentialIso.ofExtensionFamily R
    (by simpa [R] using h0)
    (fun {n a b} hR ↦ by
      simpa only [Function.comp_def, Fin.append_right] using (hsat hR).relabel (Fin.natAdd k))
    (fun hR m ↦ (hcl _ _ _ hR).2.1 m) (fun hR y ↦ (hcl _ _ _ hR).2.2 y)
  obtain ⟨e, he⟩ := P.countable_toEquiv_graph
  refine ⟨e, funext fun j ↦ ?_⟩
  obtain ⟨⟨n, a, b⟩, hp, i, hai, hbi⟩ := he (c j)
  have hij := hsat (n := n) (a := a) (b := b) hp (AtomicIdx.eq (Fin.natAdd k i) (Fin.castAdd n j))
  simp only [AtomicIdx.holds, Fin.append_right, Fin.append_left] at hij
  rw [Function.comp_apply, ← hbi]
  exact hij.1 hai

omit [Countable (Σ l, L.Relations l)] [Countable M] in
/-- Transport of `Formulaω` truth along an isomorphism. -/
private theorem realize_comp_equiv {N : Type w} [L.Structure N] (e : M ≃[L] N) {β : Type*}
    (φ : L.Formulaω β) (v : β → M) : φ.Realize v ↔ φ.Realize (⇑e ∘ v) := by
  simpa only [Formulaω.realize_def, comp_fin_elim0] using
    BoundedFormulaω.realize_equiv e φ v Fin.elim0

/-- **The pointed sentence characterizes `(M, c)`.**  For an orbit-formula family over `c`, a
countable `N` satisfies the pointed sentence at `d` iff some isomorphism carries `c` to `d`. -/
theorem montalbanSentencePointed_characterizes [L.IsRelational] {k : ℕ} {c : Fin k → M}
    {Φ : ∀ n, (Fin n → M) → L.Formulaω (Fin (k + n))} (hΦ : IsOrbitFormulaFamilyPointed c Φ)
    (N : Type w) [L.Structure N] [Countable N] (d : Fin k → N) :
    (montalbanSentencePointed c Φ).Realize d ↔ ∃ e : M ≃[L] N, ⇑e ∘ c = d :=
  ⟨exists_equiv_of_realize_montalbanSentencePointed c Φ N d, fun ⟨e, he⟩ ↦
    he ▸ (realize_comp_equiv e _ c).1 (montalbanSentencePointed_self hΦ)⟩

end Pointed

/-! ### The unpointed sentence -/

section Unpointed

variable {L : Language.{u, v}} [Countable (Σ l, L.Relations l)]
variable {M : Type w} [L.Structure M] [Countable M]

/-- The clause of Montalbán's sentence at a tuple `a`:
`∀x̄ (Φ n a (x̄) → D_a(x̄) ∧ ⋀_{m ∈ M} ∃y Φ (n+1) (a⌢m) (x̄, y) ∧ ∀y ⋁_{m ∈ M} …)`,
where `D_a = atomicDiagram a` and `…` is `Φ (n+1) (a⌢m) (x̄, y)` again. -/
noncomputable def montalbanClause (Φ : ∀ n, (Fin n → M) → L.Formulaω (Fin n)) (n : ℕ)
    (a : Fin n → M) : L.Formulaω (Fin 0) :=
  forallTuple n <| montalbanClauseBody (Φ n a) (atomicDiagram (L := L) a)
    fun m ↦ Φ (n + 1) (Fin.snoc a m)

/-- **Montalbán's sentence** of a family `Φ` indexed over all tuples of `M`:
`Φ 0 ⟨⟩ ∧ ⋀_{(n, a)} montalbanClause Φ n a`.  A sentence of the same type as
`scottSentence`, read through `Formulaω.realize_as_sentence`. -/
noncomputable def montalbanSentence (Φ : ∀ n, (Fin n → M) → L.Formulaω (Fin n)) :
    L.Formulaω (Fin 0) :=
  haveI : Encodable (Σ n, Fin n → M) := Encodable.ofCountable _
  Φ 0 Fin.elim0 ⊓ einf fun p : Σ n, Fin n → M ↦ montalbanClause Φ p.1 p.2

omit [Countable (Σ l, L.Relations l)] [Countable M] in
/-- `Φ` is a family of orbit formulas: `Φ n a` holds of `b` iff an automorphism of `M` carries
`a` to `b`. -/
def IsOrbitFormulaFamily (Φ : ∀ n, (Fin n → M) → L.Formulaω (Fin n)) : Prop :=
  ∀ n (a b : Fin n → M), (Φ n a).Realize b ↔ ∃ e : M ≃[L] M, ⇑e ∘ a = b

/-- **Montalbán's sentence, clause by clause.**  The sentence holds in `N` iff the seed `Φ 0 ⟨⟩`
holds and, whenever `Φ n a` holds of `b`, the tuples `a` and `b` satisfy the same atomic
formulas, every `m ∈ M` has a witness `y` with `Φ (n+1) (a⌢m)` true of `b⌢y` (forth), and every
`y ∈ N` is matched by some `m ∈ M` (back).  No hypothesis on `Φ`.  Not `@[simp]`, as the
right-hand side is large. -/
theorem realize_montalbanSentence {N : Type w'} [L.Structure N]
    (Φ : ∀ n, (Fin n → M) → L.Formulaω (Fin n)) :
    (montalbanSentence Φ).realize_as_sentence N ↔
      (Φ 0 Fin.elim0).Realize (Fin.elim0 : Fin 0 → N) ∧
        ∀ (n : ℕ) (a : Fin n → M) (b : Fin n → N), (Φ n a).Realize b →
          SameAtomicType (L := L) a b ∧
          (∀ m, ∃ y, (Φ (n + 1) (Fin.snoc a m)).Realize (Fin.snoc b y)) ∧
          ∀ y, ∃ m, (Φ (n + 1) (Fin.snoc a m)).Realize (Fin.snoc b y) := by
  simp only [Formulaω.realize_as_sentence, montalbanSentence, montalbanClause,
    Formulaω.realize_inf, Formulaω.realize_einf, realize_forallTuple, realize_montalbanClauseBody,
    ← sameAtomicType_iff_realize_atomicDiagram, Sigma.forall]

omit [Countable (Σ l, L.Relations l)] in
/-- The transport of an unpointed formula to `Fin (0 + n)`, read at `⟨⟩⌢b`. -/
private theorem realize_mapFreeVars_cast {N : Type w'} [L.Structure N] {n : ℕ}
    (φ : L.Formulaω (Fin n)) (b : Fin n → N) :
    Formulaω.Realize (BoundedFormulaω.mapFreeVars (Fin.cast (Nat.zero_add n).symm) φ)
      (Fin.append (Fin.elim0 : Fin 0 → N) b) ↔ φ.Realize b := by
  rw [Formulaω.realize_def, BoundedFormulaω.realize_mapFreeVars, ← Formulaω.realize_def]
  congr!
  funext i
  simp [Fin.elim0_append]

omit [Countable (Σ l, L.Relations l)] [Countable M] in
/-- Atomic agreement of `⟨⟩⌢a` and `⟨⟩⌢b` is atomic agreement of `a` and `b`. -/
private theorem sameAtomicType_elim0_append {N : Type w'} [L.Structure N] {n : ℕ}
    (a : Fin n → M) (b : Fin n → N) :
    SameAtomicType (L := L) (Fin.append (Fin.elim0 : Fin 0 → M) a)
        (Fin.append (Fin.elim0 : Fin 0 → N) b) ↔ SameAtomicType (L := L) a b := by
  rw [Fin.elim0_append, Fin.elim0_append]
  refine ⟨fun h ↦ ?_, fun h ↦ h.relabel _⟩
  simpa only [Function.comp_def, Fin.cast_cast, Fin.cast_eq_self] using
    h.relabel (Fin.cast (Nat.zero_add n).symm)

/-- **Compatibility at `k = 0`.**  The unpointed sentence holds in `N` iff the pointed sentence
over the empty parameter tuple holds there, for the family transported from `Fin n` to
`Fin (0 + n)`.  Through this lemma the unpointed theorems are the case `k = 0` of the pointed
ones. -/
theorem realize_montalbanSentence_iff_pointed {N : Type w'} [L.Structure N]
    (Φ : ∀ n, (Fin n → M) → L.Formulaω (Fin n)) :
    (montalbanSentence Φ).realize_as_sentence N ↔
      (montalbanSentencePointed (Fin.elim0 : Fin 0 → M) fun n a ↦
        BoundedFormulaω.mapFreeVars (Fin.cast (Nat.zero_add n).symm) (Φ n a)).Realize
          (Fin.elim0 : Fin 0 → N) := by
  rw [realize_montalbanSentence, realize_montalbanSentencePointed]
  have h0 := realize_mapFreeVars_cast (Φ 0 Fin.elim0) (Fin.elim0 : Fin 0 → N)
  rw [show Fin.append (Fin.elim0 : Fin 0 → N) Fin.elim0 = Fin.elim0 from funext (·.elim0)] at h0
  simp only [realize_mapFreeVars_cast, sameAtomicType_elim0_append, h0]

omit [Countable (Σ l, L.Relations l)] [Countable M] in
/-- An unpointed orbit-formula family is a pointed one over the empty parameter tuple. -/
private theorem isOrbitFormulaFamilyPointed_elim0 {Φ : ∀ n, (Fin n → M) → L.Formulaω (Fin n)}
    (hΦ : IsOrbitFormulaFamily Φ) :
    IsOrbitFormulaFamilyPointed (Fin.elim0 : Fin 0 → M) fun n a ↦
      BoundedFormulaω.mapFreeVars (Fin.cast (Nat.zero_add n).symm) (Φ n a) := fun n a b ↦ by
  rw [realize_mapFreeVars_cast, hΦ n a b]
  exact ⟨fun ⟨e, he⟩ ↦ ⟨e, comp_fin_elim0 _, he⟩, fun ⟨e, _, he⟩ ↦ ⟨e, he⟩⟩

/-- **B1.**  If `Φ` is a family of orbit formulas, `M` satisfies its Montalbán sentence. -/
theorem montalbanSentence_self {Φ : ∀ n, (Fin n → M) → L.Formulaω (Fin n)}
    (hΦ : IsOrbitFormulaFamily Φ) : (montalbanSentence Φ).realize_as_sentence M :=
  (realize_montalbanSentence_iff_pointed Φ).2
    (montalbanSentencePointed_self (isOrbitFormulaFamilyPointed_elim0 hΦ))

/-- **B2.**  For **any** family `Φ`, a countable structure satisfying Montalbán's sentence of
`Φ` is isomorphic to `M`.  No hypothesis on `Φ`: the clauses true in `N` are a back-and-forth
system by themselves. -/
theorem nonempty_equiv_of_realize_montalbanSentence [L.IsRelational]
    (Φ : ∀ n, (Fin n → M) → L.Formulaω (Fin n)) (N : Type w) [L.Structure N] [Countable N]
    (h : (montalbanSentence Φ).realize_as_sentence N) : Nonempty (M ≃[L] N) :=
  let ⟨e, _⟩ := exists_equiv_of_realize_montalbanSentencePointed _ _ N _
    ((realize_montalbanSentence_iff_pointed Φ).1 h)
  ⟨e⟩

/-- **Montalbán's sentence is a Scott sentence.**  For a family of orbit formulas, a countable
structure in `M`'s universe satisfies the sentence iff it is isomorphic to `M`. -/
theorem montalbanSentence_characterizes [L.IsRelational]
    {Φ : ∀ n, (Fin n → M) → L.Formulaω (Fin n)} (hΦ : IsOrbitFormulaFamily Φ)
    (N : Type w) [L.Structure N] [Countable N] :
    (montalbanSentence Φ).realize_as_sentence N ↔ Nonempty (M ≃[L] N) :=
  ⟨nonempty_equiv_of_realize_montalbanSentence Φ N, fun ⟨e⟩ ↦ by
    have h := (realize_comp_equiv e _ _).1 (montalbanSentence_self hΦ)
    rwa [comp_fin_elim0] at h⟩

end Unpointed

end FirstOrder.Language
