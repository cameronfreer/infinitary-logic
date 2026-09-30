/-
Regression guard for local automorphisms and infinitary truth on finite tuples
(`InfinitaryLogic/Lomega1omega/LocalAutomorphism.lean`).

Every public theorem is *applied*, not only listed for its axioms.

* **Generic statements** in arbitrary language and carrier universes.
* **Function symbols**: over a language with function symbols of every positive arity, `ℤ` with
  the symbols `xs ↦ xs i + 1`; the translation `x ↦ x + 1` commutes with them, so it agrees
  locally with automorphisms (it is one), and preserves every formula on every tuple.
* **A non-surjective map**: in the pure set `ℕ`, the successor is not surjective, yet on every
  finite tuple it agrees with a permutation (a finite partial bijection extends,
  `Cardinal.extend_function_of_lt`), so it preserves infinitary truth on finite tuples; also as
  a self-embedding (`realize_embedding_comp_of_localAutomorphisms`).
* **Empty and repeated tuples**, the **identity map**, and a **finite simultaneous valuation**
  (two free variables and one bound variable, one automorphism for the combined tuple), including
  a concrete formula evaluated on both sides.
* **Import closure**: the module reaches `Lomega1omega/Theory` (the isomorphism invariance
  `BoundedFormulaω.realize_equiv`) and no Scott-analysis, Karp, rank, Löwenheim–Skolem,
  model-theory, method, descriptive, admissible or Scott-process module.

The headline declarations use only the standard axioms.

Run with: lake env lean scripts/check_local_automorphism_regressions.lean
-/
import InfinitaryLogic.Lomega1omega.LocalAutomorphism
import Mathlib.SetTheory.Cardinal.Arithmetic
import Mathlib.Data.Set.Finite.Range

open Lean FirstOrder FirstOrder.Language BoundedFormulaω

universe u v w

noncomputable section

/-! ### Generic statements -/

section Generic

variable {L : Language.{u, v}} {M : Type w} [L.Structure M]

/-- Any language and carrier universes. -/
example {f : M → M} (hf : ∀ (n : ℕ) (a : Fin n → M), ∃ e : M ≃[L] M, ⇑e ∘ a = f ∘ a) {n : ℕ}
    (φ : L.BoundedFormulaω Empty n) (a : Fin n → M) :
    φ.Realize Empty.elim (f ∘ a) ↔ φ.Realize Empty.elim a :=
  realize_comp_of_localAutomorphisms hf φ a

/-- The identity agrees locally with the identity automorphism. -/
theorem id_localAutomorphisms : ∀ (n : ℕ) (a : Fin n → M), ∃ e : M ≃[L] M, ⇑e ∘ a = id ∘ a :=
  fun _ _ ↦ ⟨Language.Equiv.refl L M, rfl⟩

/-- **Identity map**, in any language and carrier universe. -/
theorem id_realize {n : ℕ} (φ : L.BoundedFormulaω Empty n) (a : Fin n → M) :
    φ.Realize Empty.elim (id ∘ a) ↔ φ.Realize Empty.elim a :=
  realize_comp_of_localAutomorphisms id_localAutomorphisms φ a

/-- **Empty tuple**: sentences are preserved (here trivially, `f ∘ Fin.elim0 = Fin.elim0`, but
through the theorem). -/
theorem empty_tuple_realize {f : M → M}
    (hf : ∀ (n : ℕ) (a : Fin n → M), ∃ e : M ≃[L] M, ⇑e ∘ a = f ∘ a)
    (φ : L.BoundedFormulaω Empty 0) :
    φ.Realize Empty.elim (f ∘ (Fin.elim0 : Fin 0 → M)) ↔
      φ.Realize Empty.elim (Fin.elim0 : Fin 0 → M) :=
  realize_comp_of_localAutomorphisms hf φ Fin.elim0

/-- **Repeated tuple** `(x, x)`. -/
theorem repeated_tuple_realize {f : M → M}
    (hf : ∀ (n : ℕ) (a : Fin n → M), ∃ e : M ≃[L] M, ⇑e ∘ a = f ∘ a)
    (φ : L.BoundedFormulaω Empty 2) (x : M) :
    φ.Realize Empty.elim (f ∘ ![x, x]) ↔ φ.Realize Empty.elim ![x, x] :=
  realize_comp_of_localAutomorphisms hf φ ![x, x]

/-- Simultaneous valuation, any language and carrier universe. -/
example {f : M → M} (hf : ∀ (n : ℕ) (a : Fin n → M), ∃ e : M ≃[L] M, ⇑e ∘ a = f ∘ a)
    {m n : ℕ} (φ : L.BoundedFormulaω (Fin m) n) (v : Fin m → M) (a : Fin n → M) :
    φ.Realize (f ∘ v) (f ∘ a) ↔ φ.Realize v a :=
  realize_comp_append_of_localAutomorphisms hf φ v a

end Generic

/-! ### A language with function symbols -/

section FunctionSymbols

/-- Function symbols of every positive arity `n`, one per coordinate `i : Fin n`; no relation
symbols. -/
def shiftLang : Language.{0, 0} := ⟨fun n ↦ Fin n, fun _ ↦ Empty⟩

/-- `ℤ` with the symbol `i` of arity `n` interpreted as `xs ↦ xs i + 1`. -/
instance shiftStructure : shiftLang.Structure ℤ where
  funMap i xs := xs i + 1
  RelMap r _ := Empty.elim r

/-- Translation by `1` is an automorphism of this structure. -/
def shiftEquiv : ℤ ≃[shiftLang] ℤ where
  toEquiv := Equiv.addRight 1
  map_fun' _ _ := rfl
  map_rel' r := Empty.elim r

/-- The translation agrees locally with an automorphism: itself. -/
theorem shift_localAutomorphisms :
    ∀ (n : ℕ) (a : Fin n → ℤ), ∃ e : ℤ ≃[shiftLang] ℤ, ⇑e ∘ a = (· + 1) ∘ a :=
  fun _ _ ↦ ⟨shiftEquiv, rfl⟩

/-- **Function symbols**: the translation preserves every infinitary formula on every tuple. -/
theorem shift_realize {n : ℕ} (φ : shiftLang.BoundedFormulaω Empty n) (a : Fin n → ℤ) :
    φ.Realize Empty.elim ((· + 1) ∘ a) ↔ φ.Realize Empty.elim a :=
  realize_comp_of_localAutomorphisms shift_localAutomorphisms φ a

end FunctionSymbols

/-! ### A non-surjective map on the pure set `ℕ` -/

section PureSet

/-- The empty-language structure on `ℕ`, local to this file. -/
local instance instNatStructure : Language.empty.Structure ℕ := Language.emptyStructure

/-- On every finite tuple of the pure set `ℕ`, the successor agrees with a permutation: extend
the finite partial bijection `a i ↦ a i + 1`. -/
theorem succ_localAutomorphisms :
    ∀ (n : ℕ) (a : Fin n → ℕ), ∃ e : ℕ ≃[Language.empty] ℕ, ⇑e ∘ a = Nat.succ ∘ a := by
  intro n a
  let f : Set.range a ↪ ℕ := ⟨fun x ↦ x.1 + 1, fun x y h ↦ Subtype.ext (by simpa using h)⟩
  obtain ⟨g, hg⟩ := Cardinal.extend_function_of_lt f
    (Cardinal.mk_lt_aleph0.trans_le (Cardinal.aleph0_le_mk ℕ)) ⟨Equiv.refl ℕ⟩
  exact ⟨{ toEquiv := g }, funext fun i ↦ hg ⟨a i, i, rfl⟩⟩

/-- The successor, as a self-embedding of the pure set `ℕ`; it is not surjective. -/
def succEmbedding : ℕ ↪[Language.empty] ℕ := { toEmbedding := ⟨Nat.succ, Nat.succ_injective⟩ }

/-- The successor embedding misses `0`. -/
theorem succEmbedding_not_surjective : ¬ Function.Surjective succEmbedding :=
  fun h ↦ let ⟨_, hx⟩ := h 0; Nat.succ_ne_zero _ hx

/-- **A non-surjective map preserves infinitary truth on finite tuples.** -/
theorem succ_realize {n : ℕ} (φ : Language.empty.BoundedFormulaω Empty n) (a : Fin n → ℕ) :
    φ.Realize Empty.elim (Nat.succ ∘ a) ↔ φ.Realize Empty.elim a :=
  realize_comp_of_localAutomorphisms succ_localAutomorphisms φ a

/-- **Embedding form** (`realize_embedding_comp_of_localAutomorphisms`). -/
theorem succEmbedding_realize {n : ℕ} (φ : Language.empty.BoundedFormulaω Empty n)
    (a : Fin n → ℕ) :
    φ.Realize Empty.elim (⇑succEmbedding ∘ a) ↔ φ.Realize Empty.elim a :=
  realize_embedding_comp_of_localAutomorphisms succEmbedding succ_localAutomorphisms φ a

/-- With free variables `x₀ x₁` and one bound variable `y`: the formula `y = x₀ → y ≠ x₁`. -/
def sampleFormula : Language.empty.BoundedFormulaω (Fin 2) 1 :=
  (BoundedFormulaω.equal (Term.var (Sum.inr 0)) (Term.var (Sum.inl 0))).imp
    (BoundedFormulaω.equal (Term.var (Sum.inr 0)) (Term.var (Sum.inl 1))).not

/-- **Finite simultaneous valuation**: two free variables and one bound variable, moved by one
permutation, on a concrete formula; both sides hold. -/
theorem sample_simultaneous :
    (sampleFormula.Realize (Nat.succ ∘ ![3, 5]) (Nat.succ ∘ ![3]) ↔
        sampleFormula.Realize ![3, 5] ![3]) ∧ sampleFormula.Realize ![3, 5] ![3] := by
  refine ⟨realize_comp_append_of_localAutomorphisms succ_localAutomorphisms _ _ _, ?_⟩
  simp [sampleFormula]

end PureSet

/-! ### Import closure and axiom audit -/

/-- The modules transitively imported by `m` (including `m`), read from the environment
header. -/
partial def importClosure (env : Environment) (m : Name) : NameSet :=
  go [m] {}
where
  go : List Name → NameSet → NameSet
    | [], seen => seen
    | m :: rest, seen =>
      if seen.contains m then go rest seen
      else
        let deps := match env.getModuleIdx? m with
          | some idx => (env.header.moduleData[idx.toNat]!).imports.toList.map (·.module)
          | none => []
        go (deps ++ rest) (seen.insert m)

/-- Module-name prefixes the closure may not have: Scott analysis (Scott sentences, ranks,
back-and-forth), Karp, the quantifier-rank module, Löwenheim–Skolem and the rest of the model
theory, and every later layer. -/
def forbiddenPrefixes : List Name :=
  [`InfinitaryLogic.Scott, `InfinitaryLogic.ScottProcess, `InfinitaryLogic.Karp,
   `InfinitaryLogic.Lomega1omega.QuantifierRank, `InfinitaryLogic.ModelTheory,
   `InfinitaryLogic.Methods, `InfinitaryLogic.Descriptive, `InfinitaryLogic.Admissible,
   `InfinitaryLogic.Conditional, `InfinitaryLogic.WIP]

run_cmd do
  let env ← getEnv
  let target := `InfinitaryLogic.Lomega1omega.LocalAutomorphism
  unless (env.getModuleIdx? target).isSome do
    throwError "module {target} is not in the environment"
  let cl := importClosure env target
  unless cl.contains `InfinitaryLogic.Lomega1omega.Theory do
    throwError "[MISSING ROUTE] Lomega1omega.Theory is not in the closure of {target}"
  let hits := cl.toList.filter fun m => forbiddenPrefixes.any (·.isPrefixOf m)
  unless hits.isEmpty do
    throwError "[BROAD CONE] the closure of {target} reaches {hits}"

/-- The declarations whose axioms are audited. -/
def headline : List Name :=
  ([`realize_comp_of_localAutomorphisms,
    `realize_embedding_comp_of_localAutomorphisms,
    `realize_comp_append_of_localAutomorphisms]).map (`FirstOrder.Language.BoundedFormulaω ++ ·) ++
  [`id_localAutomorphisms, `id_realize, `empty_tuple_realize, `repeated_tuple_realize,
   `shiftEquiv, `shift_localAutomorphisms, `shift_realize, `succ_localAutomorphisms,
   `succEmbedding_not_surjective, `succ_realize, `succEmbedding_realize, `sample_simultaneous]

/-- The standard axioms. -/
def standardAxioms : List Name := [`propext, `Classical.choice, `Quot.sound]

run_cmd do
  let env ← getEnv
  for n in headline do
    unless (env.find? n).isSome do throwError "headline declaration {n} not found"
    let axs ← Elab.Command.liftCoreM (collectAxioms n)
    let bad := axs.toList.filter fun a => !standardAxioms.contains a
    unless bad.isEmpty do throwError "[NONSTANDARD AXIOMS] {n} uses {bad}"
  logInfo "local-automorphism regression guard: OK (applied: generic statements in arbitrary \
    universes; the identity map; empty and repeated tuples; the translation of Z over a language \
    with function symbols; the non-surjective successor of the pure set N, which \
    agrees locally with permutations, also as a self-embedding; a finite simultaneous valuation \
    on a concrete formula; import closure without Scott analysis, Karp, rank, \
    Lowenheim-Skolem or model-theory modules; standard axioms)"
