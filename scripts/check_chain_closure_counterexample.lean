/-
Executable regression: chain closure is FALSE for `AConsistent`.

The superseded engine (`BarwiseFragment.chain_closure_consistent`, a Zorn-style maximal
consistent extension, still present in `ConsistencyBridge.lean`) assumed that the union of a
⊆-chain of `P`-consistent sets is `P`-consistent. It is not, already for `P = Set.univ`: with
one relation symbol `U` and ℕ many constants, `Sₙ := {¬⋀ₖ U(cₖ)} ∪ {U(cₖ) | k ≤ n}` are each
consistent (model ℕ, `U` true exactly on `{0,…,n}`, every element named by its constant), form
a chain, and the union derives `⊥` by the ω-rule `iInf_intro`.

Consequences recorded here so the discarded architecture cannot return:
* `FullBarwiseFragment LC` is uninhabited (its `complete` field forces `formulas = Set.univ`);
  `BarwiseFragment LC` with a proper formula set is NOT shown uninhabited by this file.
* `Admissible/Barwise/HenkinClosed.lean` therefore routes through the fair-enumeration kernel,
  whose consistency property has no chain-closure field.

Run with: lake env lean scripts/check_chain_closure_counterexample.lean
-/
import InfinitaryLogic.Admissible.Barwise.Soundness

open FirstOrder Language

namespace ChainClosureCounterexample

/-- One relation symbol at every arity, no function symbols. -/
def L1 : Language.{0, 0} := ⟨fun _ => Empty, fun _ => Unit⟩

abbrev LC : Language.{0, 0} := L1[[ℕ]]

/-- The closed constant term `c_k`. -/
def ck (k : ℕ) : LC.Term Empty := Term.func (Sum.inr k : LC.Functions 0) Fin.elim0

/-- `c_k` inside a sentence. -/
def ckS (k : ℕ) : LC.Term (Empty ⊕ Fin 0) := Term.func (Sum.inr k : LC.Functions 0) Fin.elim0

/-- The atom `U(c_k)`. -/
def atom (k : ℕ) : LC.Sentenceω :=
  BoundedFormulaω.rel (Sum.inl () : LC.Relations 1) (fun _ => ckS k)

/-- The chain members. -/
def S (n : ℕ) : Set LC.Sentenceω :=
  insert (BoundedFormulaω.iInf atom).not {φ | ∃ k ≤ n, φ = atom k}

/-- The model `Mₙ`: carrier ℕ (wrapped so the structure can depend on `n`), `U` true exactly
below `n`, `c_k ↦ k`. -/
def M (_n : ℕ) : Type := ℕ

instance (n : ℕ) : L1.Structure (M n) where
  funMap := fun f _ => f.elim
  RelMap := fun _ xs => ∀ i, @LE.le ℕ _ (xs i) n

instance (n : ℕ) : (constantsOn ℕ).Structure (M n) := constantsOn.structure (fun k => (k : M n))

theorem realize_ck (n k : ℕ) : (ck k).realize (Empty.elim : Empty → M n) = (k : M n) := rfl

/-- Every element is named by its constant. -/
def naming (n : ℕ) : NamingFunction LC (M n) where
  name := fun m => ck m
  sound := fun m => realize_ck n m

theorem realize_atom (n k : ℕ) : Sentenceω.Realize (atom k) (M n) ↔ k ≤ n := by
  exact ⟨fun h => h 0, fun h _ => h⟩

theorem model_S (n : ℕ) : Theoryω.Model (S n) (M n) := by
  intro φ hφ
  rcases hφ with rfl | ⟨k, hk, rfl⟩
  · show BoundedFormulaω.Realize _ (Empty.elim : Empty → M n) Fin.elim0
    rw [BoundedFormulaω.realize_not, BoundedFormulaω.realize_iInf]
    intro h
    have h' := (realize_atom n (n + 1)).mp (h (n + 1))
    omega
  · exact (realize_atom n k).mpr hk

theorem consistent_S (n : ℕ) : AConsistent (Set.univ : Set LC.Sentenceω) (S n) :=
  AConsistent.of_has_model (naming n) (model_S n)

theorem S_mono {m n : ℕ} (h : m ≤ n) : S m ⊆ S n := by
  intro φ hφ
  rcases hφ with rfl | ⟨k, hk, rfl⟩
  · exact Set.mem_insert _ _
  · exact Set.mem_insert_of_mem _ ⟨k, le_trans hk h, rfl⟩

theorem isChain_S : IsChain (· ⊆ ·) (Set.range S) := by
  rintro _ ⟨m, rfl⟩ _ ⟨n, rfl⟩ _
  rcases le_total m n with h | h
  · exact Or.inl (S_mono h)
  · exact Or.inr (S_mono h)

theorem union_inconsistent : ¬ AConsistent (Set.univ : Set LC.Sentenceω) (⋃₀ Set.range S) := by
  intro hc
  apply hc
  have hall : ∀ k, Derivable Set.univ (⋃₀ Set.range S) (atom k) := fun k =>
    .assumption ⟨S k, ⟨k, rfl⟩, Set.mem_insert_of_mem _ ⟨k, le_rfl, rfl⟩⟩ trivial
  have hinf : Derivable Set.univ (⋃₀ Set.range S) (BoundedFormulaω.iInf atom) :=
    .iInf_intro hall trivial
  have hneg : Derivable Set.univ (⋃₀ Set.range S) (BoundedFormulaω.iInf atom).not :=
    .assumption ⟨S 0, ⟨0, rfl⟩, Set.mem_insert _ _⟩ trivial
  exact .imp_elim hneg hinf

/-- **Chain closure is false**, in exactly the form `BarwiseFragment.chain_closure_consistent`
demands, already for `P = Set.univ`. -/
theorem no_chain_closure :
    ¬ ∀ (chain : Set (Set LC.Sentenceω)),
        chain ⊆ {T | T ⊆ Set.univ ∧ AConsistent Set.univ T} →
        IsChain (· ⊆ ·) chain → chain.Nonempty →
        AConsistent (Set.univ : Set LC.Sentenceω) (⋃₀ chain) := by
  intro h
  exact union_inconsistent
    (h (Set.range S) (by rintro _ ⟨n, rfl⟩; exact ⟨Set.subset_univ _, consistent_S n⟩)
      isChain_S ⟨S 0, 0, rfl⟩)

end ChainClosureCounterexample


open Lean in
run_cmd do
  let env ← getEnv
  unless (env.find? `ChainClosureCounterexample.no_chain_closure).isSome do
    throwError "chain-closure counterexample missing"
  logInfo "chain-closure regression: OK (AConsistent is not chain-closed, even for \
    P = Set.univ)"
