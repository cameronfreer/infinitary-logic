/-
Regression guard for the `L_{∞κ}` block-quantifier layer (`InfinitaryLogic/LinfKappa/`:
`Syntax`, `Semantics`, `Substitution`, `Unary`).

Every exported theorem the guard relies on is *applied*, not only listed for its axioms.

1. **Universe gates.**  `L.BlockFormula ι V α Γ : Type (max u v uι uQ w u')` (no `+1`); the
   short-tuple carrier `Σ q : InitCode κ, (initSeg κ q → M)` and `BlockSlots (initSeg κ) Γ` stay
   in `Type w`.
2. **Universe pins.**  `levelParams` of `BlockSlots` (`[uQ, w]`), `BlockFormula`
   (`[u, v, uι, uQ, w, u']`), `BlockFormula.Realize` (`[u, v, uι, uQ, w, u', wM]`) and of the main
   theorems are exactly the frozen lists; `[UNIVERSE DRIFT]` otherwise.
3. **Binder-kind pins.**  The `BinderInfo` sequence of `realize_allBlock`, `realize_closeAll`,
   `realize_mapSlots`, `realize_substSlots`, `realize_reassoc`, `realize_ofInf` and
   `reassocEquiv_left`/`_middle`/`_right` is the frozen one; `[BINDER DRIFT]` otherwise.
   **Mutation control:** a local copy of `realize_allBlock` with one binder made explicit must be
   reported by the same check.
4. **Transparency.**  `BlockSlots` is `@[reducible]`; the step `rw [realize_mapSlots]` at a slot
   valuation `Sum.elim b ys` and a renaming `Sum.map id ρ` (the binder case, which fails for a
   semireducible `BlockSlots`) succeeds; `realize_allBlock` is `Iff.rfl`.
5. **Block acceptance tests.**  The empty block (`exBlock` and `allBlock` agree); the singleton
   block (`unitShape`); the real pairwise-distinct formula `∃ (yₙ)ₙ ⋀_{i ≠ j} yᵢ ≠ yⱼ` with one
   `ℕ`-shaped block: realized iff there is an injection `ℕ → M`, true in `ℕ`, false in `Fin 3`, and
   false in `Unit`, where its inequality-free variant `∃ (yₙ)ₙ ⊤` is true (so the two are
   separated).  The `κ = ω` instance: with `finShapes`, the sentence `∃_2 x ∀_3 y (x₀ ≠ x₁ ∧ some
   two of x₀, x₁, y₀, y₁, y₂ coincide)` is characterized, true on `Fin 4` and false on `Fin 1`; the
   canonical `InitCode ℵ₀` blocks are finite.
6. **Substitution under nested binders.**  In a language with a constant `zero` and a unary
   function `succ`, the formula `∃ y ∀ z (z = s → succ y = z)` with the outer slot `s` substituted
   by the closed term `succ zero` is true in `ℕ` by direct evaluation and through
   `realize_substSlots`; with `s := zero` it is false.  `mapSlots_id`, `mapSlots_mapSlots` on a
   concrete formula.
7. **Three-way reassociation** on `[1] ++ ([2] ++ [3])` with the distinct shapes `Fin 1`, `Fin 2`,
   `Fin 3`: each component lands in the intended summand (`reassocEquiv_left`/`_middle`/`_right`
   and explicit values), both inverse equations, `appendEquiv_cons_inl` and `appendEquiv_nil` by
   `rfl`, and `realize_reassoc` on a concrete formula.
8. **`ofInf`.**  A `BoundedFormulaω α 1` is accepted by `ofInf ()` at `V := unitShape` with no
   cast; `realize_ofInf` on `∀ x, x = x` and on a formula with one free bound variable; the
   orientation (`Fin.last ↦ head block`) by explicit values of `finToSlots`.
9. **Independent universes.**  `M : Type 2`, `ι : Type 1`, `Q : Type 3`, `V : Q → Type 0`,
   `α : Type 1`: `realize_allBlock`, `realize_substSlots` and `realize_ofInf` elaborate.
10. **Closure pins.**  The `InfinitaryLogic` modules in the import closure of each module are
    exactly: `Syntax` none; `Semantics` `{Syntax}`; `Substitution` and `Unary`
    `{Syntax, Semantics}` (`[CLOSURE DRIFT]`).  No closure contains
    `Mathlib.SetTheory.Cardinal.HasCardinalLT` or an `InfinitaryLogic.Lomega1omega`, `Scott` or
    `Karp` module (`[BROAD CONE]`).
11. **Positive cone.**  The dependency cone of `realize_iInfAlong`, theorem bodies included (via
    `.thmInfo`), contains `FirstOrder.IndexCoding.pad`.
12. **Axiom audit.**  Every exported declaration and every guard declaration uses only `propext`,
    `Classical.choice`, `Quot.sound`.

The final `run_cmd` performs checks 2, 3, 4 (reducibility), 10, 11 and 12, and checks that every
named guard declaration exists, before printing OK.

Run with: lake env lean scripts/check_linfkappa_syntax_regressions.lean
-/
import InfinitaryLogic.LinfKappa.Substitution
import InfinitaryLogic.LinfKappa.Unary

open Lean Meta Elab Command FirstOrder FirstOrder.Language

universe u v uι uQ w u' wM

noncomputable section

namespace LinfKappaSyntaxGuard

/-! ### 1. Universe gates -/

section Gates

variable {L : Language.{u, v}} {ι : Type uι} {Q : Type uQ} {V : Q → Type w} {α : Type u'}

/-- No `+1`: block formulas live in the maximum of the parameter universes. -/
abbrev gateFormula (Γ : List Q) : Type (max u v uι uQ w u') :=
  L.BlockFormula ι V α Γ

/-- The short-tuple carrier over the canonical codes stays in `Type w`. -/
abbrev gateShortTuples (κ : Cardinal.{w}) (M : Type w) : Type w :=
  Σ q : InitCode κ, (initSeg κ q → M)

/-- Canonical slots stay in `Type w`. -/
abbrev gateCanonicalSlots (κ : Cardinal.{w}) (Γ : List (InitCode κ)) : Type w :=
  BlockSlots (initSeg κ) Γ

end Gates

/-! ### 3. Mutation control for the binder pins -/

/-- `realize_allBlock` with the slot valuation made explicit: the binder check must flag it. -/
theorem realize_allBlock_flipped {L : Language.{u, v}} {ι : Type uι} {Q : Type uQ}
    {V : Q → Type w} {α : Type u'} {M : Type wM} [L.Structure M] {Γ : List Q} {q : Q}
    {φ : L.BlockFormula ι V α (q :: Γ)} {v : α → M} (xs : BlockSlots V Γ → M) :
    (BlockFormula.allBlock q φ).Realize v xs ↔ ∀ b : V q → M, φ.Realize v (Sum.elim b xs) :=
  Iff.rfl

/-! ### 4. Transparency regression -/

section Transparency

variable {L : Language.{u, v}} {ι : Type uι} {Q : Type uQ} {V : Q → Type w} {α : Type u'}
  {M : Type wM} [L.Structure M]

/-- The binder step of `realize_mapSlots`: `rw` with the renaming lemma at the lifted renaming
`Sum.map id ρ` and the slot valuation `Sum.elim b ys`.  Under a semireducible `BlockSlots` this
`rw` fails ("motive is not type correct" at the `implicit` transparency level). -/
theorem rw_realize_mapSlots_binder {Γ Δ : List Q} {q : Q} (φ : L.BlockFormula ι V α (q :: Γ))
    (ρ : BlockSlots V Γ → BlockSlots V Δ) (v : α → M) (b : V q → M) (ys : BlockSlots V Δ → M) :
    (φ.mapSlots (Δ := q :: Δ) (Sum.map id ρ)).Realize v (Sum.elim b ys) ↔
      φ.Realize v (Sum.elim b (ys ∘ ρ)) := by
  rw [BlockFormula.realize_mapSlots]
  rw [Sum.elim_comp_map]
  rfl

/-- The block binder is definitional. -/
theorem realize_allBlock_rfl {Γ : List Q} {q : Q} (φ : L.BlockFormula ι V α (q :: Γ))
    (v : α → M) (xs : BlockSlots V Γ → M) :
    (BlockFormula.allBlock q φ).Realize v xs ↔ ∀ b : V q → M, φ.Realize v (Sum.elim b xs) :=
  Iff.rfl

end Transparency

/-! ### 5. Block acceptance tests -/

section EmptyBlock

/-- One code, whose block is empty. -/
abbrev emptyShape : Unit → Type :=
  fun _ ↦ PEmpty

variable {L : Language.{u, v}} {ι : Type uι} {α : Type u'} {M : Type wM} [L.Structure M]

/-- The empty block binds nothing: the block valuation is `PEmpty.elim`. -/
theorem empty_allBlock {Γ : List Unit} (φ : L.BlockFormula ι emptyShape α (() :: Γ))
    (v : α → M) (xs : BlockSlots emptyShape Γ → M) :
    (BlockFormula.allBlock () φ).Realize v xs ↔ φ.Realize v (Sum.elim PEmpty.elim xs) :=
  ⟨fun h ↦ h _, fun h b ↦ by rwa [Subsingleton.elim b PEmpty.elim]⟩

/-- Over the empty block, `∃` and `∀` agree on every formula. -/
theorem empty_exBlock_iff_allBlock {Γ : List Unit} (φ : L.BlockFormula ι emptyShape α (() :: Γ))
    (v : α → M) (xs : BlockSlots emptyShape Γ → M) :
    (BlockFormula.exBlock () φ).Realize v xs ↔ (BlockFormula.allBlock () φ).Realize v xs := by
  rw [BlockFormula.realize_exBlock, empty_allBlock]
  exact ⟨fun ⟨b, hb⟩ ↦ by rwa [Subsingleton.elim b PEmpty.elim] at hb, fun h ↦ ⟨_, h⟩⟩

end EmptyBlock

section SingletonBlock

variable {L : Language.{u, v}} {ι : Type uι} {α : Type u'} {M : Type wM} [L.Structure M]

/-- The singleton block is ordinary unary quantification. -/
theorem singleton_allBlock {Γ : List Unit} (φ : L.BlockFormula ι unitShape α (() :: Γ))
    (v : α → M) (xs : BlockSlots unitShape Γ → M) :
    (BlockFormula.allBlock () φ).Realize v xs ↔ ∀ x : M, φ.Realize v (Sum.elim (fun _ ↦ x) xs) :=
  ⟨fun h x ↦ h fun _ ↦ x, fun h b ↦ h (b PUnit.unit)⟩

end SingletonBlock

section PairwiseDistinct

attribute [local instance] Language.emptyStructure

/-- One code, whose block is `ℕ`-shaped. -/
abbrev omegaShape : Unit → Type :=
  fun _ ↦ ℕ

/-- Off-diagonal pairs of block positions: the carrier of the conjunction. -/
abbrev OffDiag : Type :=
  {p : ℕ × ℕ // p.1 ≠ p.2}

/-- The `n`th variable of the single `ℕ`-shaped block. -/
abbrev blockVar (n : ℕ) : Language.empty.Term (Empty ⊕ BlockSlots omegaShape [()]) :=
  Term.var (Sum.inr (Sum.inl n))

/-- `∃ (yₙ)ₙ ⋀_{i ≠ j} ¬ yᵢ = yⱼ`: there are `ω` pairwise distinct elements. -/
def pairwiseDistinctOmega : Language.empty.BlockSentence OffDiag omegaShape :=
  BlockFormula.exBlock () (BlockFormula.iInf fun p : OffDiag ↦
    (BlockFormula.equal (blockVar p.1.1) (blockVar p.1.2)).not)

/-- The inequality-free variant `∃ (yₙ)ₙ ⊤`. -/
def inequalityFreeOmega : Language.empty.BlockSentence OffDiag omegaShape :=
  BlockFormula.exBlock () ⊤

theorem realize_pairwiseDistinctOmega (M : Type) :
    pairwiseDistinctOmega.Realize M ↔ ∃ b : ℕ → M, Function.Injective b := by
  simp only [BlockSentence.Realize, pairwiseDistinctOmega, BlockFormula.realize_exBlock,
    BlockFormula.realize_iInf, BlockFormula.realize_not, BlockFormula.realize_equal,
    Term.realize_var, Sum.elim_inr, Sum.elim_inl]
  refine exists_congr fun b ↦ ⟨fun h i j hij ↦ ?_, fun h p hp ↦ p.2 (h hp)⟩
  by_contra hne
  exact h ⟨(i, j), hne⟩ hij

theorem pairwiseDistinctOmega_nat : pairwiseDistinctOmega.Realize ℕ :=
  (realize_pairwiseDistinctOmega ℕ).2 ⟨id, Function.injective_id⟩

theorem not_pairwiseDistinctOmega_fin3 : ¬ pairwiseDistinctOmega.Realize (Fin 3) := by
  rw [realize_pairwiseDistinctOmega]
  rintro ⟨b, hb⟩
  exact not_injective_infinite_finite b hb

theorem not_pairwiseDistinctOmega_unit : ¬ pairwiseDistinctOmega.Realize Unit := by
  rw [realize_pairwiseDistinctOmega]
  rintro ⟨b, hb⟩
  exact not_injective_infinite_finite b hb

/-- The inequality-free variant holds in a singleton. -/
theorem inequalityFreeOmega_unit : inequalityFreeOmega.Realize Unit := by
  simp only [BlockSentence.Realize, inequalityFreeOmega, BlockFormula.realize_exBlock,
    BlockFormula.realize_top]
  exact ⟨fun _ ↦ (), trivial⟩

/-- `Unit` separates the real formula from its inequality-free variant. -/
theorem pairwiseDistinct_separated_from_inequalityFree :
    inequalityFreeOmega.Realize Unit ∧ ¬ pairwiseDistinctOmega.Realize Unit :=
  ⟨inequalityFreeOmega_unit, not_pairwiseDistinctOmega_unit⟩

end PairwiseDistinct

section FiniteBlocks

attribute [local instance] Language.emptyStructure

/-- Off-diagonal pairs of five positions. -/
abbrev OffDiag5 : Type :=
  {p : Fin 5 × Fin 5 // p.1 ≠ p.2}

/-- The five variables `x₀, x₁` (outer block of size `2`) and `y₀, y₁, y₂` (head block of size
`3`) in the context `[3, 2]`. -/
def fiveVars : Fin 5 → Language.empty.Term (Empty ⊕ BlockSlots finShapes [3, 2]) :=
  Fin.append (fun i : Fin 2 ↦ Term.var (Sum.inr (Sum.inr (Sum.inl i))))
    (fun j : Fin 3 ↦ Term.var (Sum.inr (Sum.inl j)))

/-- `x₀ ≠ x₁ ∧ ⋁_{i ≠ j} zᵢ = zⱼ`, the conjunction written as `¬ (A → ¬ B)`. -/
def finBody : Language.empty.BlockFormula OffDiag5 finShapes Empty [3, 2] :=
  ((BlockFormula.equal (fiveVars 0) (fiveVars 1)).not.imp
    (BlockFormula.iSup fun p : OffDiag5 ↦
      BlockFormula.equal (fiveVars p.1.1) (fiveVars p.1.2)).not).not

/-- `∃_2 x ∀_3 y (x₀ ≠ x₁ ∧ some two of x₀, x₁, y₀, y₁, y₂ coincide)`. -/
def finSentence : Language.empty.BlockSentence OffDiag5 finShapes :=
  BlockFormula.exBlock 2 (BlockFormula.allBlock 3 finBody)

theorem realize_fiveVars {M : Type} (xs : BlockSlots finShapes [3, 2] → M) (k : Fin 5) :
    (fiveVars k).realize (Sum.elim (Empty.elim : Empty → M) xs) =
      Fin.append (fun i : Fin 2 ↦ xs (Sum.inr (Sum.inl i))) (fun j : Fin 3 ↦ xs (Sum.inl j)) k := by
  refine Fin.addCases (m := 2) (n := 3) (fun i ↦ ?_) (fun j ↦ ?_) k <;>
    simp [fiveVars, Fin.append_left, Fin.append_right]

/-- Atomic formulas over the five variables, at the formula level (a term-level simp lemma does
not fire here: its key mentions the unfolded slot type `Fin 3 ⊕ (Fin 2 ⊕ PEmpty)`). -/
theorem realize_equal_fiveVars {M : Type} (xs : BlockSlots finShapes [3, 2] → M) (i j : Fin 5) :
    (BlockFormula.equal (fiveVars i) (fiveVars j) :
        Language.empty.BlockFormula OffDiag5 finShapes Empty [3, 2]).Realize
      (Empty.elim : Empty → M) xs ↔
      Fin.append (fun i : Fin 2 ↦ xs (Sum.inr (Sum.inl i))) (fun j : Fin 3 ↦ xs (Sum.inl j)) i =
        Fin.append (fun i : Fin 2 ↦ xs (Sum.inr (Sum.inl i)))
          (fun j : Fin 3 ↦ xs (Sum.inl j)) j := by
  rw [BlockFormula.realize_equal, realize_fiveVars, realize_fiveVars]

theorem realize_finSentence (M : Type) :
    finSentence.Realize M ↔
      ∃ x : Fin 2 → M, ∀ y : Fin 3 → M, x 0 ≠ x 1 ∧ ¬ Function.Injective (Fin.append x y) := by
  simp only [BlockSentence.Realize, finSentence, finBody, BlockFormula.realize_exBlock,
    BlockFormula.realize_allBlock, BlockFormula.realize_not, BlockFormula.realize_imp,
    realize_equal_fiveVars, BlockFormula.realize_iSup]
  refine exists_congr fun x ↦ forall_congr' fun y ↦ ?_
  have hx : (fun i : Fin 2 ↦ (Sum.elim y (Sum.elim x PEmpty.elim) :
      BlockSlots finShapes [3, 2] → M) (Sum.inr (Sum.inl i))) = x := rfl
  have hy : (fun j : Fin 3 ↦ (Sum.elim y (Sum.elim x PEmpty.elim) :
      BlockSlots finShapes [3, 2] → M) (Sum.inl j)) = y := rfl
  rw [hx, hy]
  have h0 : Fin.append x y 0 = x 0 := Fin.append_left x y 0
  have h1 : Fin.append x y 1 = x 1 := Fin.append_left x y 1
  rw [h0, h1, Function.Injective]
  constructor
  · intro h
    by_contra hc
    exact h fun hne ⟨⟨⟨i, j⟩, hij⟩, hEq⟩ ↦ hc ⟨hne, fun hinj ↦ hij (hinj hEq)⟩
  · rintro ⟨hne, hni⟩ h
    refine h hne ?_
    by_contra hall
    exact hni fun a b hab ↦ by_contra fun hab' ↦ hall ⟨⟨(a, b), hab'⟩, hab⟩

theorem finSentence_fin4 : finSentence.Realize (Fin 4) := by
  rw [realize_finSentence]
  refine ⟨![0, 1], fun y ↦ ⟨by decide, fun h ↦ ?_⟩⟩
  have := Fintype.card_le_of_injective _ h
  simp at this

theorem not_finSentence_fin1 : ¬ finSentence.Realize (Fin 1) := by
  rw [realize_finSentence]
  rintro ⟨x, hx⟩
  exact (hx 0).1 (Subsingleton.elim _ _)

/-- The canonical `κ = ω` codes give finite blocks. -/
theorem initSeg_aleph0_finite (q : InitCode Cardinal.aleph0.{0}) :
    Finite (initSeg Cardinal.aleph0 q) :=
  Cardinal.lt_aleph0_iff_finite.1 ((Cardinal.mk_Iio_lt q (by simp)).trans_le (by simp))

/-- The canonical `κ = ω` slots elaborate in `Type`. -/
abbrev aleph0Slots (Γ : List (InitCode Cardinal.aleph0.{0})) : Type :=
  BlockSlots (initSeg Cardinal.aleph0) Γ

end FiniteBlocks

/-! ### 6. Substitution under nested binders -/

section Substitution

/-- Function symbols: a constant `zero` and a unary `succ`. -/
inductive ZSFunc : ℕ → Type
  | zero : ZSFunc 0
  | succ : ZSFunc 1

/-- The language of zero and successor. -/
abbrev zsLang : Language.{0, 0} :=
  ⟨ZSFunc, fun _ ↦ Empty⟩

instance : zsLang.Structure ℕ where
  funMap {_} f xs := match f with
    | .zero => 0
    | .succ => xs 0 + 1
  RelMap {_} r _ := Empty.elim r

/-- The constant term `zero`. -/
abbrev zeroT {β : Type} : zsLang.Term β :=
  Term.func ZSFunc.zero ![]

/-- The term `succ t`. -/
abbrev succT {β : Type} (t : zsLang.Term β) : zsLang.Term β :=
  Term.func ZSFunc.succ ![t]

theorem realize_zeroT {β : Type} (e : β → ℕ) : (zeroT : zsLang.Term β).realize e = 0 :=
  rfl

theorem realize_succT {β : Type} (e : β → ℕ) (t : zsLang.Term β) :
    (succT t).realize e = t.realize e + 1 :=
  rfl

/-- `∃ y ∀ z (z = s → succ y = z)` over the outer slot `s`, in the context `[()]`; the slots of
the body are `z` (head), `y`, `s`. -/
def predFormula : zsLang.BlockFormula Unit unitShape Empty [()] :=
  BlockFormula.exBlock () (BlockFormula.allBlock ()
    ((BlockFormula.equal (Term.var (Sum.inr (Sum.inl PUnit.unit)))
        (Term.var (Sum.inr (Sum.inr (Sum.inr (Sum.inl PUnit.unit)))))).imp
      (BlockFormula.equal (succT (Term.var (Sum.inr (Sum.inr (Sum.inl PUnit.unit)))))
        (Term.var (Sum.inr (Sum.inl PUnit.unit))))))

/-- Substitute the closed term `succ zero` for the outer slot. -/
def σOne : BlockSlots unitShape [()] → zsLang.Term (Empty ⊕ BlockSlots unitShape []) :=
  fun _ ↦ succT zeroT

/-- Substitute the closed term `zero` for the outer slot. -/
def σZero : BlockSlots unitShape [()] → zsLang.Term (Empty ⊕ BlockSlots unitShape []) :=
  fun _ ↦ zeroT

theorem realize_predFormula (s : ℕ) :
    predFormula.Realize (Empty.elim : Empty → ℕ) (Sum.elim (fun _ ↦ s) PEmpty.elim) ↔
      ∃ y : ℕ, y + 1 = s := by
  simp only [predFormula, BlockFormula.realize_exBlock, BlockFormula.realize_allBlock,
    BlockFormula.realize_imp, BlockFormula.realize_equal, realize_succT, Term.realize_var,
    Sum.elim_inr, Sum.elim_inl]
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨b PUnit.unit, hb (fun _ ↦ s) rfl⟩
  · rintro ⟨y, hy⟩
    exact ⟨fun _ ↦ y, fun c hc ↦ hy.trans hc.symm⟩

/-- Direct evaluation of the substituted formula, without `realize_substSlots`. -/
theorem substOne_direct :
    (predFormula.substSlots σOne).Realize (Empty.elim : Empty → ℕ) PEmpty.elim := by
  simp only [predFormula, σOne, BlockFormula.exBlock, BlockFormula.not,
    BlockFormula.substSlots, BlockFormula.liftSubst, BlockFormula.realize_imp,
    BlockFormula.realize_allBlock, BlockFormula.realize_equal, BlockFormula.realize_falsum,
    Term.realize_subst, Term.realize_var, Term.realize_relabel, realize_succT, realize_zeroT,
    Sum.elim_inr, Sum.elim_inl]
  intro h
  exact h (fun _ ↦ 0) fun c hc ↦ hc.symm

/-- The same through `realize_substSlots`: the outer slot is evaluated to `1`. -/
theorem substOne_via :
    (predFormula.substSlots σOne).Realize (Empty.elim : Empty → ℕ) PEmpty.elim ↔
      predFormula.Realize (Empty.elim : Empty → ℕ) (Sum.elim (fun _ ↦ 1) PEmpty.elim) := by
  rw [BlockFormula.realize_substSlots]
  have : (fun s ↦ (σOne s).realize (Sum.elim (Empty.elim : Empty → ℕ) PEmpty.elim) :
      BlockSlots unitShape [()] → ℕ) = Sum.elim (fun _ ↦ 1) PEmpty.elim := by
    funext s; rcases s with _ | s
    · rfl
    · exact s.elim
  rw [this]

theorem substOne_true :
    (predFormula.substSlots σOne).Realize (Empty.elim : Empty → ℕ) PEmpty.elim :=
  substOne_via.2 ((realize_predFormula 1).2 ⟨0, rfl⟩)

/-- Substituting `zero` instead gives a false formula: the substitution is not a renaming. -/
theorem substZero_false :
    ¬ (predFormula.substSlots σZero).Realize (Empty.elim : Empty → ℕ) PEmpty.elim := by
  rw [BlockFormula.realize_substSlots]
  have : (fun s ↦ (σZero s).realize (Sum.elim (Empty.elim : Empty → ℕ) PEmpty.elim) :
      BlockSlots unitShape [()] → ℕ) = Sum.elim (fun _ ↦ 0) PEmpty.elim := by
    funext s; rcases s with _ | s
    · rfl
    · exact s.elim
  rw [this, realize_predFormula]
  rintro ⟨y, hy⟩
  omega

theorem predFormula_mapSlots_id : predFormula.mapSlots id = predFormula :=
  BlockFormula.mapSlots_id predFormula

/-- Renaming the outer slot into a two-block context and back composes to the identity. -/
theorem predFormula_mapSlots_mapSlots :
    (predFormula.mapSlots (Δ := [(), ()]) Sum.inr).mapSlots
        (Δ := [()]) (Sum.elim (fun _ ↦ Sum.inl PUnit.unit) id) =
      predFormula.mapSlots ((Sum.elim (fun _ ↦ Sum.inl PUnit.unit) id :
        BlockSlots unitShape [(), ()] → BlockSlots unitShape [()]) ∘ Sum.inr) :=
  BlockFormula.mapSlots_mapSlots predFormula _ _

end Substitution

/-! ### 7. Three-way reassociation -/

section Reassoc

/-- A slot of the first block. -/
theorem reassoc_left :
    BlockSlots.reassocEquiv finShapes [1] [2] [3]
        (BlockSlots.inl finShapes [1] ([2] ++ [3]) (Sum.inl 0)) =
      BlockSlots.inl finShapes ([1] ++ [2]) [3] (BlockSlots.inl finShapes [1] [2] (Sum.inl 0)) :=
  BlockSlots.reassocEquiv_left [1] [2] [3] _

theorem reassoc_middle :
    BlockSlots.reassocEquiv finShapes [1] [2] [3]
        (BlockSlots.inr finShapes [1] ([2] ++ [3]) (BlockSlots.inl finShapes [2] [3] (Sum.inl 1))) =
      BlockSlots.inl finShapes ([1] ++ [2]) [3] (BlockSlots.inr finShapes [1] [2] (Sum.inl 1)) :=
  BlockSlots.reassocEquiv_middle [1] [2] [3] _

theorem reassoc_right :
    BlockSlots.reassocEquiv finShapes [1] [2] [3]
        (BlockSlots.inr finShapes [1] ([2] ++ [3]) (BlockSlots.inr finShapes [2] [3] (Sum.inl 2))) =
      BlockSlots.inr finShapes ([1] ++ [2]) [3] (Sum.inl 2) :=
  BlockSlots.reassocEquiv_right [1] [2] [3] _

/-- Explicit values: each component lands in the intended summand of `[1, 2, 3]`. -/
theorem reassoc_values :
    BlockSlots.reassocEquiv finShapes [1] [2] [3] (Sum.inl 0) = Sum.inl 0 ∧
      BlockSlots.reassocEquiv finShapes [1] [2] [3] (Sum.inr (Sum.inl 1)) =
        Sum.inr (Sum.inl 1) ∧
      BlockSlots.reassocEquiv finShapes [1] [2] [3] (Sum.inr (Sum.inr (Sum.inl 2))) =
        Sum.inr (Sum.inr (Sum.inl 2)) :=
  ⟨rfl, rfl, rfl⟩

theorem reassoc_symm_apply_apply (s : BlockSlots finShapes ([1] ++ ([2] ++ [3]))) :
    (BlockSlots.reassocEquiv finShapes [1] [2] [3]).symm
      (BlockSlots.reassocEquiv finShapes [1] [2] [3] s) = s :=
  BlockSlots.reassocEquiv_symm_apply_apply [1] [2] [3] s

theorem reassoc_apply_symm_apply (s : BlockSlots finShapes (([1] ++ [2]) ++ [3])) :
    BlockSlots.reassocEquiv finShapes [1] [2] [3]
      ((BlockSlots.reassocEquiv finShapes [1] [2] [3]).symm s) = s :=
  BlockSlots.reassocEquiv_apply_symm_apply [1] [2] [3] s

theorem appendEquiv_cons_inl_rfl (x : Fin 1) :
    BlockSlots.appendEquiv finShapes [1] [2] (Sum.inl x) = Sum.inl (Sum.inl x) :=
  rfl

theorem appendEquiv_nil_rfl (s : BlockSlots finShapes ([] ++ [2])) :
    BlockSlots.appendEquiv finShapes [] [2] s = Sum.inr s :=
  rfl

attribute [local instance] Language.emptyStructure

/-- The first slot of the third block equals the first slot of the first block. -/
def reassocFormula : Language.empty.BlockFormula Unit finShapes Empty ([1] ++ ([2] ++ [3])) :=
  BlockFormula.equal (Term.var (Sum.inr (Sum.inr (Sum.inr (Sum.inl 0)))))
    (Term.var (Sum.inr (Sum.inl 0)))

theorem realize_reassocFormula {M : Type} (ys : BlockSlots finShapes (([1] ++ [2]) ++ [3]) → M) :
    (reassocFormula.mapSlots (BlockSlots.reassocEquiv finShapes [1] [2] [3])).Realize
        (Empty.elim : Empty → M) ys ↔
      ys (Sum.inr (Sum.inr (Sum.inl 0))) = ys (Sum.inl 0) := by
  rw [BlockFormula.realize_reassoc]
  rfl

end Reassoc

/-! ### 8. `ofInf` -/

section OfInf

variable {L : Language.{u, v}} {α : Type u'} {M : Type wM} [L.Structure M]

/-- A `BoundedFormulaω` is accepted by `ofInf ()` at `V := unitShape`, with no cast. -/
def ofInfOmega (φ : L.BoundedFormulaω α 1) : L.BlockFormula ℕ unitShape α (List.replicate 1 ()) :=
  BlockFormula.ofInf (V := unitShape) () φ

/-- `∀ x, x = x`. -/
def reflAll : L.BoundedFormulaω α 0 :=
  (BoundedFormulaInf.equal (Term.var (Sum.inr 0)) (Term.var (Sum.inr 0))).all

theorem realize_ofInf_reflAll (v : α → M) :
    (BlockFormula.ofInf (V := unitShape) () (reflAll (L := L) (α := α))).Realize v
      PEmpty.elim := by
  rw [BlockFormula.realize_ofInf]
  simp [reflAll]

/-- The bound variable `x₀` equals the free variable `a`. -/
def boundEqFree (a : α) : L.BoundedFormulaω α 1 :=
  BoundedFormulaInf.equal (Term.var (Sum.inr 0)) (Term.var (Sum.inl a))

theorem realize_ofInf_boundEqFree (a : α) (v : α → M)
    (ys : BlockSlots unitShape (List.replicate 1 ()) → M) :
    (ofInfOmega (boundEqFree (L := L) a)).Realize v ys ↔ ys (Sum.inl PUnit.unit) = v a := by
  rw [ofInfOmega, BlockFormula.realize_ofInf]
  rfl

/-- Orientation: the last unary variable is the head block, the first one is deeper. -/
theorem finToSlots_orientation :
    BlockSlots.finToSlots unitShape () 2 (Fin.last 1) = Sum.inl PUnit.unit ∧
      BlockSlots.finToSlots unitShape () 2 0 = Sum.inr (Sum.inl PUnit.unit) :=
  ⟨rfl, rfl⟩

end OfInf

/-! ### 9. Independent universes -/

section Universes

variable {L : Language.{0, 0}} {ι : Type 1} {Q : Type 3} {V : Q → Type 0} {α : Type 1}
  {M : Type 2} [L.Structure M]

theorem univ_allBlock {Γ : List Q} {q : Q} (φ : L.BlockFormula ι V α (q :: Γ)) (v : α → M)
    (xs : BlockSlots V Γ → M) :
    (BlockFormula.allBlock q φ).Realize v xs ↔ ∀ b : V q → M, φ.Realize v (Sum.elim b xs) :=
  BlockFormula.realize_allBlock.{0, 0, 1, 3, 0, 1, 2}

theorem univ_substSlots {Γ Δ : List Q} (φ : L.BlockFormula ι V α Γ)
    (σ : BlockSlots V Γ → L.Term (α ⊕ BlockSlots V Δ)) (v : α → M) (ys : BlockSlots V Δ → M) :
    (φ.substSlots σ).Realize v ys ↔ φ.Realize v (fun s ↦ (σ s).realize (Sum.elim v ys)) :=
  BlockFormula.realize_substSlots.{0, 0, 1, 3, 0, 1, 2} φ σ v ys

theorem univ_ofInf (one : Q) [Unique (V one)] {n : ℕ} (φ : L.BoundedFormulaInf ι α n)
    (v : α → M) (ys : BlockSlots V (List.replicate n one) → M) :
    (BlockFormula.ofInf one φ).Realize v ys ↔
      φ.Realize v (ys ∘ BlockSlots.finToSlots V one n) :=
  BlockFormula.realize_ofInf.{0, 0, 1, 3, 0, 1, 2} one φ v ys

end Universes

/-! ### Meta checks (2, 3, 4, 10, 11, 12) -/

/-- The frozen universe lists. -/
def levelPins : List (Name × List Name) :=
  let r := [`u, `v, `uι, `uQ, `w, `u', `wM]
  [(``BlockSlots, [`uQ, `w]), (``BlockFormula, [`u, `v, `uι, `uQ, `w, `u']),
   (``BlockFormula.Realize, r), (``BlockFormula.realize_ofInf, r),
   (``BlockFormula.realize_substSlots, r), (``BlockFormula.realize_reassoc, r),
   (``BlockFormula.realize_mapSlots, r), (``BlockFormula.realize_allBlock, r),
   (``BlockFormula.realize_closeAll, r), (``BlockSentence, [`u, `v, `uι, `uQ, `w]),
   (``BlockSlots.appendEquiv, [`uQ, `w]), (``BlockSlots.reassocEquiv, [`uQ, `w]),
   (``BlockSlots.finToSlots, [`uQ, `w]), (``BlockFormula.ofInf, [`u, `v, `uι, `uQ, `w, `u']),
   (``BlockFormula.iInfAlong, [`u, `v, `uι, `uQ, `w, `u', `uκ]),
   (``InitCode, [`w]), (``initSeg, [`w])]

/-- Binder kinds as a string: `i` implicit, `e` explicit, `s` instance, `t` strict implicit. -/
def binderCode (n : Name) : MetaM String := do
  let ci ← getConstInfo n
  forallTelescope ci.type fun xs _ ↦ do
    let mut s := ""
    for x in xs do
      s := s ++ match (← x.fvarId!.getDecl).binderInfo with
        | .implicit => "i" | .default => "e" | .instImplicit => "s" | .strictImplicit => "t"
    return s

/-- The frozen binder kinds. -/
def binderPins : List (Name × String) :=
  [(``BlockFormula.realize_allBlock, "iiiiiisiiiii"),
   (``BlockFormula.realize_closeAll, "iiiiiisiii"),
   (``BlockFormula.realize_mapSlots, "iiiiiisiieeee"),
   (``BlockFormula.realize_substSlots, "iiiiiisiieeee"),
   (``BlockFormula.realize_reassoc, "iiiiiisiiieee"),
   (``BlockFormula.realize_ofInf, "iiiiiisesieee"),
   (``BlockSlots.reassocEquiv_left, "iieeee"),
   (``BlockSlots.reassocEquiv_middle, "iieeee"),
   (``BlockSlots.reassocEquiv_right, "iieeee")]

/-- `some` message when the binder kinds of `n` differ from `frozen`. -/
def binderDrift? (n : Name) (frozen : String) : MetaM (Option String) := do
  let s ← binderCode n
  return if s == frozen then none else some s!"{n} has binder kinds {s}, frozen {frozen}"

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

/-- The exact `InfinitaryLogic` modules (other than the module itself) of each closure. -/
def closurePins : List (Name × List Name) :=
  [(`InfinitaryLogic.LinfKappa.Syntax, []),
   (`InfinitaryLogic.LinfKappa.Semantics, [`InfinitaryLogic.LinfKappa.Syntax]),
   (`InfinitaryLogic.LinfKappa.Substitution,
     [`InfinitaryLogic.LinfKappa.Semantics, `InfinitaryLogic.LinfKappa.Syntax]),
   (`InfinitaryLogic.LinfKappa.Unary,
     [`InfinitaryLogic.LinfKappa.Semantics, `InfinitaryLogic.LinfKappa.Syntax])]

/-- Module-name prefixes no closure may reach. -/
def forbiddenPrefixes : List Name :=
  [`Mathlib.SetTheory.Cardinal.HasCardinalLT, `InfinitaryLogic.Lomega1omega,
   `InfinitaryLogic.Scott, `InfinitaryLogic.Karp]

/-- `value?` misses theorem bodies; match `.thmInfo` explicitly. -/
def declValue? (ci : ConstantInfo) : Option Expr :=
  match ci with
  | .defnInfo v => some v.value
  | .thmInfo v => some v.value
  | .opaqueInfo v => some v.value
  | _ => none

/-- The constants reachable from `start` through types and values (theorem bodies included). -/
partial def transitiveDeps (env : Environment) (start : Name) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut stack : List Name := [start]
  while !stack.isEmpty do
    let n := stack.head!
    stack := stack.tail!
    if seen.contains n then continue
    seen := seen.insert n
    match env.find? n with
    | none => pure ()
    | some ci =>
      let mut cs := ci.type.getUsedConstantsAsSet
      match declValue? ci with
      | some v => cs := cs.union v.getUsedConstantsAsSet
      | none => pure ()
      for c in cs do
        if !seen.contains c then stack := c :: stack
  return seen

/-- The exported declarations of the four modules. -/
def moduleDecls : List Name :=
  [`BlockSlots, `BlockFormula, `BlockFormula.falsum, `BlockFormula.equal, `BlockFormula.rel,
   `BlockFormula.imp, `BlockFormula.allBlock, `BlockFormula.iSup, `BlockFormula.iInf,
   `BlockSentence, `BlockFormula.not, `BlockFormula.verum, `BlockFormula.instBot,
   `BlockFormula.instTop, `BlockFormula.instInhabited, `BlockFormula.exBlock,
   `BlockFormula.closeAll, `BlockSlots.appendEquiv, `BlockSlots.inl, `BlockSlots.inr,
   `BlockSlots.appendEquiv_cons_inl, `BlockSlots.appendEquiv_cons_inr,
   `BlockSlots.appendEquiv_nil, `BlockSlots.reassocEquiv, `BlockSlots.reassocEquiv_left,
   `BlockSlots.reassocEquiv_middle, `BlockSlots.reassocEquiv_right,
   `BlockSlots.reassocEquiv_symm_apply_apply, `BlockSlots.reassocEquiv_apply_symm_apply,
   `InitCode, `initSeg, `finShapes, `unitShape,
   `BlockFormula.Realize, `BlockFormula.realize_falsum, `BlockFormula.realize_equal,
   `BlockFormula.realize_rel, `BlockFormula.realize_imp, `BlockFormula.realize_allBlock,
   `BlockFormula.realize_iSup, `BlockFormula.realize_iInf, `BlockFormula.realize_not,
   `BlockFormula.realize_top, `BlockFormula.realize_bot, `BlockFormula.realize_exBlock,
   `BlockFormula.realize_closeAll, `BlockFormula.iInfAlong, `BlockFormula.iSupAlong,
   `BlockFormula.realize_iInfAlong, `BlockFormula.realize_iSupAlong, `BlockSentence.Realize,
   `BlockFormula.mapSlots, `BlockFormula.realize_mapSlots, `BlockFormula.mapSlots_id,
   `BlockFormula.mapSlots_mapSlots, `BlockFormula.liftSubst, `BlockFormula.substSlots,
   `BlockFormula.realize_substSlots, `BlockFormula.realize_reassoc,
   `BlockSlots.finToSlots, `BlockSlots.comp_finToSlots_succ, `BlockFormula.ofInf,
   `BlockFormula.realize_ofInf].map (`FirstOrder.Language ++ ·)

/-- The guard's own named declarations, each of which must exist. -/
def guardDecls : List Name :=
  [`gateFormula, `gateShortTuples, `gateCanonicalSlots, `realize_allBlock_flipped,
   `rw_realize_mapSlots_binder, `realize_allBlock_rfl, `emptyShape, `empty_allBlock,
   `empty_exBlock_iff_allBlock, `singleton_allBlock, `pairwiseDistinctOmega,
   `inequalityFreeOmega, `realize_pairwiseDistinctOmega, `pairwiseDistinctOmega_nat,
   `not_pairwiseDistinctOmega_fin3, `not_pairwiseDistinctOmega_unit, `inequalityFreeOmega_unit,
   `pairwiseDistinct_separated_from_inequalityFree, `fiveVars, `finBody, `finSentence,
   `realize_fiveVars, `realize_equal_fiveVars, `realize_finSentence, `finSentence_fin4,
   `not_finSentence_fin1,
   `initSeg_aleph0_finite, `aleph0Slots, `zsLang, `predFormula, `σOne, `σZero,
   `realize_predFormula, `substOne_direct, `substOne_via, `substOne_true, `substZero_false,
   `predFormula_mapSlots_id, `predFormula_mapSlots_mapSlots, `reassoc_left, `reassoc_middle,
   `reassoc_right, `reassoc_values, `reassoc_symm_apply_apply, `reassoc_apply_symm_apply,
   `appendEquiv_cons_inl_rfl, `appendEquiv_nil_rfl, `reassocFormula, `realize_reassocFormula,
   `ofInfOmega, `reflAll, `realize_ofInf_reflAll, `boundEqFree, `realize_ofInf_boundEqFree,
   `finToSlots_orientation, `univ_allBlock, `univ_substSlots, `univ_ofInf].map
    (`LinfKappaSyntaxGuard ++ ·)

/-- The standard axioms. -/
def standardAxioms : List Name := [`propext, `Classical.choice, `Quot.sound]

run_cmd do
  let env ← getEnv
  -- 2. universe pins
  for (n, ls) in levelPins do
    let some ci := env.find? n | throwError "declaration {n} not found"
    unless ci.levelParams == ls do
      throwError "[UNIVERSE DRIFT] {n} has levelParams {ci.levelParams}, frozen {ls}"
  -- 3. binder pins, with the mutation control
  for (n, s) in binderPins do
    if let some msg ← liftTermElabM (binderDrift? n s) then
      throwError "[BINDER DRIFT] {msg}"
  match ← liftTermElabM
      (binderDrift? ``LinfKappaSyntaxGuard.realize_allBlock_flipped "iiiiiisiiiii") with
  | some _ => pure ()
  | none => throwError "[MUTATION CONTROL] the binder check did not flag the flipped copy"
  -- 4. reducibility
  unless (← liftCoreM (getReducibilityStatus ``BlockSlots)) == .reducible do
    throwError "[TRANSPARENCY] BlockSlots is not @[reducible]"
  -- 10. closure pins
  for (m, expected) in closurePins do
    unless env.getModuleIdx? m |>.isSome do throwError "module {m} is not in the environment"
    let cl := importClosure env m
    let il := (cl.toList.filter fun x ↦ (`InfinitaryLogic).isPrefixOf x && x != m).toArray
      |>.qsort Name.lt |>.toList
    unless il == expected do
      throwError "[CLOSURE DRIFT] the InfinitaryLogic closure of {m} is {il}, pinned {expected}"
    let hits := cl.toList.filter fun x ↦ forbiddenPrefixes.any (·.isPrefixOf x)
    unless hits.isEmpty do
      throwError "[BROAD CONE] the closure of {m} reaches {hits}"
  -- 11. positive cone
  unless (transitiveDeps env ``BlockFormula.realize_iInfAlong).contains
      ``FirstOrder.IndexCoding.pad do
    throwError "[CONE] realize_iInfAlong does not reach FirstOrder.IndexCoding.pad"
  -- 12. axiom audit (a declaration that failed to elaborate carries the error-recovery axiom)
  let localGuard := env.constants.map₂.toList.filterMap fun (n, _) ↦
    if (`LinfKappaSyntaxGuard).isPrefixOf n && !n.isInternal then some n else none
  for n in moduleDecls ++ guardDecls ++ localGuard do
    unless (env.find? n).isSome do throwError "declaration {n} not found"
    let axs ← liftCoreM (collectAxioms n)
    let bad := axs.toList.filter fun a ↦ !standardAxioms.contains a
    unless bad.isEmpty do throwError "[NONSTANDARD AXIOMS] {n} uses {bad}"
  logInfo m!"L∞κ block-syntax regression guard: OK ({moduleDecls.length} exported and \
    {localGuard.length} guard declarations audited; universe gates and pins; binder pins with \
    the mutation control flagged; BlockSlots reducible and the binder-case rw regression; empty, \
    singleton and pairwise-distinct omega blocks (true in N, false in Fin 3 and in Unit, where \
    the inequality-free variant is true); finShapes sentence true on Fin 4, false on Fin 1; \
    finite InitCode aleph0 blocks; substitution of succ zero and zero under nested binders; \
    reassociation components, values and inverses; ofInf on BoundedFormulaOmega with no cast \
    and the head-block orientation; independent universes; exact closures without \
    HasCardinalLT, Lomega1omega, Scott or Karp; IndexCoding.pad in the iInfAlong cone; standard \
    axioms)"

end LinfKappaSyntaxGuard
