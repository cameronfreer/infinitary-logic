/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Methods.LocalSkolem

/-!
# The countable local Skolem tower `Llocal` / `Γlocal`

`localSkolem L Γ` (in `LocalSkolem.lean`) adjoins a Skolem function symbol only for the formulas of a
**countable** family `Γ`, and so stays countable. But one layer is not closed under its own witness
formulas, so — exactly as `skolemStage`/`skolemColim` do for the *uncountable* full Skolemization —
we iterate. The difference is that here the family `Γ` grows *in lock-step* with the language, so the
language and the family are **mutually recursive**:

* `L₀ = L`, `Γ₀` = the seed family;
* `L_{k+1} = L_k.sum (localSkolem L_k Γ_k)` (adjoin Skolem symbols for the *current* family);
* `Γ_{k+1}` = the subformula/component closure of a seed built from `Γ_k` (lifted along the language
  inclusion), the Skolem-witness bodies of the new symbols, and a reserved deForm-closure slot.

The mutual recursion is packaged as a single `ℕ`-indexed sequence of `LocalStage` bundles (language +
family + countability certificates), sidestepping dependent-recursion sprawl. The **deliverable of
this chunk** is that every stage is countable — both the language's symbol types and the family
`Γ_k` — which is what keeps the eventual local colimit `L_Γ` countable (the fatal size problem that
`localSkolem` was introduced to fix). The local colimit and its cocone inclusions are a later chunk;
here we stop at the tower and its stagewise countability.
-/

universe u v w

namespace FirstOrder.Language

/-! ### Countability of `Language.sum` symbol types

A sum language's arity-graded symbol type is the fibrewise disjoint sum, so its total `Σ`-type is
countable as soon as both summands' `Σ`-types are. These feed the successor-language countability
certificate in `LocalStage.succ`. -/

/-- The full function-symbol type of `L.sum L'` is countable when both summands' are. -/
theorem sum_sigma_functions_countable {L L' : Language.{0, 0}}
    (h : Countable (Σ n, L.Functions n)) (h' : Countable (Σ n, L'.Functions n)) :
    Countable (Σ n, (L.sum L').Functions n) := by
  haveI := h; haveI := h'
  exact (Equiv.sigmaSumDistrib (fun n => L.Functions n) (fun n => L'.Functions n)).injective.countable

/-- The full relation-symbol type of `L.sum L'` is countable when both summands' are. -/
theorem sum_sigma_relations_countable {L L' : Language.{0, 0}}
    (h : Countable (Σ n, L.Relations n)) (h' : Countable (Σ n, L'.Relations n)) :
    Countable (Σ n, (L.sum L').Relations n) := by
  haveI := h; haveI := h'
  exact (Equiv.sigmaSumDistrib (fun n => L.Relations n) (fun n => L'.Relations n)).injective.countable

variable {L : Language.{0, 0}}

/-! ### The local Skolem witness term and formula

For a symbol of `localSkolem L Γ` — that is, a formula `φ ∈ Γ` of arity `n+1` — the witness body of
`∃ xₙ, φ` is `φ[skolemTerm]`, built with the template pattern `openBounds → subst → relabel` exactly
as `skolemWitnessFormula` does in `SkolemClosure.lean`, but using the *local* Skolem symbol (which
exists precisely because `φ ∈ Γ`). This is the arity-`n` formula, over `L.sum (localSkolem L Γ)`,
added to the successor family. -/

/-- The **local Skolem witness term** for the symbol `sym` (a formula `φ ∈ Γ` of arity `n+1`): the
function symbol `sym` — in the `localSkolem` summand — applied to the argument terms `ts`, as a term
of `L.sum (localSkolem L Γ)`. Local analogue of `skolemTerm`. -/
def localSkolemTerm {Γ : Set (Σ n, L.BoundedFormulaω Empty n)} {γ : Type*} {n : ℕ}
    (sym : (localSkolem L Γ).Functions n)
    (ts : Fin n → (L.sum (localSkolem L Γ)).Term γ) : (L.sum (localSkolem L Γ)).Term γ :=
  Term.func (Sum.inr sym : (L.sum (localSkolem L Γ)).Functions n) ts

/-- The **local Skolem witness formula** for the symbol `sym` (a formula `φ ∈ Γ` of arity `n+1`):
substitute the local Skolem term for the witnessed last variable of `φ`, yielding the arity-`n`
formula `φ[skolemTerm]` over `L.sum (localSkolem L Γ)`. Local analogue of `skolemWitnessFormula`. -/
def localSkolemWitnessFormula {Γ : Set (Σ n, L.BoundedFormulaω Empty n)} {n : ℕ}
    (sym : (localSkolem L Γ).Functions n) : (L.sum (localSkolem L Γ)).BoundedFormulaω Empty n :=
  ((sym.1.openBounds.mapLanguage (LHom.sumInl : L →ᴸ L.sum (localSkolem L Γ))).subst
    (Fin.snoc (fun i => Term.var i) (localSkolemTerm sym (fun i => Term.var i)))).relabel Sum.inr

/-! ### Seed of the successor family

The seed of `Γ_{k+1}` (before the subformula/component closure) has three parts. Each is countable
when `Γ` is, so the whole seed is. -/

/-- The **lift** of `Γ` into the successor language `L.sum (localSkolem L Γ)` along the left
injection `LHom.sumInl`. Arity is preserved. -/
def liftGamma (Γ : Set (Σ n, L.BoundedFormulaω Empty n)) :
    Set (Σ n, (L.sum (localSkolem L Γ)).BoundedFormulaω Empty n) :=
  (fun p : Σ n, L.BoundedFormulaω Empty n =>
    (⟨p.1, p.2.mapLanguage (LHom.sumInl : L →ᴸ L.sum (localSkolem L Γ))⟩ :
      Σ n, (L.sum (localSkolem L Γ)).BoundedFormulaω Empty n)) '' Γ

/-- The lift of a countable family is countable (image of a countable set). -/
theorem liftGamma_countable {Γ : Set (Σ n, L.BoundedFormulaω Empty n)} (hΓ : Γ.Countable) :
    (liftGamma Γ).Countable := hΓ.image _

/-- The **Skolem-witness seed**: the witness formula of every local Skolem symbol. Indexed by the
symbol type `Σ n, (localSkolem L Γ).Functions n`, which is countable when `Γ` is. -/
def localSkWitnessSeed (Γ : Set (Σ n, L.BoundedFormulaω Empty n)) :
    Set (Σ n, (L.sum (localSkolem L Γ)).BoundedFormulaω Empty n) :=
  Set.range fun sym : Σ n, (localSkolem L Γ).Functions n =>
    (⟨sym.1, localSkolemWitnessFormula sym.2⟩ :
      Σ n, (L.sum (localSkolem L Γ)).BoundedFormulaω Empty n)

/-- The Skolem-witness seed is countable: it is the range of a map out of the (countable) local
Skolem symbol type. -/
theorem localSkWitnessSeed_countable {Γ : Set (Σ n, L.BoundedFormulaω Empty n)} (hΓ : Γ.Countable) :
    (localSkWitnessSeed Γ).Countable := by
  haveI := localSkolem_sigma_functions_countable Γ hΓ
  exact Set.countable_range _

/-- **Reserved deForm-closure seed** (placeholder). The truth lemma's family must be closed under the
*de-substituted* formulas `deForm S φ ts` of its members; but `deForm` is defined over a term-model
carrier `J` (see `EMTermModel.deForm`), which does not exist at the pure language-tower level. So this
slot is currently empty and will be filled once the local colimit and its term model are in place.
It is named (not left implicit) so the closure and its countability certificate already route through
it. -/
def deFormSeed (Γ : Set (Σ n, L.BoundedFormulaω Empty n)) :
    Set (Σ n, (L.sum (localSkolem L Γ)).BoundedFormulaω Empty n) := ∅

/-- The reserved deForm seed is (trivially) countable. -/
theorem deFormSeed_countable (Γ : Set (Σ n, L.BoundedFormulaω Empty n)) :
    (deFormSeed Γ).Countable := Set.countable_empty

/-- The full **seed** of the successor family: the lift of `Γ`, the Skolem-witness bodies, and the
reserved deForm slot. -/
def localSeed (Γ : Set (Σ n, L.BoundedFormulaω Empty n)) :
    Set (Σ n, (L.sum (localSkolem L Γ)).BoundedFormulaω Empty n) :=
  liftGamma Γ ∪ localSkWitnessSeed Γ ∪ deFormSeed Γ

/-- The successor seed is countable when `Γ` is. -/
theorem localSeed_countable {Γ : Set (Σ n, L.BoundedFormulaω Empty n)} (hΓ : Γ.Countable) :
    (localSeed Γ).Countable :=
  ((liftGamma_countable hΓ).union (localSkWitnessSeed_countable hΓ)).union (deFormSeed_countable Γ)

/-! ### The successor family `Γ_{k+1}` -/

/-- The **successor family**: the subformula/component closure (`setClosure bfSubformulas`) of the
successor seed. Closing under `bfSubformulas` makes `Γ_{k+1}` closed under immediate subformulas and
countable-connective components — the structural-induction requirement of the truth lemma — while the
Skolem-witness and (reserved) deForm generators sit in the seed. -/
def localGammaNext (Γ : Set (Σ n, L.BoundedFormulaω Empty n)) :
    Set (Σ n, (L.sum (localSkolem L Γ)).BoundedFormulaω Empty n) :=
  setClosure bfSubformulas (localSeed Γ)

/-- The successor family is countable when `Γ` is: `setClosure` of a countable seed under the
pointwise-countable subformula step. -/
theorem localGammaNext_countable {Γ : Set (Σ n, L.BoundedFormulaω Empty n)} (hΓ : Γ.Countable) :
    (localGammaNext Γ).Countable :=
  setClosure_countable bfSubformulas (localSeed_countable hΓ) bfSubformulas_countable

/-- The seed is contained in the successor family. -/
theorem localSeed_subset_localGammaNext (Γ : Set (Σ n, L.BoundedFormulaω Empty n)) :
    localSeed Γ ⊆ localGammaNext Γ := subset_setClosure _ _

/-! ### The stage bundle and the tower -/

/-- A single **stage** of the local Skolem tower: a language, a family of its formulas, and
countability certificates for the family and the language's symbol types. Bundling these keeps the
mutual language/family recursion a plain `ℕ`-indexed sequence rather than a dependent recursion. -/
structure LocalStage where
  /-- The stage language. -/
  Lang : Language.{0, 0}
  /-- The stage family of formulas of `Lang`. -/
  Gamma : Set (Σ n, Lang.BoundedFormulaω Empty n)
  /-- The stage family is countable. -/
  gamma_countable : Gamma.Countable
  /-- The stage language has countably many function symbols. -/
  fun_countable : Countable (Σ n, Lang.Functions n)
  /-- The stage language has countably many relation symbols. -/
  rel_countable : Countable (Σ n, Lang.Relations n)

/-- The **successor stage**: Skolemize the current family (`Lang.sum (localSkolem Lang Gamma)`) and
replace the family by its successor closure. Every countability certificate is carried forward:
the family via `localGammaNext_countable`, the language via `sum_sigma_functions_countable` /
`sum_sigma_relations_countable` together with `localSkolem`'s own countability. -/
def LocalStage.succ (s : LocalStage) : LocalStage where
  Lang := s.Lang.sum (localSkolem s.Lang s.Gamma)
  Gamma := localGammaNext s.Gamma
  gamma_countable := localGammaNext_countable s.gamma_countable
  fun_countable :=
    sum_sigma_functions_countable s.fun_countable
      (localSkolem_sigma_functions_countable s.Gamma s.gamma_countable)
  rel_countable :=
    sum_sigma_relations_countable s.rel_countable (localSkolem_sigma_relations_countable s.Gamma)

/-- The **local Skolem tower** seeded at `s₀`: stage `0` is the seed and each successor Skolemizes
the current stage. -/
def localStage (s₀ : LocalStage) : ℕ → LocalStage
  | 0 => s₀
  | k + 1 => (localStage s₀ k).succ

@[simp] theorem localStage_zero (s₀ : LocalStage) : localStage s₀ 0 = s₀ := rfl

@[simp] theorem localStage_succ (s₀ : LocalStage) (k : ℕ) :
    localStage s₀ (k + 1) = (localStage s₀ k).succ := rfl

/-! ### Projections consumed by the later local-colimit chunk -/

/-- The **stage-`k` local language** `L_k`. -/
def Llocal (s₀ : LocalStage) (k : ℕ) : Language.{0, 0} := (localStage s₀ k).Lang

/-- The **stage-`k` local family** `Γ_k`. -/
def Γlocal (s₀ : LocalStage) (k : ℕ) : Set (Σ n, (Llocal s₀ k).BoundedFormulaω Empty n) :=
  (localStage s₀ k).Gamma

@[simp] theorem Llocal_zero (s₀ : LocalStage) : Llocal s₀ 0 = s₀.Lang := rfl

@[simp] theorem Llocal_succ (s₀ : LocalStage) (k : ℕ) :
    Llocal s₀ (k + 1) = (Llocal s₀ k).sum (localSkolem (Llocal s₀ k) (Γlocal s₀ k)) := rfl

/-- The **stage-`k` → stage-`(k+1)` language inclusion**: the left injection of the Skolemizing sum.
The later colimit's cocone is assembled from these. -/
def LlocalHom (s₀ : LocalStage) (k : ℕ) : Llocal s₀ k →ᴸ Llocal s₀ (k + 1) := LHom.sumInl

/-- Each stage-`k` family is countable. -/
theorem Γlocal_countable (s₀ : LocalStage) (k : ℕ) : (Γlocal s₀ k).Countable :=
  (localStage s₀ k).gamma_countable

/-- Each stage-`k` language has countably many function symbols. -/
theorem Llocal_fun_countable (s₀ : LocalStage) (k : ℕ) :
    Countable (Σ n, (Llocal s₀ k).Functions n) := (localStage s₀ k).fun_countable

/-- Each stage-`k` language has countably many relation symbols. -/
theorem Llocal_rel_countable (s₀ : LocalStage) (k : ℕ) :
    Countable (Σ n, (Llocal s₀ k).Relations n) := (localStage s₀ k).rel_countable

end FirstOrder.Language
