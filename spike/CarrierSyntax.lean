/-
SPIKE — Aaron Liu's carrier-parameterized infinitary syntax.

Deliberately outside the module tree (`spike/`, not `InfinitaryLogic/`) so it enters no bundle and
no CI target. Build with:  lake env lean spike/CarrierSyntax.lean

Question under test: can ONE inductive, parameterized by a fixed infinitary branching carrier `ι`,
replace the current parallel `BoundedFormulaω` / `BoundedFormulaInf` pair — with `Lω₁ω` recovered
definitionally as `ι := ℕ`?

Temporary name `BoundedFormulaIdx` so nothing existing is shadowed.
-/
import Mathlib.ModelTheory.Semantics
import Mathlib.SetTheory.Ordinal.Arithmetic

universe u v uι uα w

namespace FirstOrder.Language

/-! ## Gate 1 — the carrier-parameterized syntax -/

/-- Infinitary formulas whose infinitary nodes all branch over a FIXED carrier `ι`. -/
inductive BoundedFormulaIdx (L : Language.{u, v}) (ι : Type uι) (α : Type uα) :
    ℕ → Type (max u v uα uι) where
  | falsum {n} : BoundedFormulaIdx L ι α n
  | equal {n} (t₁ t₂ : L.Term (α ⊕ Fin n)) : BoundedFormulaIdx L ι α n
  | rel {n l : ℕ} (R : L.Relations l) (ts : Fin l → L.Term (α ⊕ Fin n)) :
      BoundedFormulaIdx L ι α n
  | imp {n} (φ ψ : BoundedFormulaIdx L ι α n) : BoundedFormulaIdx L ι α n
  | all {n} (φ : BoundedFormulaIdx L ι α (n + 1)) : BoundedFormulaIdx L ι α n
  | iSup {n} (φs : ι → BoundedFormulaIdx L ι α n) : BoundedFormulaIdx L ι α n
  | iInf {n} (φs : ι → BoundedFormulaIdx L ι α n) : BoundedFormulaIdx L ι α n

variable {L : Language.{u, v}} {ι : Type uι} {α : Type uα} {n : ℕ}

namespace BoundedFormulaIdx

/-- Negation. -/
def not (φ : L.BoundedFormulaIdx ι α n) : L.BoundedFormulaIdx ι α n := φ.imp .falsum

/-- Verum. -/
def verum : L.BoundedFormulaIdx ι α n := not .falsum

instance : Bot (L.BoundedFormulaIdx ι α n) := ⟨.falsum⟩
instance : Top (L.BoundedFormulaIdx ι α n) := ⟨verum⟩

/-! ## Gate 1 — semantics -/

/-- Realization. One recursion, serving every carrier. -/
def Realize {M : Type w} [L.Structure M] :
    ∀ {n}, L.BoundedFormulaIdx ι α n → (α → M) → (Fin n → M) → Prop
  | _, .falsum, _, _ => False
  | _, .equal t₁ t₂, v, xs => t₁.realize (Sum.elim v xs) = t₂.realize (Sum.elim v xs)
  | _, .rel R ts, v, xs => Structure.RelMap R fun i => (ts i).realize (Sum.elim v xs)
  | _, .imp φ ψ, v, xs => Realize φ v xs → Realize ψ v xs
  | _, .all φ, v, xs => ∀ y : M, Realize φ v (Fin.snoc xs y)
  | _, .iSup φs, v, xs => ∃ i, Realize (φs i) v xs
  | _, .iInf φs, v, xs => ∀ i, Realize (φs i) v xs

variable {M : Type w} [L.Structure M] {v : α → M} {xs : Fin n → M}

@[simp] theorem realize_falsum : (falsum : L.BoundedFormulaIdx ι α n).Realize v xs ↔ False :=
  Iff.rfl

@[simp] theorem realize_equal {t₁ t₂ : L.Term (α ⊕ Fin n)} :
    (equal t₁ t₂ : L.BoundedFormulaIdx ι α n).Realize v xs ↔
      t₁.realize (Sum.elim v xs) = t₂.realize (Sum.elim v xs) := Iff.rfl

@[simp] theorem realize_rel {l : ℕ} {R : L.Relations l} {ts : Fin l → L.Term (α ⊕ Fin n)} :
    (rel R ts : L.BoundedFormulaIdx ι α n).Realize v xs ↔
      Structure.RelMap R fun i => (ts i).realize (Sum.elim v xs) := Iff.rfl

@[simp] theorem realize_imp {φ ψ : L.BoundedFormulaIdx ι α n} :
    (φ.imp ψ).Realize v xs ↔ (φ.Realize v xs → ψ.Realize v xs) := Iff.rfl

@[simp] theorem realize_all {φ : L.BoundedFormulaIdx ι α (n + 1)} :
    φ.all.Realize v xs ↔ ∀ y : M, φ.Realize v (Fin.snoc xs y) := Iff.rfl

/-- **The point of the design**: one `iSup` equation, generic in the carrier and its universe. -/
@[simp] theorem realize_iSup {φs : ι → L.BoundedFormulaIdx ι α n} :
    (iSup φs).Realize v xs ↔ ∃ i, (φs i).Realize v xs := Iff.rfl

@[simp] theorem realize_iInf {φs : ι → L.BoundedFormulaIdx ι α n} :
    (iInf φs).Realize v xs ↔ ∀ i, (φs i).Realize v xs := Iff.rfl

@[simp] theorem realize_not {φ : L.BoundedFormulaIdx ι α n} :
    φ.not.Realize v xs ↔ ¬ φ.Realize v xs := Iff.rfl

@[simp] theorem realize_verum : (verum : L.BoundedFormulaIdx ι α n).Realize v xs ↔ True := by
  simp [verum, not, Realize]

@[simp] theorem realize_top : ((⊤ : L.BoundedFormulaIdx ι α n)).Realize v xs ↔ True :=
  realize_verum

@[simp] theorem realize_bot : ((⊥ : L.BoundedFormulaIdx ι α n)).Realize v xs ↔ False :=
  Iff.rfl

end BoundedFormulaIdx

/-! ## Gate 2 — the countable specialization is DEFINITIONAL -/

/-- `Lω₁ω` is not a second inductive: it is `ι := ℕ`. -/
abbrev BoundedFormulaOmega (L : Language.{u, v}) (α : Type uα) (n : ℕ) :=
  L.BoundedFormulaIdx ℕ α n

abbrev FormulaIdx (L : Language.{u, v}) (ι : Type uι) (α : Type uα) := L.BoundedFormulaIdx ι α 0
abbrev SentenceIdx (L : Language.{u, v}) (ι : Type uι) := L.FormulaIdx ι Empty
abbrev FormulaOmega (L : Language.{u, v}) (α : Type uα) := L.FormulaIdx ℕ α
abbrev SentenceOmega (L : Language.{u, v}) := L.SentenceIdx ℕ

/-! ## Gate 3 — the one structural operation Karp needs -/

namespace BoundedFormulaIdx

/-- Existential closure of the last bound variable. -/
def existsLast (φ : L.BoundedFormulaIdx ι α (n + 1)) : L.BoundedFormulaIdx ι α n :=
  φ.not.all.not

@[simp] theorem realize_existsLast {M : Type w} [L.Structure M] {v : α → M} {xs : Fin n → M}
    {φ : L.BoundedFormulaIdx ι α (n + 1)} :
    (existsLast φ).Realize v xs ↔ ∃ y : M, φ.Realize v (Fin.snoc xs y) := by
  simp only [existsLast, realize_not, realize_all, not_forall, not_not]

/-! ## Gate 4 — Karp at the sum carrier `M ⊕ N`

The current proof needs an `N`-indexed conjunction in the forth direction and an `M`-indexed one in
the back direction, over formulas of the *same* ambient type. With a fixed carrier that is only
possible at `ι := M ⊕ N`, padding the unused side with `⊤`. -/

section SumCarrier

variable {M N : Type w}

/-- A conjunction really indexed by the right summand: pad the left with `⊤`. -/
def iInfRight (ψ : N → L.BoundedFormulaIdx (M ⊕ N) α n) : L.BoundedFormulaIdx (M ⊕ N) α n :=
  .iInf (Sum.elim (fun _ : M => ⊤) ψ)

/-- A conjunction really indexed by the left summand: pad the right with `⊤`. -/
def iInfLeft (ψ : M → L.BoundedFormulaIdx (M ⊕ N) α n) : L.BoundedFormulaIdx (M ⊕ N) α n :=
  .iInf (Sum.elim ψ (fun _ : N => ⊤))

variable {P : Type w} [L.Structure P] {v : α → P} {xs : Fin n → P}

/-- **Padding is semantically neutral.** -/
@[simp] theorem realize_iInfRight {ψ : N → L.BoundedFormulaIdx (M ⊕ N) α n} :
    (iInfRight ψ).Realize v xs ↔ ∀ j : N, (ψ j).Realize v xs := by
  simp only [iInfRight, realize_iInf]
  constructor
  · intro h j; exact h (Sum.inr j)
  · rintro h (i | j)
    · simp
    · exact h j

@[simp] theorem realize_iInfLeft {ψ : M → L.BoundedFormulaIdx (M ⊕ N) α n} :
    (iInfLeft ψ).Realize v xs ↔ ∀ i : M, (ψ i).Realize v xs := by
  simp only [iInfLeft, realize_iInf]
  constructor
  · intro h i; exact h (Sum.inl i)
  · rintro h (i | j)
    · exact h i
    · simp

end SumCarrier

end BoundedFormulaIdx

/-! ### The decisive probe: the Karp backward step, both directions, one formula type

This reproduces the shape of `Karp/Theorem.lean`'s backward argument — the place that currently
forces a constructor-level arbitrary index type — at the single carrier `M ⊕ N`. -/

section KarpShape

open BoundedFormulaIdx

variable {L : Language.{u, v}} {M N : Type w} [L.Structure M] [L.Structure N] {k : ℕ}

/-- **Forth.** A separating family indexed by `N` yields a formula true at `a`, false at `b` —
built inside `BoundedFormulaIdx (M ⊕ N)`. -/
example (a : Fin k → M) (m : M)
    (ψ : N → L.BoundedFormulaIdx (M ⊕ N) (Fin k) 1)
    (hψ : ∀ j : N, (ψ j).Realize a (Fin.snoc Fin.elim0 m)) :
    (existsLast (iInfRight ψ)).Realize a Fin.elim0 := by
  rw [realize_existsLast]
  exact ⟨m, by rw [realize_iInfRight]; exact hψ⟩

/-- **Back.** The mirror, indexed by `M`, over the *same* formula type. -/
example (b : Fin k → N) (n' : N)
    (ψ : M → L.BoundedFormulaIdx (M ⊕ N) (Fin k) 1)
    (hψ : ∀ i : M, (ψ i).Realize b (Fin.snoc Fin.elim0 n')) :
    (existsLast (iInfLeft ψ)).Realize b Fin.elim0 := by
  rw [realize_existsLast]
  exact ⟨n', by rw [realize_iInfLeft]; exact hψ⟩

/-- And the refutation side: if some conjunct fails at every witness, the closure fails. -/
example (b : Fin k → N)
    (ψ : N → L.BoundedFormulaIdx (M ⊕ N) (Fin k) 1)
    (hbad : ∀ y : N, ¬ (ψ y).Realize b (Fin.snoc Fin.elim0 y)) :
    ¬ (existsLast (iInfRight ψ)).Realize b Fin.elim0 := by
  rw [realize_existsLast]
  rintro ⟨y, hy⟩
  rw [realize_iInfRight] at hy
  exact hbad y (hy y)

end KarpShape

/-! ## Gate 7 — quantifier rank, the flagged technical risk

Does rank stay universe-correct? For `ι : Type uι` the `iSup`/`iInf` cases take a supremum over `ι`,
so the natural target is `Ordinal.{uι}` — and at `ι := ℕ` that must be `Ordinal.{0}`, exactly where
the Scott analysis wants it. -/

namespace BoundedFormulaIdx

/-- Quantifier rank, valued in the carrier's own ordinal universe. -/
noncomputable def qrank : ∀ {n}, L.BoundedFormulaIdx ι α n → Ordinal.{uι}
  | _, .falsum => 0
  | _, .equal _ _ => 0
  | _, .rel _ _ => 0
  | _, .imp φ ψ => max (qrank φ) (qrank ψ)
  | _, .all φ => Order.succ (qrank φ)
  | _, .iSup φs => ⨆ i, qrank (φs i)
  | _, .iInf φs => ⨆ i, qrank (φs i)

@[simp] theorem qrank_iInf {φs : ι → L.BoundedFormulaIdx ι α n} :
    (iInf φs).qrank = ⨆ i, (φs i).qrank := rfl

@[simp] theorem qrank_all {φ : L.BoundedFormulaIdx ι α (n + 1)} :
    φ.all.qrank = Order.succ φ.qrank := rfl

end BoundedFormulaIdx

section RankProbes

/-- At the countable carrier the rank lands in `Ordinal.{0}` — where Scott analysis needs it. -/
noncomputable example {L : Language.{u, v}} {α : Type uα}
    (φ : L.BoundedFormulaOmega α 0) : Ordinal.{0} := φ.qrank

/-- At a structure-carrier the rank lives in that carrier's universe, as expected. -/
noncomputable example {L : Language.{u, v}} {α : Type uα} {M N : Type w}
    (φ : L.BoundedFormulaIdx (M ⊕ N) α 0) : Ordinal.{w} := φ.qrank

end RankProbes

/-! ## Gate 7 (partial) — falsification probes -/

section Probes

/-- **Universe probe.** Is the `uι + 1` bump gone? -/
example : True := trivial
#check @BoundedFormulaIdx
#check @BoundedFormulaOmega

/-- Carrier at `Type 0`. -/
example (L : Language.{u, v}) (α : Type uα) : Type _ := L.BoundedFormulaIdx (ULift.{0} Bool) α 0

/-- Carrier at `Type 1` — the case that motivated the whole universe discussion. -/
example (L : Language.{u, v}) (α : Type uα) : Type _ := L.BoundedFormulaIdx (Type 0) α 0

/-- Carrier at an arbitrary structure's universe: the Karp shape. -/
example (L : Language.{u, v}) (M N : Type w) (α : Type uα) : Type _ :=
  L.BoundedFormulaIdx (M ⊕ N) α 0

/-- The universal carrier, which should reproduce the OLD syntax's universe cost — and only then. -/
example (L : Language.{u, v}) (α : Type uα) : Type _ :=
  L.BoundedFormulaIdx (Σ J : Type uι, J) α 0

/-- **Induction through the abbreviation.** Does `BoundedFormulaOmega` still get all seven cases,
with ℕ-indexed induction hypotheses? -/
example {L : Language.{u, v}} {α : Type uα} {M : Type w} [L.Structure M] {k : ℕ}
    (φ : L.BoundedFormulaOmega α k) (v : α → M) (xs : Fin k → M) :
    φ.Realize v xs ∨ ¬ φ.Realize v xs := by
  induction φ with
  | falsum => exact Or.inr (by simp)
  | equal => exact Classical.em _
  | rel => exact Classical.em _
  | imp => exact Classical.em _
  | all => exact Classical.em _
  | iSup φs ih => exact Classical.em _
  | iInf φs ih => exact Classical.em _

/-- Constructor dot-notation still elaborates at the `ℕ` specialization. -/
example {L : Language.{u, v}} {α : Type uα} (φs : ℕ → L.BoundedFormulaOmega α 0) :
    L.BoundedFormulaOmega α 0 := .iInf φs

end Probes

end FirstOrder.Language
