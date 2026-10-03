/-
Regression guard for eliminating orbit parameters
(`InfinitaryLogic/Scott/OrbitParameters.lean`).

Every public theorem is *applied*, not only listed for its axioms.

* **The right-addition rank test at a limit.**  `deepω := ⋀_m existsTupleFrom 1 m ⊤` has rank
  exactly `ω`; with one parameter, `existsOrbitParams deepω ⊤` has rank `ω + 1`, which is
  **not** `1 + ω` (`= ω`): the parameter quantifiers are added on the right.  The bound
  `qrank_existsOrbitParams_le` at `α = ω`, and the tuple-block rank family on concrete blocks.
* **`k = 0`.**  `existsOrbitParams θ ψ` unfolds by `rfl` to the conjunction of the two renamed
  formulas (no quantifier); the orbit theorem at `c₀ := Fin.elim0`, where the hypothesis on `θ`
  is just "`θ` holds" and the relative orbit is the orbit.
* **`n = 0`.**  The conclusion makes the sentence true at `Fin.elim0`.
* **The empty carrier.**  `PEmpty` with `k = n = 0`, no `Nonempty`, in an arbitrary carrier
  universe.
* **Independent universes.**  The theorem at `Language.{3, 4}` and a `Type 2` carrier.
* **Test A, a function symbol.**  `(Bool, f = not)`, automorphisms `id` and `not`; over
  `c₀ = (true)`, `ψ(z, x) := x = f(z)` defines the relative orbit of `a = (false)`, and the
  formula holds at `(true)`, witnessed by `not`: the hypotheses and the conclusion go through a
  function term.  The composite-form variant on the same data.
* **Test B, repeated coordinates.**  Same structure, `c₀ = (true, true)`, `a = (false, false)`,
  `θ := z₀ = z₁`, `ψ := x₀ = f z₀ ∧ x₁ = f z₁`: the formula holds at `(true, true)` and
  **fails** at `(true, false)`.
* **Test C, the relative hypothesis at `c₀` only.**  `(Fin 2, f ≡ 1)` is rigid; over
  `c₀ = (1)`, `ψ(z, x) := ¬ x = z` defines the relative orbit of `a = (0)`.  The *uniform*
  hypothesis (at every parameter tuple `c`) is **refuted** at `c = b = (0)`, yet the theorem
  applies.
* **The pointed-family corollary** on the pure set `ℕ` over the repeated parameters `(1, 1)`,
  with the atomic diagrams as orbit formulas: the eliminated formula of `a = (1, 2)` holds at
  `(4, 7)` and **fails** at `(4, 4)`.
* **Import closure** of the module: exactly the expected `InfinitaryLogic` modules
  (`[CLOSURE DRIFT]` otherwise).
* **Standard axioms** for every public declaration added by the tranche (the base-layer and
  Montalbán-module additions included) and for the guard's own theorems.

The proof-term boundary (satisfaction invariance, no Karp, no rank lemma) is checked separately
by `check_orbit_parameters_deps.lean`.

Run with: lake env lean scripts/check_orbit_parameters_regressions.lean
-/
import InfinitaryLogic.Scott.OrbitParameters
import InfinitaryLogic.Scott.FiniteMatching

set_option warningAsError true

open Lean FirstOrder FirstOrder.Language Structure BoundedFormulaω

universe u v w

noncomputable section

namespace OrbitParamsGuard

/-! ### Right addition at a limit ordinal -/

section RankTest

variable {L : Language.{u, v}}

/-- `m` existential quantifiers over `⊤`, one free variable. -/
def deep (m : ℕ) : L.Formulaω (Fin 1) := existsTupleFrom 1 m ⊤

theorem qrank_deep (m : ℕ) : (deep (L := L) m).qrank = m := by
  simp [deep, qrank_existsTupleFrom]

/-- A formula of rank exactly `ω`. -/
def deepω : L.Formulaω (Fin 1) := BoundedFormulaω.iInf fun m ↦ deep m

theorem qrank_deepω : (deepω (L := L)).qrank = Ordinal.omega0 := by
  show (BoundedFormulaω.iInf _).qrank = _
  rw [qrank_iInf]
  exact (congrArg _root_.iSup (funext fun m ↦ qrank_deep (L := L) m)).trans Ordinal.iSup_natCast

/-- One parameter over a rank-`ω` orbit formula: rank `ω + 1`. -/
theorem rank_omega_add_one (n : ℕ) :
    (existsOrbitParams (deepω (L := L)) (⊤ : L.Formulaω (Fin (1 + n)))).qrank =
      Ordinal.omega0 + 1 := by
  rw [qrank_existsOrbitParams, qrank_deepω]
  simp

/-- ... which is not `1 + ω = ω`: the addition is on the right. -/
theorem rank_ne_one_add_omega (n : ℕ) :
    (existsOrbitParams (deepω (L := L)) (⊤ : L.Formulaω (Fin (1 + n)))).qrank ≠
      1 + Ordinal.omega0 := by
  rw [qrank_existsOrbitParams, qrank_deepω, Ordinal.one_add_omega0]
  simp

/-- The bound at `α = ω`. -/
theorem rank_le (n : ℕ) :
    (existsOrbitParams (deepω (L := L)) (⊤ : L.Formulaω (Fin (1 + n)))).qrank ≤
      Ordinal.omega0 + 1 := by
  exact_mod_cast qrank_existsOrbitParams_le (qrank_deepω (L := L)).le
    (by rw [Formulaω.qrank, qrank_top]; exact zero_le)

/-- The tuple-block rank family on concrete blocks. -/
theorem block_ranks :
    (forallTuple 3 (⊤ : L.Formulaω (Fin 3))).qrank = 3 ∧
      (existsTuple 2 (⊤ : L.Formulaω (Fin 2))).qrank = 2 ∧
      (forallTupleFrom 1 2 (⊤ : L.Formulaω (Fin (1 + 2)))).qrank = 2 ∧
      (existsTupleFrom 1 2 ((deepω (L := L)).mapFreeVars (Fin.castLE (by omega)))).qrank =
        Ordinal.omega0 + 2 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [qrank_forallTuple]; simp
  · rw [qrank_existsTuple]; simp
  · rw [qrank_forallTupleFrom]; simp
  · rw [qrank_existsTupleFrom, Formulaω.qrank, qrank_mapFreeVars]
    simp [qrank_deepω]

end RankTest

/-! ### Zero-length tuples, empty carrier, independent universes -/

section Generic

variable {L : Language.{u, v}} {M : Type w} [L.Structure M]

/-- `k = 0`: no quantifier, just the conjunction of the renamed formulas. -/
theorem k_zero_rfl {n : ℕ} (θ : L.Formulaω (Fin 0)) (ψ : L.Formulaω (Fin (0 + n))) :
    existsOrbitParams θ ψ =
      θ.mapFreeVars (Fin.natAdd n) ⊓ ψ.mapFreeVars (finAddFlip : Fin (0 + n) ≃ Fin (n + 0)) :=
  rfl

/-- `k = 0`: the orbit hypothesis on `θ` is just `θ` true, the relative orbit is the orbit. -/
theorem k_zero {n : ℕ} {θ : L.Formulaω (Fin 0)} {ψ : L.Formulaω (Fin (0 + n))} {a : Fin n → M}
    (hθ : θ.Realize (Fin.elim0 : Fin 0 → M))
    (hψ : ∀ b, ψ.Realize (Fin.append Fin.elim0 b) ↔ ∃ f : M ≃[L] M, ⇑f ∘ a = b) :
    ∀ b, (existsOrbitParams θ ψ).Realize b ↔ ∃ g : M ≃[L] M, ⇑g ∘ a = b :=
  realize_existsOrbitParams_iff_orbit (c₀ := Fin.elim0)
    (fun c ↦ ⟨fun _ ↦ ⟨Language.Equiv.refl L M, Subsingleton.elim _ _⟩,
      fun _ ↦ by rwa [Subsingleton.elim c Fin.elim0]⟩)
    (fun b ↦ (hψ b).trans ⟨fun ⟨f, hf⟩ ↦ ⟨f, fun i ↦ i.elim0, hf⟩, fun ⟨f, _, hf⟩ ↦ ⟨f, hf⟩⟩)

/-- `n = 0`: the conclusion makes the sentence true. -/
theorem n_zero {k : ℕ} {θ : L.Formulaω (Fin k)} {ψ : L.Formulaω (Fin (k + 0))} {c₀ : Fin k → M}
    {a : Fin 0 → M}
    (hθ : ∀ c, θ.Realize c ↔ ∃ e : M ≃[L] M, ⇑e ∘ c₀ = c)
    (hψ : ∀ b, ψ.Realize (Fin.append c₀ b) ↔
      ∃ f : M ≃[L] M, (∀ i, f (c₀ i) = c₀ i) ∧ ⇑f ∘ a = b) :
    (existsOrbitParams θ ψ).Realize (Fin.elim0 : Fin 0 → M) :=
  (realize_existsOrbitParams_iff_orbit hθ hψ _).2 ⟨Language.Equiv.refl L M, Subsingleton.elim _ _⟩

/-- Empty carrier, `k = n = 0`, in an arbitrary carrier universe; no `Nonempty`. -/
theorem empty_carrier [L.Structure PEmpty.{w + 1}] {θ : L.Formulaω (Fin 0)}
    {ψ : L.Formulaω (Fin (0 + 0))}
    (hθ : ∀ c, θ.Realize c ↔ ∃ e : PEmpty.{w + 1} ≃[L] PEmpty, ⇑e ∘ Fin.elim0 = c)
    (hψ : ∀ b, ψ.Realize (Fin.append Fin.elim0 b) ↔
      ∃ f : PEmpty.{w + 1} ≃[L] PEmpty, (∀ i, f (Fin.elim0 i) = Fin.elim0 i) ∧
        ⇑f ∘ Fin.elim0 = b) :
    ∀ b, (existsOrbitParams θ ψ).Realize b ↔
      ∃ g : PEmpty.{w + 1} ≃[L] PEmpty, ⇑g ∘ Fin.elim0 = b :=
  realize_existsOrbitParams_iff_orbit hθ hψ

end Generic

/-- Independent language and carrier universes. -/
theorem universes {L' : Language.{3, 4}} {M : Type 2} [L'.Structure M] {k n : ℕ}
    {θ : L'.Formulaω (Fin k)} {ψ : L'.Formulaω (Fin (k + n))} {c₀ : Fin k → M} {a : Fin n → M}
    (hθ : ∀ c, θ.Realize c ↔ ∃ e : M ≃[L'] M, ⇑e ∘ c₀ = c)
    (hψ : ∀ b, ψ.Realize (Fin.append c₀ b) ↔
      ∃ f : M ≃[L'] M, (∀ i, f (c₀ i) = c₀ i) ∧ ⇑f ∘ a = b) :
    ∀ b, (existsOrbitParams θ ψ).Realize b ↔ ∃ g : M ≃[L'] M, ⇑g ∘ a = b :=
  realize_existsOrbitParams_iff_orbit hθ hψ

/-! ### A language with a function symbol -/

/-- One unary function symbol. -/
inductive UFun : ℕ → Type
  | f : UFun 1

/-- One unary function symbol, no relations. -/
def Lf : Language.{0, 0} := ⟨UFun, fun _ => Empty⟩

/-- `(Bool, not)`: automorphisms `id` and `not`. -/
instance : Lf.Structure Bool where
  funMap := fun {_} g xs => match g with | .f => !(xs 0)
  RelMap := fun {_} r _ => Empty.elim r

/-- `not` as an automorphism of `(Bool, not)`. -/
def notAut : Bool ≃[Lf] Bool where
  toEquiv := ⟨not, not, Bool.not_not, Bool.not_not⟩
  map_fun' := by intro n g x; cases g; rfl
  map_rel' := by intro n r; exact r.elim

theorem aut_false (e : Bool ≃[Lf] Bool) (h : e true = true) : e false = false := by
  have : e false ≠ e true := fun h' ↦ Bool.false_ne_true (e.injective h')
  rw [h] at this; simpa using this

theorem exists_aut (x : Bool) : ∃ e : Bool ≃[Lf] Bool, e true = x := by
  cases x
  · exact ⟨notAut, rfl⟩
  · exact ⟨Language.Equiv.refl _ _, rfl⟩

/-! Test A: `k = n = 1`, `c₀ = (true)`, `a = (false)`, `ψ(z, x) := x = f z`. -/

def ψA : Lf.Formulaω (Fin (1 + 1)) :=
  equal (Term.var (Sum.inl 1)) (Term.func UFun.f ![Term.var (Sum.inl 0)])

theorem realize_ψA (c b : Fin 1 → Bool) : ψA.Realize (Fin.append c b) ↔ b 0 = !(c 0) :=
  Iff.rfl

theorem hθA (c : Fin 1 → Bool) :
    (⊤ : Lf.Formulaω (Fin 1)).Realize c ↔ ∃ e : Bool ≃[Lf] Bool, ⇑e ∘ ![true] = c := by
  simp only [Formulaω.realize_top, true_iff]
  obtain ⟨e, he⟩ := exists_aut (c 0)
  exact ⟨e, funext fun i ↦ by rw [Subsingleton.elim i 0]; simpa using he⟩

theorem hψA (b : Fin 1 → Bool) : ψA.Realize (Fin.append ![true] b) ↔
    ∃ f : Bool ≃[Lf] Bool, (∀ i, f (![true] i) = ![true] i) ∧ ⇑f ∘ ![false] = b := by
  rw [realize_ψA]
  constructor
  · intro h
    refine ⟨Language.Equiv.refl _ _, fun _ ↦ rfl, funext fun i ↦ ?_⟩
    rw [Subsingleton.elim i 0]; simpa using h.symm
  · rintro ⟨f, hf, rfl⟩
    have := aut_false f (by simpa using hf 0)
    simpa using this

/-- The orbit of `false` is all of `Bool`; witnessed through the function symbol. -/
theorem testA : (existsOrbitParams (⊤ : Lf.Formulaω (Fin 1)) ψA).Realize ![true] :=
  (realize_existsOrbitParams_iff_orbit hθA hψA _).2
    ⟨notAut, funext fun i ↦ by rw [Subsingleton.elim i 0]; rfl⟩

/-- The composite-form variant on the same data. -/
theorem testA' : (existsOrbitParams (⊤ : Lf.Formulaω (Fin 1)) ψA).Realize ![true] :=
  (realize_existsOrbitParams_iff_orbit' hθA
    (fun b ↦ (hψA b).trans (exists_congr fun _ ↦ and_congr_left' funext_iff.symm)) _).2
    ⟨notAut, funext fun i ↦ by rw [Subsingleton.elim i 0]; rfl⟩

/-! Test B: repeated coordinates, `k = n = 2`, `c₀ = (true, true)`, `a = (false, false)`. -/

def θB : Lf.Formulaω (Fin 2) := equal (Term.var (Sum.inl 0)) (Term.var (Sum.inl 1))

def ψB : Lf.Formulaω (Fin (2 + 2)) :=
  equal (Term.var (Sum.inl 2)) (Term.func UFun.f ![Term.var (Sum.inl 0)]) ⊓
    equal (Term.var (Sum.inl 3)) (Term.func UFun.f ![Term.var (Sum.inl 1)])

theorem realize_ψB (c b : Fin 2 → Bool) :
    ψB.Realize (Fin.append c b) ↔ b 0 = !(c 0) ∧ b 1 = !(c 1) := by
  rw [ψB, Formulaω.realize_inf]; exact Iff.rfl

theorem hθB (c : Fin 2 → Bool) :
    θB.Realize c ↔ ∃ e : Bool ≃[Lf] Bool, ⇑e ∘ ![true, true] = c := by
  show c 0 = c 1 ↔ _
  constructor
  · intro h
    obtain ⟨e, he⟩ := exists_aut (c 0)
    refine ⟨e, funext fun i ↦ ?_⟩
    revert i; rw [Fin.forall_fin_two]
    exact ⟨he, he.trans h⟩
  · rintro ⟨e, rfl⟩; rfl

theorem hψB (b : Fin 2 → Bool) : ψB.Realize (Fin.append ![true, true] b) ↔
    ∃ f : Bool ≃[Lf] Bool, (∀ i, f (![true, true] i) = ![true, true] i) ∧
      ⇑f ∘ ![false, false] = b := by
  rw [realize_ψB]
  constructor
  · rintro ⟨h0, h1⟩
    refine ⟨Language.Equiv.refl _ _, fun _ ↦ rfl, funext fun i ↦ ?_⟩
    revert i; rw [Fin.forall_fin_two]
    exact ⟨by simpa using h0.symm, by simpa using h1.symm⟩
  · rintro ⟨f, hf, rfl⟩
    have := aut_false f (by simpa using hf 0)
    simp [this]

/-- Positive: `(true, true)` is in the orbit of `(false, false)`. -/
theorem testB_pos : (existsOrbitParams θB ψB).Realize ![true, true] :=
  (realize_existsOrbitParams_iff_orbit hθB hψB _).2
    ⟨notAut, funext fun i ↦ by revert i; rw [Fin.forall_fin_two]; exact ⟨rfl, rfl⟩⟩

/-- Negative: `(true, false)` is not. -/
theorem testB_neg : ¬ (existsOrbitParams θB ψB).Realize ![true, false] := by
  rw [realize_existsOrbitParams_iff_orbit hθB hψB]
  rintro ⟨g, hg⟩
  have h0 := congrFun hg 0
  have h1 := congrFun hg 1
  simp only [Function.comp_apply] at h0 h1
  simp at h0 h1
  rw [h0] at h1
  exact Bool.noConfusion h1

/-! Test C: the relative orbit hypothesis is used only at `c₀`.  `Fin 2` with `f` constant `1`:
the only automorphism is the identity, the orbit of `c₀ = (1)` is `{(1)}`, and `ψ(z, x) := x ≠ z`
defines the relative orbit of `a = (0)` at `c₀` but not at the parameter `(0)`. -/

instance : Lf.Structure (Fin 2) where
  funMap := fun {_} g _ => match g with | .f => 1
  RelMap := fun {_} r _ => Empty.elim r

theorem aut_fin2 (e : Fin 2 ≃[Lf] Fin 2) : ∀ x, e x = x := by
  have h1 : e 1 = 1 := e.map_fun UFun.f ![0]
  have h0 : e 0 ≠ e 1 := fun h' ↦ by simpa using e.injective h'
  rw [h1] at h0
  rw [Fin.forall_fin_two]
  exact ⟨by omega, h1⟩

def θC : Lf.Formulaω (Fin 1) :=
  equal (Term.var (Sum.inl 0)) (Term.func UFun.f ![Term.var (Sum.inl 0)])

def ψC : Lf.Formulaω (Fin (1 + 1)) := (equal (Term.var (Sum.inl 1)) (Term.var (Sum.inl 0))).not

theorem hθC (c : Fin 1 → Fin 2) : θC.Realize c ↔ ∃ e : Fin 2 ≃[Lf] Fin 2, ⇑e ∘ ![1] = c := by
  show c 0 = 1 ↔ _
  constructor
  · intro h
    exact ⟨Language.Equiv.refl _ _, funext fun i ↦ by rw [Subsingleton.elim i 0]; simp [h]⟩
  · rintro ⟨e, rfl⟩; exact aut_fin2 e 1

theorem hψC (b : Fin 1 → Fin 2) : ψC.Realize (Fin.append ![1] b) ↔
    ∃ f : Fin 2 ≃[Lf] Fin 2, (∀ i, f (![1] i) = ![1] i) ∧ ⇑f ∘ ![0] = b := by
  show ¬ b 0 = 1 ↔ _
  constructor
  · intro h
    refine ⟨Language.Equiv.refl _ _, fun _ ↦ rfl, funext fun i ↦ ?_⟩
    rw [Subsingleton.elim i 0]; simp; omega
  · rintro ⟨f, -, rfl⟩
    simp [aut_fin2 f]

/-- The uniform version of the relative orbit hypothesis fails (at the parameter `(0)`). -/
theorem testC_uniform_fails : ¬ ∀ c b : Fin 1 → Fin 2, ψC.Realize (Fin.append c b) ↔
    ∃ f : Fin 2 ≃[Lf] Fin 2, (∀ i, f (c i) = c i) ∧ ⇑f ∘ ![0] = b := by
  intro h
  exact (h ![0] ![0]).2 ⟨Language.Equiv.refl _ _, fun _ ↦ rfl, rfl⟩ rfl

/-- ... yet the theorem applies. -/
theorem testC : ∀ b, (existsOrbitParams θC ψC).Realize b ↔
    ∃ g : Fin 2 ≃[Lf] Fin 2, ⇑g ∘ ![0] = b :=
  realize_existsOrbitParams_iff_orbit hθC hψC

/-! ### The pointed-family corollary on the pure set -/

section Pure

attribute [local instance] Language.emptyStructure

/-- An automorphism preserves atomic types. -/
theorem sameAtomicType_comp {M : Type w} [Language.empty.Structure M]
    (e : M ≃[Language.empty] M) {n : ℕ} (a : Fin n → M) :
    SameAtomicType (L := Language.empty) a (⇑e ∘ a) :=
  (SameAtomicType.map_equiv (Language.Equiv.refl _ M) e).2 (SameAtomicType.refl a)

/-- In the empty language, atomic agreement is witnessed by a permutation, on any carrier. -/
theorem pure_homogeneous {X : Type w} {n : ℕ} (a b : Fin n → X)
    (h : SameAtomicType (L := Language.empty) a b) :
    ∃ e : X ≃[Language.empty] X, ⇑e ∘ a = b := by
  obtain ⟨e, he, -, -⟩ := FiberAssembly.exists_equiv_of_matching
    (E := fun (_ _ : X) ↦ True) ⟨fun _ ↦ trivial, fun _ ↦ trivial, fun _ _ ↦ trivial⟩ n a b
    (fun i j ↦ h (AtomicIdx.eq i j)) (fun _ ↦ trivial)
  exact ⟨{ toEquiv := e }, funext he⟩

/-- Composition commutes with appending. -/
theorem comp_append' {α β : Type*} (f : α → β) {k n : ℕ} (c : Fin k → α) (a : Fin n → α) :
    f ∘ Fin.append c a = Fin.append (f ∘ c) (f ∘ a) := by
  funext i
  refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i <;> simp

/-- The atomic diagram of a tuple of `ℕ` defines its orbit. -/
theorem pure_hθ {k : ℕ} (c₀ c : Fin k → ℕ) :
    (atomicDiagram (L := Language.empty) c₀).Realize c ↔
      ∃ e : ℕ ≃[Language.empty] ℕ, ⇑e ∘ c₀ = c := by
  rw [← sameAtomicType_iff_realize_atomicDiagram]
  exact ⟨pure_homogeneous c₀ c, fun ⟨e, he⟩ ↦ he ▸ sameAtomicType_comp e c₀⟩

/-- Atomic diagrams over parameters `c₀` in the pure set `ℕ`. -/
abbrev pureΦc {k : ℕ} (c₀ : Fin k → ℕ) :
    ∀ n, (Fin n → ℕ) → Language.empty.Formulaω (Fin (k + n)) :=
  fun _ a ↦ atomicDiagram (L := Language.empty) (Fin.append c₀ a)

/-- The pointed family of atomic diagrams over `c₀` is an orbit-formula family. -/
theorem pure_isOrbitPointed {k : ℕ} (c₀ : Fin k → ℕ) :
    IsOrbitFormulaFamilyPointed (L := Language.empty) c₀ (pureΦc c₀) := fun n a b ↦ by
  rw [← sameAtomicType_iff_realize_atomicDiagram]
  constructor
  · intro h
    obtain ⟨e, he⟩ := pure_homogeneous _ _ h
    rw [comp_append'] at he
    refine ⟨e, funext fun j ↦ ?_, funext fun i ↦ ?_⟩
    · simpa using congrFun he (Fin.castAdd n j)
    · simpa using congrFun he (Fin.natAdd k i)
  · rintro ⟨e, hec, rfl⟩
    have := sameAtomicType_comp e (Fin.append c₀ a)
    rwa [comp_append', hec] at this

/-- The eliminated formula of `(1, 2)` over the repeated parameters `(1, 1)`. -/
abbrev pureφ : Language.empty.Formulaω (Fin 2) :=
  existsOrbitParams (atomicDiagram (L := Language.empty) (![1, 1] : Fin 2 → ℕ))
    (pureΦc ![1, 1] 2 ![1, 2])

/-- Positive: `(4, 7)` is in the orbit of `(1, 2)`. -/
theorem pure_pos : pureφ.Realize (![4, 7] : Fin 2 → ℕ) :=
  (realize_existsOrbitParams_of_isOrbitFormulaFamilyPointed (pure_hθ ![1, 1])
    (pure_isOrbitPointed ![1, 1]) 2 ![1, 2] ![4, 7]).2
    (pure_homogeneous _ _ fun idx ↦ by
      cases idx with
      | eq i j => exact (by decide : ∀ i j : Fin 2, (![1, 2] : Fin 2 → ℕ) i = ![1, 2] j ↔
          (![4, 7] : Fin 2 → ℕ) i = ![4, 7] j) i j
      | rel R _ => exact isEmptyElim R)

/-- Negative: `(4, 4)` is not (an automorphism is injective). -/
theorem pure_neg : ¬ pureφ.Realize (![4, 4] : Fin 2 → ℕ) := by
  rw [realize_existsOrbitParams_of_isOrbitFormulaFamilyPointed (pure_hθ ![1, 1])
    (pure_isOrbitPointed ![1, 1])]
  rintro ⟨g, hg⟩
  have h := (congrFun hg 0).trans (congrFun hg 1).symm
  simp only [Function.comp_apply] at h
  exact absurd (g.injective h) (by decide)

end Pure

end OrbitParamsGuard

end

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

/-- The exact `InfinitaryLogic` part of the import closure of `Scott.OrbitParameters`. -/
def expectedClosure : List Name :=
  [`InfinitaryLogic.Util, `InfinitaryLogic.Lomega1omega.Syntax,
   `InfinitaryLogic.Lomega1omega.Semantics, `InfinitaryLogic.Lomega1omega.Operations,
   `InfinitaryLogic.Lomega1omega.OpenBoundsSemantics, `InfinitaryLogic.Lomega1omega.QuantifierRank,
   `InfinitaryLogic.Lomega1omega.Theory, `InfinitaryLogic.Scott.AtomicDiagram,
   `InfinitaryLogic.Scott.BackAndForth, `InfinitaryLogic.Scott.BFEquivRelabel,
   `InfinitaryLogic.Scott.Formula, `InfinitaryLogic.Scott.Sentence,
   `InfinitaryLogic.Scott.Stabilization, `InfinitaryLogic.Scott.OrbitRank,
   `InfinitaryLogic.Scott.MontalbanSentence, `InfinitaryLogic.Scott.QuantifierRank,
   `InfinitaryLogic.Karp.PotentialIso, `InfinitaryLogic.Karp.CarrierTheorem,
   `InfinitaryLogic.Scott.OrbitParameters]

run_cmd do
  let env ← getEnv
  let target := `InfinitaryLogic.Scott.OrbitParameters
  unless (env.getModuleIdx? target).isSome do
    throwError "module {target} is not in the environment"
  let cl := importClosure env target
  let il := cl.toList.filter (`InfinitaryLogic).isPrefixOf
  let extra := il.filter fun m ↦ !expectedClosure.contains m
  let missing := expectedClosure.filter fun m ↦ !cl.contains m
  unless extra.isEmpty && missing.isEmpty do
    throwError "[CLOSURE DRIFT] the closure of {target}: unexpected {extra}, missing {missing}"

/-- The public declarations added by the tranche, in every module it touches. -/
def trancheDecls : List Name :=
  [`Fin.append_comp_finAddFlip, `Fin.append_comp_natAdd] ++
  ([`BoundedFormulaω.qrank_mapFreeVars, `BoundedFormulaω.qrank_inf, `BoundedFormulaω.qrank_sup,
    `Formulaω.realize_mapFreeVars, `existsTupleFrom, `realize_existsTupleFrom,
    `qrank_existsTupleFrom, `qrank_forallTupleFrom, `qrank_forallTuple, `qrank_existsTuple,
    `existsOrbitParams, `realize_existsOrbitParams, `qrank_existsOrbitParams,
    `qrank_existsOrbitParams_le, `realize_existsOrbitParams_iff_orbit,
    `realize_existsOrbitParams_iff_orbit',
    `realize_existsOrbitParams_of_isOrbitFormulaFamilyPointed].map (`FirstOrder.Language ++ ·))

/-- The guard's own theorems whose axioms are audited. -/
def guardDecls : List Name :=
  [`qrank_deep, `qrank_deepω, `rank_omega_add_one, `rank_ne_one_add_omega, `rank_le,
   `block_ranks, `k_zero_rfl, `k_zero, `n_zero, `empty_carrier, `universes, `aut_false,
   `exists_aut, `realize_ψA, `hθA, `hψA, `testA, `testA', `realize_ψB, `hθB, `hψB, `testB_pos,
   `testB_neg, `aut_fin2, `hθC, `hψC, `testC_uniform_fails, `testC, `sameAtomicType_comp,
   `pure_homogeneous, `pure_hθ, `pure_isOrbitPointed, `pure_pos, `pure_neg].map
    (`OrbitParamsGuard ++ ·)

/-- The standard axioms. -/
def standardAxioms : List Name := [`propext, `Classical.choice, `Quot.sound]

run_cmd do
  let env ← getEnv
  for n in trancheDecls ++ guardDecls do
    unless (env.find? n).isSome do throwError "declaration {n} not found"
    let axs ← Elab.Command.liftCoreM (collectAxioms n)
    let bad := axs.toList.filter fun a ↦ !standardAxioms.contains a
    unless bad.isEmpty do throwError "[NONSTANDARD AXIOMS] {n} uses {bad}"
  logInfo "Orbit-parameters regression guard: OK (applied: rank omega + 1 at one parameter over \
    a rank-omega orbit formula, not 1 + omega, the bound at omega, the tuple-block rank family; \
    k = 0 by rfl and through the theorem at Fin.elim0; n = 0; the empty carrier PEmpty; \
    Language.{3, 4} with a Type 2 carrier; a unary function symbol on (Bool, not), with the \
    composite-form variant; repeated coordinates (true, true) positive and (true, false) \
    negative; the uniform relative hypothesis refuted on the rigid (Fin 2, f = 1) while the \
    theorem applies; the pointed-family corollary on the pure set over (1, 1), positive at \
    (4, 7) and negative at (4, 4); exact import closure; standard axioms)"
