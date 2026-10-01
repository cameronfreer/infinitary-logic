/-
Regression guard for descriptive boundedness of analytic families of well-founded trees
(`InfinitaryLogic/Descriptive/AnalyticTreeBoundedness.lean`) and the tree-height helpers it
consumes (`KleeneBrouwer`, `OrdinalUtil`).

* every public declaration of the tranche is applied to a term: `rank_le_rank_of_relHom` on a
  non-injective homomorphism, `hasInfiniteBranch_iff_exists_seq` in both directions,
  `treeHeight_le_of_relHom` along an inclusion and along a non-injective collapse,
  `treeHeight_lt_omega1` on the empty, root-only and two-level trees, and
  `analytic_tree_rank_bounded` on the empty family, a constant family, and a nonconstant family
  of finite-height trees whose heights are unbounded below `ω`, so that every bound is at least
  the limit `ω`, and `ω` is one;
* exact heights: the empty tree has height `0`, the root-only tree height `1`, and the tree of
  lists of length at most `n` height `n + 1`;
* standard axioms (`propext`, `Classical.choice`, `Quot.sound`);
* minimal imports: the module's import closure reaches no coding, separation, well-order,
  model-theory, methods, interpolation, Henkin, Scott, Karp or infinitary-syntax module, and
  among `InfinitaryLogic` modules is exactly `OrdinalUtil`, `KleeneBrouwer` and this module.

Run with: lake env lean scripts/check_analytic_tree_boundedness_regressions.lean
-/
import InfinitaryLogic.Descriptive.AnalyticTreeBoundedness

open Descriptive KleeneBrouwer MeasureTheory Set

namespace AnalyticTreeBoundednessRegressions

/-! ## Concrete trees -/

/-- The lists of length at most `n`. -/
def boundedTree (n : ℕ) : tree ℕ :=
  ⟨{l | l.length ≤ n}, fun l a (h : (l ++ [a]).length ≤ n) ↦
    show l.length ≤ n by simp at h; omega⟩

theorem mem_boundedTree {n : ℕ} {l : List ℕ} : l ∈ boundedTree n ↔ l.length ≤ n := Iff.rfl

theorem not_hasInfiniteBranch_boundedTree (n : ℕ) : ¬ HasInfiniteBranch (boundedTree n) := by
  rw [hasInfiniteBranch_iff_exists_seq]
  rintro ⟨z, hz⟩
  have := mem_boundedTree.mp (hz (n + 1))
  simp at this

instance wellFounded_boundedTree (n : ℕ) : WellFounded (extBelow (boundedTree n)) :=
  (wellFounded_extBelow_iff_not_hasInfiniteBranch _).mpr (not_hasInfiniteBranch_boundedTree n)

/-- Ranks in `boundedTree n` are at most `n - length`. -/
theorem rank_boundedTree_le (n : ℕ) (x : ↥(boundedTree n)) :
    WellFounded.rank (extBelow (boundedTree n)) x ≤ ((n - (x : List ℕ).length : ℕ) : Ordinal) := by
  induction x using WellFounded.induction' (extBelow (boundedTree n)) with
  | ind x ih =>
    rw [WellFounded.rank_eq]
    refine Ordinal.iSup_le fun b ↦ Order.succ_le_of_lt ((ih b b.2).trans_lt ?_)
    have hlt : (x : List ℕ).length < (b : List ℕ).length :=
      lt_of_le_of_ne b.2.1.length_le fun h ↦ b.2.2 (b.2.1.eq_of_length h)
    have hb : (b : List ℕ).length ≤ n := mem_boundedTree.mp b.1.2
    exact_mod_cast (by omega : n - (b : List ℕ).length < n - (x : List ℕ).length)

/-- Ranks in `boundedTree n` are at least `n - length`. -/
theorem le_rank_boundedTree (n : ℕ) :
    ∀ k (x : ↥(boundedTree n)), (x : List ℕ).length + k ≤ n →
      (k : Ordinal) ≤ WellFounded.rank (extBelow (boundedTree n)) x
  | 0, _, _ => by simp
  | k + 1, x, hx => by
    have hmem : (x : List ℕ) ++ [0] ∈ boundedTree n := by
      rw [mem_boundedTree, List.length_append]; simp; omega
    let y : ↥(boundedTree n) := ⟨_, hmem⟩
    have hyx : extBelow (boundedTree n) y x := ⟨List.prefix_append _ _, by simp [y]⟩
    have hk := le_rank_boundedTree n k y (by simp [y]; omega)
    rw [Nat.cast_succ, ← Order.succ_eq_add_one]
    exact Order.succ_le_of_lt (hk.trans_lt (WellFounded.rank_lt_of_rel hyx))

/-- **The tree of lists of length at most `n` has height `n + 1`.** -/
theorem treeHeight_boundedTree (n : ℕ) : treeHeight (boundedTree n) = n + 1 := by
  refine le_antisymm (Ordinal.iSup_le fun x ↦ ?_) ?_
  · rw [← Nat.cast_succ, Nat.cast_succ, ← Order.succ_eq_add_one]
    refine Order.succ_le_succ ((rank_boundedTree_le n x).trans ?_)
    exact_mod_cast Nat.sub_le n _
  · let root : ↥(boundedTree n) := ⟨[], by simp [mem_boundedTree]⟩
    have h := le_rank_boundedTree n n root (by simp [root])
    rw [← Order.succ_eq_add_one]
    exact (Order.succ_le_succ h).trans
      (Ordinal.le_iSup (fun y : ↥(boundedTree n) ↦
        Order.succ (WellFounded.rank (extBelow (boundedTree n)) y)) root)

/-- The root-only tree has height `1`. -/
example : treeHeight (boundedTree 0) = 1 := by simpa using treeHeight_boundedTree 0

/-- The two-level tree (the root and every one-letter list) has height `2`. -/
example : treeHeight (boundedTree 1) = 2 := by
  rw [treeHeight_boundedTree]; norm_num

/-- The empty tree. -/
instance : IsEmpty ↥(⊥ : tree ℕ) := ⟨fun ⟨l, hl⟩ ↦ by simp at hl⟩

instance wellFounded_bot : WellFounded (extBelow (⊥ : tree ℕ)) := ⟨fun a ↦ isEmptyElim a⟩

/-- The empty tree has height `0`. -/
example : treeHeight (⊥ : tree ℕ) = 0 := by
  simp [treeHeight]

/-! ## `treeHeight_lt_omega1` -/

example : treeHeight (⊥ : tree ℕ) < Ordinal.omega 1 := treeHeight_lt_omega1 _
example : treeHeight (boundedTree 0) < Ordinal.omega 1 := treeHeight_lt_omega1 _
example : treeHeight (boundedTree 1) < Ordinal.omega 1 := treeHeight_lt_omega1 _

/-! ## `hasInfiniteBranch_iff_exists_seq`, both directions -/

/-- The full tree has an infinite branch, read off the constant sequence. -/
example : HasInfiniteBranch (⊤ : tree ℕ) :=
  (hasInfiniteBranch_iff_exists_seq _).mpr ⟨fun _ ↦ 0, fun _ ↦ by simp⟩

/-- A branch yields a sequence with every initial segment in the tree. -/
example (T : tree ℕ) (h : HasInfiniteBranch T) :
    ∃ z : ℕ → ℕ, ∀ n, List.ofFn (fun i : Fin n ↦ z i) ∈ T :=
  (hasInfiniteBranch_iff_exists_seq T).mp h

/-! ## Rank domination, injective or not -/

/-- The inclusion of the root-only tree into the two-level tree. -/
def inclusion01 : extBelow (boundedTree 0) →r extBelow (boundedTree 1) where
  toFun x := ⟨x.1, mem_boundedTree.mpr ((mem_boundedTree.mp x.2).trans zero_le_one)⟩
  map_rel' h := h

example : treeHeight (boundedTree 0) ≤ treeHeight (boundedTree 1) :=
  treeHeight_le_of_relHom inclusion01

/-- Collapse every letter to `0`: a non-injective homomorphism of strict extension. -/
def collapse (n : ℕ) : extBelow (boundedTree n) →r extBelow (boundedTree n) where
  toFun x := ⟨x.1.map fun _ ↦ 0, mem_boundedTree.mpr (by simpa using mem_boundedTree.mp x.2)⟩
  map_rel' {a b} h := by
    obtain ⟨⟨r, hr⟩, hne⟩ := h
    refine ⟨⟨r.map fun _ ↦ 0, by simp [← hr]⟩, fun heq ↦ hne ?_⟩
    have hlen := congrArg List.length heq
    simp only [List.length_map] at hlen
    exact List.IsPrefix.eq_of_length ⟨r, hr⟩ hlen

theorem collapse_not_injective : ¬ Function.Injective (collapse 1) := by
  intro h
  have := h (a₁ := ⟨[1], by simp [mem_boundedTree]⟩) (a₂ := ⟨[2], by simp [mem_boundedTree]⟩)
    (Subtype.ext rfl)
  simp at this

example : treeHeight (boundedTree 1) ≤ treeHeight (boundedTree 1) :=
  treeHeight_le_of_relHom (collapse 1)

/-- A relation on `Fin 3`: both `0` and `1` lie below `2`. -/
def vee (a b : Fin 3) : Prop := a.val < 2 ∧ b.val = 2

/-- The two-point chain on `Bool`. -/
def step (a b : Bool) : Prop := a = false ∧ b = true

instance : WellFounded vee :=
  Subrelation.wf (fun {a b} (h : vee a b) ↦ show a < b by
    rw [Fin.lt_def]; exact h.2 ▸ h.1) wellFounded_lt

instance : WellFounded step :=
  Subrelation.wf (fun {a b} (h : step a b) ↦ show a < b by rw [h.1, h.2]; decide) wellFounded_lt

/-- `0` and `1` both go to `false`: a non-injective homomorphism. -/
def veeHom : vee →r step where
  toFun a := decide (a.val = 2)
  map_rel' {a b} h := ⟨by simp [Nat.ne_of_lt h.1], by simp [h.2]⟩

example : veeHom 0 = veeHom 1 := rfl

example : WellFounded.rank vee 2 ≤ WellFounded.rank step true :=
  InfinitaryLogic.rank_le_rank_of_relHom veeHom 2

example : WellFounded.rank vee 0 ≤ WellFounded.rank step false :=
  InfinitaryLogic.rank_le_rank_of_relHom veeHom 0

/-! ## `analytic_tree_rank_bounded` -/

theorem isClosed_const_tree (T₀ : tree ℕ) (s : List ℕ) :
    IsClosed {_x : ℕ → ℕ | s ∈ T₀} := isClosed_const

theorem analyticSet_univ_baire : AnalyticSet (univ : Set (ℕ → ℕ)) := by
  simpa using analyticSet_range_of_polishSpace (continuous_id (X := ℕ → ℕ))

/-- The empty family. -/
example : ∃ β : Ordinal.{0}, β < Ordinal.omega 1 ∧
    ∀ x (hx : x ∈ (∅ : Set (ℕ → ℕ))),
      @treeHeight (boundedTree 0) ((fun _ h ↦ h.elim : ∀ x ∈ (∅ : Set (ℕ → ℕ)),
        WellFounded (extBelow (boundedTree 0))) x hx) < β :=
  analytic_tree_rank_bounded analyticSet_empty (fun _ ↦ boundedTree 0)
    (isClosed_const_tree _) fun _ h ↦ h.elim

/-- A constant family: the bound exceeds the common height `4`. -/
example : ∃ β : Ordinal.{0}, β < Ordinal.omega 1 ∧ 4 < β := by
  obtain ⟨β, hβ, hb⟩ := analytic_tree_rank_bounded analyticSet_univ_baire
    (fun _ ↦ boundedTree 3) (isClosed_const_tree _) fun _ _ ↦ wellFounded_boundedTree 3
  refine ⟨β, hβ, ?_⟩
  have := hb (fun _ ↦ 0) (mem_univ _)
  rw [treeHeight_boundedTree] at this
  norm_num at this
  exact this

/-- The nonconstant family `x ↦ boundedTree (x 0)` on Baire space: node sets are clopen. -/
theorem isClosed_boundedTree_family (s : List ℕ) :
    IsClosed {x : ℕ → ℕ | s ∈ boundedTree (x 0)} :=
  (isClosed_discrete {m : ℕ | s.length ≤ m}).preimage (continuous_apply 0)

/-- **The nonconstant family**: every bound produced by the theorem is at least `ω`, since the
heights `n + 1` are unbounded below `ω`, while `ω`, a limit, is itself a bound. -/
theorem nonconstant_family :
    (∃ β : Ordinal.{0}, β < Ordinal.omega 1 ∧
      ∀ x : ℕ → ℕ, treeHeight (boundedTree (x 0)) < β) ∧
    (∀ β : Ordinal.{0}, (∀ x : ℕ → ℕ, treeHeight (boundedTree (x 0)) < β) →
      Ordinal.omega0 ≤ β) ∧
    (∀ x : ℕ → ℕ, treeHeight (boundedTree (x 0)) < Ordinal.omega0) ∧
    Order.IsSuccLimit Ordinal.omega0 := by
  refine ⟨?_, fun β hβ ↦ ?_, fun x ↦ ?_, Ordinal.isSuccLimit_omega0⟩
  · obtain ⟨β, hβ, hb⟩ := analytic_tree_rank_bounded analyticSet_univ_baire
      (fun x ↦ boundedTree (x 0)) isClosed_boundedTree_family
      fun x _ ↦ wellFounded_boundedTree (x 0)
    exact ⟨β, hβ, fun x ↦ hb x (mem_univ x)⟩
  · refine Ordinal.omega0_le.mpr fun n ↦ ?_
    have := hβ fun _ ↦ n
    rw [treeHeight_boundedTree] at this
    exact (Order.le_succ _).trans (Order.succ_le_of_lt ((lt_add_one _).trans this))
  · rw [treeHeight_boundedTree]
    exact_mod_cast Ordinal.natCast_lt_omega0 (x 0 + 1)

/-! ## Axioms -/

/-- The declarations whose axioms are audited. -/
def headline : List Lean.Name :=
  [`KleeneBrouwer.analytic_tree_rank_bounded, `KleeneBrouwer.treeHeight_lt_omega1,
   `KleeneBrouwer.treeHeight_le_of_relHom, `KleeneBrouwer.hasInfiniteBranch_iff_exists_seq,
   `InfinitaryLogic.rank_le_rank_of_relHom, `InfinitaryLogic.rank_le_rank_of_imp,
   `AnalyticTreeBoundednessRegressions.treeHeight_boundedTree,
   `AnalyticTreeBoundednessRegressions.nonconstant_family,
   `AnalyticTreeBoundednessRegressions.collapse_not_injective]

/-- The standard axioms. -/
def standardAxioms : List Lean.Name := [`propext, `Classical.choice, `Quot.sound]

end AnalyticTreeBoundednessRegressions

open Lean AnalyticTreeBoundednessRegressions

run_cmd do
  let env ← getEnv
  for n in headline do
    unless (env.find? n).isSome do throwError "headline declaration {n} not found"
    let axs ← Elab.Command.liftCoreM (collectAxioms n)
    let bad := axs.toList.filter fun a ↦ !standardAxioms.contains a
    unless bad.isEmpty do throwError "[NONSTANDARD AXIOMS] {n} uses {bad}"

/-! ## Minimal imports -/

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

/-- Substrings no `InfinitaryLogic` module of the closure may contain (Mathlib and core modules
are exempt: `Mathlib.Order.ScottContinuity` and `Lean.Parser.StrInterpolation` are unrelated).  A
substring match catches a module only while its name retains the substring; the guard enforces
the present boundary and does not track renames. -/
def forbiddenModuleSub : List String :=
  ["LopezEscobar", "InvariantSeparation", "PCSentence", "PCClass", "PCMem", "WellOrdering",
   "WellOrderBridge", "AnalyticWellOrderBoundedness", "TreeCodes", "SmallVocabulary",
   "Interpolation", "Henkin", "Scott", "Karp", "Lomega1omega", "Methods", "ModelTheory",
   "WellOrder", "Code"]

/-- The exact `InfinitaryLogic` import closure of the module.  Extending it is a deliberate
decision: update this list together with the module docstring. -/
def allowedClosure : List Name :=
  [`InfinitaryLogic.OrdinalUtil, `InfinitaryLogic.Descriptive.KleeneBrouwer,
   `InfinitaryLogic.Descriptive.AnalyticTreeBoundedness]

run_cmd do
  let env ← getEnv
  let target := `InfinitaryLogic.Descriptive.AnalyticTreeBoundedness
  unless (env.getModuleIdx? target).isSome do
    throwError "module {target} is not in the environment"
  let cl := importClosure env target
  for m in [`InfinitaryLogic.Descriptive.KleeneBrouwer, `InfinitaryLogic.OrdinalUtil,
            `Mathlib.MeasureTheory.Constructions.Polish.Basic] do
    unless cl.contains m do throwError "[MISSING ROUTE] {m} is not in the closure of {target}"
  let ilModules := cl.toList.filter fun m ↦ (`InfinitaryLogic).isPrefixOf m
  let hits := ilModules.filter fun m ↦
    forbiddenModuleSub.any fun s ↦ (m.toString.splitOn s).length ≠ 1
  unless hits.isEmpty do
    throwError "[BROAD CONE] the closure of {target} reaches {hits}"
  let extra := ilModules.filter fun m ↦ !allowedClosure.contains m
  let missing := allowedClosure.filter fun m ↦ !ilModules.contains m
  unless extra.isEmpty && missing.isEmpty do
    throwError "[CLOSURE DRIFT] the InfinitaryLogic closure of {target} is {ilModules}; \
      update allowedClosure deliberately (extra {extra}, missing {missing})"
  logInfo m!"analytic tree boundedness regression guard: OK (applied: the empty family, a \
    constant family, and the nonconstant family of trees of length at most x 0 on Baire space, \
    whose bounds are all at least the limit omega while omega is a bound; exact heights 0, 1, 2 \
    and n + 1; heights below omega_1; branches as sequences both ways; rank domination along an \
    inclusion and along a non-injective collapse; ranks along a non-injective relation \
    homomorphism; standard axioms; import closure {ilModules} with no coding, separation, \
    well-order, interpolation, Henkin, Scott, Karp or infinitary-syntax module)"
