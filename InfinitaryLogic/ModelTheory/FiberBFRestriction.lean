/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.ModelTheory.FiberIsoAssembly
import InfinitaryLogic.Scott.BackAndForth

/-!
# Pointed back-and-forth restriction to a fiber

The converse of the back-and-forth assembly, in pointed form and with the **owner row
retained**.  For rows `r : R`, `s : S`, a label `τ`, and component tuples `ā : Fin k → C r τ`,
`b̄ : Fin k → D s τ`, write `rowPts r ā` for the assembled tuple `(row r, pt r τ (ā 0), …)` of
length `k + 1`.

**Theorem** (`bfEquiv_restrict_pointed`): if `rowPts r ā ≡_β rowPts s b̄` in the assembled
language, then `ā ≡_β b̄` in the components, at the **same** level `β`.

The owner row is kept throughout the induction because it is what forces responses into the
correct fiber: a move by a point of the fiber `(r, τ)` is answered, by the `lab τ` and `own`
atoms against the retained row, by a point of the fiber `(s, τ)` (a private lemma).  Owner-indexed nullary atoms
(`lift0`) read at the row supply the component nullary facts, so **empty fibers** are handled
with no fiber point.  At level zero the component atoms are exactly the assembled `eq`, `lift`,
and `lift0` atoms on the canonical points (`relMap_lift_pt`, `relMap_lift0_row`).

**Corollary** (`bfEquiv_restrict_nil`): `row r ≡_β row s` gives `C r τ ≡_β D s τ` as
structures (empty tuples) for every label `τ`.

Lifted nullary facts distinguish rows already at level zero, so the corollary is a genuine
constraint on the rows, not an automatic agreement.
-/

namespace FirstOrder.Language

namespace FiberAssembly

universe u v w

variable {U : Type u} {Lc : Language.{v, w}} {R S : Type u} {C : R → Label U → Type u}
  {D : S → Label U → Type u} [∀ r τ, Lc.Structure (C r τ)] [∀ s τ, Lc.Structure (D s τ)]

/-- The assembled tuple of a row followed by points of one of its fibers. -/
def rowPts (r : R) (τ : Label U) {k : ℕ} (a : Fin k → C r τ) : Fin (k + 1) → Carrier R C :=
  Fin.cons (Carrier.row r) (fun j => Carrier.pt r τ (a j))

@[simp] theorem rowPts_zero (r : R) (τ : Label U) {k : ℕ} (a : Fin k → C r τ) :
    rowPts r τ a 0 = Carrier.row r := rfl

@[simp] theorem rowPts_succ (r : R) (τ : Label U) {k : ℕ} (a : Fin k → C r τ) (j : Fin k) :
    rowPts r τ a j.succ = Carrier.pt r τ (a j) := rfl

/-- Appending a point of the fiber to the assembled tuple appends it to the component tuple. -/
theorem snoc_rowPts (r : R) (τ : Label U) {k : ℕ} (a : Fin k → C r τ) (x : C r τ) :
    (Fin.snoc (rowPts r τ a) (Carrier.pt r τ x) : Fin (k + 1 + 1) → Carrier R C) =
      rowPts r τ (Fin.snoc a x) := by
  unfold rowPts
  rw [← Fin.cons_snoc_eq_snoc_cons]
  congr 1
  funext j
  refine Fin.lastCases ?_ (fun j => ?_) j
  · simp
  · simp

/-! ### The response to a fiber point lands in the image fiber -/

/-- At any level, a point of the fiber `(r, τ)` matched against the retained rows is answered by
a point of the fiber `(s, τ)`: the `lab τ` and `own` atoms force it. -/
private theorem exists_pt_of_bfEquiv_snoc {β : Ordinal} {r : R} {s : S} {τ : Label U} {k : ℕ}
    {a : Fin k → C r τ} {b : Fin k → D s τ} {x : C r τ} {m : Carrier S D}
    (h : BFEquiv (L := lang U Lc) β (k + 1 + 1)
      (Fin.snoc (rowPts r τ a) (Carrier.pt r τ x)) (Fin.snoc (rowPts s τ b) m)) :
    ∃ y : D s τ, m = Carrier.pt s τ y := by
  have h0 := (BFEquiv.zero _ _).mp (BFEquiv.monotone (_root_.zero_le) h)
  -- the label
  have hlab := h0 (AtomicIdx.rel (Sym.lab τ) ![Fin.last _])
  simp only [AtomicIdx.holds] at hlab
  have hl : Structure.RelMap (L := lang U Lc) (Sym.lab τ)
      (Fin.snoc (rowPts r τ a) (Carrier.pt r τ x) ∘ ![Fin.last _]) := by
    refine ⟨r, x, ?_⟩
    simp
  obtain ⟨s', y, hy⟩ := hlab.mp hl
  simp only [Function.comp, Matrix.cons_val_zero, Fin.snoc_last] at hy
  -- the owner
  have hown := h0 (AtomicIdx.rel Sym.own ![Fin.last _, 0])
  simp only [AtomicIdx.holds] at hown
  have ho : Structure.RelMap (L := lang U Lc) Sym.own
      (Fin.snoc (rowPts r τ a) (Carrier.pt r τ x) ∘ ![Fin.last _, 0]) := by
    refine ⟨r, τ, x, ?_, ?_⟩
    · simp
    · show (Fin.snoc (rowPts r τ a) (Carrier.pt r τ x) : Fin (k + 1 + 1) → Carrier R C) 0 =
        Carrier.row r
      rw [show (0 : Fin (k + 1 + 1)) = Fin.castSucc 0 from rfl, Fin.snoc_castSucc]
      rfl
  obtain ⟨s'', τ'', y'', h1, h2⟩ := hown.mp ho
  simp only [Function.comp, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.snoc_last] at h1 h2
  have h2' : (Carrier.row s : Carrier S D) = Carrier.row s'' := by
    have : (Fin.snoc (rowPts s τ b) m : Fin (k + 1 + 1) → Carrier S D) 0 = Carrier.row s := by
      rw [show (0 : Fin (k + 1 + 1)) = Fin.castSucc 0 from rfl, Fin.snoc_castSucc]
      rfl
    exact this.symm.trans h2
  rw [hy] at h1
  obtain ⟨hs, -, -⟩ := Carrier.pt_inj h1
  have hss : s'' = s := (Carrier.row.inj h2').symm
  subst hss
  subst hs
  exact ⟨y, hy⟩

/-- The symmetric statement: a point of the fiber `(s, τ)` is answered by a point of `(r, τ)`. -/
private theorem exists_pt_of_bfEquiv_snoc' {β : Ordinal} {r : R} {s : S} {τ : Label U} {k : ℕ}
    {a : Fin k → C r τ} {b : Fin k → D s τ} {y : D s τ} {m : Carrier R C}
    (h : BFEquiv (L := lang U Lc) β (k + 1 + 1)
      (Fin.snoc (rowPts r τ a) m) (Fin.snoc (rowPts s τ b) (Carrier.pt s τ y))) :
    ∃ x : C r τ, m = Carrier.pt r τ x :=
  exists_pt_of_bfEquiv_snoc (BFEquiv.symm h)

/-! ### Level zero -/

/-- Assembled atomic agreement of the pointed tuples gives component atomic agreement. -/
theorem sameAtomicType_of_rowPts {r : R} {s : S} {τ : Label U} {k : ℕ} {a : Fin k → C r τ}
    {b : Fin k → D s τ}
    (h : SameAtomicType (L := lang U Lc) (rowPts r τ a) (rowPts s τ b)) :
    SameAtomicType (L := Lc) a b := by
  intro idx
  cases idx with
  | eq i j =>
    have h2 := h (AtomicIdx.eq i.succ j.succ)
    simp only [AtomicIdx.holds, rowPts_succ] at h2 ⊢
    constructor
    · intro hij
      exact Carrier.pt_inj_same (h2.mp (by rw [hij]))
    · intro hij
      exact Carrier.pt_inj_same (h2.mpr (by rw [hij]))
  | rel Sy f =>
    simp only [AtomicIdx.holds]
    -- split on the arity of the component symbol
    rename_i l
    cases l with
      | zero =>
        -- nullary: read at the owner rows through `lift0`
        have h2 := h (AtomicIdx.rel (Sym.lift0 Sy τ) ![0])
        simp only [AtomicIdx.holds] at h2
        have e1 : rowPts r τ a ∘ ![(0 : Fin (k + 1))] = fun _ => Carrier.row r := by
          funext i; fin_cases i; rfl
        have e2 : rowPts s τ b ∘ ![(0 : Fin (k + 1))] = fun _ => Carrier.row s := by
          funext i; fin_cases i; rfl
        rw [e1, e2, relMap_lift0_row, relMap_lift0_row] at h2
        rw [show a ∘ f = Fin.elim0 from funext fun i => i.elim0,
          show b ∘ f = Fin.elim0 from funext fun i => i.elim0]
        exact h2
      | succ l =>
        have h2 := h (AtomicIdx.rel (Sym.lift Sy) (fun i => (f i).succ))
        simp only [AtomicIdx.holds] at h2
        have e1 : rowPts r τ a ∘ (fun i => (f i).succ) =
            fun i => (Carrier.pt r τ ((a ∘ f) i) : Carrier R C) := funext fun i => rfl
        have e2 : rowPts s τ b ∘ (fun i => (f i).succ) =
            fun i => (Carrier.pt s τ ((b ∘ f) i) : Carrier S D) := funext fun i => rfl
        rw [e1, e2, relMap_lift_pt, relMap_lift_pt] at h2
        exact h2

/-! ### The theorem -/

/-- **Pointed back-and-forth restriction**: assembled equivalence of the pointed tuples, owner
rows retained, restricts to component equivalence of the points at the same level. -/
theorem bfEquiv_restrict_pointed (β : Ordinal) {r : R} {s : S} (τ : Label U) :
    ∀ {k : ℕ} {a : Fin k → C r τ} {b : Fin k → D s τ},
      BFEquiv (L := lang U Lc) β (k + 1) (rowPts r τ a) (rowPts s τ b) →
        BFEquiv (L := Lc) β k a b := by
  induction β using Ordinal.limitRecOn with
  | zero =>
    intro k a b h
    exact (BFEquiv.zero _ _).mpr (sameAtomicType_of_rowPts ((BFEquiv.zero _ _).mp h))
  | add_one β ih =>
    intro k a b h
    rw [← Order.succ_eq_add_one] at h ⊢
    rw [BFEquiv.succ] at h ⊢
    obtain ⟨h0, hf, hb⟩ := h
    refine ⟨ih h0, fun x => ?_, fun y => ?_⟩
    · obtain ⟨m, hm⟩ := hf (Carrier.pt r τ x)
      obtain ⟨y, rfl⟩ := exists_pt_of_bfEquiv_snoc hm
      refine ⟨y, ih ?_⟩
      rwa [snoc_rowPts, snoc_rowPts] at hm
    · obtain ⟨m, hm⟩ := hb (Carrier.pt s τ y)
      obtain ⟨x, rfl⟩ := exists_pt_of_bfEquiv_snoc' hm
      refine ⟨x, ih ?_⟩
      rwa [snoc_rowPts, snoc_rowPts] at hm
  | limit β hβ ih =>
    intro k a b h
    rw [BFEquiv.limit β hβ] at h ⊢
    exact fun γ hγ => ih γ hγ (h γ hγ)

/-- **Empty-tuple corollary**: equivalent rows have equivalent fibers at every label. -/
theorem bfEquiv_restrict_nil (β : Ordinal) {r : R} {s : S}
    (h : BFEquiv (L := lang U Lc) β 1 ![(Carrier.row r : Carrier R C)]
      ![(Carrier.row s : Carrier S D)]) (τ : Label U) :
    BFEquiv (L := Lc) β 0 (Fin.elim0 : Fin 0 → C r τ) (Fin.elim0 : Fin 0 → D s τ) := by
  apply bfEquiv_restrict_pointed β τ
  have e1 : rowPts r τ (Fin.elim0 : Fin 0 → C r τ) = ![(Carrier.row r : Carrier R C)] := by
    funext i; fin_cases i; rfl
  have e2 : rowPts s τ (Fin.elim0 : Fin 0 → D s τ) = ![(Carrier.row s : Carrier S D)] := by
    funext i; fin_cases i; rfl
  rw [e1, e2]
  exact h

end FiberAssembly

end FirstOrder.Language
