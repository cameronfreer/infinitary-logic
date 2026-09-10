/-
Regression guard for nullary tags (`ModelTheory/NullaryTags.lean`).

Checked: back-and-forth equivalence at every level is preserved and reflected by tagging with
matching tags, at **arity zero** and on the **empty carrier**; with differing tags the expansions
are inequivalent at level `0`, including on the empty carrier; isomorphisms transfer both ways
and round-trip, including over a language with a **function symbol**; orbit rank and
internal Scott rank are unchanged.  Headline declarations use
only the standard axioms.

Run with: lake env lean scripts/check_nullary_tags_regressions.lean
-/
import InfinitaryLogic.ModelTheory.NullaryTags

open Lean FirstOrder Language

/-- A one-binary-symbol language and the graph `Bool` with inequality. -/
inductive GSym : ℕ → Type
  | e : GSym 2

abbrev Lg : Language := ⟨fun _ => Empty, GSym⟩

instance : Lg.IsRelational := fun _ => inferInstanceAs (IsEmpty Empty)

instance : Lg.Structure Bool where
  funMap f _ := (f : Empty).elim
  RelMap {n} R v := match n, R with
    | _, GSym.e => v 0 ≠ v 1

instance : Lg.Structure Empty where
  funMap f _ := (f : Empty).elim
  RelMap {n} R _ := match n, R with
    | _, GSym.e => False

/-- Arity zero, matching tags: equivalence at every level is preserved and reflected. -/
theorem arity_zero_regression (X : Set ℕ) (α : Ordinal) :
    BFEquiv (L := withTags Lg) α 0 (Fin.elim0 : Fin 0 → Tagged X Bool)
        (Fin.elim0 : Fin 0 → Tagged X Bool) ↔
      BFEquiv (L := Lg) (M := Tagged X Bool) (N := Tagged X Bool) α 0 Fin.elim0 Fin.elim0 :=
  bfEquiv_tagged_iff X α _ _

/-- Empty carrier, matching tags: the empty tuples are equivalent at every level. -/
theorem empty_carrier_regression (X : Set ℕ) (α : Ordinal) :
    BFEquiv (L := withTags Lg) α 0 (Fin.elim0 : Fin 0 → Tagged X Empty)
      (Fin.elim0 : Fin 0 → Tagged X Empty) :=
  (bfEquiv_tagged_iff X α _ _).mpr (BFEquiv.refl α _)

/-- Differing tags: inequivalent at level `0`, on the empty carrier. -/
theorem differing_tags_empty_regression :
    ¬ BFEquiv (L := withTags Lg) 0 0 (Fin.elim0 : Fin 0 → Tagged ∅ Empty)
      (Fin.elim0 : Fin 0 → Tagged Set.univ Empty) :=
  not_bfEquiv_tagged_of_ne (k := 0) (by simp) _ _

/-- Differing tags on a nonempty carrier and a nonempty tuple. -/
theorem differing_tags_regression :
    ¬ BFEquiv (L := withTags Lg) 0 1 (![true] : Fin 1 → Tagged {1} Bool)
      (![true] : Fin 1 → Tagged {2} Bool) :=
  not_bfEquiv_tagged_of_ne (k := 1) (by simp) _ _

/-- Isomorphisms transfer both ways and round-trip. -/
theorem iso_regression (X : Set ℕ) (f : Bool ≃[Lg] Bool) :
    Equiv.ofTagged X (Equiv.toTagged X f) = f ∧
    ∀ x : Bool, Equiv.toTagged X f x = f x :=
  ⟨(taggedEquivEquiv X).right_inv f, fun _ => rfl⟩

/-- Ranks are unchanged. -/
theorem ranks_regression (X : Set ℕ) (a : Fin 2 → Tagged X Bool) :
    orbitRank (L := withTags Lg) a = orbitRank (L := Lg) (M := Tagged X Bool) a ∧
    internalScottRank (L := withTags Lg) (Tagged X Bool) =
      internalScottRank (L := Lg) (Tagged X Bool) :=
  ⟨orbitRank_tagged X a, internalScottRank_tagged X⟩

/-! ### A language with a function symbol -/

/-- One unary function symbol. -/
inductive FSym : ℕ → Type
  | f : FSym 1

abbrev Lf : Language := ⟨FSym, fun _ => Empty⟩

/-- `Bool` with the function symbol interpreted as negation. -/
instance : Lf.Structure Bool where
  funMap {n} g v := match n, g with
    | _, FSym.f => !(v 0)
  RelMap {_} R _ := (R : Empty).elim

/-- Negation is an automorphism: it commutes with the function symbol. -/
def notEquiv : Bool ≃[Lf] Bool where
  toEquiv := ⟨not, not, Bool.not_not, Bool.not_not⟩
  map_fun' := by
    intro n g v
    cases g
    rfl
  map_rel' := fun {_} R _ => (R : Empty).elim

/-- **Function symbols are preserved through tagging**: the transported automorphism commutes
with the function symbol, and the round trip returns it. -/
theorem function_symbol_regression (X : Set ℕ) (x : Tagged X Bool) :
    Equiv.toTagged X notEquiv (Structure.funMap (L := withTags Lf) (Sum.inl FSym.f) ![x]) =
      Structure.funMap (L := withTags Lf) (Sum.inl FSym.f) ![Equiv.toTagged X notEquiv x] ∧
    Equiv.ofTagged X (Equiv.toTagged X notEquiv) = notEquiv := by
  refine ⟨?_, (taggedEquivEquiv X).right_inv notEquiv⟩
  have := (Equiv.toTagged X notEquiv).map_fun (Sum.inl FSym.f) ![x]
  rw [this]
  congr 1
  funext i
  rw [Subsingleton.elim i 0]
  rfl

/-! ### Axiom hygiene -/

def headline : List Name :=
  [`FirstOrder.Language.sameAtomicType_tagged_iff, `FirstOrder.Language.bfEquiv_tagged_iff,
   `FirstOrder.Language.not_bfEquiv_tagged_of_ne, `FirstOrder.Language.Equiv.toTagged,
   `FirstOrder.Language.Equiv.ofTagged, `FirstOrder.Language.taggedEquivEquiv,
   `FirstOrder.Language.orbitRank_tagged, `FirstOrder.Language.internalScottRank_tagged,
   `arity_zero_regression, `empty_carrier_regression, `differing_tags_empty_regression,
   `differing_tags_regression, `iso_regression, `ranks_regression,
   `function_symbol_regression]

def standardAxioms : List Name := [`propext, `Classical.choice, `Quot.sound]

run_cmd do
  let env ← getEnv
  for n in headline do
    unless (env.find? n).isSome do throwError "headline declaration {n} not found"
    let axs ← Elab.Command.liftCoreM (collectAxioms n)
    let bad := axs.toList.filter fun a => !standardAxioms.contains a
    unless bad.isEmpty do throwError "[NONSTANDARD AXIOMS] {n} uses {bad}"
  logInfo "nullary-tags regression guard: OK (arity zero and empty carrier with matching tags, \
    differing tags inequivalent at level 0 incl. the empty carrier, isomorphism round trip, ranks \
    unchanged, function symbols preserved through tagging; headline declarations on standard axioms)"
