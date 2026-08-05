/-
SPIKE — Aaron Liu's carrier-parameterized infinitary syntax.

Deliberately outside the module tree (`spike/`, not `InfinitaryLogic/`) so it enters no bundle and
no CI target. Build with:  lake env lean spike/CarrierSyntax.lean

Question under test: can ONE inductive, parameterized by a fixed infinitary branching carrier `ι`,
replace the current parallel `BoundedFormulaω` / `BoundedFormulaInf` pair — with `Lω₁ω` recovered
definitionally as `ι := ℕ`?

Imports `InfinitaryLogic.Karp.PotentialIso` so that the Karp gate is stated against the REAL
back-and-forth notion (`PotentialIso`), not a toy reconstruction. `PotentialIso` is
syntax-independent (a family of tuple pairs), so this creates no dependence on the old formula
types.

Temporary name `BoundedFormulaIdx` so nothing existing is shadowed.
-/
import InfinitaryLogic.Karp.PotentialIso
import Mathlib.SetTheory.Ordinal.Arithmetic

universe u v uι uκ uμ uα w

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

variable {L : Language.{u, v}} {ι : Type uι} {κ : Type uκ} {μ : Type uμ} {α : Type uα} {n : ℕ}

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

end BoundedFormulaIdx

/-! ## Gate 5a — `IndexCoding`: the reusable coding API

A coding of `ι` into `κ`: an injection with an explicit partial inverse. This is the intended
replacement for the old universe-lift (`liftUI`) and embedding-triangle machinery: moving a
formula from carrier `ι` to carrier `κ` is `reindex` along a coding, and the composition law
plays the role of the old triangle. -/

/-- A coding of the index type `ι` into `κ`: encode injectively, decode partially. -/
structure IndexCoding (ι : Type uι) (κ : Type uκ) where
  /-- The injection. -/
  encode : ι → κ
  /-- The partial inverse. -/
  decode : κ → Option ι
  /-- Decoding recovers every encoded index. -/
  decode_encode : ∀ i, decode (encode i) = some i

namespace IndexCoding

/-- The identity coding. -/
def id (ι : Type uι) : IndexCoding ι ι := ⟨fun i => i, some, fun _ => rfl⟩

/-- Composition of codings. -/
def comp (c₂ : IndexCoding κ μ) (c₁ : IndexCoding ι κ) : IndexCoding ι μ where
  encode := c₂.encode ∘ c₁.encode
  decode := fun m => (c₂.decode m).bind c₁.decode
  decode_encode := fun i => by
    simp [Function.comp, c₂.decode_encode, c₁.decode_encode]

/-- The canonical coding of the left summand. -/
def sumInl (A : Type uι) (B : Type uκ) : IndexCoding A (A ⊕ B) :=
  ⟨Sum.inl, Sum.getLeft?, fun _ => rfl⟩

/-- The canonical coding of the right summand. -/
def sumInr (A : Type uι) (B : Type uκ) : IndexCoding B (A ⊕ B) :=
  ⟨Sum.inr, Sum.getRight?, fun _ => rfl⟩

/-- The canonical coding of an encodable type into `ℕ` — the bridge to `Lω₁ω`.
Deliberately `Encodable`, not `Countable`: no choice in the coding itself. -/
def ofEncodable (ι : Type uι) [Encodable ι] : IndexCoding ι ℕ :=
  ⟨Encodable.encode, Encodable.decode, Encodable.encodek⟩

/-- Extensionality: the coherence proof is irrelevant. -/
@[ext] theorem ext {c₁ c₂ : IndexCoding ι κ} (he : c₁.encode = c₂.encode)
    (hd : c₁.decode = c₂.decode) : c₁ = c₂ := by
  cases c₁; cases c₂; cases he; cases hd; rfl

/-- The canonical coding of one member of a family of carriers into their dependent sum — the
escape hatch for heterogeneous carrier families. Recorded, not consumed: the theory-level
audit found no production consumer needing heterogeneous carriers (`TheoryInf` has no
consumers outside its defining file, and all working theory-level machinery is at the `ℕ`
carrier), so `TheoryInf L ι` stays carrier-uniform and this coding waits for a real use. -/
def sigmaIn {J : Type uκ} [DecidableEq J] (ιs : J → Type uι) (j : J) :
    IndexCoding (ιs j) (Σ j, ιs j) where
  encode i := ⟨j, i⟩
  decode p := if h : p.1 = j then some (h ▸ p.2) else none
  decode_encode i := by simp

/-- The coding induced by an equivalence of carriers; `decode` is total. -/
def ofEquiv (e : ι ≃ κ) : IndexCoding ι κ :=
  ⟨e, fun k => some (e.symm k), fun i => by simp⟩

@[simp] theorem ofEquiv_symm_comp (e : ι ≃ κ) :
    (ofEquiv e.symm).comp (ofEquiv e) = IndexCoding.id ι := by
  refine ext (funext fun i => ?_) (funext fun i => ?_) <;>
    simp [comp, ofEquiv, IndexCoding.id]

/-- Total extension of a family along a coding: decoded indices select a branch,
undecodable ones get the default. -/
def pad {β : Sort*} (c : IndexCoding ι κ) (default : β) (f : ι → β) : κ → β :=
  fun k => (c.decode k).elim default f

@[simp] theorem pad_encode {β : Sort*} (c : IndexCoding ι κ) (default : β) (f : ι → β) (i : ι) :
    c.pad default f (c.encode i) = f i := by
  rw [pad, c.decode_encode]; rfl

theorem pad_of_decode_none {β : Sort*} (c : IndexCoding ι κ) {default : β} {f : ι → β} {k : κ}
    (h : c.decode k = none) : c.pad default f k = default := by
  rw [pad, h]; rfl

theorem pad_of_decode_some {β : Sort*} (c : IndexCoding ι κ) {default : β} {f : ι → β} {k : κ}
    {i : ι} (h : c.decode k = some i) : c.pad default f k = f i := by
  rw [pad, h]; rfl

@[simp] theorem id_pad {β : Sort*} (default : β) (f : ι → β) : (id ι).pad default f = f := rfl

end IndexCoding

namespace BoundedFormulaIdx

/-! ### Coded infinitary constructors

A conjunction/disjunction genuinely indexed by `ι`, built at carrier `κ` through a coding:
unused branches are padded neutrally (`⊤` for `iInf`, `⊥` for `iSup`). -/

/-- An `ι`-indexed conjunction at carrier `κ`, along a coding. -/
def iInfAlong (c : IndexCoding ι κ) (φs : ι → L.BoundedFormulaIdx κ α n) :
    L.BoundedFormulaIdx κ α n :=
  .iInf (c.pad ⊤ φs)

/-- An `ι`-indexed disjunction at carrier `κ`, along a coding. -/
def iSupAlong (c : IndexCoding ι κ) (φs : ι → L.BoundedFormulaIdx κ α n) :
    L.BoundedFormulaIdx κ α n :=
  .iSup (c.pad ⊥ φs)

section CodedRealize

variable {P : Type w} [L.Structure P] {v : α → P} {xs : Fin n → P}

/-- **Padding is semantically neutral**, generically in the coding. -/
@[simp] theorem realize_iInfAlong {c : IndexCoding ι κ} {φs : ι → L.BoundedFormulaIdx κ α n} :
    (iInfAlong c φs).Realize v xs ↔ ∀ i, (φs i).Realize v xs := by
  simp only [iInfAlong, realize_iInf]
  constructor
  · intro h i
    have hi := h (c.encode i)
    rwa [IndexCoding.pad_encode] at hi
  · intro h k
    rcases hd : c.decode k with _ | i
    · rw [c.pad_of_decode_none hd]; simp
    · rw [c.pad_of_decode_some hd]; exact h i

@[simp] theorem realize_iSupAlong {c : IndexCoding ι κ} {φs : ι → L.BoundedFormulaIdx κ α n} :
    (iSupAlong c φs).Realize v xs ↔ ∃ i, (φs i).Realize v xs := by
  simp only [iSupAlong, realize_iSup]
  constructor
  · rintro ⟨k, hk⟩
    rcases hd : c.decode k with _ | i
    · rw [c.pad_of_decode_none hd] at hk; simp at hk
    · rw [c.pad_of_decode_some hd] at hk; exact ⟨i, hk⟩
  · rintro ⟨i, hi⟩
    exact ⟨c.encode i, by rwa [IndexCoding.pad_encode]⟩

end CodedRealize

/-! ### Gate 5b — `reindex`: transporting a formula along a coding

The replacement for the old `liftUI` and the embedding triangle: `reindex` moves a whole
formula between carriers, and its laws (semantic preservation, identity, composition) are the
triangle's replacement. -/

/-- Transport a formula along a coding of its carrier. -/
def reindex (c : IndexCoding ι κ) : ∀ {n}, L.BoundedFormulaIdx ι α n → L.BoundedFormulaIdx κ α n
  | _, .falsum => .falsum
  | _, .equal t₁ t₂ => .equal t₁ t₂
  | _, .rel R ts => .rel R ts
  | _, .imp φ ψ => (reindex c φ).imp (reindex c ψ)
  | _, .all φ => (reindex c φ).all
  | _, .iSup φs => iSupAlong c fun i => reindex c (φs i)
  | _, .iInf φs => iInfAlong c fun i => reindex c (φs i)

section ReindexEqs

variable (c : IndexCoding ι κ)

@[simp] theorem reindex_falsum : reindex c (.falsum : L.BoundedFormulaIdx ι α n) = .falsum := rfl
@[simp] theorem reindex_equal (t₁ t₂ : L.Term (α ⊕ Fin n)) :
    reindex c (.equal t₁ t₂ : L.BoundedFormulaIdx ι α n) = .equal t₁ t₂ := rfl
@[simp] theorem reindex_rel {l : ℕ} (R : L.Relations l) (ts : Fin l → L.Term (α ⊕ Fin n)) :
    reindex c (.rel R ts : L.BoundedFormulaIdx ι α n) = .rel R ts := rfl
@[simp] theorem reindex_imp (φ ψ : L.BoundedFormulaIdx ι α n) :
    reindex c (φ.imp ψ) = (reindex c φ).imp (reindex c ψ) := rfl
@[simp] theorem reindex_all (φ : L.BoundedFormulaIdx ι α (n + 1)) :
    reindex c φ.all = (reindex c φ).all := rfl
@[simp] theorem reindex_iInf (φs : ι → L.BoundedFormulaIdx ι α n) :
    reindex c (.iInf φs) = iInfAlong c fun i => reindex c (φs i) := rfl
@[simp] theorem reindex_iSup (φs : ι → L.BoundedFormulaIdx ι α n) :
    reindex c (.iSup φs) = iSupAlong c fun i => reindex c (φs i) := rfl
@[simp] theorem reindex_not (φ : L.BoundedFormulaIdx ι α n) :
    reindex c φ.not = (reindex c φ).not := rfl
@[simp] theorem reindex_top : reindex c (⊤ : L.BoundedFormulaIdx ι α n) = ⊤ := rfl
@[simp] theorem reindex_bot : reindex c (⊥ : L.BoundedFormulaIdx ι α n) = ⊥ := rfl

end ReindexEqs

/-- **Semantic preservation** (and hence equivalence transport, in both directions). -/
@[simp] theorem realize_reindex {P : Type w} [L.Structure P] (c : IndexCoding ι κ) :
    ∀ {n} (φ : L.BoundedFormulaIdx ι α n) (v : α → P) (xs : Fin n → P),
      (reindex c φ).Realize v xs ↔ φ.Realize v xs := by
  intro n φ
  induction φ with
  | falsum => intro v xs; exact Iff.rfl
  | equal t₁ t₂ => intro v xs; exact Iff.rfl
  | rel R ts => intro v xs; exact Iff.rfl
  | imp φ ψ ihφ ihψ =>
    intro v xs
    simp only [reindex_imp, realize_imp]
    exact imp_congr (ihφ v xs) (ihψ v xs)
  | all φ ih =>
    intro v xs
    simp only [reindex_all, realize_all]
    exact forall_congr' fun y => ih v (Fin.snoc xs y)
  | iSup φs ih =>
    intro v xs
    simp only [reindex_iSup, realize_iSupAlong]
    exact exists_congr fun i => ih i v xs
  | iInf φs ih =>
    intro v xs
    simp only [reindex_iInf, realize_iInfAlong]
    exact forall_congr' fun i => ih i v xs

/-- **Identity law**: reindexing along the identity coding is syntactically the identity. -/
theorem reindex_id : ∀ {n} (φ : L.BoundedFormulaIdx ι α n), reindex (.id ι) φ = φ := by
  intro n φ
  induction φ with
  | falsum => rfl
  | equal t₁ t₂ => rfl
  | rel R ts => rfl
  | imp φ ψ ihφ ihψ => rw [reindex_imp, ihφ, ihψ]
  | all φ ih => rw [reindex_all, ih]
  | iSup φs ih =>
    rw [reindex_iSup]
    show BoundedFormulaIdx.iSup _ = _
    exact congrArg _ (funext fun i => ih i)
  | iInf φs ih =>
    rw [reindex_iInf]
    show BoundedFormulaIdx.iInf _ = _
    exact congrArg _ (funext fun i => ih i)

/-- **Composition law** — the replacement for the old embedding triangle, and syntactic,
not merely semantic. -/
theorem reindex_comp (c₂ : IndexCoding κ μ) (c₁ : IndexCoding ι κ) :
    ∀ {n} (φ : L.BoundedFormulaIdx ι α n),
      reindex (c₂.comp c₁) φ = reindex c₂ (reindex c₁ φ) := by
  intro n φ
  induction φ with
  | falsum => rfl
  | equal t₁ t₂ => rfl
  | rel R ts => rfl
  | imp φ ψ ihφ ihψ => rw [reindex_imp, reindex_imp, reindex_imp, ihφ, ihψ]
  | all φ ih => rw [reindex_all, reindex_all, reindex_all, ih]
  | iSup φs ih =>
    show BoundedFormulaIdx.iSup _ = BoundedFormulaIdx.iSup _
    refine congrArg _ (funext fun m => ?_)
    show (c₂.comp c₁).pad ⊥ _ m = c₂.pad ⊥ _ m
    rcases h₂ : c₂.decode m with _ | k
    · have hc : (c₂.comp c₁).decode m = none := by simp [IndexCoding.comp, h₂]
      rw [(c₂.comp c₁).pad_of_decode_none hc, c₂.pad_of_decode_none h₂]
    · rcases h₁ : c₁.decode k with _ | i
      · have hc : (c₂.comp c₁).decode m = none := by simp [IndexCoding.comp, h₂, h₁]
        rw [(c₂.comp c₁).pad_of_decode_none hc,
          c₂.pad_of_decode_some h₂, c₁.pad_of_decode_none h₁, reindex_bot]
      · have hc : (c₂.comp c₁).decode m = some i := by simp [IndexCoding.comp, h₂, h₁]
        rw [(c₂.comp c₁).pad_of_decode_some hc,
          c₂.pad_of_decode_some h₂, c₁.pad_of_decode_some h₁, ih i]
  | iInf φs ih =>
    show BoundedFormulaIdx.iInf _ = BoundedFormulaIdx.iInf _
    refine congrArg _ (funext fun m => ?_)
    show (c₂.comp c₁).pad ⊤ _ m = c₂.pad ⊤ _ m
    rcases h₂ : c₂.decode m with _ | k
    · have hc : (c₂.comp c₁).decode m = none := by simp [IndexCoding.comp, h₂]
      rw [(c₂.comp c₁).pad_of_decode_none hc, c₂.pad_of_decode_none h₂]
    · rcases h₁ : c₁.decode k with _ | i
      · have hc : (c₂.comp c₁).decode m = none := by simp [IndexCoding.comp, h₂, h₁]
        rw [(c₂.comp c₁).pad_of_decode_none hc,
          c₂.pad_of_decode_some h₂, c₁.pad_of_decode_none h₁, reindex_top]
      · have hc : (c₂.comp c₁).decode m = some i := by simp [IndexCoding.comp, h₂, h₁]
        rw [(c₂.comp c₁).pad_of_decode_some hc,
          c₂.pad_of_decode_some h₂, c₁.pad_of_decode_some h₁, ih i]

/-- Equivalence transport: reindexing preserves semantic equivalence, in both directions. -/
theorem reindex_semanticallyEquivalent_iff {P : Type w} [L.Structure P] (c : IndexCoding ι κ)
    (φ ψ : L.BoundedFormulaIdx ι α n) (v : α → P) (xs : Fin n → P) :
    ((reindex c φ).Realize v xs ↔ (reindex c ψ).Realize v xs) ↔
      (φ.Realize v xs ↔ ψ.Realize v xs) := by
  rw [realize_reindex, realize_reindex]

/-- Equivalence codings round-trip syntactically. -/
@[simp] theorem reindex_ofEquiv_symm_reindex_ofEquiv (e : ι ≃ κ)
    (φ : L.BoundedFormulaIdx ι α n) :
    reindex (.ofEquiv e.symm) (reindex (.ofEquiv e) φ) = φ := by
  rw [← reindex_comp, IndexCoding.ofEquiv_symm_comp, reindex_id]

/-- **Carrier equivalences are actual syntax equivalences.** In particular
`reindexEquiv Equiv.ulift.symm` is the universe-lift operation on formulas, with its exact
syntactic inverse. -/
def reindexEquiv (e : ι ≃ κ) : L.BoundedFormulaIdx ι α n ≃ L.BoundedFormulaIdx κ α n where
  toFun := reindex (.ofEquiv e)
  invFun := reindex (.ofEquiv e.symm)
  left_inv φ := reindex_ofEquiv_symm_reindex_ofEquiv e φ
  right_inv φ := by simpa using reindex_ofEquiv_symm_reindex_ofEquiv e.symm φ

/-! ## Gate 4 — Karp padding, now THROUGH the generic coded constructors

The bespoke `Sum.elim`-with-`⊤` definitions are gone: `iInfLeft`/`iInfRight` are wrappers
around `iInfAlong` at the canonical sum codings, and their realization lemmas are instances
of the generic one. -/

section SumCarrier

variable {M N : Type w}

/-- A conjunction really indexed by the right summand: `iInfAlong` at the `Sum.inr` coding. -/
def iInfRight (ψ : N → L.BoundedFormulaIdx (M ⊕ N) α n) : L.BoundedFormulaIdx (M ⊕ N) α n :=
  iInfAlong (.sumInr M N) ψ

/-- A conjunction really indexed by the left summand: `iInfAlong` at the `Sum.inl` coding. -/
def iInfLeft (ψ : M → L.BoundedFormulaIdx (M ⊕ N) α n) : L.BoundedFormulaIdx (M ⊕ N) α n :=
  iInfAlong (.sumInl M N) ψ

variable {P : Type w} [L.Structure P] {v : α → P} {xs : Fin n → P}

/-- **Padding is semantically neutral** — an instance of `realize_iInfAlong`. -/
@[simp] theorem realize_iInfRight {ψ : N → L.BoundedFormulaIdx (M ⊕ N) α n} :
    (iInfRight ψ).Realize v xs ↔ ∀ j : N, (ψ j).Realize v xs :=
  realize_iInfAlong

@[simp] theorem realize_iInfLeft {ψ : M → L.BoundedFormulaIdx (M ⊕ N) α n} :
    (iInfLeft ψ).Realize v xs ↔ ∀ i : M, (ψ i).Realize v xs :=
  realize_iInfAlong

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

/-! ## Gate 5c — Karp's theorem, packaged, against the REAL `PotentialIso`

`InfEquivAt ι` is sentence equivalence for the new syntax at a fixed carrier `ι`. The theorem:

* forward — a `PotentialIso` yields `InfEquivAt ι` for EVERY carrier `ι`, at every universe;
* backward — `InfEquivAt (M ⊕ N)` alone suffices to build the `PotentialIso`.

So the universal quantification over index types lives OUTSIDE the syntax (`InfEquivW` below),
not inside every infinitary node. No universe lifts, no constructor-quantified index types.

The back-and-forth family here quantifies over formulas with `Empty` free variables and `p.1`
BOUND variables (the tuple sits in bound positions), so `existsLast` does the quantification in
the forth/back arguments and no free-variable relabeling operation is needed at all — compare
`existsLastVarInf` and its ~150-line `Fin` support in `Linf/Operations.lean`. -/

/-- Sentence realization for the new syntax. -/
def SentenceIdx.Realize (φ : L.SentenceIdx ι) (M : Type w) [L.Structure M] : Prop :=
  BoundedFormulaIdx.Realize (M := M) φ Empty.elim Fin.elim0

/-- L∞ω-equivalence at a fixed branching carrier `ι`. -/
def InfEquivAt (L : Language.{u, v}) (ι : Type uι) (M N : Type w)
    [L.Structure M] [L.Structure N] : Prop :=
  ∀ φ : L.SentenceIdx ι, φ.Realize M ↔ φ.Realize N

/-- L∞ω-equivalence with carriers at universe `w`: the quantifier over index types is OUTSIDE
the syntax. Compare `LinfEquivW`, where it lives inside every `iSup`/`iInf` node. -/
def InfEquivW (L : Language.{u, v}) (M N : Type w) [L.Structure M] [L.Structure N] : Prop :=
  ∀ ι : Type w, InfEquivAt L ι M N

/-- **Expressive strength is contravariant in carrier codings**: a larger carrier can express
every smaller-carrier sentence, so agreement at the larger carrier implies agreement at the
smaller. -/
theorem InfEquivAt.of_reindex {M N : Type w} [L.Structure M] [L.Structure N]
    (c : IndexCoding ι κ) (h : InfEquivAt L κ M N) : InfEquivAt L ι M N := fun φ =>
  ((BoundedFormulaIdx.realize_reindex c φ _ _).symm.trans
    (h (BoundedFormulaIdx.reindex c φ))).trans (BoundedFormulaIdx.realize_reindex c φ _ _)

section KarpViaCoding

open BoundedFormulaIdx

variable [L.IsRelational] {M N : Type w} [L.Structure M] [L.Structure N]

/-- In a relational language, every term is a variable. -/
private theorem term_eq_var {γ : Type*} (t : L.Term γ) : ∃ x, t = Term.var x := by
  cases t with
  | var x => exact ⟨x, rfl⟩
  | func f _ => exact (IsEmpty.false f).elim

/-- The atomic formula of an `AtomicIdx`, with the tuple in BOUND positions — generic in the
carrier `ι`. -/
def atomicFormulaIdx (idx : L.AtomicIdx n) : L.BoundedFormulaIdx ι Empty n :=
  match idx with
  | .eq i j => .equal (.var (.inr i)) (.var (.inr j))
  | .rel R f => .rel R fun k => .var (.inr (f k))

omit [L.IsRelational] in
theorem realize_atomicFormulaIdx {P : Type w} [L.Structure P] (idx : L.AtomicIdx n)
    (xs : Fin n → P) :
    (atomicFormulaIdx (ι := ι) idx).Realize Empty.elim xs ↔ idx.holds xs := by
  cases idx with
  | eq i j => simp [atomicFormulaIdx, AtomicIdx.holds, Term.realize]
  | rel R f =>
    simp only [atomicFormulaIdx, realize_rel, Term.realize, Sum.elim_inr, AtomicIdx.holds]
    exact Iff.rfl

/-- **Forward Karp, generic in the carrier**: a `PotentialIso` forces agreement on every
formula over every carrier `ι`, at every index universe. The tuple sits in bound positions,
so the `all` case consumes `forth`/`back` directly, with no `Fin.append` plumbing. -/
private theorem potentialIso_agree_aux (P : PotentialIso L M N) :
    ∀ {k : ℕ} (φ : L.BoundedFormulaIdx ι Empty k) (xs : Fin k → M) (ys : Fin k → N),
      (⟨k, xs, ys⟩ : Σ n : ℕ, (Fin n → M) × (Fin n → N)) ∈ P.family →
      (φ.Realize Empty.elim xs ↔ φ.Realize Empty.elim ys) := by
  intro k φ
  induction φ with
  | falsum => intro xs ys _; simp
  | equal t₁ t₂ =>
    intro xs ys hmem
    obtain ⟨x₁, rfl⟩ := term_eq_var t₁
    obtain ⟨x₂, rfl⟩ := term_eq_var t₂
    rcases x₁ with e | i; · exact e.elim
    rcases x₂ with e | j; · exact e.elim
    simp only [realize_equal, Term.realize, Sum.elim_inr]
    exact (P.compatible _ hmem) (.eq i j)
  | rel R ts =>
    intro xs ys hmem
    have hvar : ∀ i, ∃ j, ts i = Term.var (Sum.inr j) := by
      intro i
      obtain ⟨x, hx⟩ := term_eq_var (ts i)
      rcases x with e | j
      · exact e.elim
      · exact ⟨j, hx⟩
    choose f hf using hvar
    simp only [realize_rel, hf, Term.realize, Sum.elim_inr]
    exact (P.compatible _ hmem) (.rel R f)
  | imp φ ψ ihφ ihψ =>
    intro xs ys hmem
    exact imp_congr (ihφ xs ys hmem) (ihψ xs ys hmem)
  | all φ ih =>
    intro xs ys hmem
    simp only [realize_all]
    constructor
    · intro hAll y
      obtain ⟨m, hm⟩ := P.back ⟨_, xs, ys⟩ hmem y
      exact (ih (Fin.snoc xs m) (Fin.snoc ys y) hm).mp (hAll m)
    · intro hAll m
      obtain ⟨y, hy⟩ := P.forth ⟨_, xs, ys⟩ hmem m
      exact (ih (Fin.snoc xs m) (Fin.snoc ys y) hy).mpr (hAll y)
  | iSup φs ih =>
    intro xs ys hmem
    exact exists_congr fun i => ih i xs ys hmem
  | iInf φs ih =>
    intro xs ys hmem
    exact forall_congr' fun i => ih i xs ys hmem

/-- **Forward direction, generic in the carrier and its universe.** -/
theorem PotentialIso.infEquivAt (P : PotentialIso L M N) (ι : Type uι) : InfEquivAt L ι M N :=
  fun φ => potentialIso_agree_aux P φ Fin.elim0 Fin.elim0 P.empty_mem

/-- **Backward direction at ANY common carrier**: the sum carrier is canonical but not
essential. Sentence equivalence at any single carrier `κ` admitting codings of BOTH
structures already yields a potential isomorphism — the separating conjunctions are
`iInfAlong` along the two given codings. -/
theorem infEquivAt_implies_potentialIso (cM : IndexCoding M κ) (cN : IndexCoding N κ)
    (h : InfEquivAt L κ M N) :
    Nonempty (PotentialIso L M N) := by
  refine ⟨{
    family := { p : Σ n : ℕ, (Fin n → M) × (Fin n → N) |
      ∀ φ : L.BoundedFormulaIdx κ Empty p.1,
        φ.Realize Empty.elim p.2.1 ↔ φ.Realize Empty.elim p.2.2 }
    empty_mem := fun φ => h φ
    compatible := ?_
    forth := ?_
    back := ?_ }⟩
  · -- compatible: atomic formulas (in bound positions) detect atomic type
    intro p hp idx
    exact (realize_atomicFormulaIdx idx p.2.1).symm.trans
      ((hp _).trans (realize_atomicFormulaIdx idx p.2.2))
  · -- forth: contradiction via an N-indexed conjunction coded along `cN`
    rintro ⟨n, a, b⟩ hmem m
    by_contra h_no
    have h_no' : ∀ n' : N, ∃ φ : L.BoundedFormulaIdx κ Empty (n + 1),
        ¬ (φ.Realize Empty.elim (Fin.snoc a m) ↔ φ.Realize Empty.elim (Fin.snoc b n')) := by
      intro n'
      by_contra hn
      refine h_no ⟨n', fun φ => ?_⟩
      by_contra hφ
      exact hn ⟨φ, hφ⟩
    choose φ_bad h_bad using h_no'
    have h_sep : ∀ n' : N, ∃ ψ : L.BoundedFormulaIdx κ Empty (n + 1),
        ψ.Realize Empty.elim (Fin.snoc a m) ∧ ¬ ψ.Realize Empty.elim (Fin.snoc b n') := by
      intro n'
      by_cases hA : (φ_bad n').Realize Empty.elim (Fin.snoc a m)
      · exact ⟨φ_bad n', hA, fun hB => h_bad n' (iff_of_true hA hB)⟩
      · have hB : (φ_bad n').Realize Empty.elim (Fin.snoc b n') := by
          by_contra hB
          exact h_bad n' (iff_of_false hA hB)
        exact ⟨(φ_bad n').not, (realize_not).mpr hA, fun hc => (realize_not).mp hc hB⟩
    choose ψ hψ using h_sep
    set χ : L.BoundedFormulaIdx κ Empty n := existsLast (iInfAlong cN ψ) with hχ
    have hM : χ.Realize Empty.elim a := by
      rw [hχ, realize_existsLast]
      exact ⟨m, by rw [realize_iInfAlong]; exact fun n' => (hψ n').1⟩
    have hN : ¬ χ.Realize Empty.elim b := by
      rw [hχ, realize_existsLast]
      rintro ⟨y, hy⟩
      rw [realize_iInfAlong] at hy
      exact (hψ y).2 (hy y)
    exact hN ((hmem χ).mp hM)
  · -- back: the mirror via an M-indexed conjunction coded along `cM`
    rintro ⟨n, a, b⟩ hmem n'
    by_contra h_no
    have h_no' : ∀ m : M, ∃ φ : L.BoundedFormulaIdx κ Empty (n + 1),
        ¬ (φ.Realize Empty.elim (Fin.snoc a m) ↔ φ.Realize Empty.elim (Fin.snoc b n')) := by
      intro m
      by_contra hn
      refine h_no ⟨m, fun φ => ?_⟩
      by_contra hφ
      exact hn ⟨φ, hφ⟩
    choose φ_bad h_bad using h_no'
    have h_sep : ∀ m : M, ∃ ψ : L.BoundedFormulaIdx κ Empty (n + 1),
        ψ.Realize Empty.elim (Fin.snoc b n') ∧ ¬ ψ.Realize Empty.elim (Fin.snoc a m) := by
      intro m
      by_cases hB : (φ_bad m).Realize Empty.elim (Fin.snoc b n')
      · exact ⟨φ_bad m, hB, fun hA => h_bad m (iff_of_true hA hB)⟩
      · have hA : (φ_bad m).Realize Empty.elim (Fin.snoc a m) := by
          by_contra hA
          exact h_bad m (iff_of_false hA hB)
        exact ⟨(φ_bad m).not, (realize_not).mpr hB, fun hc => (realize_not).mp hc hA⟩
    choose ψ hψ using h_sep
    set χ : L.BoundedFormulaIdx κ Empty n := existsLast (iInfAlong cM ψ) with hχ
    have hN : χ.Realize Empty.elim b := by
      rw [hχ, realize_existsLast]
      exact ⟨n', by rw [realize_iInfAlong]; exact fun m => (hψ m).1⟩
    have hM : ¬ χ.Realize Empty.elim a := by
      rw [hχ, realize_existsLast]
      rintro ⟨x, hx⟩
      rw [realize_iInfAlong] at hx
      exact (hψ x).2 (hx x)
    exact hM ((hmem χ).mpr hN)

/-- **Karp's theorem at any sufficiently large common carrier**: agreement in ONE carrier
admitting codings of both structures already characterizes potential isomorphism. The sum
carrier below is the canonical instance, not a mathematical necessity. -/
theorem karp_theorem_at (cM : IndexCoding M κ) (cN : IndexCoding N κ) :
    Nonempty (PotentialIso L M N) ↔ InfEquivAt L κ M N :=
  ⟨fun ⟨P⟩ => P.infEquivAt _, infEquivAt_implies_potentialIso cM cN⟩

/-- **Karp's theorem at the sum carrier** — the canonical instance of `karp_theorem_at`. -/
theorem karp_theorem_on_sum :
    Nonempty (PotentialIso L M N) ↔ InfEquivAt L (M ⊕ N) M N :=
  karp_theorem_at (.sumInl M N) (.sumInr M N)

/-- **Karp's theorem, public packaging**: the universal quantification over index carriers
belongs OUTSIDE the syntax. Forward instantiates the generic direction at each `ι`;
backward specializes to `ι := M ⊕ N`. Pure packaging around `karp_theorem_at`. -/
theorem karp_theorem_idx :
    Nonempty (PotentialIso L M N) ↔ InfEquivW L M N :=
  ⟨fun ⟨P⟩ ι => P.infEquivAt ι,
   fun h => infEquivAt_implies_potentialIso (.sumInl M N) (.sumInr M N) (h (M ⊕ N))⟩

end KarpViaCoding

/-! ## Gate 6 — the `Encodable` coding into ℕ: recovering `Lω₁ω` -/

namespace BoundedFormulaIdx

/-- Recode a formula over an encodable carrier down to the `ℕ` carrier — i.e. into `Lω₁ω`.
The coding is `Encodable`, so no choice is involved in the operation itself. -/
def toOmega [Encodable ι] (φ : L.BoundedFormulaIdx ι α n) : L.BoundedFormulaOmega α n :=
  reindex (.ofEncodable ι) φ

@[simp] theorem realize_toOmega [Encodable ι] {P : Type w} [L.Structure P]
    (φ : L.BoundedFormulaIdx ι α n) (v : α → P) (xs : Fin n → P) :
    (toOmega φ).Realize v xs ↔ φ.Realize v xs :=
  realize_reindex _ φ v xs

section OmegaProbes

variable {P : Type w} [L.Structure P] {v : α → P} {xs : Fin n → P}

/-- `ι := Empty`: no accidental `Nonempty` assumption — the empty conjunction recodes to a
realizable (vacuously true) `Lω₁ω` formula. -/
example (φs : Empty → L.BoundedFormulaIdx Empty α n) :
    (toOmega (.iInf φs)).Realize v xs := by
  rw [realize_toOmega, realize_iInf]
  exact fun i => i.elim

/-- `ι := Fin k`: finite carriers recode with realization preserved. -/
example {k : ℕ} (φs : Fin k → L.BoundedFormulaIdx (Fin k) α n) :
    (toOmega (.iInf φs)).Realize v xs ↔ ∀ i, (φs i).Realize v xs := by
  rw [realize_toOmega, realize_iInf]

/-- Arbitrary `[Encodable ι]`, arbitrary formula: the generic preservation statement. -/
example {ι' : Type uι} [Encodable ι'] (φ : L.BoundedFormulaIdx ι' α n) :
    (toOmega φ).Realize v xs ↔ φ.Realize v xs :=
  realize_toOmega φ v xs

/-- The `[Countable ι]` corollary: choice enters only HERE, to produce the encoding — the
coding operation itself stays `Encodable`. -/
noncomputable example {ι' : Type uι} [Countable ι'] (φ : L.BoundedFormulaIdx ι' α n) :
    { ψ : L.BoundedFormulaOmega α n //
      ∀ (Q : Type w) [L.Structure Q] (v : α → Q) (xs : Fin n → Q),
        ψ.Realize v xs ↔ φ.Realize v xs } := by
  haveI : Encodable ι' := Encodable.ofCountable ι'
  exact ⟨toOmega φ, fun Q _ v xs => realize_toOmega φ v xs⟩

end OmegaProbes

end BoundedFormulaIdx

/-! ## Gate 7 — quantifier rank, the flagged technical risk

Does rank stay universe-correct? For `ι : Type uι` the `iSup`/`iInf` cases take a supremum over
`ι`, so the natural target is `Ordinal.{uι}` — and at `ι := ℕ` that must be `Ordinal.{0}`,
exactly where the Scott analysis wants it. The transport gate: `reindex` preserves rank up to
`Ordinal.lift`, including for empty carriers. -/

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

@[simp] theorem qrank_falsum : (falsum : L.BoundedFormulaIdx ι α n).qrank = 0 := rfl
@[simp] theorem qrank_equal {t₁ t₂ : L.Term (α ⊕ Fin n)} :
    (equal t₁ t₂ : L.BoundedFormulaIdx ι α n).qrank = 0 := rfl
@[simp] theorem qrank_rel {l : ℕ} {R : L.Relations l} {ts : Fin l → L.Term (α ⊕ Fin n)} :
    (rel R ts : L.BoundedFormulaIdx ι α n).qrank = 0 := rfl
@[simp] theorem qrank_imp {φ ψ : L.BoundedFormulaIdx ι α n} :
    (φ.imp ψ).qrank = max φ.qrank ψ.qrank := rfl
@[simp] theorem qrank_all {φ : L.BoundedFormulaIdx ι α (n + 1)} :
    φ.all.qrank = Order.succ φ.qrank := rfl
@[simp] theorem qrank_iSup {φs : ι → L.BoundedFormulaIdx ι α n} :
    (iSup φs).qrank = ⨆ i, (φs i).qrank := rfl
@[simp] theorem qrank_iInf {φs : ι → L.BoundedFormulaIdx ι α n} :
    (iInf φs).qrank = ⨆ i, (φs i).qrank := rfl

@[simp] theorem qrank_top : (⊤ : L.BoundedFormulaIdx ι α n).qrank = 0 :=
  max_self 0

@[simp] theorem qrank_bot : (⊥ : L.BoundedFormulaIdx ι α n).qrank = 0 := rfl

/-- `Ordinal.lift` commutes with small suprema (including over empty index types).
Proved here since Mathlib has the `Cardinal` version but not the `Ordinal` one. -/
private theorem lift_iSup_ord {ι' : Type uι} (f : ι' → Ordinal.{uι}) :
    Ordinal.lift.{uκ} (⨆ i, f i) = ⨆ i, Ordinal.lift.{uκ} (f i) := by
  haveI : Small.{max uι uκ} ι' := small_max.{uκ} ι'
  apply le_antisymm
  · have hub : (⨆ i, Ordinal.lift.{uκ} (f i)) ≤ Ordinal.lift.{uκ} (⨆ i, f i) :=
      Ordinal.iSup_le fun i => Ordinal.lift_le.mpr (Ordinal.le_iSup f i)
    obtain ⟨t, ht⟩ := Ordinal.mem_range_lift_of_le hub
    rw [← ht]
    refine Ordinal.lift_le.mpr (Ordinal.iSup_le fun i => Ordinal.lift_le.mp ?_)
    rw [ht]
    exact Ordinal.le_iSup (fun i => Ordinal.lift.{uκ} (f i)) i
  · exact Ordinal.iSup_le fun i => Ordinal.lift_le.mpr (Ordinal.le_iSup f i)

/-- **Rank transport**: `reindex` preserves quantifier rank up to `Ordinal.lift` — the
rank-side replacement for the old `liftUI` compatibility lemma. Padding contributes only
rank-0 `⊤`/`⊥` branches, so the supremum is unchanged, including for empty carriers. -/
theorem qrank_reindex (c : IndexCoding ι κ) :
    ∀ {n} (φ : L.BoundedFormulaIdx ι α n),
      Ordinal.lift.{uι} (reindex c φ).qrank = Ordinal.lift.{uκ} φ.qrank := by
  intro n φ
  induction φ with
  | falsum => simp
  | equal t₁ t₂ => simp
  | rel R ts => simp
  | imp φ ψ ihφ ihψ =>
    show Ordinal.lift.{uι} (max _ _) = Ordinal.lift.{uκ} (max _ _)
    rw [Monotone.map_max (fun _ _ h => Ordinal.lift_le.mpr h),
      Monotone.map_max (fun _ _ h => Ordinal.lift_le.mpr h), ihφ, ihψ]
  | all φ ih =>
    show Ordinal.lift.{uι} (Order.succ _) = Ordinal.lift.{uκ} (Order.succ _)
    rw [Ordinal.lift_succ, Ordinal.lift_succ, ih]
  | iSup φs ih =>
    haveI : Small.{max uι uκ} ι := small_max.{uκ} ι
    haveI : Small.{max uι uκ} κ := small_max.{uι} κ
    show Ordinal.lift.{uι} (⨆ k, ((c.pad ⊥ fun i => reindex c (φs i)) k).qrank) =
      Ordinal.lift.{uκ} (⨆ i, (φs i).qrank)
    rw [lift_iSup_ord, lift_iSup_ord]
    apply le_antisymm
    · refine Ordinal.iSup_le fun k => ?_
      rcases hd : c.decode k with _ | i
      · rw [c.pad_of_decode_none hd, qrank_bot, Ordinal.lift_zero]
        exact Ordinal.bot_eq_zero ▸ bot_le
      · rw [c.pad_of_decode_some hd, ih i]
        exact Ordinal.le_iSup (fun i => Ordinal.lift.{uκ} (φs i).qrank) i
    · refine Ordinal.iSup_le fun i => ?_
      rw [← ih i]
      have hb := Ordinal.le_iSup
        (fun k => Ordinal.lift.{uι} ((c.pad ⊥ fun i => reindex c (φs i)) k).qrank) (c.encode i)
      rwa [IndexCoding.pad_encode] at hb
  | iInf φs ih =>
    haveI : Small.{max uι uκ} ι := small_max.{uκ} ι
    haveI : Small.{max uι uκ} κ := small_max.{uι} κ
    show Ordinal.lift.{uι} (⨆ k, ((c.pad ⊤ fun i => reindex c (φs i)) k).qrank) =
      Ordinal.lift.{uκ} (⨆ i, (φs i).qrank)
    rw [lift_iSup_ord, lift_iSup_ord]
    apply le_antisymm
    · refine Ordinal.iSup_le fun k => ?_
      rcases hd : c.decode k with _ | i
      · rw [c.pad_of_decode_none hd, qrank_top, Ordinal.lift_zero]
        exact Ordinal.bot_eq_zero ▸ bot_le
      · rw [c.pad_of_decode_some hd, ih i]
        exact Ordinal.le_iSup (fun i => Ordinal.lift.{uκ} (φs i).qrank) i
    · refine Ordinal.iSup_le fun i => ?_
      rw [← ih i]
      have hb := Ordinal.le_iSup
        (fun k => Ordinal.lift.{uι} ((c.pad ⊤ fun i => reindex c (φs i)) k).qrank) (c.encode i)
      rwa [IndexCoding.pad_encode] at hb

end BoundedFormulaIdx

section RankProbes

open BoundedFormulaIdx

/-- At the countable carrier the rank lands in `Ordinal.{0}` — where Scott analysis needs it. -/
noncomputable example {L : Language.{u, v}} {α : Type uα}
    (φ : L.BoundedFormulaOmega α 0) : Ordinal.{0} := φ.qrank

/-- At a structure-carrier the rank lives in that carrier's universe, as expected. -/
noncomputable example {L : Language.{u, v}} {α : Type uα} {M N : Type w}
    (φ : L.BoundedFormulaIdx (M ⊕ N) α 0) : Ordinal.{w} := φ.qrank

/-- Rank transport for `toOmega`: since `qrank (toOmega φ) : Ordinal.{0}` and `lift.{0}` is
the identity, the recoded rank IS the original rank's lift into universe 0's ordinals. -/
example {L : Language.{u, v}} {α : Type uα} {ι' : Type uι} [Encodable ι']
    (φ : L.BoundedFormulaIdx ι' α 0) :
    Ordinal.lift.{uι} (toOmega φ).qrank = Ordinal.lift.{0} φ.qrank :=
  qrank_reindex _ φ

/-- Rank transport at an EMPTY carrier: the empty supremum is preserved. -/
example {L : Language.{u, v}} {α : Type uα}
    (φs : Empty → L.BoundedFormulaIdx Empty α 0) :
    Ordinal.lift.{0} (toOmega (.iInf φs)).qrank = Ordinal.lift.{0} (iInf φs).qrank :=
  qrank_reindex _ _

end RankProbes

/-! ## Gate 7 (remaining) — falsification probes -/

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
