/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Methods.WellOrdering.GraphTranslation

/-!
# Boundedness and undefinability of well-ordering: public facade

The stable entry point for the project's well-ordering results (issue #12, Marker §4.4).
Importing this file — or any bundle containing it, including the default
`import InfinitaryLogic` — exposes the four **arbitrary-language** endpoints (all proved in
`Methods/WellOrdering/GraphTranslation.lean`, no hypotheses on `L`):

* **`exists_model_relPreserving`** — Marker Theorem 4.26 (blueprint node
  `thm:wellordering-map`): if `φ` has models with `lt`-chains of every countable length,
  some nonempty model of `φ` carries a relation-preserving map `f : ℚ → M` (for all
  `q < r`, `RelMap lt ![f q, f r]`) — the raw positive conclusion.  Injectivity is the
  derived corollary `RelPreserving.injective_of_irreflexive` (`Methods/WellOrdering/
  Descent.lean`), not part of the raw theorem;
* `wellFounded_boundedness` — if every model of `φ` interprets `lt` as a well-founded
  relation, some countable ordinal chains into no model of `φ`;
* **`wellOrder_type_boundedness`** — Marker Corollary 4.27 (blueprint node
  `thm:wellordering-boundedness`): if every model of `φ` interprets `lt` as a well-order,
  some countable ordinal strictly bounds every model's order type;
* **`wellOrdering_undefinable`** — (blueprint node `thm:wellordering-undefinable`): no
  sentence has as models exactly the structures whose interpreted relation is a well-order.

## Statement discipline

The four results are deliberately separate in strength: the raw positive map (no
injectivity), the derived injectivity corollary, the uniform order-type bound (the strong
form), and undefinability (the weak form).  A stronger induced-copy / relational-embedding
conclusion is tracked separately in issue #31 and is **not** claimed here; the
countable-coded/Borel form of undefinability (non-Borelness of the well-order class) is
issue #33 and additionally needs López–Escobar with a fragment-elementary-substructure
bridge.

## Architecture

A dedicated consistency property over the constants-expanded relational core forces the
positive rational diagram (base diagram + finite remainders with `α`-margin gap witnesses,
Marker's `(*)`); the fair Henkin enumeration and the quotient term model of the Craig
kernel realize it; symbol countability is removed by the two-sorted generated sublanguage,
and function symbols by the Craig relationalization layer, under which the distinguished
base relation is preserved definitionally.

Nothing here has any sorry, and every result is axiom-clean
`[propext, Classical.choice, Quot.sound]`.
-/
