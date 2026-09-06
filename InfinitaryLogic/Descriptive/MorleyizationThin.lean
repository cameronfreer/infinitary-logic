/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Descriptive.MorleyizationCode
import InfinitaryLogic.Descriptive.AntichainTransport
import InfinitaryLogic.Descriptive.StructureIsoSetoid

/-!
# Thinness transport through canonical expansions

The expansion code `morleyCode Φ` is a measurable embedding (`measurableEmbedding_morleyCode`)
that preserves and reflects isomorphism (`morleyCode_iso_iff`), so antichain transport applies:
a class of base codes is thin for isomorphism iff its class of canonical expansion codes is
(`isThinOn_morleyCode_image_iff`), and likewise for Cantor antichains.  The class need not be
Borel.  Nothing about continuity of the expansion code, the logic topology, or spectra is used.
-/

namespace FirstOrder.Language

open MeasureTheory

variable {L : Language.{0, 0}} [L.IsRelational] [Countable (Σ l, L.Relations l)]
  {Φ : Set (Σ n, L.BoundedFormulaω Empty n)} [Countable ↥Φ]

/-- **Cantor antichains transport through the expansion code**, in both directions. -/
theorem hasCantorAntichainOn_morleyCode_image_iff (C : Set (StructureSpace L)) :
    HasCantorAntichainOn (structureIsoSetoid (L.morleyize Φ)) (morleyCode Φ '' C) ↔
      HasCantorAntichainOn (structureIsoSetoid L) C :=
  hasCantorAntichainOn_image_iff measurableEmbedding_morleyCode
    (fun c d => morleyCode_iso_iff c d) C

/-- **Thinness transport**: a class of base codes is thin iff its class of canonical expansion
codes is.  No Borelness of the class is assumed. -/
theorem isThinOn_morleyCode_image_iff (C : Set (StructureSpace L)) :
    IsThinOn (structureIsoSetoid (L.morleyize Φ)) (morleyCode Φ '' C) ↔
      IsThinOn (structureIsoSetoid L) C :=
  isThinOn_image_iff measurableEmbedding_morleyCode (fun c d => morleyCode_iso_iff c d) C

end FirstOrder.Language
