/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import InfinitaryLogic.Methods.Henkin.CountableCompletion.FairEnumeration

/-!
# Deprecated re-export shim (issue #34 rehoming)

The countable Henkin-completion kernel serves two arcs (#8 Craig interpolation, #12
well-ordering) and was rehomed to `Methods/Henkin/CountableCompletion/FairEnumeration.lean`.
This shim keeps the old import path working for at least one release; update imports to
the new path.  All declaration names and namespaces are unchanged.
-/

deprecated_module (since := "2026-07-21")
