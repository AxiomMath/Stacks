module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Subobject.MonoOver
import StacksCore.Tactic.StacksAttribute

/-! ## `MonoOver.exists` along monomorphisms and composites.

## Relation to mathlib

This file used to hold the `MonoOver` half of mathlib#42757 (`full_exists`,
`factorThruImage_comp_existsPullbackAdj_counit_app_hom_left`, `existsComp`), ported ahead of
the pin. Mathlib now has all three in `Mathlib.CategoryTheory.Subobject.MonoOver` under the
same names and statements, so the local copies were deleted; the file can be removed.
-/
