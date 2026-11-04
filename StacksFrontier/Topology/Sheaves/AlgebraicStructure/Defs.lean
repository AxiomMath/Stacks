module
-- Narrow imports on purpose. This file is the canonical 007M definition, so everything that
-- speaks about types of algebraic structure imports it; a `public import Mathlib` here
-- propagates the whole library into files that deliberately kept their imports small, and that
-- is not cosmetic — it enlarged the instance search space enough to make typeclass synthesis
-- time out at 20000 heartbeats in OpenImmersion/ExtensionByInitialAlgStruct.
public import Mathlib.CategoryTheory.Limits.Filtered
public import Mathlib.CategoryTheory.Limits.Preserves.Filtered
public import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 007M — types of algebraic structure

Tag 007M defines a *type of algebraic structure*: a category `C` together with a functor
`F : C ⥤ Sets` such that

1. `F` is faithful,
2. `C` has limits and `F` commutes with limits,
3. `C` has filtered colimits and `F` commutes with them, and
4. `F` reflects isomorphisms.

The definition is formalized here as the structure `AlgebraicStructureType`, bundling the
category, the functor to sets, and the four properties as instance fields (which are then made
available to instance synthesis). The objects of `C` live in universe `u` and its homs in
universe `v`, and the target is `Type v`.

## Why the target is `Type v` and not `Type u`

Conditions 2 and 3 are size conditions, and they must talk about the *same* size class on both
sides. `Limits.HasFilteredColimits C` unfolds to `HasFilteredColimitsOfSize.{v, v} C`, indexed by
`C`'s hom universe, while `Limits.PreservesFilteredColimits F` unfolds to
`PreservesFilteredColimitsOfSize.{v₂, v₂} F` indexed by the hom universe of `F`'s *target*. The
category `Type w` has `Category.{w, w + 1}`, so a target of `Type u` would ask `C` to *have*
filtered colimits of shapes in `{v, v}` while asking `F` to *preserve* those of shapes in
`{u, u}` — different classes whenever `u ≠ v`. Taking the target to be `Type v` puts both at
`{v, v}`, so the bundle says what 007M says for all `u` and `v`, not only on the diagonal.

The lemma `algebraicStructureType_properties` records that the four properties are recovered
from the bundle, i.e. that the structure really packages the definition.
-/

@[expose] public section

open CategoryTheory

universe v u

-- checkUnivs false positive: `C`, `inst_cat` and `F` use `u`/`v` separately, but they only
-- occur together in the structure's sort; always used with explicit universe arguments.
/-- A *type of algebraic structure* is a category `C` together with a functor
`F : C ⥤ Type v` to the category of sets which is faithful, preserves all
(small) limits, preserves filtered colimits, and reflects isomorphisms.

The objects of `C` live in universe `u` and its homs in universe `v`, and the target is
`Type v` so that the two size conditions are indexed by the same universe — see the module
docstring. -/
@[stacks_fixed 007M]
structure AlgebraicStructureType where
  /-- The underlying category. -/
  C : Type u
  /-- The category structure on `C`. -/
  [inst_cat : Category.{v} C]
  /-- The "forgetful" functor `F : C ⥤ Type v`. -/
  F : C ⥤ Type v
  /-- The functor `F` is faithful. -/
  [faithful : F.Faithful]
  /-- The category `C` has all (small) limits. -/
  [has_limits : Limits.HasLimits C]
  /-- The functor `F` preserves limits. -/
  [preserves_limits : Limits.PreservesLimits F]
  /-- The category `C` has filtered colimits. -/
  [has_filtered_colimits : Limits.HasFilteredColimits C]
  /-- The functor `F` preserves filtered colimits. -/
  [preserves_filtered_colimits : Limits.PreservesFilteredColimits F]
  /-- The functor `F` reflects isomorphisms. -/
  [reflects_iso : F.ReflectsIsomorphisms]

attribute [instance] AlgebraicStructureType.inst_cat
  AlgebraicStructureType.faithful
  AlgebraicStructureType.has_limits
  AlgebraicStructureType.preserves_limits
  AlgebraicStructureType.has_filtered_colimits
  AlgebraicStructureType.preserves_filtered_colimits
  AlgebraicStructureType.reflects_iso

/-- The four defining properties of a type of algebraic structure all hold
for any `A : AlgebraicStructureType`. This packages the definition. -/
theorem algebraicStructureType_properties (A : AlgebraicStructureType.{v, u}) :
    A.F.Faithful ∧ Limits.HasLimits A.C ∧ Limits.PreservesLimits A.F ∧
      Limits.HasFilteredColimits A.C ∧ Limits.PreservesFilteredColimits A.F ∧
        A.F.ReflectsIsomorphisms :=
  ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance⟩

