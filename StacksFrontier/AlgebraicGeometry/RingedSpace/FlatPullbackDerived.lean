module

public import StacksFrontier.Topology.Sheaves.RingedSpace.FlatModulePullback
public import StacksFrontier.Homology.KFlat.Pullback
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives

/-!
# Derived pullback along a flat morphism of ringed spaces

For a flat morphism of ringed spaces `f : X ⟶ Y`, the inverse image functor `f^*` on sheaves of
modules is exact (`StacksFrontier.Topology.Sheaves.RingedSpace.FlatModulePullback`), so its right
derived functor on bounded-below derived categories is computed degreewise: the canonical
right-derived-functor unit is invertible.  This is the statement that makes the derived flat
base-change morphism of Tag 02N7 exist.

## Main results

* `Stacks.Cohomology.isIso_rightDerivedFunctorPlusUnit_of_exact`: an exact additive functor
  between abelian categories, the source having enough injectives, has an invertible
  right-derived-functor unit.
* `Stacks.RingedSpace.flatPullbackUnit_isIso`: the right-derived-functor unit of `f^*` is
  invertible on every bounded-below complex, when `f` is flat.
* `Stacks.RingedSpace.flatPullback`: derived pullback along a flat morphism.
* `Stacks.RingedSpace.flatPullbackComparison`: the resulting identification of degreewise
  pullback with derived pullback, whose forward map is the unit
  (`flatPullbackComparison_hom_app`).

## Implementation notes

Everything in this file is stated for an arbitrary derived-category model, that is, at
`[HasDerivedCategory.{w} _]` instance binders rather than under a file-level
`attribute [local instance] HasDerivedCategory.standard`. This is why
`isIso_rightDerivedFunctorPlusUnit_of_exact` is stated here:
`Stacks.Cohomology.BaseChange.exactUnit_isIso` is the same statement for the model
`HasDerivedCategory.standard` only, which its file fixes, so it does not apply to any other
model. The proof needs nothing about the model.

`flatPullback` takes the flatness hypothesis as an argument it does not use, matching
`flatPullbackComparison`, whose hypothesis is genuinely used.  Keeping the argument makes the
pair usable as the two halves of one interface and records in the type that derived pullback is
only being claimed to be computed degreewise in the flat case.

## References

* [Stacks Project, Tag 02N7](https://stacks.math.columbia.edu/tag/02N7)
* [Stacks Project, Tag 02N3](https://stacks.math.columbia.edu/tag/02N3)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction

universe w w' v v' u u'

namespace Stacks.Cohomology

/-- **An exact additive functor has an invertible right-derived-functor unit**, so its right
derived functor on bounded-below derived categories is computed degreewise.

This is the free-model form of `Stacks.Cohomology.BaseChange.exactUnit_isIso`, which is stated
only for `HasDerivedCategory.standard` because its file pins that model. -/
theorem isIso_rightDerivedFunctorPlusUnit_of_exact
    {A : Type u} {B : Type u'} [Category.{v} A] [Category.{v'} B]
    [Abelian A] [Abelian B] [HasDerivedCategory.{w} A] [HasDerivedCategory.{w'} B]
    [EnoughInjectives A] (F : A ⥤ B) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    IsIso F.rightDerivedFunctorPlusUnit := by
  apply Functor.isIso_of_isRightDerivedFunctor_of_inverts
    (W := HomotopyCategory.Plus.quasiIso A)
    F.rightDerivedFunctorPlus F.rightDerivedFunctorPlusUnit
  intro K L φ hφ
  have : IsIso (DerivedCategory.Qh.map φ.hom) :=
    Localization.inverts DerivedCategory.Qh (HomotopyCategory.quasiIso A (.up ℤ)) _ hφ
  have : IsIso ((DerivedCategory.Plus.ι).map
      ((F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).map φ)) := by
    change IsIso (DerivedCategory.Qh.map ((F.mapHomotopyCategory (.up ℤ)).map φ.hom))
    exact (NatIso.isIso_map_iff F.mapDerivedCategoryFactorsh φ.hom).mp (by
      change IsIso (F.mapDerivedCategory.map (DerivedCategory.Qh.map φ.hom))
      infer_instance)
  exact isIso_of_reflects_iso _ DerivedCategory.Plus.ι

end Stacks.Cohomology

namespace Stacks.RingedSpace

variable {X Y : AlgebraicGeometry.RingedSpace.{u, u}} (f : X ⟶ Y)
  [HasDerivedCategory.{w} (SheafOfModules.{u} (structureSheafRing Y))]
  [HasDerivedCategory.{w'} (SheafOfModules.{u} (structureSheafRing X))]

/-- **Flatness makes the unit from degreewise pullback to its right derived functor an
isomorphism on every bounded-below complex.** Flat pullback is exact
(`RingedSpaceModuleAdjunction.preservesFiniteLimits_modulePullback_of_isFlat` together with the
unconditional right exactness of a left adjoint), and an exact functor's right derived functor
is computed degreewise. -/
theorem flatPullbackUnit_isIso (hf : AlgebraicGeometry.IsFlat f)
    (K : HomotopyCategory.Plus (SheafOfModules.{u} (structureSheafRing Y))) :
    IsIso ((modulePullback f).rightDerivedFunctorPlusUnit.app K) := by
  have : PreservesFiniteLimits (modulePullback f) :=
    preservesFiniteLimits_modulePullback_of_isFlat f hf
  have : PreservesColimits (modulePullback f) := preservesColimits_modulePullback f
  exact (NatTrans.isIso_iff_isIso_app _).mp
    (Stacks.Cohomology.isIso_rightDerivedFunctorPlusUnit_of_exact (modulePullback f)) K

/-- **Derived pullback along a flat morphism of ringed spaces.** Flatness identifies this right
derived functor with pullback applied degreewise, which is `flatPullbackComparison`. -/
noncomputable def flatPullback (_hf : AlgebraicGeometry.IsFlat f) :
    DerivedCategory.Plus (SheafOfModules.{u} (structureSheafRing Y)) ⥤
      DerivedCategory.Plus (SheafOfModules.{u} (structureSheafRing X)) :=
  (modulePullback f).rightDerivedFunctorPlus

/-- **The canonical identification of degreewise pullback with derived pullback** along a flat
morphism, on bounded-below derived categories. -/
noncomputable def flatPullbackComparison (hf : AlgebraicGeometry.IsFlat f) :
    (modulePullback f).mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh ≅
      DerivedCategory.Plus.Qh ⋙ flatPullback f hf :=
  @asIso _ _ _ _ (modulePullback f).rightDerivedFunctorPlusUnit
    ((NatTrans.isIso_iff_isIso_app _).mpr (flatPullbackUnit_isIso f hf))

/-- The forward map of `flatPullbackComparison` is the canonical right-derived-functor unit, so
the identification is the canonical one and not a choice. -/
theorem flatPullbackComparison_hom_app (hf : AlgebraicGeometry.IsFlat f)
    (K : HomotopyCategory.Plus (SheafOfModules.{u} (structureSheafRing Y))) :
    (flatPullbackComparison f hf).hom.app K =
      (modulePullback f).rightDerivedFunctorPlusUnit.app K :=
  rfl

end Stacks.RingedSpace
