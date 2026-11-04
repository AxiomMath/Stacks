module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.FlatDegreewise
public import
  StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.InternalHomStalkPresentation

/-!
# The derived half of the stalk presentation, reduced to an abelian comparison

`Stacks.Cohomology.DerivedInternalHomStalk.StalkPullbackComparison X x` is the compatibility of
derived pullback along the one-point inclusion `Y = {x} ⟶ X`, read through the identification
`D(𝒪_Y) ≌ D(𝒪_{X,x})` given by the one-point description of modules, with the derived stalk at
`x`.  This file reduces it to a natural isomorphism of functors on the *abelian* categories,

`h^* ⋙ (one-point description) ≅ (-)_x`.

## Main definitions

* `Stacks.Cohomology.DerivedInternalHomStalk.pointPullback`: degreewise pullback along the
  one-point inclusion `Y = {x} ⟶ X`.
* `Stacks.Cohomology.DerivedInternalHomStalk.PointPullbackStalkComparison`: **the abelian
  comparison** — pulling a sheaf of `𝒪_X`-modules back to the one-point space and
  reading it as an `𝒪_{X,x}`-module is taking its stalk at `x`, naturally in the sheaf.

## Main results

* `Stacks.Cohomology.DerivedInternalHomStalk.isFlat_pointHom`: **the one-point inclusion is
  flat** in the sense of `AlgebraicGeometry.IsFlat`.
* `Stacks.Cohomology.DerivedInternalHomStalk.stalkPullbackComparison_of_abelian`: **the
  reduction**, `PointPullbackStalkComparison X x → StalkPullbackComparison X x`.
* `Stacks.Cohomology.DerivedInternalHomStalk.stalkPresentation_of_abelian`:
  a `StalkPresentation X x` from the abelian comparison together with
  `Stacks.Cohomology.DerivedInternalHomStalk.InternalHomComparison`, the other compatibility.

## References

* [Stacks Project, Tag 0GM8](https://stacks.math.columbia.edu/tag/0GM8)
* [Stacks Project, Tag 0098](https://stacks.math.columbia.edu/tag/0098)
* [Stacks Project, Tag 02N3](https://stacks.math.columbia.edu/tag/02N3)
* [Stacks Project, Tag 06YJ](https://stacks.math.columbia.edu/tag/06YJ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.AssociatedSheaf
open Stacks.Cohomology.DerivedInternalHomPullback

namespace Stacks.Cohomology.DerivedInternalHomStalk

universe u

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local implicit_reducible] CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf

variable (X : RingedSpace.{u, u}) (x : X.carrier)

attribute [local instance] stalkCommRing

/-! ### The one-point inclusion is flat -/

/-- **The one-point inclusion `Y = {x} ⟶ X` is flat**, in the sense of
`AlgebraicGeometry.IsFlat`: the germ map is flat at every point of the source. -/
theorem isFlat_pointHom : AlgebraicGeometry.IsFlat (pointHom X x) := by
  intro p
  obtain rfl := pointSpace_unique_pt X x p
  exact RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso _)

/-! ### The abelian comparison -/

/-- **Degreewise pullback along the one-point inclusion** `Y = {x} ⟶ X`, written at the spelling
of the category of module sheaves that `StalkPresentation` is stated at. -/
abbrev pointPullback :
    AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X ⥤
      AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules (pointSpace X x) :=
  RingedSpaceModuleAdjunction.modulePullback (pointHom X x)

/-- **The abelian comparison**: pulling a sheaf of
`𝒪_X`-modules back along the one-point inclusion `Y = {x} ⟶ X` and reading the result as an
`𝒪_{X,x}`-module through the one-point description of sheaves of modules is taking its stalk at
`x`, naturally in the sheaf of modules. -/
abbrev PointPullbackStalkComparison :=
  pointPullback X x ⋙ (pointModulesEquiv X x).functor ≅
    AlgebraicGeometry.SheafOfModules.stalkFunctor
      (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf) x

/-! ### The reduction -/

/-- **The first compatibility of the stalk presentation follows from the abelian comparison.** -/
def stalkPullbackComparison_of_abelian (e : PointPullbackStalkComparison X x) :
    StalkPullbackComparison X x :=
  haveI : PreservesFiniteLimits
      (RingedSpaceModuleAdjunction.modulePullback (pointHom X x)) :=
    RingedSpaceModuleAdjunction.preservesFiniteLimits_modulePullback_of_isFlat _
      (isFlat_pointHom X x)
  haveI : PreservesColimits
      (RingedSpaceModuleAdjunction.modulePullback (pointHom X x)) :=
    RingedSpaceModuleAdjunction.preservesColimits_modulePullback (pointHom X x)
  haveI : PreservesFiniteLimits (pointPullback X x) :=
    RingedSpaceModuleAdjunction.preservesFiniteLimits_modulePullback_of_isFlat _
      (isFlat_pointHom X x)
  haveI : PreservesColimits (pointPullback X x) :=
    RingedSpaceModuleAdjunction.preservesColimits_modulePullback (pointHom X x)
  haveI : PreservesFiniteColimits (pointPullback X x) := inferInstance
  haveI : (pointPullback X x).PreservesZeroMorphisms :=
    ⟨fun _ _ ↦ Functor.map_zero
      (RingedSpaceModuleAdjunction.modulePullback (pointHom X x)) _ _⟩
  haveI : (pointPullback X x).Additive :=
    Functor.additive_of_preserves_binary_products _
  haveI : (pointModulesEquiv X x).functor.Additive :=
    Functor.additive_of_preserves_binary_products _
  have : (AlgebraicGeometry.SheafOfModules.stalkFunctor
      (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf) x).Additive :=
    AlgebraicGeometry.SheafOfModules.stalkFunctor_additive _ _
  have : PreservesFiniteLimits (AlgebraicGeometry.SheafOfModules.stalkFunctor
      (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf) x) :=
    AlgebraicGeometry.SheafOfModules.stalkFunctor_preservesFiniteLimits _ _
  have : PreservesFiniteColimits (AlgebraicGeometry.SheafOfModules.stalkFunctor
      (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf) x) :=
    have := AlgebraicGeometry.SheafOfModules.stalkFunctor_preservesColimits
      (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf) x
    inferInstance
  Functor.isoWhiskerRight
      (show derivedPullbackFunctor (pointHom X x) ≅ (pointPullback X x).mapDerivedCategory from
        Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackIsoMapDerivedCategory
          (pointHom X x) (isFlat_pointHom X x))
      (pointDerivedEquiv X x).functor ≪≫
    Dualizing.mapDerivedCategoryCompNatIso (pointPullback X x)
      (pointModulesEquiv X x).functor
      (AlgebraicGeometry.SheafOfModules.stalkFunctor
        (Stacks.SheafOfModules.Tensor.ringSheaf X.sheaf) x) e

/-- **A presentation of the point from the abelian comparison and the internal-hom
compatibility.** -/
def stalkPresentation_of_abelian (e : PointPullbackStalkComparison X x)
    (homIso : InternalHomComparison X x) : StalkPresentation X x :=
  stalkPresentationOfCompatibilities X x (stalkPullbackComparison_of_abelian X x e) homIso

end Stacks.Cohomology.DerivedInternalHomStalk

end
