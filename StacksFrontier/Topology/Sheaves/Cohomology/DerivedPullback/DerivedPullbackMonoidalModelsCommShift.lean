module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.DerivedPullbackMonoidalModels
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.PullbackTensorComparisonCommShift
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.AdjunctionCommShift
public import StacksFrontier.Homology.DerivedCategory.DerivedPullbackModelIsoCommShift
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ModelComparisonCommShift

/-!
# The tensorator of `Lf^*` at the locally small model commutes with the shift

For a morphism of ringed spaces `f : X ⟶ Y`, the oplax tensorator
`δ K M : Lf^*(K ⊗ᴸ M) ⟶ Lf^*K ⊗ᴸ Lf^*M` of
`Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackCanonicalMonoidal f`, at the locally small
model of the derived categories, commutes with the shift in `K`, for the left-derived commutation
of `Lf^*` with the shift and the commutation of the derived tensor products with the shift of
`Stacks.SheafOfModules.DerivedMonoidal.canonicalTensor_commShift₂Int`.

At the images of the standard model the tensorator is the comparison of [Stacks, Tag 079U]
transported along the comparisons of the two models
(`derivedPullbackCanonicalMonoidal_δ_model`). That comparison commutes with the shift in its first
variable (`derivedPullbackTensorIso_bifunctorComparisonFlip_commShift`), and so do the
comparisons of the two models (`StacksDraft.DerivedModel.derivedPullbackModelIso_hom_commShift`,
`Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctorModelIso_hom_flipApp_commShift`), so
`CategoryTheory.Functor.commShift_of_eq_transportBifunctorComparison` carries the commutation with
the shift across.

## Main results

* `Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackCanonicalMonoidalδLeft`: the tensorator
  at a fixed second argument, as a morphism of functors of the first.
* `Stacks.Cohomology.DerivedPullbackTensor.commShift_derivedPullbackCanonicalMonoidalδLeft`: it
  commutes with the shift.

## Implementation notes

The statements are at the locally small model as the global instance
`SheafOfModules.hasDerivedCategory` provides it, not seated by `letI`: a seated model is a local
variable, which instance search does not identify with the global instance that the derived
tensor product's spelling of the category of modules picks up, and the commutation data of the
composites then fail to be found. For the same reason the commutation data in the statement are
written out, and the tensor data are passed to the transport lemma by name.

## References

* [Stacks Project, Tag 079U](https://stacks.math.columbia.edu/tag/079U)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
attribute [local instance] SheafOfModules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry TopologicalSpace
open CochainComplex.KFlatBifunctor RingedSpaceModuleAdjunction
open scoped CategoryTheory.Prod

universe u

namespace Stacks.Cohomology.DerivedPullbackTensor

attribute [local instance] abelianModulesSheafTensor monoidalModules symmetricModules
  monoidalPreadditiveModules
  monoidalClosedModules hasTensorModules monoidalComplexes
  modulePullback_preservesAntidiagonalCoproducts liftMonoidal CochainComplex.symmetricCategory
  abelianStructureSheafRing

attribute [local implicit_reducible] structureSheafRing
  StacksDraft.KFlat.modulePullback TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf Stacks.SheafOfModules.Tensor.ringSheaf

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

/-- **The tensorator of `Lf^*` at the locally small model, at a fixed second argument `M`**, as a
morphism of functors of the first: `K ↦ (δ K M : Lf^*(K ⊗ᴸ M) ⟶ Lf^*K ⊗ᴸ Lf^*M)`, for
`derivedPullbackCanonicalMonoidal f`, at the locally small model
`Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian`. -/
def derivedPullbackCanonicalMonoidalδLeft
    (M : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))) :
    (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y.sheaf).flip.obj M ⋙
        Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f ⟶
      Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f ⋙
        (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf).flip.obj
          ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f).obj M) :=
  { app := fun K => @Functor.OplaxMonoidal.δ _ _
      (Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal Y.sheaf) _ _
      (Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal X.sheaf)
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f)
      (derivedPullbackCanonicalMonoidal f).toOplaxMonoidal K M
    naturality := fun {_K _K'} u =>
      (@Functor.OplaxMonoidal.δ_natural_left _ _
        (Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal Y.sheaf) _ _
        (Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal X.sheaf)
        (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f)
        (derivedPullbackCanonicalMonoidal f).toOplaxMonoidal _ _ u M).symm }

/-- The component of `derivedPullbackCanonicalMonoidalδLeft f M` at `K` is the tensorator
`δ K M : Lf^*(K ⊗ᴸ M) ⟶ Lf^*K ⊗ᴸ Lf^*M` of `derivedPullbackCanonicalMonoidal f`. -/
theorem derivedPullbackCanonicalMonoidalδLeft_app
    (M K : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))) :
    (derivedPullbackCanonicalMonoidalδLeft f M).app K =
      @Functor.OplaxMonoidal.δ _ _
        (Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal Y.sheaf) _ _
        (Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal X.sheaf)
        (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f)
        (derivedPullbackCanonicalMonoidal f).toOplaxMonoidal K M :=
  rfl



/-- **The tensorator of `Lf^*` at the locally small model commutes with the shift in its first
variable**, for the left-derived commutation of `Lf^*` with the shift and the commutation of the
derived tensor products with the shift of `canonicalTensor_commShift₂Int`. -/
theorem commShift_derivedPullbackCanonicalMonoidalδLeft
    (M : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))) :
    @NatTrans.CommShift _ _ _ _ _ _ (derivedPullbackCanonicalMonoidalδLeft f M) ℤ _ _ _
      (@Functor.CommShift.comp _ _ _ _ _ _ _ _ ℤ _ _ _ _
        ((Stacks.SheafOfModules.DerivedMonoidal.canonicalTensor_commShift₂Int
          Y.sheaf).commShiftFlipObj M)
        (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackLeftDerivedCommShift f))
      (@Functor.CommShift.comp _ _ _ _ _ _ _ _ ℤ _ _ _ _
        (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackLeftDerivedCommShift f)
        ((Stacks.SheafOfModules.DerivedMonoidal.canonicalTensor_commShift₂Int
          X.sheaf).commShiftFlipObj
          ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f).obj M))) := by
  let := Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackLeftDerivedCommShift f
  let := Stacks.SheafOfModules.DerivedMonoidal.canonicalTensor_commShift₂Int Y.sheaf
  let := Stacks.SheafOfModules.DerivedMonoidal.canonicalTensor_commShift₂Int X.sheaf
  let := Stacks.Injectives.grothendieckModelEquivCommShift.{u}
    (SheafOfModules.{u} (structureSheafRing X))
  let := Stacks.Injectives.grothendieckModelEquivCommShift.{u}
    (SheafOfModules.{u} (structureSheafRing Y))
  let := Stacks.Injectives.grothendieckModelEquiv_functor_additive.{u}
    (SheafOfModules.{u} (structureSheafRing X))
  let := Stacks.Injectives.grothendieckModelEquiv_functor_additive.{u}
    (SheafOfModules.{u} (structureSheafRing Y))
  let := Stacks.Cohomology.KFlatDerivedPullback.derivedPullback_commShift f
  let := derivedTensorCommShift₂Int Y
  let := derivedTensorCommShift₂Int X
  have := StacksDraft.DerivedModel.derivedPullbackModelIso_hom_commShift f
  exact Functor.commShift_of_eq_transportBifunctorComparisonInt
    (Stacks.Injectives.grothendieckModelEquiv (SheafOfModules.{u} (structureSheafRing Y))).functor
    (Stacks.Injectives.grothendieckModelEquiv (SheafOfModules.{u} (structureSheafRing X))).functor
    (StacksDraft.DerivedModel.derivedPullbackModelIso f)
    (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctorModelIso Y.sheaf)
    (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctorModelIso X.sheaf)
    (Stacks.Cohomology.DerivedProjectionFormula.pullbackTensorComparison f)
    (hCs := fun _ => inferInstance) (hCl := fun _ => inferInstance)
    (hDs := fun _ => inferInstance) (hDl := fun _ => inferInstance)
    (sTs := derivedTensorCommShift₂Int Y) (sTs' := derivedTensorCommShift₂Int X)
    (sTl := Stacks.SheafOfModules.DerivedMonoidal.canonicalTensor_commShift₂Int Y.sheaf)
    (sTl' := Stacks.SheafOfModules.DerivedMonoidal.canonicalTensor_commShift₂Int X.sheaf)
    (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctorModelIso_hom_flipApp_commShift
      Y.sheaf)
    (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctorModelIso_hom_flipApp_commShift
      X.sheaf)
    (derivedPullbackTensorIso_bifunctorComparisonFlip_commShift f)
    (fun K L => @Functor.OplaxMonoidal.δ _ _
      (Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal Y.sheaf) _ _
      (Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal X.sheaf)
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f)
      (derivedPullbackCanonicalMonoidal f).toOplaxMonoidal K L)
    (fun u v => (@Functor.OplaxMonoidal.δ_natural _ _
      (Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal Y.sheaf) _ _
      (Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal X.sheaf)
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f)
      (derivedPullbackCanonicalMonoidal f).toOplaxMonoidal _ _ _ _ u v).symm)
    (fun K L => derivedPullbackCanonicalMonoidal_δ_model f K L) M _ (fun K => rfl)

end Stacks.Cohomology.DerivedPullbackTensor

end
