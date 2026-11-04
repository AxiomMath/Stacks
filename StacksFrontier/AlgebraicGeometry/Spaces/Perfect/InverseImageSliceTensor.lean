module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RelativeBaseChange

/-!
# The tensor product on the slices of the inverse-image ringed site

For a morphism `f : X ⟶ Y` of algebraic spaces, the tensor bifunctor of sheaves of modules on
each slice of `AlgebraicGeometry.Space.inverseImageRingedSite` is additive in each variable, and
its total tensor complexes exist. These are the instance arguments that
`AlgebraicGeometry.Space.IsPerfectRelativeToCanonical` carries, read at the universes of the
slices.

## Main results

* `AlgebraicGeometry.Space.sheafTensor_additive_inverseImageRingedSite_over`
* `AlgebraicGeometry.Space.sheafTensor_obj_additive_inverseImageRingedSite_over`
* `AlgebraicGeometry.Space.hasMapBifunctor_sheafTensor_inverseImageRingedSite_over`

## Implementation notes

Not global instances: instance search reaches the additivity of the slice tensor bifunctor
through an assignment of its two module universes that it cannot solve, so files that need these
make them local instances.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X Y : AlgebraicSpaces B S hS}
  (f : X ⟶ Y)

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat
  RingedSite.sliceHasSheafify RingedSite.sliceWEqualsLocallyBijective

/-- The tensor bifunctor of sheaves of modules on a slice of the inverse-image ringed site is
additive. -/
theorem sheafTensor_additive_inverseImageRingedSite_over (U : (inverseImageRingedSite B S hS f).C) :
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
      ((inverseImageRingedSite B S hS f).over U).O).Additive :=
  Stacks.SheafOfModules.Tensor.sheafTensor_additive.{u + 1, u, u, u, u} _

/-- The tensor product with a fixed sheaf of modules on a slice of the inverse-image ringed site
is additive. -/
theorem sheafTensor_obj_additive_inverseImageRingedSite_over
    (U : (inverseImageRingedSite B S hS f).C)
    (M : RingedSite.Modules.{u + 1, u, u} ((inverseImageRingedSite B S hS f).over U)) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
      ((inverseImageRingedSite B S hS f).over U).O).obj M).Additive :=
  Stacks.SheafOfModules.Tensor.sheafTensor_obj_additive.{u + 1, u, u, u, u} _ M

/-- The total tensor complexes of sheaves of modules on a slice of the inverse-image ringed site
exist. -/
theorem hasMapBifunctor_sheafTensor_inverseImageRingedSite_over
    (U : (inverseImageRingedSite B S hS f).C)
    (K L : CochainComplex
      (RingedSite.Modules.{u + 1, u, u} ((inverseImageRingedSite B S hS f).over U)) ℤ) :
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        ((inverseImageRingedSite B S hS f).over U).O) (ComplexShape.up ℤ) :=
  Stacks.SheafOfModules.Tensor.hasMapBifunctor_sheafTensor.{u + 1, u, u, u, u} _ K L

end AlgebraicGeometry.Space
