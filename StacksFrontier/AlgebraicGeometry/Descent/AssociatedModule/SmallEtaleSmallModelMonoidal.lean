module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleSmallModelPullbackExact
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleSmallModelTorAmplitude
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PointsOtherTopologies.SmallEtale
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackMonoidal
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.StalkBaseChangeAtTheTargetPoint

/-!
# `ε^*` on the model of the small étale site is monoidal on derived categories

Let `S` be a scheme and `ε : (S_étale, 𝒪) ⟶ (S_Zar, 𝒪_S)` the morphism of ringed sites of
Stacks 08H7, read on the `Type u` model of the small étale site
(`AlgebraicGeometry.SmallEtale.toZariskiSmallModelHom`). The pullback of sheaves of modules along
it is exact (Stacks 08H8) and carries K-flat complexes to K-flat complexes (Stacks 0DEP, the
small étale site having enough points by Stacks 06VX). So it induces a monoidal functor on
derived categories, which is the derived pullback `Lε^*`.

## Main results

* `AlgebraicGeometry.SmallEtale.hasConservativeFamily_smallModelTopology`: Stacks 06VX on the
  model: the model of the small étale site has a conservative family of points.
* `AlgebraicGeometry.SmallEtale.kFlat_pullbackTopos_toZariskiSmallModelHom`: `ε^*` on the model
  carries K-flat complexes to K-flat complexes.

## Main definitions

* `AlgebraicGeometry.SmallEtale.derivedPullbackSmallModelMonoidal`: `ε^*` applied termwise is
  monoidal for the derived tensor products of Stacks 0FPT on either side.
* `AlgebraicGeometry.SmallEtale.derivedPullbackSmallModelIso`: it is `Lε^*`.

## Implementation notes

Tensoring with a fixed module and the existence of total tensor complexes are named as local
instances at the two ringed topoi, and `Stacks.SheafOfModules.Tensor.ringSheaf` is made
implicit-reducible, as in
`StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleSmallModelTorAmplitude`:
otherwise instance search for them exceeds its budget at these concrete ringed topoi.
-/

@[expose] public noncomputable section

attribute [local implicit_reducible] Stacks.SheafOfModules.Tensor.ringSheaf

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 06VX on the model**: the model of the small étale site has a conservative family of
points, the comparison with the small étale site being a dense subsite inclusion for the
induced topology. -/
public theorem hasConservativeFamily_smallModelTopology :
    (smallModelTopology B S hS).HasConservativeFamily.{u} :=
  have : (smallModelEquiv B S hS).functor.IsDenseSubsite (topology B S hS)
      (smallModelTopology B S hS) := inferInstance
  have : (smallModelEquiv B S hS).functor.IsContinuous (topology B S hS)
      (smallModelTopology B S hS) := inferInstance
  have : (smallModelEquiv B S hS).functor.IsCocontinuous (topology B S hS)
      (smallModelTopology B S hS) := inferInstance
  hasConservativeFamily_of_denseSubsite.{u + 1, u, u} (topology B S hS)
    (smallModelTopology B S hS) (smallModelEquiv B S hS).functor
    (SmallEtale.hasConservativeFamily B S hS)

/-- Tensoring with a fixed `𝒪_S`-module is additive; named so that instance search does not have
to rediscover it at the Zariski ringed topos, where the search exceeds its budget. -/
local instance sheafTensorObjAdditiveZariski
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf S.zariskiRingedTopos.O)) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} S.zariskiRingedTopos.O).obj
      M).Additive :=
  Stacks.SheafOfModules.Tensor.sheafTensor_obj_additive.{u, u, u, u, u} S.zariskiRingedTopos.O M

/-- Tensoring with a fixed module on the model is additive; see
`sheafTensorObjAdditiveZariski`. -/
local instance sheafTensorObjAdditiveModel
    (M : SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallModelRingedTopos B S hS).O)) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      (smallModelRingedTopos B S hS).O).obj M).Additive :=
  Stacks.SheafOfModules.Tensor.sheafTensor_obj_additive.{u, u, u, u, u}
    (smallModelRingedTopos B S hS).O M

/-- The total tensor complexes of complexes of `𝒪_S`-modules exist; named for the reason recorded
at `sheafTensorObjAdditiveZariski`. -/
local instance hasMapBifunctorZariski
    (K₁ K₂ : CochainComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf S.zariskiRingedTopos.O)) ℤ) :
    HomologicalComplex.HasMapBifunctor K₁ K₂
      (Stacks.SheafOfModules.Tensor.sheafTensor S.zariskiRingedTopos.O)
      (ComplexShape.up ℤ) :=
  Stacks.SheafOfModules.Tensor.hasMapBifunctor_sheafTensor S.zariskiRingedTopos.O K₁ K₂

/-- The total tensor complexes of complexes of modules on the model exist. -/
local instance hasMapBifunctorModel
    (K₁ K₂ : CochainComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallModelRingedTopos B S hS).O)) ℤ) :
    HomologicalComplex.HasMapBifunctor K₁ K₂
      (Stacks.SheafOfModules.Tensor.sheafTensor (smallModelRingedTopos B S hS).O)
      (ComplexShape.up ℤ) :=
  Stacks.SheafOfModules.Tensor.hasMapBifunctor_sheafTensor (smallModelRingedTopos B S hS).O K₁ K₂

/-- **`ε^*` on the model preserves K-flatness**: Stacks 0DEP, the model of the small étale site
having a conservative family of points. -/
public theorem kFlat_pullbackTopos_toZariskiSmallModelHom
    (K : CochainComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf S.zariskiRingedTopos.O)) ℤ)
    (hK : CochainComplex.KFlatBifunctor.KFlat
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} S.zariskiRingedTopos.O) K) :
    CochainComplex.KFlatBifunctor.KFlat
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (smallModelRingedTopos B S hS).O)
      (((toZariskiSmallModelHom B S hS).pullbackTopos.mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K) :=
  Stacks.Sheaves.DerivedPullback.KFlatPullbackMorphismOfSites.kFlat_pullbackComplex
    (toZariskiSmallModelHom B S hS) (isMorphismOfSites_toZariskiSmallModelHom_u B S hS)
    (hasConservativeFamily_smallModelTopology B S hS) K hK

/-- **`ε^*` on the model, applied termwise, is monoidal on derived categories**, for the derived
tensor products of Stacks 0FPT on `D(𝒪_S)` and on the model: `ε^*` is exact (Stacks 08H8) and
preserves K-flatness (`kFlat_pullbackTopos_toZariskiSmallModelHom`). -/
@[instance_reducible]
public def derivedPullbackSmallModelMonoidal :
    letI := Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal S.zariskiRingedTopos.O
    letI := Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal (smallModelRingedTopos B S hS).O
    (Stacks.Sheaves.DerivedPullback.pullbackToposMapDerived
      (toZariskiSmallModelHom B S hS)).Monoidal :=
  Stacks.Sheaves.DerivedPullback.pullbackToposMapDerivedMonoidal (toZariskiSmallModelHom B S hS)
    (isMorphismOfSites_toZariskiSmallModelHom_u B S hS)
    (kFlat_pullbackTopos_toZariskiSmallModelHom B S hS)

/-- **`Lε^*` on the model is `ε^*` applied termwise**, `ε^*` being exact. -/
public def derivedPullbackSmallModelIso :
    derivedPullbackSmallModel B S hS ≅
      Stacks.Sheaves.DerivedPullback.pullbackToposMapDerived (toZariskiSmallModelHom B S hS) :=
  Stacks.Sheaves.DerivedPullback.derivedPullbackIsoMapDerived (toZariskiSmallModelHom B S hS)

end AlgebraicGeometry.SmallEtale

end
