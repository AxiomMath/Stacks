module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleBinaryProducts
public import StacksFrontier.AlgebraicGeometry.Spaces.FreeModuleSections
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.BifunctorReductionMachinery
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.LocallyFiniteTorDimension

/-!
# The tensor product of modules on the small étale site of an algebraic space

The tensor product of sheaves of modules on a ringed site is additive in each variable, and its
total complexes exist, as soon as the site has sheafification and binary biproducts of modules;
these are the instances `Stacks.SheafOfModules.Tensor.sheafTensor_additive`,
`Stacks.SheafOfModules.Tensor.sheafTensor_obj_additive` and
`Stacks.SheafOfModules.Tensor.hasMapBifunctor_sheafTensor`.  On the small étale ringed site of an
algebraic space, whose objects lie one universe above its morphisms and its sections, instance
search cannot find them: it would have to solve a `max` of universe levels before looking for
their hypotheses.  This file restates them, at the universes of the small étale ringed site and
of its slices, so that the derived tensor product of Stacks 06YU is available on `D(𝒪_X)` with
no hypothesis.

## Main definitions

* `AlgebraicGeometry.Space.smallEtaleRingedSite_sheafTensor_additive` and its companions, for
  the site and for its slices.

## References

* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat
  RingedSite.sliceHasSheafify RingedSite.sliceWEqualsLocallyBijective

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-- The modules on the small étale site of an algebraic space have binary biproducts. -/
instance smallEtaleRingedSite_hasBinaryBiproducts_modules :
    HasBinaryBiproducts (Modules.{u, u} B S hS F hF) :=
  @Abelian.hasBinaryBiproducts _ _ (SheafOfModules.instAbelian _)

/-- The tensor product of modules on the small étale site is additive in its first variable. -/
instance smallEtaleRingedSite_sheafTensor_additive :
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
      (smallEtaleRingedSite B S hS F hF).O).Additive :=
  Stacks.SheafOfModules.Tensor.sheafTensor_additive.{u + 1, u, u, u, u}
    (J := (smallEtaleRingedSite B S hS F hF).J) (smallEtaleRingedSite B S hS F hF).O

/-- The tensor product of modules on the small étale site is additive in its second variable. -/
instance smallEtaleRingedSite_sheafTensor_obj_additive (M : Modules.{u, u} B S hS F hF) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
      (smallEtaleRingedSite B S hS F hF).O).obj M).Additive :=
  Stacks.SheafOfModules.Tensor.sheafTensor_obj_additive.{u + 1, u, u, u, u}
    (J := (smallEtaleRingedSite B S hS F hF).J) (smallEtaleRingedSite B S hS F hF).O M

/-- The total tensor complexes of complexes of modules on the small étale site exist. -/
instance smallEtaleRingedSite_hasMapBifunctor_sheafTensor
    (K L : CochainComplex (Modules.{u, u} B S hS F hF) ℤ) :
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        (smallEtaleRingedSite B S hS F hF).O) (ComplexShape.up ℤ) :=
  Stacks.SheafOfModules.Tensor.hasMapBifunctor_sheafTensor
    (J := (smallEtaleRingedSite B S hS F hF).J) (smallEtaleRingedSite B S hS F hF).O K L

/-- The modules on a slice of the small étale site form an abelian category, at the spelling of
the localized ringed site. -/
instance (priority := high) smallEtaleRingedSite_over_abelian
    (U : (smallEtaleRingedSite B S hS F hF).C) :
    Abelian (RingedSite.Modules.{u + 1, u, u} ((smallEtaleRingedSite B S hS F hF).over U)) :=
  SheafOfModules.instAbelian _

/-- The modules on a slice of the small étale site form an abelian category, at the spelling
`(ringSheaf 𝒪).over U` of the slice of the structure sheaf. -/
instance (priority := high) smallEtaleRingedSite_over_abelian'
    (U : (smallEtaleRingedSite B S hS F hF).C) :
    Abelian (SheafOfModules.{u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O).over U)) :=
  SheafOfModules.instAbelian _

/-- The modules on a slice of the small étale site form an abelian category, at the spelling
`ringSheaf (𝒪.over U)` of the slice of the structure sheaf. -/
instance (priority := high) smallEtaleRingedSite_over_abelian''
    (U : (smallEtaleRingedSite B S hS F hF).C) :
    Abelian (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf ((smallEtaleRingedSite B S hS F hF).O.over U))) :=
  SheafOfModules.instAbelian _

/-- The modules on a slice of the small étale site have binary biproducts. -/
instance smallEtaleRingedSite_over_hasBinaryBiproducts_modules
    (U : (smallEtaleRingedSite B S hS F hF).C) :
    HasBinaryBiproducts
      (RingedSite.Modules.{u + 1, u, u} ((smallEtaleRingedSite B S hS F hF).over U)) :=
  @Abelian.hasBinaryBiproducts _ _ (SheafOfModules.instAbelian _)

/-- The tensor product of modules on a slice of the small étale site is additive in its first
variable. -/
instance smallEtaleRingedSite_over_sheafTensor_additive
    (U : (smallEtaleRingedSite B S hS F hF).C) :
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
      ((smallEtaleRingedSite B S hS F hF).over U).O).Additive :=
  Stacks.SheafOfModules.Tensor.sheafTensor_additive.{u + 1, u, u, u, u}
    (J := ((smallEtaleRingedSite B S hS F hF).over U).J)
    ((smallEtaleRingedSite B S hS F hF).over U).O

/-- The tensor product of modules on a slice of the small étale site is additive in its second
variable. -/
instance smallEtaleRingedSite_over_sheafTensor_obj_additive
    (U : (smallEtaleRingedSite B S hS F hF).C)
    (M : RingedSite.Modules.{u + 1, u, u} ((smallEtaleRingedSite B S hS F hF).over U)) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
      ((smallEtaleRingedSite B S hS F hF).over U).O).obj M).Additive :=
  Stacks.SheafOfModules.Tensor.sheafTensor_obj_additive.{u + 1, u, u, u, u}
    (J := ((smallEtaleRingedSite B S hS F hF).over U).J)
    ((smallEtaleRingedSite B S hS F hF).over U).O M

/-- The total tensor complexes of complexes of modules on a slice of the small étale site
exist. -/
instance smallEtaleRingedSite_over_hasMapBifunctor_sheafTensor
    (U : (smallEtaleRingedSite B S hS F hF).C)
    (K L : CochainComplex
      (RingedSite.Modules.{u + 1, u, u} ((smallEtaleRingedSite B S hS F hF).over U)) ℤ) :
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        ((smallEtaleRingedSite B S hS F hF).over U).O) (ComplexShape.up ℤ) :=
  Stacks.SheafOfModules.Tensor.hasMapBifunctor_sheafTensor
    (J := ((smallEtaleRingedSite B S hS F hF).over U).J)
    ((smallEtaleRingedSite B S hS F hF).over U).O K L

/-- The tensor product of modules on a slice of the small étale site is additive in its first
variable, at the spelling `𝒪.over U` of the slice of the structure sheaf. -/
instance smallEtaleRingedSite_O_over_sheafTensor_additive
    (U : (smallEtaleRingedSite B S hS F hF).C) :
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
      ((smallEtaleRingedSite B S hS F hF).O.over U)).Additive :=
  smallEtaleRingedSite_over_sheafTensor_additive B S hS F hF U

/-- The tensor product of modules on a slice of the small étale site is additive in its second
variable, at the spelling `𝒪.over U`. -/
instance smallEtaleRingedSite_O_over_sheafTensor_obj_additive
    (U : (smallEtaleRingedSite B S hS F hF).C)
    (M : SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf ((smallEtaleRingedSite B S hS F hF).O.over U))) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
      ((smallEtaleRingedSite B S hS F hF).O.over U)).obj M).Additive :=
  smallEtaleRingedSite_over_sheafTensor_obj_additive B S hS F hF U M

/-- The total tensor complexes on a slice of the small étale site exist, at the spelling
`𝒪.over U`. -/
instance smallEtaleRingedSite_O_over_hasMapBifunctor_sheafTensor
    (U : (smallEtaleRingedSite B S hS F hF).C)
    (K L : CochainComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf ((smallEtaleRingedSite B S hS F hF).O.over U))) ℤ) :
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        ((smallEtaleRingedSite B S hS F hF).O.over U)) (ComplexShape.up ℤ) :=
  smallEtaleRingedSite_over_hasMapBifunctor_sheafTensor B S hS F hF U K L

end AlgebraicGeometry.Space

end
