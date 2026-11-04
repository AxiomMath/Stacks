module

public import StacksFrontier.AlgebraicGeometry.Quot.DerivedPullbackSectionFunctor
public import StacksFrontier.AlgebraicGeometry.Spaces.DefiningIdealBaseRingTensor
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.LimitDerivedHomUnitColimHomUnitHom
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleModelDerivedEquivalence

/-!
# The structure sheaf of the small étale site, read on the spaces-étale model

The derived equivalence `AlgebraicGeometry.Space.spacesEtaleModelDerivedEquiv`, induced by the
equivalence of module categories of Stacks 03G1, carries the structure sheaf of the spaces-étale
model, placed in degree `0`, to the structure sheaf of the small étale site placed in degree `0`,
`AlgebraicGeometry.Space.structureObject`, the first argument of the affine leaf of Stacks 09RI.
Through it, morphisms out of `AlgebraicGeometry.Space.structureObject` into the image of a point
tensor `T_ψ : M ↦ 𝒪_X ⊗_A M` are computed by maps of complexes of `A`-modules.

## Main definitions

* `AlgebraicGeometry.Space.spacesEtaleModelModulesEquivUnitIso`: **`e_X(𝒪_X) ≅ 𝒪_X`**, the
  structure sheaf of the model goes to the structure sheaf of the small étale site.
* `AlgebraicGeometry.Space.spacesEtaleModelDerivedEquivStructureObjectIso`: the same in the
  derived category, at the first argument of the affine leaf of Stacks 09RI.
* `AlgebraicGeometry.Space.structureObjectPointTensorIso`: **the first argument of the affine leaf
  of Stacks 09RI is the image of a point tensor**, namely of the one-term complex `A` in
  degree `0`, for `X ≅ h_{Spec A}`.

## Main results

* `AlgebraicGeometry.Space.exists_structureObject_pointTensor_map_eq`: **every morphism
  `𝒪_X[0] ⟶ e_X(Q(T_ψ C))` of `D(𝒪_X)` is induced by a map of complexes `A[0] ⟶ C`**, for an
  arbitrary complex `C` of `A`-modules.
* `AlgebraicGeometry.Space.structureObject_pointTensor_map_eq_iff`: **two such maps induce the
  same morphism exactly when they agree in `D(A)`.**

## References

* [Stacks Project, Tag 09RI](https://stacks.math.columbia.edu/tag/09RI)
* [Stacks Project, Tag 03G1](https://stacks.math.columbia.edu/tag/03G1)
* [Stacks Project, Tag 09RJ](https://stacks.math.columbia.edu/tag/09RJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

attribute [local instance] RingedSite.hasSheafCompose_forget₂_ringCat

attribute [local instance 10000] HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Transport

variable (X : AlgebraicSpaces B S hS)

/-- **`e_X(𝒪_X) ≅ 𝒪_X`**: the equivalence of Stacks 03G1 carries the structure sheaf of the model
of the spaces-étale site to the structure sheaf of the small étale site. -/
def spacesEtaleModelModulesEquivUnitIso :
    (spacesEtaleModelModulesEquiv B S hS X).functor.obj
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
          (spacesEtaleModelRingedTopos B S hS X).O)) ≅
      unitModule B S hS X.2 :=
  (spacesEtaleModelModulesEquiv B S hS X).functor.mapIso
      (spacesEtaleModelPointTensorObjSelfIso B S hS
        (pointRingHomOfModel B S hS (RingHom.id (modelGlobalFunctions B S hS X)))).symm ≪≫
    (pointTensorModulesEquivIso B S hS
        (spacesEtaleModelGlobalHom_pointRingHomOfModel B S hS
          (RingHom.id (modelGlobalFunctions B S hS X)))).app
      (ModuleCat.of (modelGlobalFunctions B S hS X) (modelGlobalFunctions B S hS X)) ≪≫
    asIso (baseRingTensorModuleSelfHom B S hS X (RingHom.id (modelGlobalFunctions B S hS X)))

/-- **The structure sheaf of the model, placed in degree `0`, is the first argument of the affine
leaf of Stacks 09RI** under the derived equivalence
`AlgebraicGeometry.Space.spacesEtaleModelDerivedEquiv`. -/
def spacesEtaleModelDerivedEquivStructureObjectIso :
    (spacesEtaleModelDerivedEquiv B S hS X).functor.obj
        ((DerivedCategory.singleFunctor (SheafOfModules.{u}
            (Stacks.SheafOfModules.Tensor.ringSheaf
              (spacesEtaleModelRingedTopos B S hS X).O)) 0).obj
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
            (spacesEtaleModelRingedTopos B S hS X).O))) ≅
      structureObject B S hS X :=
  letI e := spacesEtaleModelModulesEquiv B S hS X
  haveI : PreservesFiniteLimits e.functor := @PreservesLimitsOfSize.preservesFiniteLimits.{0, 0}
    _ _ _ _ _ e.symm.toAdjunction.rightAdjoint_preservesLimits
  haveI : PreservesFiniteColimits e.functor :=
    @PreservesColimitsOfSize.preservesFiniteColimits.{0, 0} _ _ _ _ _
      e.toAdjunction.leftAdjoint_preservesColimits
  haveI : PreservesBinaryBiproducts e.functor :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  haveI : e.functor.Additive := Functor.additive_of_preservesBinaryBiproducts _
  (e.functor.mapDerivedCategorySingleFunctor 0).app
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
        (spacesEtaleModelRingedTopos B S hS X).O)) ≪≫
    (DerivedCategory.singleFunctor (Modules.{u, u} B S hS X.1 X.2) 0).mapIso
      (spacesEtaleModelModulesEquivUnitIso B S hS X)

end Transport

section Affine

variable {A : Type u} [CommRing A] (hA : B.Contains (Spec (CommRingCat.of A)))
  (p : Spec (CommRingCat.of A) ⟶ S) {X : AlgebraicSpaces B S hS}
  (g : X ≅ ⟨yoneda.obj (BigFppfOver.mk B S hS hA p), isAlgebraicSpace_yoneda B S hS _⟩)

/-- **The first argument of the affine leaf of Stacks 09RI is the image of a point tensor.**  For
`X ≅ h_{Spec A}` the structure sheaf of the small étale site placed in degree `0` is the image
under `AlgebraicGeometry.Space.spacesEtaleModelDerivedEquiv` of `Q(T_ψ(A[0]))`, with
`ψ : A ≅ Γ(X, 𝒪_X)` the ring isomorphism of
`AlgebraicGeometry.Space.representedTildeOfIsoPointRingHom`. -/
def structureObjectPointTensorIso :
    structureObject B S hS X ≅
      (spacesEtaleModelDerivedEquiv B S hS X).functor.obj (DerivedCategory.Q.obj
        (((spacesEtaleModelPointTensor B S hS
          (representedTildeOfIsoPointRingHom B S hS hA p g)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj
          ((HomologicalComplex.single (ModuleCat.{u} A) (ComplexShape.up ℤ) 0).obj
            (ModuleCat.of A A)))) :=
  (spacesEtaleModelDerivedEquivStructureObjectIso B S hS X).symm ≪≫
    (spacesEtaleModelDerivedEquiv B S hS X).functor.mapIso
      (pointTensorSingleSelfIso B S hS
        (representedTildeOfIsoPointRingHom B S hS hA p g)).symm

/-- **Every morphism `𝒪_X[0] ⟶ e_X(Q(𝒪_X ⊗_A C))` of `D(𝒪_X)` is induced by a map of complexes
`A[0] ⟶ C`**, for an arbitrary complex `C` of `A`-modules. -/
theorem exists_structureObject_pointTensor_map_eq (C : CochainComplex (ModuleCat.{u} A) ℤ)
    (φ : structureObject B S hS X ⟶ (spacesEtaleModelDerivedEquiv B S hS X).functor.obj
      (DerivedCategory.Q.obj (((spacesEtaleModelPointTensor B S hS
        (representedTildeOfIsoPointRingHom B S hS hA p g)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj C))) :
    ∃ u : (HomologicalComplex.single (ModuleCat.{u} A) (ComplexShape.up ℤ) 0).obj
        (ModuleCat.of A A) ⟶ C,
      (structureObjectPointTensorIso B S hS hA p g).hom ≫
        (spacesEtaleModelDerivedEquiv B S hS X).functor.map (DerivedCategory.Q.map
          (((spacesEtaleModelPointTensor B S hS
            (representedTildeOfIsoPointRingHom B S hS hA p g)).mapHomologicalComplex
              (ComplexShape.up ℤ)).map u)) = φ := by
  have hpre := (spacesEtaleModelDerivedEquiv B S hS X).fullyFaithfulFunctor.map_preimage
    ((structureObjectPointTensorIso B S hS hA p g).inv ≫ φ)
  obtain ⟨u, hu⟩ := exists_unit_pointTensor_Q_map_eq B S hS hA p g C
    ((pointTensorSingleSelfIso B S hS
        (representedTildeOfIsoPointRingHom B S hS hA p g)).inv ≫
      (spacesEtaleModelDerivedEquiv B S hS X).fullyFaithfulFunctor.preimage
        ((structureObjectPointTensorIso B S hS hA p g).inv ≫ φ))
  refine ⟨u, ?_⟩
  rw [(cancel_epi (pointTensorSingleSelfIso B S hS
    (representedTildeOfIsoPointRingHom B S hS hA p g)).inv).1 hu, hpre, Iso.hom_inv_id_assoc]

/-- **Two maps of complexes `A[0] ⟶ C` induce the same morphism `𝒪_X[0] ⟶ e_X(Q(𝒪_X ⊗_A C))`
exactly when they agree in `D(A)`**, for an arbitrary complex `C` of `A`-modules. -/
theorem structureObject_pointTensor_map_eq_iff (C : CochainComplex (ModuleCat.{u} A) ℤ)
    (u u' : (HomologicalComplex.single (ModuleCat.{u} A) (ComplexShape.up ℤ) 0).obj
      (ModuleCat.of A A) ⟶ C) :
    (structureObjectPointTensorIso B S hS hA p g).hom ≫
        (spacesEtaleModelDerivedEquiv B S hS X).functor.map (DerivedCategory.Q.map
          (((spacesEtaleModelPointTensor B S hS
            (representedTildeOfIsoPointRingHom B S hS hA p g)).mapHomologicalComplex
              (ComplexShape.up ℤ)).map u)) =
      (structureObjectPointTensorIso B S hS hA p g).hom ≫
        (spacesEtaleModelDerivedEquiv B S hS X).functor.map (DerivedCategory.Q.map
          (((spacesEtaleModelPointTensor B S hS
            (representedTildeOfIsoPointRingHom B S hS hA p g)).mapHomologicalComplex
              (ComplexShape.up ℤ)).map u')) ↔
      DerivedCategory.Q.map u = DerivedCategory.Q.map u' := by
  rw [cancel_epi, ← unit_pointTensor_Q_map_eq_iff B S hS hA p g C u u', cancel_epi]
  exact ⟨fun h => (spacesEtaleModelDerivedEquiv B S hS X).functor.map_injective h, congrArg _⟩

end Affine

end AlgebraicGeometry.Space

end
