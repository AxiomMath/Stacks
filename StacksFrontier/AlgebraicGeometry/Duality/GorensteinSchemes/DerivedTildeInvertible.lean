module

public import StacksFrontier.AlgebraicGeometry.Duality.GorensteinSchemes.DualizingInvertible
public import StacksFrontier.Homology.DerivedCategory.GrothendieckModelTargetIso
public import StacksFrontier.AlgebraicGeometry.Modules.DerivedMonoidalInstanceIndependence

/-!
# The complex associated to an invertible object of `D(R)` is invertible on `Spec R`

Let `R` be a commutative ring and `K` an invertible object of `D(R)` for the symmetric monoidal
structure of [Stacks, Tag 0FNQ]. Then the associated complex `K̃` is an invertible object of
`D(𝒪_{Spec R})` for the monoidal structure of [Stacks, Tag 0FPT].

## Main results

* `Stacks.Duality.isInvertible_canonical_of_isInvertible`: the two monoidal structures on `D(R)`
  in play, that of [Stacks, Tag 0FNQ] and its transport to an independent module universe, have the
  same invertible objects.
* `Stacks.Duality.isInvertible_derivedTilde_of_isInvertible`: the complex `K̃` associated to an
  invertible object `K` of `D(R)` is an invertible object of `D(𝒪_{Spec R})`.
* `Stacks.Duality.isInvertible_tilde_restrict_of_isInvertible`: the same transported to an affine
  open `U ≅ Spec Γ(X, U)` of a scheme, at the locally small model of `D(𝒪_U)`.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open TopologicalSpace

universe u

namespace Stacks.Duality

attribute [local instance 10000] HasDerivedCategory.standard

/-- **An invertible object of `D(R)` for the monoidal structure of [Stacks, Tag 0FNQ] is invertible
for its transport to the module universe of `R`.** -/
theorem isInvertible_canonical_of_isInvertible (R : Type u) [CommRing R]
    {K : DerivedCategory (ModuleCat.{u} R)}
    (hK : letI := (DerivedCategory.Invertible.derivedCategory_symmetricMonoidalCategory R).choose
      MonoidalCategory.IsInvertible K) :
    letI := CochainComplex.DerivedTensor.canonicalDerivedMonoidalStructure.{u, u} R
    MonoidalCategory.IsInvertible K := by
  let m₁ := (DerivedCategory.Invertible.derivedCategory_symmetricMonoidalCategory R).choose
  let m₂ := CochainComplex.DerivedTensor.canonicalDerivedMonoidalStructure.{u, u} R
  let T := CochainComplex.DerivedTensor.canonicalSymmetricDerivedTensorProduct R
  let e := (DerivedCategory.Invertible.derivedCategory_symmetricMonoidalCategory
    R).choose_spec.choose_spec.choose
  let t : ∀ A B : DerivedCategory (ModuleCat.{u} R),
      (𝟭 _).obj (@MonoidalCategoryStruct.tensorObj _ _ m₁.toMonoidalCategoryStruct A B) ≅
        @MonoidalCategoryStruct.tensorObj _ _ m₂.toMonoidalCategoryStruct ((𝟭 _).obj A)
          ((𝟭 _).obj B) := fun A B ↦
    (e.app A).app B ≪≫
      derivedTensorGeneralCompare R T.tensorProduct.toGeneral
        (CochainComplex.DerivedTensor.canonicalDerivedTensorProductGeneral.{u, u} R) A B ≪≫
      (((CochainComplex.DerivedTensor.canonicalDerivedMonoidalTensorIso.{u, u} R).app A).app
        B).symm
  let ε : (𝟭 _).obj (@MonoidalCategoryStruct.tensorUnit _ _ m₁.toMonoidalCategoryStruct) ≅
      @MonoidalCategoryStruct.tensorUnit _ _ m₂.toMonoidalCategoryStruct :=
    CochainComplex.DerivedTensor.monoidalUnitIsoSingleFunctorObj R ≪≫
      (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).mapIso
        (ULift.moduleEquiv : ULift.{u} R ≃ₗ[R] R).toModuleIso.symm ≪≫
      (CochainComplex.DerivedTensor.canonicalDerivedMonoidalUnitIso.{u, u} R).symm
  exact @isInvertible_obj_of_tensorIso _ _ _ _ m₁ m₂ (𝟭 _) t ε K hK

variable (R : CommRingCat.{u})
  [HasSheafify (Opens.grothendieckTopology (Spec R)) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology (Spec R)).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u} (Spec R).sheaf).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u} (Spec R).sheaf).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} (Spec R).sheaf)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂
      (Stacks.SheafOfModules.Tensor.sheafTensor (Spec R).sheaf) (ComplexShape.up ℤ)]

/-- **The complex associated to an invertible object of `D(R)` is an invertible object of
`D(𝒪_{Spec R})`**, for the monoidal structures of [Stacks, Tag 0FNQ] and [Stacks, Tag 0FPT]. -/
theorem isInvertible_derivedTilde_of_isInvertible {K : DerivedCategory (ModuleCat.{u} R)}
    (hK : letI := (DerivedCategory.Invertible.derivedCategory_symmetricMonoidalCategory R).choose
      MonoidalCategory.IsInvertible K) :
    @MonoidalCategory.IsInvertible _ _
      (Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal (Spec R).sheaf)
      ((derivedTildeStructureSheafModules R).obj K) := by
  let := CochainComplex.DerivedTensor.canonicalDerivedMonoidalStructure.{u, u} (R : Type u)
  let := Stacks.SheafOfModules.derivedMonoidalStructure (Spec R).sheaf
  exact @MonoidalCategory.isInvertible_of_tensorComparison_of_braided _ _
    (Stacks.SheafOfModules.derivedMonoidalStructure (Spec R).sheaf) _ _
    (Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal (Spec R).sheaf)
    (Stacks.SheafOfModules.DerivedMonoidal.derivedSymmetric (Spec R).sheaf).toBraidedCategory
    (𝟭 _)
    (fun A B ↦ (((Stacks.SheafOfModules.derivedTensorMonoidalIso (Spec R).sheaf).app A).app
      B).symm)
    (Stacks.SheafOfModules.DerivedMonoidal.canonicalUnitIso (Spec R).sheaf).symm _
    (isInvertible_obj_of_tensorIso (derivedTildeStructureSheafModules R)
      (derivedTildeTensorIsoStandard R) (derivedTildeUnitIsoStandard R)
      (isInvertible_canonical_of_isInvertible R hK))

/-- **On an affine open `U ≅ Spec Γ(X, U)` the complex associated to an invertible object of
`D(Γ(X, U))` is invertible**, read in `D(𝒪_U)` at the locally small model. -/
theorem isInvertible_tilde_restrict_of_isInvertible {X : Scheme.{u}} {U : X.Opens}
    (hU : IsAffineOpen U) {K : DerivedCategory (ModuleCat.{u} Γ(X, U))}
    (hK : letI := (DerivedCategory.Invertible.derivedCategory_symmetricMonoidalCategory
        Γ(X, U)).choose
      MonoidalCategory.IsInvertible K) :
    letI := AlgebraicGeometry.Scheme.Modules.hasDerivedCategory U.toScheme
    letI := Scheme.Modules.derivedMonoidal U.toScheme
    MonoidalCategory.IsInvertible ((tilde.functor Γ(X, U) ⋙
      Scheme.Modules.restrictFunctor hU.isoSpec.hom).mapDerivedCategory.obj K) := by
  have h := @MonoidalCategory.isInvertible_of_iso _ _
    (Scheme.Modules.derivedMonoidal U.toScheme) _ _
    ((Stacks.Cohomology.PerfectComplexTriangles.mapDerivedCategoryCompIso
      (tilde.functor Γ(X, U)) (Scheme.Modules.restrictFunctor hU.isoSpec.hom)).app K).symm
    (Stacks.SheafOfModules.PullbackIsoTensor.isInvertible_restrictFunctor hU.isoSpec.hom _
      (isInvertible_derivedTilde_of_isInvertible Γ(X, U) hK))
  exact @MonoidalCategory.isInvertible_of_iso _ _
    (@Scheme.Modules.derivedMonoidal U.toScheme
      (AlgebraicGeometry.Scheme.Modules.hasDerivedCategory U.toScheme)) _ _
    ((Stacks.Injectives.mapDerivedCategoryTargetModelIso U.toScheme.Modules
      (tilde.functor Γ(X, U) ⋙ Scheme.Modules.restrictFunctor hU.isoSpec.hom)).app K)
    ((Scheme.Modules.isInvertible_standard_iff U.toScheme _).1 h)

end Stacks.Duality

end
