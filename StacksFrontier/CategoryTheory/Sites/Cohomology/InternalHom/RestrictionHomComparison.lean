module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.MonoidalHomComparison
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.DerivedRestrictionMonoidal
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedHomRestriction
public import StacksFrontier.CategoryTheory.Sites.Modules.ExtensionByZeroUnitIso

/-!
# Restriction to a slice commutes with the derived internal Hom, as a monoidal comparison

Let `(C, O)` be a ringed site and `U` an object of `C`. Restriction to the localized site `C/U`
is a monoidal functor `ρ : D(O) ⥤ D(O|_U)` (`Stacks.Cohomology.DerivedRestriction`), so it
carries the comparison `ρ RSheafHom(A, B) ⟶ RSheafHom(ρ A, ρ B)` of
`AlgebraicGeometry.RingedSite.homComparisonMonoidal`. This file proves that the comparison is an
isomorphism when `U` is subterminal, which is the case of every open of a topological space and
the one the locality arguments of Stacks 08JP need.

The argument is the projection formula: restriction has the exact left adjoint `j_!` of
Stacks 08FJ, which is fully faithful over a subterminal object, and `ρ` kills `RSheafHom(A, C)`
whenever it kills `C`, by Stacks 08DL. So the projection maps `j_!(W ⊗ ρ A) ⟶ j_! W ⊗ A` are
isomorphisms (`Transpose.isIso_projectionMap_of_isIso_unit`) and the comparison is invertible
(`Transpose.isIso_homComparison_of_isIso_projectionMap`), both in the namespace
`Stacks.Cohomology.DerivedInternalHomPullback`.

## Main results

* `AlgebraicGeometry.RingedSite.isIso_derivedExtensionByZeroRestrictionAdjunction_unit`: over a
  subterminal object the unit of the derived adjunction `Rj_! ⊣ ρ` of Stacks 08FJ is an
  isomorphism.
* `AlgebraicGeometry.RingedSite.isZero_derivedSheafHom_of_isZero`: `RSheafHom(A, 0) = 0`.
* `AlgebraicGeometry.RingedSite.isIso_homComparisonMonoidal_restriction`: the comparison of
  restriction to a subterminal object with the derived internal Hom is an isomorphism.

## References

* [Stacks Project, Tag 08DL](https://stacks.math.columbia.edu/tag/08DL)
* [Stacks Project, Tag 08FJ](https://stacks.math.columbia.edu/tag/08FJ)
* [Stacks Project, Tag 03DI](https://stacks.math.columbia.edu/tag/03DI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Prod
open Stacks.Cohomology.DerivedInternalHomPullback

namespace AlgebraicGeometry.RingedSite

universe u

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal
attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat

section LocalizedUnit

variable {A B : Type*} [Category A] [Abelian A] [Category B] [Abelian B]
  [HasDerivedCategory A] [HasDerivedCategory B]
  {F : A ⥤ B} {G : B ⥤ A} [F.Additive] [G.Additive] (adj : F ⊣ G)
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]

/-- **The derived adjunction of an adjunction of exact functors has invertible unit when the
underived one does.** Its unit at the class of a complex is the class of the degreewise unit,
followed by isomorphisms. -/
theorem isIso_localization_unit_of_isIso (hu : IsIso adj.unit) :
    letI : CatCommSq (F.mapHomologicalComplex (ComplexShape.up ℤ))
        DerivedCategory.Q DerivedCategory.Q F.mapDerivedCategory :=
      ⟨F.mapDerivedCategoryFactors.symm⟩
    letI : CatCommSq (G.mapHomologicalComplex (ComplexShape.up ℤ))
        DerivedCategory.Q DerivedCategory.Q G.mapDerivedCategory :=
      ⟨G.mapDerivedCategoryFactors.symm⟩
    IsIso ((adj.mapHomologicalComplex (ComplexShape.up ℤ)).localization
      DerivedCategory.Q (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ))
      DerivedCategory.Q (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ))
      F.mapDerivedCategory G.mapDerivedCategory).unit := by
  let : CatCommSq (F.mapHomologicalComplex (ComplexShape.up ℤ))
      DerivedCategory.Q DerivedCategory.Q F.mapDerivedCategory :=
    ⟨F.mapDerivedCategoryFactors.symm⟩
  let : CatCommSq (G.mapHomologicalComplex (ComplexShape.up ℤ))
      DerivedCategory.Q DerivedCategory.Q G.mapDerivedCategory :=
    ⟨G.mapDerivedCategoryFactors.symm⟩
  rw [NatTrans.isIso_iff_isIso_app]
  intro K
  refine (NatTrans.isIso_app_iff_of_iso _ (DerivedCategory.Q.objObjPreimageIso K)).1 ?_
  rw [Adjunction.localization_unit_app]
  have hc : IsIso ((adj.mapHomologicalComplex (ComplexShape.up ℤ)).unit.app
      (DerivedCategory.Q.objPreimage K)) := by
    have : ∀ n, IsIso (((adj.mapHomologicalComplex (ComplexShape.up ℤ)).unit.app
        (DerivedCategory.Q.objPreimage K)).f n) := fun n => by
      simp only [Adjunction.mapHomologicalComplex, Adjunction.mkOfUnitCounit_unit,
        NatTrans.mapHomologicalComplex_app_f]
      infer_instance
    exact HomologicalComplex.Hom.isIso_of_components _
  infer_instance

end LocalizedUnit

section Unit

variable (X : RingedSite.{u, u, u}) (U : X.C)
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (X.J.over U) AddCommGrpCat.{u}]
  [(X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **Over a subterminal object the unit of `Rj_! ⊣ ρ` is an isomorphism.** The derived
adjunction of Stacks 08FJ is the localization of the degreewise one, whose unit is an
isomorphism by `Stacks.SheafOfModules.ExtensionByZero.isIso_extensionByZeroAdjunction_unit`. -/
theorem isIso_derivedExtensionByZeroRestrictionAdjunction_unit [HasBinaryProducts X.C]
    [IsIso (Over.forgetAdjStar U).unit] :
    IsIso (Stacks.Cohomology.Localization.derivedExtensionByZeroRestrictionAdjunction X U).unit :=
  isIso_localization_unit_of_isIso _
    (Stacks.SheafOfModules.ExtensionByZero.isIso_extensionByZeroAdjunction_unit X U)

end Unit

section Zero

variable (Z : RingedSite.{u, u, u})
  [HasSheafify Z.J AddCommGrpCat.{u}] [Z.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Z.O)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor Z.O)
      (ComplexShape.up ℤ)]

/-- **The derived internal Hom into a zero object is zero**: its identity and its zero
endomorphism have the same transpose under Stacks 08J8, a morphism into a zero object. -/
theorem isZero_derivedSheafHom_of_isZero
    (B C : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)))
    (hC : IsZero C) : IsZero (((derivedSheafHomBifunctor Z).obj (op B)).obj C) := by
  rw [IsZero.iff_id_eq_zero]
  exact (monoidalCurryEquiv Z _ B C).injective (hC.eq_of_tgt _ _)

end Zero

section Adjoint

variable {X Y : RingedSite.{u, u, u}}
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Y.O)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor Y.O)
      (ComplexShape.up ℤ)]

/-- **A monoidal triangulated functor with a fully faithful left adjoint commutes with the
derived internal Hom**, as soon as it kills `RSheafHom(A, C)` whenever it kills `C`: the
projection maps are then invertible, and with them the comparison. -/
theorem isIso_homComparisonMonoidal_of_adjunction
    (P : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⥤
      DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
    [P.Monoidal] [P.CommShift ℤ] [P.IsTriangulated]
    {L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ⥤
      DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (adj : L ⊣ P) (hunit : IsIso adj.unit)
    (hker : ∀ A C : DerivedCategory (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O)),
      IsZero (P.obj C) → IsZero (P.obj (((derivedSheafHomBifunctor X).obj (op A)).obj C)))
    (A B : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    IsIso (homComparisonMonoidal P A B) :=
  Transpose.isIso_homComparison_of_isIso_projectionMap P
    (derivedSheafHomBifunctor X) (derivedSheafHomBifunctor Y) (monoidalTensorPair X)
    (monoidalTensorPair Y) (monoidalCurryEquiv X) (monoidalCurryEquiv Y)
    (monoidalTensorIso P) adj (monoidalCurryEquiv_naturalLeft X)
    (monoidalCurryEquiv_naturalLeft Y) A B
    (fun W => Transpose.isIso_projectionMap_of_isIso_unit P (derivedSheafHomBifunctor X)
      (monoidalTensorPair X) (monoidalTensorPair Y) (monoidalCurryEquiv X)
      (monoidalTensorIso P) adj hunit hker W A)

end Adjoint

section Comparison

variable (X : RingedSite.{u, u, u}) (U : X.C)
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (X.J.over U) AddCommGrpCat.{u}]
  [(X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (X.over U).O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (X.over U).O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} (X.over U).O)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂
      (Stacks.SheafOfModules.Tensor.sheafTensor (X.over U).O) (ComplexShape.up ℤ)]

/-- **Restriction to a subterminal object commutes with the derived internal Hom**: the
comparison `ρ RSheafHom(A, B) ⟶ RSheafHom(ρ A, ρ B)` of the monoidal functor `ρ` is an
isomorphism. -/
theorem isIso_homComparisonMonoidal_restriction [HasBinaryProducts X.C]
    [IsIso (Over.forgetAdjStar U).unit]
    (A B : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    letI := Stacks.Cohomology.DerivedRestriction.mapDerivedCategoryMonoidal X U
    IsIso (homComparisonMonoidal (Y := X.over U)
      (Stacks.DerivedTensor.ExtensionByZero.restriction X U).mapDerivedCategory A B) := by
  let := Stacks.Cohomology.DerivedRestriction.mapDerivedCategoryMonoidal X U
  exact isIso_homComparisonMonoidal_of_adjunction (Y := X.over U)
    (Stacks.DerivedTensor.ExtensionByZero.restriction X U).mapDerivedCategory
    (Stacks.Cohomology.Localization.derivedExtensionByZeroRestrictionAdjunction X U)
    (isIso_derivedExtensionByZeroRestrictionAdjunction_unit X U)
    (fun A' C hC => IsZero.of_iso (isZero_derivedSheafHom_of_isZero (X.over U) _ _ hC)
      ((derivedHomRestriction X U).iso A' C)) A B

end Comparison

end AlgebraicGeometry.RingedSite

end
