module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CoefficientChange.DerivedExtendRestrictCounit

/-!
# The derived counit of extension of coefficients on complexes

For `φ : Λ₁ → Λ₂`, a scheme `X`, a complex `J` of étale sheaves of `Λ₂`-modules and a map
`p : P ⟶ res J` of complexes of `Λ₁`-modules, this file computes the counit of the derived
adjunction `- ⊗^L_{Λ₁} Λ₂ ⊣ res_φ` at `Q J`, precomposed with the class of `p`: it is the counit
of derived extension of coefficients at `P` followed by the class of `ext(p)` and the counit of
the adjunction on complexes.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open CochainComplex.KFlatBifunctor

attribute [local instance] HasDerivedCategory.standard

universe u r

namespace Stacks.EtaleCohomology

attribute [local instance] etaleModuleMonoidalCategory etaleModuleBraidedCategory

/- The instance proofs `F.Additive`, `(F.obj X).Additive` and `HasMapBifunctor` for the tensor
product over `Λ₁` are the named ones of `ModuleTensor.TensorBifunctorInstances`, stated as
`etaleModuleDerivedTensor` records them, so that every `derivedBifunctor (etaleModuleTensor Λ₁ X)`
written here is the unfolding of `etaleModuleDerivedTensor Λ₁ X` up to proofs of the same
propositions; with independently synthesized proofs the kernel compares the two by evaluating the
derived bifunctor, which is prohibitively slow. -/
attribute [local instance high] etaleModuleTensor_additive etaleModuleTensor_obj_additive
  etaleModuleTensor_hasTotal_mapBifunctor

variable {Λ₁ Λ₂ : Type r} [CommRing Λ₁] [CommRing Λ₂] (φ : Λ₁ →+* Λ₂) (X : Scheme.{u})

/-- The class of `ext(p)` followed by the homotopy-category counit is the class of `ext(p)`
followed by the counit of the adjunction on complexes, moved to the derived category. -/
private theorem etaleModuleExtendScalars_mapHomotopyCategory_counit_Qh
    (J : CochainComplex (EtaleModules.{u, r} Λ₂ X) ℤ)
    {P : CochainComplex (EtaleModules.{u, r} Λ₁ X) ℤ}
    (p : P ⟶ ((etaleModuleRestrictScalarsUniv.{u, r} φ X).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj J) :
    DerivedCategory.Qh.map (((etaleModuleExtendScalarsUniv.{u, r} φ X).mapHomotopyCategory
        (ComplexShape.up ℤ)).map
        ((HomotopyCategory.quotient (EtaleModules.{u, r} Λ₁ X) (ComplexShape.up ℤ)).map p ≫
          ((etaleModuleRestrictScalarsUniv.{u, r} φ X).mapHomotopyCategoryFactors
            (ComplexShape.up ℤ)).inv.app J)) ≫
      DerivedCategory.Qh.map (((etaleModuleExtendRestrictAdj.{u, r} φ X).mapHomotopyCategory
        (ComplexShape.up ℤ)).counit.app
          ((HomotopyCategory.quotient (EtaleModules.{u, r} Λ₂ X) (ComplexShape.up ℤ)).obj J)) ≫
        (DerivedCategory.quotientCompQhIso (EtaleModules.{u, r} Λ₂ X)).hom.app J =
      (DerivedCategory.quotientCompQhIso (EtaleModules.{u, r} Λ₂ X)).hom.app
          (((etaleModuleExtendScalarsUniv.{u, r} φ X).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P) ≫
        DerivedCategory.Q.map
          (((etaleModuleExtendScalarsUniv.{u, r} φ X).mapHomologicalComplex
            (ComplexShape.up ℤ)).map p ≫
            (NatTrans.mapHomologicalComplex (etaleModuleExtendRestrictAdj.{u, r} φ X).counit
              (ComplexShape.up ℤ)).app J) := by
  let Jh := (HomotopyCategory.quotient (EtaleModules.{u, r} Λ₂ X) (ComplexShape.up ℤ)).obj J
  have hi : ((etaleModuleRestrictScalarsUniv.{u, r} φ X).mapHomotopyCategoryFactors
      (ComplexShape.up ℤ)).inv.app J = 𝟙 _ := Quotient.lift.isLift_inv _ _ _ J
  have h1 : ((etaleModuleExtendScalarsUniv.{u, r} φ X).mapHomotopyCategory
        (ComplexShape.up ℤ)).map
        ((HomotopyCategory.quotient (EtaleModules.{u, r} Λ₁ X) (ComplexShape.up ℤ)).map p ≫
          ((etaleModuleRestrictScalarsUniv.{u, r} φ X).mapHomotopyCategoryFactors
            (ComplexShape.up ℤ)).inv.app J) ≫
      ((etaleModuleExtendRestrictAdj.{u, r} φ X).mapHomotopyCategory
        (ComplexShape.up ℤ)).counit.app Jh =
      (HomotopyCategory.quotient (EtaleModules.{u, r} Λ₂ X) (ComplexShape.up ℤ)).map
        (((etaleModuleExtendScalarsUniv.{u, r} φ X).mapHomologicalComplex
            (ComplexShape.up ℤ)).map p ≫
          (NatTrans.mapHomologicalComplex (etaleModuleExtendRestrictAdj.{u, r} φ X).counit
            (ComplexShape.up ℤ)).app J) := by
    have h3 : ((etaleModuleExtendScalarsUniv.{u, r} φ X).mapHomotopyCategory
          (ComplexShape.up ℤ)).map
        (((etaleModuleRestrictScalarsUniv.{u, r} φ X).mapHomotopyCategoryFactors
          (ComplexShape.up ℤ)).inv.app J) ≫
        ((etaleModuleExtendRestrictAdj.{u, r} φ X).mapHomotopyCategory
          (ComplexShape.up ℤ)).counit.app Jh =
        ((etaleModuleExtendRestrictAdj.{u, r} φ X).mapHomotopyCategory
          (ComplexShape.up ℤ)).counit.app Jh := by
      rw [hi]
      exact (congrArg (· ≫ _) (CategoryTheory.Functor.map_id _ _)).trans (Category.id_comp _)
    rw [Functor.map_comp, Category.assoc, h3, Functor.map_comp]
    rfl
  rw [← Category.assoc, ← Functor.map_comp, h1]
  exact DerivedCategory.quotientCompQhIso_hom_naturality _

/-- The inverse of the comparison `Q ⋙ res ≅ res ⋙ Q` at `J`, factored through the
homotopy category. -/
private theorem etaleModuleRestrictScalars_mapDerivedCategoryFactors_inv_app
    (J : CochainComplex (EtaleModules.{u, r} Λ₂ X) ℤ) :
    (etaleModuleRestrictScalarsUniv.{u, r} φ X).mapDerivedCategoryFactors.inv.app J =
      ((DerivedCategory.quotientCompQhIso (EtaleModules.{u, r} Λ₁ X)).inv.app
          (((etaleModuleRestrictScalarsUniv.{u, r} φ X).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj J) ≫
        DerivedCategory.Qh.map
          (((etaleModuleRestrictScalarsUniv.{u, r} φ X).mapHomotopyCategoryFactors
            (ComplexShape.up ℤ)).inv.app J)) ≫
      (etaleModuleRestrictScalarsUniv.{u, r} φ X).mapDerivedCategoryFactorsh.inv.app
          ((HomotopyCategory.quotient (EtaleModules.{u, r} Λ₂ X) (ComplexShape.up ℤ)).obj J) ≫
        (etaleModuleDerivedRestrictScalars.{u, r} φ X).map
          ((DerivedCategory.quotientCompQhIso (EtaleModules.{u, r} Λ₂ X)).hom.app J) := by
  let RG := etaleModuleDerivedRestrictScalars.{u, r} φ X
  let res := etaleModuleRestrictScalarsUniv.{u, r} φ X
  let Jh := (HomotopyCategory.quotient (EtaleModules.{u, r} Λ₂ X) (ComplexShape.up ℤ)).obj J
  let ν := (DerivedCategory.quotientCompQhIso (EtaleModules.{u, r} Λ₂ X)).hom.app J
  let Y := (DerivedCategory.quotientCompQhIso (EtaleModules.{u, r} Λ₁ X)).inv.app
      ((res.mapHomologicalComplex (ComplexShape.up ℤ)).obj J) ≫
    DerivedCategory.Qh.map ((res.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).inv.app J)
  have h' : (RG.map ν ≫ res.mapDerivedCategoryFactors.hom.app J) ≫ Y =
      res.mapDerivedCategoryFactorsh.hom.app Jh := by
    rw [res.mapDerivedCategoryFactorsh_hom_app J]
    simp only [Y, Category.assoc]
    rfl
  show res.mapDerivedCategoryFactors.inv.app J =
    Y ≫ res.mapDerivedCategoryFactorsh.inv.app Jh ≫ RG.map ν
  rw [← cancel_epi (RG.map ν ≫ res.mapDerivedCategoryFactors.hom.app J),
    ← Category.assoc _ Y, h', Iso.hom_inv_id_app_assoc, Category.assoc, Iso.hom_inv_id_app]
  exact Category.comp_id _

/-- **The derived counit on the class of a complex**, against a map `p : P ⟶ res J`: extension
of coefficients of `p` followed by the derived counit at `J` is the derived counit of extension of
coefficients at `P` followed by the class of `ext(p)` and the counit of the adjunction on
complexes. -/
theorem etaleModuleDerivedExtendRestrictAdj_counit_app_Q
    (J : CochainComplex (EtaleModules.{u, r} Λ₂ X) ℤ)
    {P : CochainComplex (EtaleModules.{u, r} Λ₁ X) ℤ}
    (p : P ⟶ ((etaleModuleRestrictScalarsUniv.{u, r} φ X).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj J) :
    (etaleModuleDerivedExtendScalars.{u, r} φ X).map (DerivedCategory.Q.map p ≫
        (etaleModuleRestrictScalarsUniv.{u, r} φ X).mapDerivedCategoryFactors.inv.app J) ≫
      (etaleModuleDerivedExtendRestrictAdj.{u, r} φ X).counit.app (DerivedCategory.Q.obj J) =
      (etaleModuleDerivedExtendScalars.{u, r} φ X).map
          ((DerivedCategory.quotientCompQhIso _).inv.app P) ≫
        (etaleModuleDerivedExtendScalarsCounit.{u, r} φ X).app
          ((HomotopyCategory.quotient _ _).obj P) ≫
        (DerivedCategory.quotientCompQhIso _).hom.app
          (((etaleModuleExtendScalarsUniv.{u, r} φ X).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P) ≫
      DerivedCategory.Q.map
        (((etaleModuleExtendScalarsUniv.{u, r} φ X).mapHomologicalComplex
            (ComplexShape.up ℤ)).map p ≫
          (NatTrans.mapHomologicalComplex (etaleModuleExtendRestrictAdj.{u, r} φ X).counit
            (ComplexShape.up ℤ)).app J) := by
  let RG := etaleModuleDerivedRestrictScalars.{u, r} φ X
  let res := etaleModuleRestrictScalarsUniv.{u, r} φ X
  let Jh := (HomotopyCategory.quotient (EtaleModules.{u, r} Λ₂ X) (ComplexShape.up ℤ)).obj J
  let ν := (DerivedCategory.quotientCompQhIso (EtaleModules.{u, r} Λ₂ X)).hom.app J
  let Y := (DerivedCategory.quotientCompQhIso (EtaleModules.{u, r} Λ₁ X)).inv.app
      ((res.mapHomologicalComplex (ComplexShape.up ℤ)).obj J) ≫
    DerivedCategory.Qh.map ((res.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).inv.app J)
  have hA : res.mapDerivedCategoryFactors.inv.app J =
      Y ≫ res.mapDerivedCategoryFactorsh.inv.app Jh ≫ RG.map ν :=
    etaleModuleRestrictScalars_mapDerivedCategoryFactors_inv_app φ X J
  have hB : (etaleModuleDerivedExtendScalars.{u, r} φ X).map
        ((etaleModuleDerivedRestrictScalars.{u, r} φ X).map ν) ≫
      (etaleModuleDerivedExtendRestrictAdj.{u, r} φ X).counit.app (DerivedCategory.Q.obj J) =
      (etaleModuleDerivedExtendRestrictAdj.{u, r} φ X).counit.app (DerivedCategory.Qh.obj Jh) ≫
        ν :=
    (etaleModuleDerivedExtendRestrictAdj.{u, r} φ X).counit.naturality ν
  have hD : DerivedCategory.Q.map p ≫ Y =
      (DerivedCategory.quotientCompQhIso (EtaleModules.{u, r} Λ₁ X)).inv.app P ≫
      DerivedCategory.Qh.map
        ((HomotopyCategory.quotient (EtaleModules.{u, r} Λ₁ X) (ComplexShape.up ℤ)).map p ≫
          ((etaleModuleRestrictScalarsUniv.{u, r} φ X).mapHomotopyCategoryFactors
            (ComplexShape.up ℤ)).inv.app J) := by
    simp only [Y]
    rw [← Category.assoc, DerivedCategory.quotientCompQhIso_inv_naturality, Category.assoc,
      Functor.map_comp]
  have hE : (etaleModuleDerivedExtendScalars.{u, r} φ X).map (DerivedCategory.Qh.map
        ((HomotopyCategory.quotient (EtaleModules.{u, r} Λ₁ X) (ComplexShape.up ℤ)).map p ≫
          ((etaleModuleRestrictScalarsUniv.{u, r} φ X).mapHomotopyCategoryFactors
            (ComplexShape.up ℤ)).inv.app J)) ≫
      (etaleModuleDerivedExtendScalarsCounit.{u, r} φ X).app
        (((etaleModuleRestrictScalarsUniv.{u, r} φ X).mapHomotopyCategory
          (ComplexShape.up ℤ)).obj Jh) =
      (etaleModuleDerivedExtendScalarsCounit.{u, r} φ X).app
        ((HomotopyCategory.quotient (EtaleModules.{u, r} Λ₁ X) (ComplexShape.up ℤ)).obj P) ≫
      (etaleModuleExtendScalarsHomotopy.{u, r} φ X).map
        ((HomotopyCategory.quotient (EtaleModules.{u, r} Λ₁ X) (ComplexShape.up ℤ)).map p ≫
          ((etaleModuleRestrictScalarsUniv.{u, r} φ X).mapHomotopyCategoryFactors
            (ComplexShape.up ℤ)).inv.app J) :=
    (etaleModuleDerivedExtendScalarsCounit.{u, r} φ X).naturality _
  rw [hA, ← Category.assoc (DerivedCategory.Q.map p) Y, hD, Category.assoc,
    (etaleModuleDerivedExtendScalars.{u, r} φ X).map_comp,
    (etaleModuleDerivedExtendScalars.{u, r} φ X).map_comp,
    (etaleModuleDerivedExtendScalars.{u, r} φ X).map_comp, Category.assoc, Category.assoc,
    Category.assoc, hB, reassoc_of% (etaleModuleDerivedExtendRestrictAdj_counit_fac φ X Jh),
    reassoc_of% hE, etaleModuleExtendScalars_mapHomotopyCategory_counit_Qh φ X J p]
  rfl

end Stacks.EtaleCohomology

end
