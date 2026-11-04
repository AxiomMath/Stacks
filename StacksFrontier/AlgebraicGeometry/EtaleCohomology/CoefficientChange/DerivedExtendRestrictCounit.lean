module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CoefficientChange.ComparisonLeftEqComparison
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CoefficientChange.DerivedExtensionOfScalars

/-!
# The derived extension-restriction adjunction on complexes

For `φ : Λ₁ → Λ₂` and a scheme `X`, this file computes on complexes two pieces of the derived
adjunction `- ⊗^L_{Λ₁} Λ₂ ⊣ res_φ` on étale sheaves of modules: its counit at the class of a
complex of `Λ₂`-modules, through the counit of the adjunction on homotopy categories, and the
isomorphism `res(E ⊗^L_{Λ₁} Λ₂) ≅ E ⊗^L_{Λ₁} Λ̲₂` at the class of a complex K-flat in the left
variable of the tensor product.
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

/-- A natural transformation obtained as a preimage along precomposition with `L` has, at an
object `L.obj K`, the component of the transformation it is a preimage of. -/
theorem whiskeringLeft_preimage_app {C D E : Type*} [Category C] [Category D] [Category E]
    {L : C ⥤ D} (FF : ((Functor.whiskeringLeft C D E).obj L).FullyFaithful) {G H : D ⥤ E}
    (θ : L ⋙ G ⟶ L ⋙ H) (K : C) : (FF.preimage θ).app (L.obj K) = θ.app K :=
  NatTrans.congr_app (FF.map_preimage θ) K

/-- **The counit of derived extension of coefficients against restriction**, on the class of a
complex of `Λ₂`-modules: the derived counit precomposed with the comparison
`res(Qh K) ≅ Qh(res K)` is the counit of the derived extension of coefficients at `res K`
followed by the counit of the adjunction on homotopy categories. -/
theorem etaleModuleDerivedExtendRestrictAdj_counit_fac
    (K : HomotopyCategory (EtaleModules.{u, r} Λ₂ X) (ComplexShape.up ℤ)) :
    (etaleModuleDerivedExtendScalars.{u, r} φ X).map
        ((etaleModuleRestrictScalarsUniv.{u, r} φ X).mapDerivedCategoryFactorsh.inv.app K) ≫
      (etaleModuleDerivedExtendRestrictAdj.{u, r} φ X).counit.app (DerivedCategory.Qh.obj K) =
    (etaleModuleDerivedExtendScalarsCounit.{u, r} φ X).app
        (((etaleModuleRestrictScalarsUniv.{u, r} φ X).mapHomotopyCategory
          (ComplexShape.up ℤ)).obj K) ≫
      DerivedCategory.Qh.map (((etaleModuleExtendRestrictAdj.{u, r} φ X).mapHomotopyCategory
        (ComplexShape.up ℤ)).counit.app K) := by
  let W₂ := HomotopyCategory.quasiIso (EtaleModules.{u, r} Λ₂ X) (ComplexShape.up ℤ)
  let LF := etaleModuleDerivedExtendScalars.{u, r} φ X
  let RG := etaleModuleDerivedRestrictScalars.{u, r} φ X
  let e := (etaleModuleRestrictScalarsUniv.{u, r} φ X).mapDerivedCategoryFactorsh
  have : RG.IsRightDerivedFunctor e.inv W₂ :=
    Functor.isRightDerivedFunctor_of_inverts W₂ RG e
  have : (RG ⋙ LF).IsRightDerivedFunctor
      (Functor.whiskerRight e.inv LF ≫ (Functor.associator _ _ _).hom) W₂ :=
    Functor.isRightDerivedFunctor_of_inverts W₂ (RG ⋙ LF)
      ((Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight e LF)
  have h : (etaleModuleDerivedExtendRestrictAdj.{u, r} φ X).counit =
      ((etaleModuleExtendRestrictAdj.{u, r} φ X).mapHomotopyCategory (ComplexShape.up ℤ)).derivedε
        W₂ (etaleModuleDerivedExtendScalarsCounit.{u, r} φ X) e.inv := rfl
  rw [h]
  exact Adjunction.derivedε_fac_app _ _ _ _ K

/-- The derived extension-restriction isomorphism `res(E ⊗^L_{Λ₁} Λ₂) ≅ E ⊗^L_{Λ₁} Λ̲₂` at the
class of a complex `P` which is K-flat in the left variable: the derived counit at `P`, the
identification of `res(P ⊗_{Λ₁} Λ₂)` with `P ⊗_{Λ₁} Λ̲₂` on complexes, and the one-sided
comparison `comparisonLeftFac` read backwards. -/
theorem etaleModuleDerivedExtendRestrictScalarsIso_hom_app_kFlatLeft
    (P : CochainComplex (EtaleModules.{u, r} Λ₁ X) ℤ)
    (hP : kFlatObjectsLeft (etaleModuleTensor.{u, r} Λ₁ X)
      ((HomotopyCategory.quotient _ _).obj P)) :
    (etaleModuleDerivedExtendRestrictScalarsIso.{u, r} φ X).hom.app
        ((kFlatQLeft (etaleModuleTensor.{u, r} Λ₁ X)).obj
          ⟨(HomotopyCategory.quotient _ _).obj P, hP⟩) =
      (etaleModuleDerivedRestrictScalars.{u, r} φ X).map
          ((etaleModuleDerivedExtendScalarsCounit.{u, r} φ X).app
            ((HomotopyCategory.quotient _ _).obj P)) ≫
        (etaleModuleExtendScalarsRestrictComplexIso.{u, r} φ X).hom.app P ≫
        (tensorCoefficientSheafComplexIso.{u, r} φ X).inv.app P ≫
        ((comparisonLeftFac (etaleModuleTensor.{u, r} Λ₁ X)).inv.app
          (coefficientSheafComplex.{u, r} φ X)).app
          ⟨(HomotopyCategory.quotient _ _).obj P, hP⟩ := by
  rw [etaleModuleDerivedExtendRestrictScalarsIso, Functor.FullyFaithful.preimageIso_hom,
    whiskeringLeft_preimage_app]
  simp only [Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, asIso_hom, Functor.whiskerLeft_app, Iso.app_inv, Iso.trans_inv,
    Category.id_comp, Category.assoc]
  simp only [Functor.whiskerLeft_app, comparisonLeftFac, Iso.trans_inv, NatTrans.comp_app,
    Functor.isoWhiskerLeft_inv, ObjectProperty.ι_obj]
  have h₀ : ((kFlatObjectsLeft (etaleModuleTensor.{u, r} Λ₁ X)).ι.isoWhiskerLeft
      (Quotient.natIsoLift (homotopic (EtaleModules.{u, r} Λ₁ X) (ComplexShape.up ℤ))
        (etaleModuleExtendScalarsRestrictComplexIso.{u, r} φ X ≪≫
          (tensorCoefficientSheafComplexIso.{u, r} φ X).symm))).hom.app
        ⟨(HomotopyCategory.quotient _ _).obj P, hP⟩ =
      (etaleModuleExtendScalarsRestrictComplexIso.{u, r} φ X).hom.app P ≫
        (tensorCoefficientSheafComplexIso.{u, r} φ X).inv.app P := rfl
  rw [h₀, Category.assoc]

end Stacks.EtaleCohomology

end
