module

public import StacksFrontier.Homology.DerivedIndexing.SingleDegreeUnit
public import StacksFrontier.AlgebraicGeometry.HigherDirectImage.RightDerivedPlus

/-!
# `R ⁰F = F` through the canonical map `(F X)[0] ⟶ RF(X[0])`

For a left exact functor `F`, the identification `R ⁰F ≅ F` of
`Stacks.RightDerivedPlus.rightDerivedPlusZeroIso` is, in the direction `F ⟶ R ⁰F`, the degree-zero
cohomology of the canonical map `(F X)[0] ⟶ RF(X[0])` of
`Stacks.DerivedIndexing.rightDerivedPlusUnitSingle`, read through `H ⁰((F X)[0]) = F X`.

## Main results

* `Stacks.DerivedIndexing.rightDerivedPlusZeroIso_inv_app`: the identification of `F` with
  `R ⁰F` is `H ⁰` of the canonical map.
-/

@[expose] public noncomputable section

open CategoryTheory Category Limits

namespace Stacks.DerivedIndexing

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D] (F : C ⥤ D)
  [F.Additive]

/-- Identity morphisms cancelled out of a composite, the one that is not syntactically an
identity given as a hypothesis. -/
theorem ids_comp_eq {E : Type*} [Category* E] {a c : E} (m : a ⟶ c) (i : c ⟶ c)
    (hi : i = 𝟙 c) : ((((((𝟙 a ≫ 𝟙 a) ≫ m) ≫ i) ≫ 𝟙 c) ≫ 𝟙 c) ≫ 𝟙 c) = m := by
  subst hi
  simp

/-- The comparison of the single functors into the bounded below homotopy categories with `F`
is the class of `HomologicalComplex.singleMapHomologicalComplex`. -/
theorem ι_map_mapHomotopyCategoryPlusSingleFunctor_inv_app (X : C) :
    (HomotopyCategory.Plus.ι D).map
        ((Functor.mapHomotopyCategoryPlusSingleFunctor F 0).inv.app X) =
      (HomotopyCategory.quotient D (ComplexShape.up ℤ)).map
        ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).inv.app X) := by
  rw [Functor.mapHomotopyCategoryPlusSingleFunctor, Functor.fullyFaithfulCancelRight_inv_app,
    Functor.map_preimage]
  simp only [Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.isoWhiskerLeft_inv,
    Functor.isoWhiskerRight_inv, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    mapHomotopyCategorySingleFunctor_inv_app]
  exact ids_comp_eq _ _ (CategoryTheory.Functor.map_id _ _)

variable [HasDerivedCategory C] [HasDerivedCategory D]

omit [HasDerivedCategory C] in
/-- The comparison of `(F X)[0]` with the image of `X[0]` under `F` in `D⁺`, through the bounded
below homotopy category. -/
theorem mapSingleFunctorCompQhIso_inv_app_eq' (X : C) :
    (Functor.mapSingleFunctorCompQhIso F).inv.app X =
      (Functor.singleFunctorPlusIsoCompQh (A := D) 0).hom.app (F.obj X) ≫
        DerivedCategory.Plus.Qh.map
          ((Functor.mapHomotopyCategoryPlusSingleFunctor F 0).inv.app X) :=
  DerivedCategory.Plus.ι.map_injective (by
    rw [ι_map_mapSingleFunctorCompQhIso_inv_app, Functor.map_comp,
      ι_map_singleFunctorPlusIsoCompQh_hom_app 0 (F.obj X), ι_map_Plus_Qh_map,
      ι_map_mapHomotopyCategoryPlusSingleFunctor_inv_app]
    rfl)

variable [EnoughInjectives C] [PreservesFiniteLimits F]

/-- **`F ⟶ R ⁰F` is `H ⁰` of the canonical map `(F X)[0] ⟶ RF(X[0])`.** -/
theorem rightDerivedPlusZeroIso_inv_app (X : C) :
    (Stacks.RightDerivedPlus.rightDerivedPlusZeroIso F).inv.app X =
      (DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso (C := D) 0).inv.app (F.obj X) ≫
        (DerivedCategory.Plus.homologyFunctor D 0).map ((rightDerivedPlusUnitSingle F).app X) := by
  have e₁ : (Functor.rightDerivedZeroSourceIso F).inv.app X =
      (DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso (C := D) 0).inv.app (F.obj X) ≫
        (DerivedCategory.Plus.homologyFunctor D 0).map
          ((Functor.singleFunctorPlusIsoCompQh (A := D) 0).hom.app (F.obj X) ≫
            DerivedCategory.Plus.Qh.map
              ((Functor.mapHomotopyCategoryPlusSingleFunctor F 0).inv.app X)) := by
    simp [Functor.rightDerivedZeroSourceIso]
  have e₃ : (Stacks.RightDerivedPlus.unitTargetIso (A := C) F.rightDerivedFunctorPlus).hom.app X =
      (DerivedCategory.Plus.homologyFunctor D 0).map
        (F.rightDerivedFunctorPlus.map
          ((Functor.singleFunctorPlusIsoCompQh (A := C) 0).inv.app X)) := by
    simp [Stacks.RightDerivedPlus.unitTargetIso]
  refine (show (Stacks.RightDerivedPlus.rightDerivedPlusZeroIso F).inv.app X =
    (Functor.rightDerivedZeroSourceIso F).inv.app X ≫
      (DerivedCategory.Plus.homologyFunctor D 0).map
        (F.rightDerivedFunctorPlusUnith.app ((HomotopyCategory.Plus.singleFunctor C 0).obj X)) ≫
      (Stacks.RightDerivedPlus.unitTargetIso (A := C) F.rightDerivedFunctorPlus).hom.app X
    from by
      unfold Stacks.RightDerivedPlus.rightDerivedPlusZeroIso
      exact Eq.trans (congrArg (fun e : F.rightDerivedPlus 0 ≅ F => e.inv.app X) rfl)
        (Category.assoc _ _ _)).trans ?_
  rw [e₁, e₃, show (rightDerivedPlusUnitSingle F).app X =
      (Functor.mapSingleFunctorCompQhIso F).inv.app X ≫
        F.rightDerivedFunctorPlusUnith.app ((HomotopyCategory.Plus.singleFunctor C 0).obj X) ≫
          F.rightDerivedFunctorPlus.map
            ((Functor.singleFunctorPlusIsoCompQh (A := C) 0).inv.app X) from rfl,
    mapSingleFunctorCompQhIso_inv_app_eq', assoc,
    ← Functor.map_comp, ← Functor.map_comp, assoc]

end Stacks.DerivedIndexing
