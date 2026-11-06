module

public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactPlusCompositionNatTrans

/-!
# The degree-zero embedding comparison of an exact functor is compatible with a composition

Let `U₁ : C₀ ⥤ C₁`, `U₂ : C₁ ⥤ C₂` and `U : C₀ ⥤ C₂` be exact additive functors of abelian
categories with derived categories, the sources of the first two having enough injectives, and
let `c : U₁ ⋙ U₂ ≅ U`. For an exact functor `F` the comparison
`Stacks.DerivedFunctor.exactSingleFunctorRightDerivedPlusIso` identifies `F(X)[0]` with
`RF(X[0])`. The comparison for `U`, precomposed with `c`, is the composite of the comparisons
for `U₁` and for `U₂`, read through the comparison `RU₁ ⋙ RU₂ ≅ RU` of
`CategoryTheory.Functor.rightDerivedFunctorPlusCompIsoOfExact`.

## Main results

* `Stacks.DerivedFunctor.mapCochainComplexSingleFunctor_comp_inv_app`: the cocycle identity
  for the degree-zero embedding of complexes,
  `CategoryTheory.Functor.mapCochainComplexSingleFunctor`.
* `Stacks.DerivedFunctor.mapDerivedCategorySingleFunctor_comp_inv_app`: the same on the unbounded
  derived category, for `CategoryTheory.Functor.mapDerivedCategorySingleFunctor` and the
  degreewise comparison of the actions.
* `Stacks.DerivedFunctor.exactMapDerivedCategoryPlusSingle_comp_inv_app`: the same on the bounded
  below derived category.
* `Stacks.DerivedFunctor.exactSingleFunctorRightDerivedPlusIso_comp`: the cocycle identity for
  the comparisons `F(X)[0] ≅ RF(X[0])`.

## References

* [Stacks Project, Tag 0EZF](https://stacks.math.columbia.edu/tag/0EZF)
* [Stacks Project, Tag 015M](https://stacks.math.columbia.edu/tag/015M)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] CategoryTheory.Limits.comp_preservesFiniteLimits
  CategoryTheory.Limits.comp_preservesFiniteColimits

universe v₀ v₁ v₂ u₀ u₁ u₂

namespace Stacks.DerivedFunctor

section Complexes

variable {C₀ : Type u₀} {C₁ : Type u₁} {C₂ : Type u₂}
  [Category.{v₀} C₀] [Category.{v₁} C₁] [Category.{v₂} C₂]
  [Abelian C₀] [Abelian C₁] [Abelian C₂]
  (U₁ : C₀ ⥤ C₁) (U₂ : C₁ ⥤ C₂) (U : C₀ ⥤ C₂)
  [U₁.Additive] [U₂.Additive] [U.Additive]
  (c : U₁ ⋙ U₂ ≅ U)

/-- **The cocycle identity for the degree-zero embedding of complexes.** The comparison
`U.mapCochainComplexSingleFunctor 0` for `U`, precomposed with `c`, is the comparison for `U₂`
followed by the image under `U₂` of the comparison for `U₁` and the action of `c`. -/
theorem mapCochainComplexSingleFunctor_comp_inv_app (Y : C₀) :
    (CochainComplex.singleFunctor C₂ 0).map (c.hom.app Y) ≫
        (U.mapCochainComplexSingleFunctor 0).inv.app Y =
      (U₂.mapCochainComplexSingleFunctor 0).inv.app (U₁.obj Y) ≫
        (U₂.mapHomologicalComplex (ComplexShape.up ℤ)).map
            ((U₁.mapCochainComplexSingleFunctor 0).inv.app Y) ≫
          (c.hom.mapHomologicalComplex (ComplexShape.up ℤ)).app
            ((CochainComplex.singleFunctor C₀ 0).obj Y) := by
  ext
  simpa [Functor.mapCochainComplexSingleFunctor, CochainComplex.singleFunctor,
    CochainComplex.singleFunctors, HomologicalComplex.single_map_f_self,
    HomologicalComplex.singleObjXSelf] using (c.hom.naturality _).symm

end Complexes

section Unbounded

variable {C₀ : Type u₀} {C₁ : Type u₁} {C₂ : Type u₂}
  [Category.{v₀} C₀] [Category.{v₁} C₁] [Category.{v₂} C₂]
  [Abelian C₀] [Abelian C₁] [Abelian C₂]
  [HasDerivedCategory C₀] [HasDerivedCategory C₁] [HasDerivedCategory C₂]
  (U₁ : C₀ ⥤ C₁) (U₂ : C₁ ⥤ C₂) (U : C₀ ⥤ C₂)
  [U₁.Additive] [U₂.Additive] [U.Additive]
  [PreservesFiniteLimits U₁] [PreservesFiniteColimits U₁]
  [PreservesFiniteLimits U₂] [PreservesFiniteColimits U₂]
  [PreservesFiniteLimits U] [PreservesFiniteColimits U]
  (c : U₁ ⋙ U₂ ≅ U)

/-- **The cocycle identity for the degree-zero embedding on the unbounded derived category.**
The comparison `U.mapDerivedCategorySingleFunctor 0` for `U`, precomposed with `c`, is the
comparison for `U₂` followed by the image under `U₂` of the comparison for `U₁` and the degreewise
comparison of the actions. -/
theorem mapDerivedCategorySingleFunctor_comp_inv_app (Y : C₀) :
    (DerivedCategory.singleFunctor C₂ 0).map (c.hom.app Y) ≫
        (U.mapDerivedCategorySingleFunctor 0).inv.app Y =
      (U₂.mapDerivedCategorySingleFunctor 0).inv.app (U₁.obj Y) ≫
        U₂.mapDerivedCategory.map ((U₁.mapDerivedCategorySingleFunctor 0).inv.app Y) ≫
          (mapDerivedCategoryCompIso U₁ U₂).hom.app
              (DerivedCategory.Q.obj
                ((HomologicalComplex.single C₀ (ComplexShape.up ℤ) 0).obj Y)) ≫
            (mapDerivedNatTrans c.hom).app
              (DerivedCategory.Q.obj
                ((HomologicalComplex.single C₀ (ComplexShape.up ℤ) 0).obj Y)) := by
  have : IsIso (U.mapDerivedCategoryFactors.hom.app
      ((HomologicalComplex.single C₀ (ComplexShape.up ℤ) 0).obj Y)) :=
    (U.mapDerivedCategoryFactors.app _).isIso_hom
  have hc₂ := congrArg U₂.mapDerivedCategory.map
    (Functor.mapDerivedCategorySingleFunctor_inv_app_mapDerivedCategoryFactors_hom_app U₁ Y)
  rw [U₂.mapDerivedCategory.map_comp] at hc₂
  have m₄ : U₂.mapDerivedCategory.map
        (DerivedCategory.Q.map ((U₁.mapCochainComplexSingleFunctor 0).inv.app Y)) ≫
      U₂.mapDerivedCategoryFactors.hom.app
        ((U₁.mapHomologicalComplex (ComplexShape.up ℤ)).obj
          ((HomologicalComplex.single C₀ (ComplexShape.up ℤ) 0).obj Y)) =
      U₂.mapDerivedCategoryFactors.hom.app
          ((HomologicalComplex.single C₁ (ComplexShape.up ℤ) 0).obj (U₁.obj Y)) ≫
        DerivedCategory.Q.map ((U₂.mapHomologicalComplex (ComplexShape.up ℤ)).map
          ((U₁.mapCochainComplexSingleFunctor 0).inv.app Y)) :=
    U₂.mapDerivedCategoryFactors.hom.naturality _
  have m₁₂ : (U₂.mapDerivedCategorySingleFunctor 0).inv.app (U₁.obj Y) ≫
      U₂.mapDerivedCategoryFactors.hom.app
        ((HomologicalComplex.single C₁ (ComplexShape.up ℤ) 0).obj (U₁.obj Y)) =
      DerivedCategory.Q.map ((U₂.mapCochainComplexSingleFunctor 0).inv.app (U₁.obj Y)) :=
    Functor.mapDerivedCategorySingleFunctor_inv_app_mapDerivedCategoryFactors_hom_app U₂
      (U₁.obj Y)
  have hA := congrArg DerivedCategory.Q.map
    (mapCochainComplexSingleFunctor_comp_inv_app U₁ U₂ U c Y)
  simp only [Functor.map_comp] at hA
  rw [← cancel_mono (U.mapDerivedCategoryFactors.hom.app
    ((HomologicalComplex.single C₀ (ComplexShape.up ℤ) 0).obj Y))]
  simp only [Category.assoc]
  rw [Functor.mapDerivedCategorySingleFunctor_inv_app_mapDerivedCategoryFactors_hom_app,
    mapDerivedNatTrans_factors_app c.hom _, mapDerivedCategoryCompIso_hom_app_Q U₁ U₂ _]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  rw [reassoc_of% hc₂, reassoc_of% m₄, reassoc_of% m₁₂]
  exact hA

end Unbounded

section Transfer

variable {A : Type u₁} {B : Type u₂} [Category.{v₁} A] [Category.{v₂} B]
  [Abelian A] [Abelian B] [HasDerivedCategory A] [HasDerivedCategory B]
  (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- The inclusion of the bounded below subcategory carries the bounded below degree-`n`
embedding comparison to the unbounded one. -/
theorem ι_map_exactMapDerivedCategoryPlusSingle_inv_app (n : ℤ) (Y : A) :
    DerivedCategory.Plus.ι.map ((exactMapDerivedCategoryPlusSingle F n).inv.app Y) =
      (F.mapDerivedCategorySingleFunctor n).inv.app Y := by
  have h : Functor.whiskerRight (exactMapDerivedCategoryPlusSingle F n).inv
        DerivedCategory.Plus.ι =
      (F.mapDerivedCategorySingleFunctor n).inv :=
    (DerivedCategory.TStructure.t.plus.fullyFaithfulι.whiskeringRight _).map_preimage _
  exact congr_app h Y

end Transfer

/-! ### A rearrangement of composites -/

/-- The rearrangement of the three squares of the cocycle identity for the degree-zero
embedding. -/
private theorem single_chain {E : Type*} [Category* E] {o₁ o₂ o₃ o₄ o₅ o₆ o₇ o₈ o₉ : E}
    {s : o₁ ⟶ o₂} {ψU : o₂ ⟶ o₃} {ΦU : o₃ ⟶ o₄}
    {ψ₂ : o₁ ⟶ o₅} {Φ₂ : o₅ ⟶ o₆} {Rψ : o₆ ⟶ o₇} {RΦ : o₇ ⟶ o₈} {cI : o₈ ⟶ o₄}
    {mψ : o₅ ⟶ o₉} {Φ₂' : o₉ ⟶ o₇} {D : o₉ ⟶ o₃}
    (hnat : Φ₂ ≫ Rψ = mψ ≫ Φ₂') (hglue : Φ₂' ≫ RΦ ≫ cI = D ≫ ΦU)
    (hD : s ≫ ψU = ψ₂ ≫ mψ ≫ D) :
    s ≫ ψU ≫ ΦU = (ψ₂ ≫ Φ₂) ≫ (Rψ ≫ RΦ) ≫ cI := by
  rw [← Category.assoc s, hD]
  simp only [Category.assoc]
  rw [reassoc_of% hnat, hglue]

/-! ### The cocycle identity -/

section Plus

variable {C₀ : Type u₀} {C₁ : Type u₁} {C₂ : Type u₂}
  [Category.{v₀} C₀] [Category.{v₁} C₁] [Category.{v₂} C₂]
  [Abelian C₀] [Abelian C₁] [Abelian C₂]
  [HasDerivedCategory C₀] [HasDerivedCategory C₁] [HasDerivedCategory C₂]
  (U₁ : C₀ ⥤ C₁) (U₂ : C₁ ⥤ C₂) (U : C₀ ⥤ C₂)
  [U₁.Additive] [U₂.Additive] [U.Additive]
  [PreservesFiniteLimits U₁] [PreservesFiniteColimits U₁]
  [PreservesFiniteLimits U₂] [PreservesFiniteColimits U₂]
  [PreservesFiniteLimits U] [PreservesFiniteColimits U]
  (c : U₁ ⋙ U₂ ≅ U)

/-- **The cocycle identity for the degree-zero embedding on the bounded below derived
category**, against the degreewise comparison `U₂ ∘ U₁ ⟶ U`. -/
theorem exactMapDerivedCategoryPlusSingle_comp_inv_app (Y : C₀) :
    (DerivedCategory.Plus.singleFunctor C₂ 0).map (c.hom.app Y) ≫
        (exactMapDerivedCategoryPlusSingle U 0).inv.app Y =
      (exactMapDerivedCategoryPlusSingle U₂ 0).inv.app (U₁.obj Y) ≫
        U₂.mapDerivedCategoryPlus.map
            ((exactMapDerivedCategoryPlusSingle U₁ 0).inv.app Y) ≫
          (mapDerivedCategoryPlusCompNatTrans U₁ U₂ U c).app
            ((DerivedCategory.Plus.singleFunctor C₀ 0).obj Y) := by
  have hB : (DerivedCategory.singleFunctor C₂ 0).map (c.hom.app Y) ≫
        (U.mapDerivedCategorySingleFunctor 0).inv.app Y =
      (U₂.mapDerivedCategorySingleFunctor 0).inv.app (U₁.obj Y) ≫
        U₂.mapDerivedCategory.map ((U₁.mapDerivedCategorySingleFunctor 0).inv.app Y) ≫
          ((mapDerivedCategoryCompIso U₁ U₂).hom.app
              (DerivedCategory.Plus.ι.obj
                ((DerivedCategory.Plus.singleFunctor C₀ 0).obj Y)) ≫
            (mapDerivedNatTrans c.hom).app
              (DerivedCategory.Plus.ι.obj
                ((DerivedCategory.Plus.singleFunctor C₀ 0).obj Y))) :=
    mapDerivedCategorySingleFunctor_comp_inv_app U₁ U₂ U c Y
  have hL : DerivedCategory.Plus.ι.map
        ((DerivedCategory.Plus.singleFunctor C₂ 0).map (c.hom.app Y) ≫
          (exactMapDerivedCategoryPlusSingle U 0).inv.app Y) =
      (DerivedCategory.singleFunctor C₂ 0).map (c.hom.app Y) ≫
        (U.mapDerivedCategorySingleFunctor 0).inv.app Y := by
    show (DerivedCategory.singleFunctor C₂ 0).map (c.hom.app Y) ≫
      DerivedCategory.Plus.ι.map ((exactMapDerivedCategoryPlusSingle U 0).inv.app Y) = _
    rw [ι_map_exactMapDerivedCategoryPlusSingle_inv_app]
    rfl
  have hR : DerivedCategory.Plus.ι.map
        ((exactMapDerivedCategoryPlusSingle U₂ 0).inv.app (U₁.obj Y) ≫
          U₂.mapDerivedCategoryPlus.map
              ((exactMapDerivedCategoryPlusSingle U₁ 0).inv.app Y) ≫
            (mapDerivedCategoryPlusCompNatTrans U₁ U₂ U c).app
              ((DerivedCategory.Plus.singleFunctor C₀ 0).obj Y)) =
      (U₂.mapDerivedCategorySingleFunctor 0).inv.app (U₁.obj Y) ≫
        U₂.mapDerivedCategory.map ((U₁.mapDerivedCategorySingleFunctor 0).inv.app Y) ≫
          ((mapDerivedCategoryCompIso U₁ U₂).hom.app
              (DerivedCategory.Plus.ι.obj
                ((DerivedCategory.Plus.singleFunctor C₀ 0).obj Y)) ≫
            (mapDerivedNatTrans c.hom).app
              (DerivedCategory.Plus.ι.obj
                ((DerivedCategory.Plus.singleFunctor C₀ 0).obj Y))) := by
    show DerivedCategory.Plus.ι.map
          ((exactMapDerivedCategoryPlusSingle U₂ 0).inv.app (U₁.obj Y)) ≫
        U₂.mapDerivedCategory.map (DerivedCategory.Plus.ι.map
            ((exactMapDerivedCategoryPlusSingle U₁ 0).inv.app Y)) ≫
          (DerivedCategory.Plus.ι.map
              ((mapDerivedCategoryPlusCompIso U₁ U₂).hom.app
                ((DerivedCategory.Plus.singleFunctor C₀ 0).obj Y)) ≫
            (mapDerivedNatTrans c.hom).app
              (DerivedCategory.Plus.ι.obj
                ((DerivedCategory.Plus.singleFunctor C₀ 0).obj Y))) = _
    rw [ι_map_exactMapDerivedCategoryPlusSingle_inv_app,
      ι_map_exactMapDerivedCategoryPlusSingle_inv_app,
      ι_map_mapDerivedCategoryPlusCompIso_hom_app]
    rfl
  exact DerivedCategory.Plus.ι.map_injective (hL.trans (hB.trans hR.symm))

end Plus

section Exact

variable {C₀ : Type u₀} {C₁ : Type u₁} {C₂ : Type u₂}
  [Category.{v₀} C₀] [Category.{v₁} C₁] [Category.{v₂} C₂]
  [Abelian C₀] [Abelian C₁] [Abelian C₂]
  [HasDerivedCategory C₀] [HasDerivedCategory C₁] [HasDerivedCategory C₂]
  [EnoughInjectives C₀] [EnoughInjectives C₁]
  (U₁ : C₀ ⥤ C₁) (U₂ : C₁ ⥤ C₂) (U : C₀ ⥤ C₂)
  [U₁.Additive] [U₂.Additive] [U.Additive]
  [PreservesFiniteLimits U₁] [PreservesFiniteColimits U₁]
  [PreservesFiniteLimits U₂] [PreservesFiniteColimits U₂]
  [PreservesFiniteLimits U] [PreservesFiniteColimits U]
  (c : U₁ ⋙ U₂ ≅ U)

/-- **The cocycle identity for the degree-zero embedding comparison of an exact functor.** The
comparison `U(X)[0] ≅ RU(X[0])` for `U`, precomposed with `c`, is the composite of the
comparisons for `U₁` and for `U₂`, read through the comparison `RU₁ ⋙ RU₂ ≅ RU` of
`CategoryTheory.Functor.rightDerivedFunctorPlusCompIsoOfExact`. -/
theorem exactSingleFunctorRightDerivedPlusIso_comp (Y : C₀) :
    (DerivedCategory.Plus.singleFunctor C₂ 0).map (c.hom.app Y) ≫
        (exactSingleFunctorRightDerivedPlusIso U 0).hom.app Y =
      (exactSingleFunctorRightDerivedPlusIso U₂ 0).hom.app (U₁.obj Y) ≫
        U₂.rightDerivedFunctorPlus.map
            ((exactSingleFunctorRightDerivedPlusIso U₁ 0).hom.app Y) ≫
          (Functor.rightDerivedFunctorPlusCompIsoOfExact U₁ U₂ U c).hom.app
            ((DerivedCategory.Plus.singleFunctor C₀ 0).obj Y) := by
  have eσU : (exactSingleFunctorRightDerivedPlusIso U 0).hom.app Y =
      (exactMapDerivedCategoryPlusSingle U 0).inv.app Y ≫
        (exactMapDerivedCategoryPlusIso U).hom.app
          ((DerivedCategory.Plus.singleFunctor C₀ 0).obj Y) := rfl
  have eσ₂ : (exactSingleFunctorRightDerivedPlusIso U₂ 0).hom.app (U₁.obj Y) =
      (exactMapDerivedCategoryPlusSingle U₂ 0).inv.app (U₁.obj Y) ≫
        (exactMapDerivedCategoryPlusIso U₂).hom.app
          ((DerivedCategory.Plus.singleFunctor C₁ 0).obj (U₁.obj Y)) := rfl
  have hmap : U₂.rightDerivedFunctorPlus.map
        ((exactSingleFunctorRightDerivedPlusIso U₁ 0).hom.app Y) =
      U₂.rightDerivedFunctorPlus.map
          ((exactMapDerivedCategoryPlusSingle U₁ 0).inv.app Y) ≫
        U₂.rightDerivedFunctorPlus.map ((exactMapDerivedCategoryPlusIso U₁).hom.app
          ((DerivedCategory.Plus.singleFunctor C₀ 0).obj Y)) :=
    U₂.rightDerivedFunctorPlus.map_comp _ _
  rw [eσU, eσ₂, hmap]
  exact single_chain
    ((exactMapDerivedCategoryPlusIso U₂).hom.naturality
      ((exactMapDerivedCategoryPlusSingle U₁ 0).inv.app Y)).symm
    (exactMapDerivedCategoryPlusIso_compNatTrans U₁ U₂ U c
      ((DerivedCategory.Plus.singleFunctor C₀ 0).obj Y))
    (exactMapDerivedCategoryPlusSingle_comp_inv_app U₁ U₂ U c Y)

end Exact

end Stacks.DerivedFunctor

end
