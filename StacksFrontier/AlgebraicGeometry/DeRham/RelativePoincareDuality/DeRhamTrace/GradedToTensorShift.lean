module

public import StacksFrontier.AlgebraicGeometry.DeRham.RelativePoincareDuality.ToTensorShiftedPairing

/-!
# The canonical map to the total tensor complex and the shift in the second variable

Let `Z` be a ringed space and `K`, `L` cochain complexes of `𝒪_Z`-modules. The canonical map
`QK ⊗^L QL ⟶ Q(Tot(K ⊗ L))` of [Stacks, Tag 06YU] commutes with the shift in the second variable:
through `Q(L[m]) ≅ (QL)[m]`, the commutation `QK ⊗^L (QL)[m] ≅ (QK ⊗^L QL)[m]` followed by the
shift of the canonical map is the canonical map at `(K, L[m])` followed by `Q` of the commutation
`Tot(K ⊗ L[m]) ≅ Tot(K ⊗ L)[m]` of the total complex with the shift.

## Main results

* `Stacks.Cohomology.DerivedPullbackTensor.toTensor_shift_right`

## References

* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped Stacks.StandardDerivedModel
open AlgebraicGeometry.RingedSpace.KFlatDerivedPullback renaming Modules → ModulesOn
open Stacks.DerivedTensor.RingedSite (derivedTensorProductFunctor canonicalDerivedTensorProduct)

universe u

namespace CategoryTheory.Functor

variable {C₁ C₂ C₁' C₂' D D' : Type*} [Category* C₁] [Category* C₂] [Category* C₁']
  [Category* C₂'] [Category* D] [Category* D']
  [HasShift C₁ ℤ] [HasShift C₂ ℤ] [HasShift C₁' ℤ] [HasShift C₂' ℤ] [HasShift D ℤ]
  [HasShift D' ℤ] [Preadditive D] [Preadditive D'] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [∀ n : ℤ, (shiftFunctor D' n).Additive]

/-- The commutation with the shift in the second variable of a bifunctor restricted along
`F : C₂' ⥤ C₂` in its second variable. -/
theorem commShiftIso_precomp₂_obj_hom_app (F : C₂' ⥤ C₂) [F.CommShift ℤ] (G : C₁ ⥤ C₂ ⥤ D)
    [G.CommShift₂Int] (K : C₁) (L : C₂') (m : ℤ) :
    (((G ⋙ (whiskeringLeft C₂' C₂ D).obj F).obj K).commShiftIso m).hom.app L =
      (G.obj K).map ((F.commShiftIso m).hom.app L) ≫
        ((G.obj K).commShiftIso m).hom.app (F.obj L) :=
  Functor.commShiftIso_comp_hom_app F (G.obj K) m L

/-- The commutation with the shift in the second variable of a bifunctor restricted along
`F : C₁' ⥤ C₁` in its first variable. -/
theorem commShiftIso_precomp₁_obj_hom_app (F : C₁' ⥤ C₁) [F.CommShift ℤ] (G : C₁ ⥤ C₂ ⥤ D)
    [G.CommShift₂Int] (K : C₁') (L : C₂) (m : ℤ) :
    (((F ⋙ G).obj K).commShiftIso m).hom.app L = ((G.obj (F.obj K)).commShiftIso m).hom.app L :=
  rfl

/-- The commutation with the shift in the second variable of a bifunctor postcomposed with `H`. -/
theorem commShiftIso_postcompInt_obj_hom_app (G : C₁ ⥤ C₂ ⥤ D) [G.CommShift₂Int] (H : D ⥤ D')
    [H.CommShift ℤ] [H.Additive] (K : C₁) (L : C₂) (m : ℤ) :
    (((G ⋙ (whiskeringRight C₂ D D').obj H).obj K).commShiftIso m).hom.app L =
      H.map (((G.obj K).commShiftIso m).hom.app L) ≫
        (H.commShiftIso m).hom.app ((G.obj K).obj L) :=
  Functor.commShiftIso_comp_hom_app (G.obj K) H m L

/-- A transformation of bifunctors compatible with the shifts commutes with the shift in the
second variable. -/
theorem commShiftIso_obj_natTrans {G₁ G₂ : C₁ ⥤ C₂ ⥤ D} [G₁.CommShift₂Int] [G₂.CommShift₂Int]
    (τ : G₁ ⟶ G₂) [NatTrans.CommShift₂Int τ] (K : C₁) (L : C₂) (m : ℤ) :
    ((G₁.obj K).commShiftIso m).hom.app L ≫ ((τ.app K).app L)⟦m⟧' =
      (τ.app K).app (L⟦m⟧) ≫ ((G₂.obj K).commShiftIso m).hom.app L :=
  NatTrans.shift_app_comm (τ.app K) m L

end CategoryTheory.Functor

namespace Stacks.Cohomology.DerivedPullbackTensor

attribute [local implicit_reducible] structureSheafRing
  StacksDraft.KFlat.modulePullback TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf

variable (Z : RingedSpace.{u, u})
  [HasSheafify (Opens.grothendieckTopology Z.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Z.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The commutation of the curried `Q(-) ⊗^L Q(-)` with the shift in the second variable. -/
theorem curryComplexesDerivedTensor_commShiftIso_hom_app (K L : CochainComplex (ModulesOn Z) ℤ)
    (m : ℤ) :
    letI := curryComplexesDerivedTensor_commShift₂Int Z
    (((Functor.curry.obj (DerivedCategory.Q.prod DerivedCategory.Q ⋙
        Functor.uncurry.obj (derivedTensorProductFunctor Z.sheaf))).obj K).commShiftIso
          m).hom.app L =
      letI := derivedTensorCommShift₂Int Z
      ((derivedTensorProductFunctor Z.sheaf).obj (DerivedCategory.Q.obj K)).map
          ((DerivedCategory.Q.commShiftIso m).hom.app L) ≫
        (((derivedTensorProductFunctor Z.sheaf).obj (DerivedCategory.Q.obj K)).commShiftIso
          m).hom.app (DerivedCategory.Q.obj L) := by
  let := curriedComplexesDerivedTensor_commShift₂Int Z
  let := curryComplexesDerivedTensor_commShift₂Int Z
  have := Functor.CommShift₂.ofIsoInt_commShift₂ (curryComplexesDerivedTensorIso Z)
  have e := Functor.commShiftIso_obj_natTrans (curryComplexesDerivedTensorIso Z).hom K L m
  have e₁ : (shiftFunctor _ m).map (((curryComplexesDerivedTensorIso Z).hom.app K).app L) =
      𝟙 _ := (shiftFunctor _ m).map_id _
  have e₂ : ((curryComplexesDerivedTensorIso Z).hom.app K).app (L⟦m⟧) = 𝟙 _ := rfl
  rw [e₁, e₂] at e
  refine ((Category.comp_id _).symm.trans (e.trans (Category.id_comp _))).symm.trans ?_
  let := derivedTensorCommShift₂Int Z
  exact Functor.commShiftIso_precomp₂_obj_hom_app DerivedCategory.Q
    (derivedTensorProductFunctor Z.sheaf) (DerivedCategory.Q.obj K) L m

/-- The commutation of the curried `Q(Tot(- ⊗ -))` with the shift in the second variable. -/
theorem curryComplexesTotal_commShiftIso_hom_app (K L : CochainComplex (ModulesOn Z) ℤ)
    (m : ℤ) :
    letI := curryComplexesTotal_commShift₂Int Z
    (((Functor.curry.obj (totalComplexPair
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.sheaf) ⋙
          DerivedCategory.Q)).obj K).commShiftIso m).hom.app L =
      DerivedCategory.Q.map ((((tensorComplexBifunctorOn Z).obj K).commShiftIso m).hom.app L) ≫
        (DerivedCategory.Q.commShiftIso m).hom.app
          (((tensorComplexBifunctorOn Z).obj K).obj L) := by
  let := curriedComplexesTotal_commShift₂Int Z
  let := curryComplexesTotal_commShift₂Int Z
  have := Functor.CommShift₂.ofIsoInt_commShift₂ (curryComplexesTotalIso Z)
  have e := Functor.commShiftIso_obj_natTrans (curryComplexesTotalIso Z).hom K L m
  have e₁ : (shiftFunctor _ m).map (((curryComplexesTotalIso Z).hom.app K).app L) = 𝟙 _ := by
    rw [show ((curryComplexesTotalIso Z).hom.app K).app L = 𝟙 _ from
      Functor.curryObjUncurryObjCompIso_hom_app_app _ _ _ _]
    exact (shiftFunctor _ m).map_id _
  have e₂ : ((curryComplexesTotalIso Z).hom.app K).app (L⟦m⟧) = 𝟙 _ :=
    Functor.curryObjUncurryObjCompIso_hom_app_app _ _ _ _
  rw [e₁, e₂] at e
  refine ((Category.comp_id _).symm.trans (e.trans (Category.id_comp _))).symm.trans ?_
  exact Functor.commShiftIso_postcompInt_obj_hom_app (tensorComplexBifunctorOn Z)
    DerivedCategory.Q K L m

/-- **The canonical map to the total tensor complex commutes with the shift in the second
variable.** -/
theorem toTensor_shift_right (K L : CochainComplex (ModulesOn Z) ℤ) (m : ℤ) :
    letI := (canonicalDerivedTensorProduct Z.sheaf).commShift₂
    ((derivedTensorProductFunctor Z.sheaf).obj (DerivedCategory.Q.obj K)).map
        ((DerivedCategory.Q.commShiftIso m).hom.app L) ≫
      (((derivedTensorProductFunctor Z.sheaf).obj (DerivedCategory.Q.obj K)).commShiftIso
        m).hom.app (DerivedCategory.Q.obj L) ≫
      ((canonicalDerivedTensorProduct Z.sheaf).toTensor K L)⟦m⟧' =
    (canonicalDerivedTensorProduct Z.sheaf).toTensor K (L⟦m⟧) ≫
      DerivedCategory.Q.map ((((tensorComplexBifunctorOn Z).obj K).commShiftIso m).hom.app L) ≫
      (DerivedCategory.Q.commShiftIso m).hom.app (((tensorComplexBifunctorOn Z).obj K).obj L) := by
  have key : ∀ d : (derivedTensorProductFunctor Z.sheaf).CommShift₂Int,
      d = Stacks.SheafOfModules.DerivedMonoidal.canonicalTensor_commShift₂Int Z.sheaf →
      let := d
      ((derivedTensorProductFunctor Z.sheaf).obj (DerivedCategory.Q.obj K)).map
          ((DerivedCategory.Q.commShiftIso m).hom.app L) ≫
        (((derivedTensorProductFunctor Z.sheaf).obj (DerivedCategory.Q.obj K)).commShiftIso
          m).hom.app (DerivedCategory.Q.obj L) ≫
        ((canonicalDerivedTensorProduct Z.sheaf).toTensor K L)⟦m⟧' =
      (canonicalDerivedTensorProduct Z.sheaf).toTensor K (L⟦m⟧) ≫
        DerivedCategory.Q.map ((((tensorComplexBifunctorOn Z).obj K).commShiftIso m).hom.app L) ≫
        (DerivedCategory.Q.commShiftIso m).hom.app
          (((tensorComplexBifunctorOn Z).obj K).obj L) := by
    rintro _ rfl
    let := curryComplexesDerivedTensor_commShift₂Int Z
    let := curryComplexesTotal_commShift₂Int Z
    have : NatTrans.CommShift₂Int (Functor.curry.map (derivedToTensorNatTrans Z)) :=
      derivedToTensorCommShift₂ Z
    have h := Functor.commShiftIso_obj_natTrans (Functor.curry.map (derivedToTensorNatTrans Z))
      K L m
    rw [curryComplexesDerivedTensor_commShiftIso_hom_app,
      curryComplexesTotal_commShiftIso_hom_app] at h
    exact (Category.assoc _ _ _).symm.trans h
  exact key _ (Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedTensorProduct_commShift₂_eq
    Z.sheaf)

end Stacks.Cohomology.DerivedPullbackTensor
