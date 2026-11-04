module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.HigherDirectImageVanishing
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.QcCohomologicalDescent
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.ZariskiDerivedBaseChangeIso
import StacksCore.Tactic.StacksAttribute

/-!
# The quasi-compact and the Zariski sites of locally quasi-compact spaces

The category `LC_qc` of Hausdorff, locally quasi-compact spaces carries the quasi-compact topology
and the coarser Zariski topology. For an object `X` write `ε_X : Sh(LC_qc/X) → Sh(LC_Zar/X)` for
the change-of-topology morphism, `π_X : Sh(LC_Zar/X) → Sh(X)` for the comparison with the
underlying space and `a_X = π_X ∘ ε_X`. Stacks 0DCY deduces four comparison statements from the
results of Section 21.30 on comparing two topologies, applied to Situation 0EZ3 for this pair of
topologies with the proper maps as distinguished class and the sheaves pulled back from the space
as weak Serre class (Stacks 0EZI).

## Main results

In the namespace `Stacks.Topology.LocallyQuasiCompactZariskiSituation`:

* `isIso_qcAbelianComparisonAdjunction_unit_app_and_isZero_rightDerived`: Stacks 0DCY (1),
  `ε_{X,*}a_X^{-1}F = π_X^{-1}F` and `R^i ε_{X,*}(a_X^{-1}F) = 0` for `i > 0`.
* `qcTopologicalHigherDirectImageIsoOfProper`: Stacks 0DCY (2),
  `a_Y^{-1}(R^i f_*F) = R^i f_{qc,*}(a_X^{-1}F)` for a proper `f`.
* `isIso_qcDerivedComparisonUnit_app_abelianComparisonInverseImage`: Stacks 0DCY (3), the map
  `π_X^{-1}K ⟶ Rε_{X,*}(a_X^{-1}K)` is an isomorphism for `K` in `D⁺(X)`.
* `isIso_qcTopologicalDerivedBaseChangeMap_app_of_proper`: Stacks 0DCY (4), the map
  `a_Y^{-1}(Rf_*K) ⟶ Rf_{qc,*}(a_X^{-1}K)` is an isomorphism for a proper `f` and `K` in `D⁺(X)`.

## References

* [Stacks Project, Tag 0DCY](https://stacks.math.columbia.edu/tag/0DCY)
* [Stacks Project, Tag 0EZF](https://stacks.math.columbia.edu/tag/0EZF)
* [Stacks Project, Tag 0EZI](https://stacks.math.columbia.edu/tag/0EZI)
* [Stacks Project, Tag 015E](https://stacks.math.columbia.edu/tag/015E)
* [Stacks Project, Tag 0DCU](https://stacks.math.columbia.edu/tag/0DCU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace Stacks.Topology.LocallyQuasiCompactZariskiSituation

universe u w v

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable {S₀ : Set LocallyQuasiCompactHausdorff.{u}} {Bound : Cardinal.{u} → Cardinal.{u}}

attribute [local instance] enoughInjectives_sheafOpens_site enoughInjectives_zariskiSliceSheaf
  enoughInjectives_qcSliceSheaf

/-- For `X` in `LC_qc` and an abelian sheaf `F` on `X`, `R^i ε_{X,*}(a_X^{-1}F) = 0` for
`i > 0`. -/
theorem isZero_rightDerived_qcAbelianDirectImage_obj_qcTopologicalInverseImage
    (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound) (X : S.category)
    (F : Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{max (u + 1) v})
    (i : ℕ) (hi : 0 < i) :
    IsZero (((qcAbelianDirectImage.{u, w, v} S X).rightDerived i).obj
      ((qcTopologicalAbelianInverseImage.{u, w, v} S X).obj F)) :=
  isZero_rightDerived_qcAbelianDirectImage_of_vanishingCondition.{u, w, v} S
    (comparisonSituation.{u, w, v} S).vanishingCondition_all X _
    (zariskiPullbackClass_abelianComparisonInverseImage.{u, w, v} S X F) i hi

/-- **Stacks 0DCY (1).** For `X` in `LC_qc` and an abelian sheaf `F` on `X`, the change-of-topology
unit `π_X^{-1}F ⟶ ε_{X,*}ε_X^{-1}π_X^{-1}F = ε_{X,*}a_X^{-1}F` is an isomorphism, that is
`ε_{X,*}a_X^{-1}F = π_X^{-1}F`, and `R^i ε_{X,*}(a_X^{-1}F) = 0` for `i > 0`. -/
@[stacks 0DCY "clause (1): `ε_{X,*}a_X^{-1}F = π_X^{-1}F` (the unit is an isomorphism) and
`R^i ε_{X,*}(a_X^{-1}F) = 0` for `i > 0`"]
theorem isIso_qcAbelianComparisonAdjunction_unit_app_and_isZero_rightDerived
    (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound) (X : S.category)
    (F : Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{max (u + 1) v}) :
    IsIso ((qcAbelianComparisonAdjunction.{u, w, v} S X).unit.app
        ((S.abelianComparisonInverseImage.{u, w, max (u + 1) v} X).obj F)) ∧
      ∀ i : ℕ, 0 < i → IsZero (((qcAbelianDirectImage.{u, w, v} S X).rightDerived i).obj
        ((qcTopologicalAbelianInverseImage.{u, w, v} S X).obj F)) :=
  ⟨isIso_qcAbelianComparisonAdjunction_unit_app.{u, w, v} S X _
      (zariskiPullbackClass_isSheaf_qc.{u, w, v} S X _
        (zariskiPullbackClass_abelianComparisonInverseImage.{u, w, v} S X F)),
    isZero_rightDerived_qcAbelianDirectImage_obj_qcTopologicalInverseImage.{u, w, v} S X F⟩

/-- **Stacks 0DCY (2).** For a proper morphism `f : X ⟶ Y` of `LC_qc` and an abelian sheaf `F` on
`X`, `a_Y^{-1}(R^i f_*F) = R^i f_{qc,*}(a_X^{-1}F)` for every `i`. -/
@[stacks 0DCY "clause (2): `a_Y^{-1}(R^i f_* F) = R^i f_{qc,*}(a_X^{-1}F)` for proper `f` and
every `i`"]
def qcTopologicalHigherDirectImageIsoOfProper
    (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound) {X Y : S.category} (f : X ⟶ Y)
    (hf : S.properMorphisms f) (i : ℕ)
    (F : Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{max (u + 1) v}) :
    (qcTopologicalAbelianInverseImage.{u, w, v} S Y).obj
        (((spaceDirectImage S f AddCommGrpCat.{max (u + 1) v}).rightDerived i).obj F) ≅
      ((qcAbelianSliceDirectImage.{u, w, v} S f).rightDerived i).obj
        ((qcTopologicalAbelianInverseImage.{u, w, v} S X).obj F) :=
  qcTopologicalHigherDirectImageIsoOfVanishing.{u, w, v} S f hf i
    (fun G hG j hj ↦ isZero_rightDerived_qcAbelianDirectImage_of_vanishingCondition.{u, w, v} S
      (comparisonSituation.{u, w, v} S).vanishingCondition_all X G hG j hj) F

/-- After restriction along the localization functor, the canonical map `K ⟶ Rε_{X,*}(ε_X^{-1}K)`
is the degreewise unit followed by the unit of right derivation of `ε_{X,*}` and the degreewise
description of `ε_X^{-1}`. -/
theorem qcDerivedComparisonUnit_fac
    (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound) (X : S.category) :
    Functor.whiskerLeft DerivedCategory.Plus.Qh (qcDerivedComparisonUnit.{u, w, v} S X) =
      Functor.whiskerRight (Functor.mapHomotopyCategoryPlusIdComparison
            (Sheaf (S.zariskiTopology.over X) AddCommGrpCat.{max (u + 1) v}))
          DerivedCategory.Plus.Qh ≫
        Functor.whiskerRight (Functor.mapHomotopyCategoryPlusNatTrans
            (qcAbelianComparisonAdjunction.{u, w, v} S X).unit) DerivedCategory.Plus.Qh ≫
        Functor.whiskerRight (Functor.mapHomotopyCategoryPlusCompIso
            (Iso.refl (qcAbelianInverseImage.{u, w, v} S X ⋙
              qcAbelianDirectImage.{u, w, v} S X))).inv DerivedCategory.Plus.Qh ≫
        Functor.whiskerLeft (qcAbelianInverseImage.{u, w, v} S X).mapHomotopyCategoryPlus
          (qcAbelianDirectImage.{u, w, v} S X).rightDerivedFunctorPlusUnit ≫
        Functor.whiskerRight
          (qcAbelianInverseImage.{u, w, v} S X).mapDerivedCategoryPlusFactorsh.inv
          (qcAbelianDirectImage.{u, w, v} S X).rightDerivedFunctorPlus :=
  (Localization.fullyFaithfulWhiskeringLeft DerivedCategory.Plus.Qh
    (HomotopyCategory.Plus.quasiIso
      (Sheaf (S.zariskiTopology.over X) AddCommGrpCat.{max (u + 1) v})) _).map_preimage _

/-- At the image of a complex, the canonical map `K ⟶ Rε_{X,*}(ε_X^{-1}K)` is the degreewise unit
followed by the unit of right derivation of `ε_{X,*}`, up to the coherence isomorphisms. -/
theorem qcDerivedComparisonUnit_app_Qh_obj
    (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound) (X : S.category)
    (L : HomotopyCategory.Plus (Sheaf (S.zariskiTopology.over X) AddCommGrpCat.{max (u + 1) v})) :
    (qcDerivedComparisonUnit.{u, w, v} S X).app (DerivedCategory.Plus.Qh.obj L) =
      DerivedCategory.Plus.Qh.map ((Functor.mapHomotopyCategoryPlusIdComparison
          (Sheaf (S.zariskiTopology.over X) AddCommGrpCat.{max (u + 1) v})).app L) ≫
        DerivedCategory.Plus.Qh.map ((Functor.mapHomotopyCategoryPlusNatTrans
          (qcAbelianComparisonAdjunction.{u, w, v} S X).unit).app L) ≫
        DerivedCategory.Plus.Qh.map ((Functor.mapHomotopyCategoryPlusCompIso
            (Iso.refl (qcAbelianInverseImage.{u, w, v} S X ⋙
              qcAbelianDirectImage.{u, w, v} S X))).inv.app L) ≫
        (qcAbelianDirectImage.{u, w, v} S X).rightDerivedFunctorPlusUnit.app
          ((qcAbelianInverseImage.{u, w, v} S X).mapHomotopyCategoryPlus.obj L) ≫
        (qcAbelianDirectImage.{u, w, v} S X).rightDerivedFunctorPlus.map
          ((qcAbelianInverseImage.{u, w, v} S X).mapDerivedCategoryPlusFactorsh.inv.app L) := by
  simpa only [Functor.whiskerLeft_app, NatTrans.comp_app, Functor.whiskerRight_app] using
    NatTrans.congr_app (qcDerivedComparisonUnit_fac.{u, w, v} S X) L

/-- The transformation induced on bounded below homotopy categories by a natural transformation is
invertible at a complex all of whose terms it is invertible at. -/
theorem isIso_mapHomotopyCategoryPlusNatTrans_app {A B : Type*} [Category* A] [Category* B]
    [Preadditive A] [Preadditive B] {F G : A ⥤ B} [F.Additive] [G.Additive] (α : F ⟶ G)
    (K : HomotopyCategory.Plus A) (hK : ∀ n : ℤ, IsIso (α.app (K.obj.as.X n))) :
    IsIso ((Functor.mapHomotopyCategoryPlusNatTrans α).app K) := by
  have : ∀ n : ℤ, IsIso (((NatTrans.mapHomologicalComplex α (ComplexShape.up ℤ)).app
      K.obj.as).f n) := hK
  have : IsIso ((NatTrans.mapHomologicalComplex α (ComplexShape.up ℤ)).app K.obj.as) :=
    HomologicalComplex.Hom.isIso_of_components _
  have hι : IsIso ((HomotopyCategory.Plus.ι B).map
      ((Functor.mapHomotopyCategoryPlusNatTrans α).app K)) :=
    inferInstanceAs (IsIso ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).map
      ((NatTrans.mapHomologicalComplex α (ComplexShape.up ℤ)).app K.obj.as)))
  exact isIso_of_reflects_iso _ (HomotopyCategory.Plus.ι B)

/-- **Stacks 0DCY (3).** For `X` in `LC_qc` and `K` in `D⁺(X)`, the canonical map
`π_X^{-1}K ⟶ Rε_{X,*}(a_X^{-1}K)` is an isomorphism. -/
@[stacks 0DCY "clause (3): `π_X^{-1}K ⟶ Rε_{X,*}(a_X^{-1}K)` is an isomorphism for `K` in
`D⁺(X)`"]
theorem isIso_qcDerivedComparisonUnit_app_abelianComparisonInverseImage
    (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound) (X : S.category)
    (K : DerivedCategory.Plus
      (Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{max (u + 1) v})) :
    IsIso ((qcDerivedComparisonUnit.{u, w, v} S X).app
      ((S.abelianComparisonInverseImage.{u, w, max (u + 1) v} X).mapDerivedCategoryPlus.obj
        K)) := by
  have hQh : ∀ L : HomotopyCategory.Plus
      (Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{max (u + 1) v}),
      IsIso ((qcDerivedComparisonUnit.{u, w, v} S X).app (DerivedCategory.Plus.Qh.obj
        ((S.abelianComparisonInverseImage.{u, w, max (u + 1) v}
          X).mapHomotopyCategoryPlus.obj L))) := by
    intro L
    rw [qcDerivedComparisonUnit_app_Qh_obj]
    have h₀ : (Functor.mapHomotopyCategoryPlusIdComparison
        (Sheaf (S.zariskiTopology.over X) AddCommGrpCat.{max (u + 1) v})).app
          ((S.abelianComparisonInverseImage.{u, w, max (u + 1) v}
            X).mapHomotopyCategoryPlus.obj L) = 𝟙 _ := rfl
    have h₂ : (Functor.mapHomotopyCategoryPlusCompIso
        (Iso.refl (qcAbelianInverseImage.{u, w, v} S X ⋙
          qcAbelianDirectImage.{u, w, v} S X))).inv.app
          ((S.abelianComparisonInverseImage.{u, w, max (u + 1) v}
            X).mapHomotopyCategoryPlus.obj L) = 𝟙 _ := rfl
    have i₀ : IsIso (DerivedCategory.Plus.Qh.map ((Functor.mapHomotopyCategoryPlusIdComparison
        (Sheaf (S.zariskiTopology.over X) AddCommGrpCat.{max (u + 1) v})).app
          ((S.abelianComparisonInverseImage.{u, w, max (u + 1) v}
            X).mapHomotopyCategoryPlus.obj L))) := by
      rw [h₀]
      exact (DerivedCategory.Plus.Qh.mapIso (Iso.refl _)).isIso_hom
    have i₁ : IsIso (DerivedCategory.Plus.Qh.map ((Functor.mapHomotopyCategoryPlusNatTrans
        (qcAbelianComparisonAdjunction.{u, w, v} S X).unit).app
          ((S.abelianComparisonInverseImage.{u, w, max (u + 1) v}
            X).mapHomotopyCategoryPlus.obj L))) := by
      have := isIso_mapHomotopyCategoryPlusNatTrans_app
        (qcAbelianComparisonAdjunction.{u, w, v} S X).unit
        ((S.abelianComparisonInverseImage.{u, w, max (u + 1) v}
          X).mapHomotopyCategoryPlus.obj L) (fun n ↦
          isIso_qcAbelianComparisonAdjunction_unit_app.{u, w, v} S X _
            (zariskiPullbackClass_isSheaf_qc.{u, w, v} S X _
              (zariskiPullbackClass_abelianComparisonInverseImage.{u, w, v} S X _)))
      infer_instance
    have i₂ : IsIso (DerivedCategory.Plus.Qh.map ((Functor.mapHomotopyCategoryPlusCompIso
        (Iso.refl (qcAbelianInverseImage.{u, w, v} S X ⋙
          qcAbelianDirectImage.{u, w, v} S X))).inv.app
          ((S.abelianComparisonInverseImage.{u, w, max (u + 1) v}
            X).mapHomotopyCategoryPlus.obj L))) := by
      rw [h₂]
      exact (DerivedCategory.Plus.Qh.mapIso (Iso.refl _)).isIso_hom
    have i₃ : IsIso ((qcAbelianDirectImage.{u, w, v} S X).rightDerivedFunctorPlusUnit.app
        ((qcAbelianInverseImage.{u, w, v} S X).mapHomotopyCategoryPlus.obj
          ((S.abelianComparisonInverseImage.{u, w, max (u + 1) v}
            X).mapHomotopyCategoryPlus.obj L))) :=
      Functor.isIso_rightDerivedFunctorPlusUnit_app_of_rightAcyclic _ _ fun n ↦
        rightAcyclic_qcAbelianDirectImage_qcTopologicalInverseImage.{u, w, v} S X
          (L.obj.as.X n)
    have i₄ : IsIso ((qcAbelianDirectImage.{u, w, v} S X).rightDerivedFunctorPlus.map
        ((qcAbelianInverseImage.{u, w, v} S X).mapDerivedCategoryPlusFactorsh.inv.app
          ((S.abelianComparisonInverseImage.{u, w, max (u + 1) v}
            X).mapHomotopyCategoryPlus.obj L))) := inferInstance
    exact IsIso.comp_isIso' i₀ (IsIso.comp_isIso' i₁ (IsIso.comp_isIso' i₂
      (IsIso.comp_isIso' i₃ i₄)))
  let e := DerivedCategory.Plus.Qh.objObjPreimageIso K
  refine (NatTrans.isIso_app_iff_of_iso (qcDerivedComparisonUnit.{u, w, v} S X)
    ((S.abelianComparisonInverseImage.{u, w, max (u + 1) v} X).mapDerivedCategoryPlus.mapIso
      e.symm ≪≫
      (S.abelianComparisonInverseImage.{u, w, max (u + 1) v}
        X).mapDerivedCategoryPlusFactorsh.app _)).2 (hQh _)

/-- A sheaf pulled back from the space along `π_X`, of an injective sheaf, is right acyclic for the
Zariski direct image `f_{Zar,*}` of a proper `f`. -/
theorem rightAcyclic_sliceDirectImage_abelianComparisonInverseImage
    (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound) {X Y : S.category} (f : X ⟶ Y)
    (hf : S.properMorphisms f)
    (I : Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{max (u + 1) v}) [Injective I] :
    (sliceDirectImage S f AddCommGrpCat.{max (u + 1) v}).rightAcyclic
      ((S.abelianComparisonInverseImage.{u, w, max (u + 1) v} X).obj I) := by
  have : PreservesFiniteLimits (sliceDirectImage S f AddCommGrpCat.{max (u + 1) v}) :=
    preservesFiniteLimits_zariskiSlicePushforward.{u, w, v} S f
  refine (rightAcyclic_iff_isZero_rightDerived _ _).2 fun i hi ↦ ?_
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi.ne'
  exact ((S.abelianComparisonInverseImage.{u, w, max (u + 1) v} Y).map_isZero
    (Functor.isZero_rightDerived_obj_injective_succ _ j I)).of_iso
      (rightDerivedZariskiBaseChangeIso.{u, w, v} S f
        (isProperMap_of_properMorphisms S f hf) I (j + 1))

/-- `a_X^{-1}` of an injective sheaf is right acyclic for the direct image `f_{qc,*}` of a proper
`f`. -/
theorem rightAcyclic_qcAbelianSliceDirectImage_qcTopologicalInverseImage
    (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound) {X Y : S.category} (f : X ⟶ Y)
    (hf : S.properMorphisms f)
    (I : Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{max (u + 1) v}) [Injective I] :
    (qcAbelianSliceDirectImage.{u, w, v} S f).rightAcyclic
      ((qcTopologicalAbelianInverseImage.{u, w, v} S X).obj I) := by
  refine (rightAcyclic_iff_isZero_rightDerived _ _).2 fun i hi ↦ ?_
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi.ne'
  exact ((qcTopologicalAbelianInverseImage.{u, w, v} S Y).map_isZero
    (Functor.isZero_rightDerived_obj_injective_succ _ j I)).of_iso
      (qcTopologicalHigherDirectImageIsoOfProper.{u, w, v} S f hf (j + 1) I).symm

/-- The change-of-topology base change map `ε_Y^{-1}f_{Zar,*} ⟶ f_{qc,*}ε_X^{-1}` is invertible at
a sheaf pulled back from the space. -/
theorem isIso_qcAbelianComparisonBaseChange_app
    (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound) {X Y : S.category} (f : X ⟶ Y)
    (G : Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{max (u + 1) v}) :
    IsIso ((qcAbelianComparisonBaseChange.{u, w, v} S f).app
      ((S.abelianComparisonInverseImage.{u, w, max (u + 1) v} X).obj G)) := by
  have hu := isIso_qcAbelianComparisonAdjunction_unit_app.{u, w, v} S X _
    (zariskiPullbackClass_isSheaf_qc.{u, w, v} S X _
      (zariskiPullbackClass_abelianComparisonInverseImage.{u, w, v} S X G))
  have hc : IsIso (qcAbelianComparisonAdjunction.{u, w, v} S Y).counit :=
    Adjunction.counit_isIso_of_R_fully_faithful _
  have e : (qcAbelianComparisonBaseChange.{u, w, v} S f).app
      ((S.abelianComparisonInverseImage.{u, w, max (u + 1) v} X).obj G) =
      (qcAbelianInverseImage.{u, w, v} S Y).map ((sliceDirectImage S f
        AddCommGrpCat.{max (u + 1) v}).map ((qcAbelianComparisonAdjunction.{u, w, v} S X).unit.app
          ((S.abelianComparisonInverseImage.{u, w, max (u + 1) v} X).obj G))) ≫
        (qcAbelianComparisonAdjunction.{u, w, v} S Y).counit.app
          ((qcAbelianSliceDirectImage.{u, w, v} S f).obj ((qcAbelianInverseImage.{u, w, v} S X).obj
            ((S.abelianComparisonInverseImage.{u, w, max (u + 1) v} X).obj G))) := rfl
  rw [e]
  have h₁ : IsIso ((qcAbelianInverseImage.{u, w, v} S Y).map ((sliceDirectImage S f
      AddCommGrpCat.{max (u + 1) v}).map ((qcAbelianComparisonAdjunction.{u, w, v} S X).unit.app
        ((S.abelianComparisonInverseImage.{u, w, max (u + 1) v} X).obj G)))) := inferInstance
  have h₂ : IsIso ((qcAbelianComparisonAdjunction.{u, w, v} S Y).counit.app
      ((qcAbelianSliceDirectImage.{u, w, v} S f).obj ((qcAbelianInverseImage.{u, w, v} S X).obj
        ((S.abelianComparisonInverseImage.{u, w, max (u + 1) v} X).obj G)))) :=
    NatIso.isIso_app_of_isIso _ _
  exact IsIso.comp_isIso' h₁ h₂

/-- **The change-of-topology derived base change map is invertible at a complex computing both
direct images.** Let `L` be a bounded below complex of abelian sheaves on `LC_Zar/X` whose terms
are right acyclic for `f_{Zar,*}`, at whose terms the degreewise base change map
`ε_Y^{-1}f_{Zar,*} ⟶ f_{qc,*}ε_X^{-1}` is invertible, and whose image under `ε_X^{-1}` has terms
right acyclic for `f_{qc,*}`. Then `ε_Y^{-1}Rf_{Zar,*}L ⟶ Rf_{qc,*}ε_X^{-1}L` is invertible. -/
theorem isIso_qcDerivedComparisonBaseChangeMap_app_Qh_obj
    (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound) {X Y : S.category} (f : X ⟶ Y)
    (L : HomotopyCategory.Plus (Sheaf (S.zariskiTopology.over X) AddCommGrpCat.{max (u + 1) v}))
    (hZ : ∀ n : ℤ, (sliceDirectImage S f AddCommGrpCat.{max (u + 1) v}).rightAcyclic
      (L.obj.as.X n))
    (hβ : ∀ n : ℤ, IsIso ((qcAbelianComparisonBaseChange.{u, w, v} S f).app (L.obj.as.X n)))
    (hqc : ∀ n : ℤ, (qcAbelianSliceDirectImage.{u, w, v} S f).rightAcyclic
      ((qcAbelianInverseImage.{u, w, v} S X).obj (L.obj.as.X n))) :
    IsIso ((qcDerivedComparisonBaseChangeMap.{u, w, v} S f).app
      (DerivedCategory.Plus.Qh.obj L)) := by
  have hfac := NatTrans.congr_app (qcDerivedComparisonBaseChangeMap_fac.{u, w, v} S f) L
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at hfac
  have hu : IsIso ((sliceDirectImage S f
      AddCommGrpCat.{max (u + 1) v}).rightDerivedFunctorPlusUnit.app L) :=
    Functor.isIso_rightDerivedFunctorPlusUnit_app_of_rightAcyclic _ _ hZ
  have hcomp : IsIso ((qcAbelianInverseImage.{u, w, v} S Y).rightDerivedFunctorPlus.map
        ((sliceDirectImage S f AddCommGrpCat.{max (u + 1) v}).rightDerivedFunctorPlusUnit.app L) ≫
      (qcDerivedComparisonBaseChangeMap.{u, w, v} S f).app (DerivedCategory.Plus.Qh.obj L)) := by
    rw [hfac]
    dsimp only [qcDerivedComparisonBaseChangeOnHomotopy]
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
    have i₃ : IsIso (DerivedCategory.Plus.Qh.map ((Functor.mapHomotopyCategoryPlusNatTrans
        (qcAbelianComparisonBaseChange.{u, w, v} S f)).app L)) := by
      have := isIso_mapHomotopyCategoryPlusNatTrans_app
        (qcAbelianComparisonBaseChange.{u, w, v} S f) L hβ
      infer_instance
    have i₅ : IsIso ((qcAbelianSliceDirectImage.{u, w, v} S f).rightDerivedFunctorPlusUnit.app
        ((qcAbelianInverseImage.{u, w, v} S X).mapHomotopyCategoryPlus.obj L)) :=
      Functor.isIso_rightDerivedFunctorPlusUnit_app_of_rightAcyclic _ _ hqc
    have i₆ : IsIso ((qcAbelianSliceDirectImage.{u, w, v} S f).rightDerivedFunctorPlus.map
        ((qcAbelianInverseImage.{u, w, v} S X).rightDerivedFunctorPlusUnit.app L)) := by
      have : IsIso ((qcAbelianInverseImage.{u, w, v} S X).rightDerivedFunctorPlusUnit.app L) :=
        NatIso.isIso_app_of_isIso _ _
      infer_instance
    infer_instance
  exact IsIso.of_isIso_comp_left
    ((qcAbelianInverseImage.{u, w, v} S Y).rightDerivedFunctorPlus.map
      ((sliceDirectImage S f AddCommGrpCat.{max (u + 1) v}).rightDerivedFunctorPlusUnit.app L)) _

/-- **Stacks 0DCY (4).** For a proper morphism `f : X ⟶ Y` of `LC_qc` and `K` in `D⁺(X)`, the
canonical map `a_Y^{-1}(Rf_*K) ⟶ Rf_{qc,*}(a_X^{-1}K)` is an isomorphism. -/
@[stacks 0DCY "clause (4): `a_Y^{-1}(Rf_*K) = Rf_{qc,*}(a_X^{-1}K)` for proper `f` and `K` in
`D⁺(X)`"]
theorem isIso_qcTopologicalDerivedBaseChangeMap_app_of_proper
    (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound) {X Y : S.category} (f : X ⟶ Y)
    (hf : S.properMorphisms f)
    (K : DerivedCategory.Plus
      (Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{max (u + 1) v})) :
    IsIso ((qcTopologicalDerivedBaseChangeMap.{u, w, v} S f).app K) := by
  have h₁ : IsIso ((derivedComparisonBaseChangeMap.{u, w, v} S f).app K) :=
    have := isIso_derivedComparisonBaseChangeMap.{u, w, v} S f hf
    NatIso.isIso_app_of_isIso _ K
  have h₂ : IsIso ((qcDerivedComparisonBaseChangeMap.{u, w, v} S f).app
      ((S.abelianComparisonInverseImage.{u, w, max (u + 1) v}
        X).rightDerivedFunctorPlus.obj K)) := by
    obtain ⟨lower, hlower⟩ := K.property
    have : K.IsGE lower := (K.isGE_ι_obj_iff lower).1 hlower
    obtain ⟨L, hL, ⟨eL⟩⟩ := DerivedCategory.Plus.exists_injective_nonempty_iso K lower
    let I := (InjectiveObject.ι
      (Sheaf (Opens.grothendieckTopology X.obj)
        AddCommGrpCat.{max (u + 1) v})).mapCochainComplexPlus.obj L
    let IH := (HomotopyCategory.Plus.quotient _).obj I
    have eK : DerivedCategory.Plus.Qh.obj IH ≅ K :=
      DerivedCategory.Plus.ι.preimageIso (Y := DerivedCategory.Plus.Q.obj I)
        ((DerivedCategory.Plus.QhCompιIsoιCompQh _).app IH ≪≫
          DerivedCategory.Qh.mapIso ((HomotopyCategory.Plus.quotientCompιIso _).app I) ≪≫
          (DerivedCategory.quotientCompQhIso _).app I.obj) ≪≫ eL
    let M := (S.abelianComparisonInverseImage.{u, w, max (u + 1) v}
      X).mapHomotopyCategoryPlus.obj IH
    have hM : IsIso ((qcDerivedComparisonBaseChangeMap.{u, w, v} S f).app
        (DerivedCategory.Plus.Qh.obj M)) :=
      isIso_qcDerivedComparisonBaseChangeMap_app_Qh_obj.{u, w, v} S f M
        (fun n ↦ rightAcyclic_sliceDirectImage_abelianComparisonInverseImage.{u, w, v} S f hf
          (IH.obj.as.X n))
        (fun n ↦ isIso_qcAbelianComparisonBaseChange_app.{u, w, v} S f (IH.obj.as.X n))
        (fun n ↦ rightAcyclic_qcAbelianSliceDirectImage_qcTopologicalInverseImage.{u, w, v} S f hf
          (IH.obj.as.X n))
    have hunit : IsIso ((S.abelianComparisonInverseImage.{u, w, max (u + 1) v}
        X).rightDerivedFunctorPlusUnit.app IH) := NatIso.isIso_app_of_isIso _ _
    exact (NatTrans.isIso_app_iff_of_iso (qcDerivedComparisonBaseChangeMap.{u, w, v} S f)
      (asIso ((S.abelianComparisonInverseImage.{u, w, max (u + 1) v}
        X).rightDerivedFunctorPlusUnit.app IH) ≪≫
        (S.abelianComparisonInverseImage.{u, w, max (u + 1) v}
          X).rightDerivedFunctorPlus.mapIso eK)).1 hM
  have e : (qcTopologicalDerivedBaseChangeMap.{u, w, v} S f).app K =
      (qcAbelianInverseImage.{u, w, v} S Y).rightDerivedFunctorPlus.map
          ((derivedComparisonBaseChangeMap.{u, w, v} S f).app K) ≫
        (qcDerivedComparisonBaseChangeMap.{u, w, v} S f).app
          ((S.abelianComparisonInverseImage.{u, w, max (u + 1) v} X).rightDerivedFunctorPlus.obj
            K) := rfl
  rw [e]
  infer_instance

end Stacks.Topology.LocallyQuasiCompactZariskiSituation

end
