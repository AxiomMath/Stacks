module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.QcAbelianComparison
public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.ZariskiHigherDirectImageClass
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.ZariskiPullbackQcSheaf

/-!
# The quasi-compact and Zariski comparisons on abelian sheaves, without carried conditions

Let `X` be an object of the site `LC` of locally quasi-compact Hausdorff spaces, and write
`ε_X : LC_qc/X ⟶ LC_Zar/X`, `a_X : LC_qc/X ⟶ X_Zar` and `π_X : LC_Zar/X ⟶ X_Zar` for the
comparison morphisms of Stacks 0DCY.  For an abelian sheaf `F` on `X` the change-of-topology
direct image of `a_X^{-1}F` is `π_X^{-1}F`, and for a proper arrow `f : X ⟶ Y` of the site
the higher direct images along `f` for the two topologies agree on `a_X^{-1}F` once the
higher direct images along `ε_X` of the sheaves pulled back from the space vanish.

## Main definitions

In the namespace `Stacks.Topology.LocallyQuasiCompactZariskiSituation`:

* `qcAbelianDirectImageTopologicalInverseImageIsoUnconditional`: `ε_{X,*}(a_X^{-1}F) ≅ π_X^{-1}F`.
* `qcTopologicalHigherDirectImageIsoOfVanishing`: `a_Y^{-1}(R^i f_* F) ≅ R^i f_{qc,*}(a_X^{-1}F)`
  for a proper arrow `f`, given the vanishing condition `(V_n)` of Stacks 0EZF.

## Main results

* `isGrothendieckAbelian_qcSliceSheaf` and `enoughInjectives_qcSliceSheaf`: abelian sheaves on the
  localized quasi-compact site form a Grothendieck abelian category, hence have enough injectives.

## Implementation notes

Condition (0EZ6) of Situation 0EZ3 holds for the sheaves pulled back from the space
(`zariskiPullbackClass_isSheaf_qc`), and the Zariski proper base change in degree `i` is
`rightDerivedZariskiBaseChangeIso`; neither is carried as a hypothesis here.

## References

* [Stacks Project, Tag 0DCY](https://stacks.math.columbia.edu/tag/0DCY)
* [Stacks Project, Tag 0EZI](https://stacks.math.columbia.edu/tag/0EZI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace Stacks.Topology.LocallyQuasiCompactZariskiSituation

universe u w v

attribute [local instance] HasDerivedCategory.standard

variable {S₀ : Set LocallyQuasiCompactHausdorff.{u}} {Bound : Cardinal.{u} → Cardinal.{u}}

/-- Abelian sheaves on the localized quasi-compact site form a Grothendieck abelian category. -/
theorem isGrothendieckAbelian_qcSliceSheaf
    (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound) (X : S.category) :
    IsGrothendieckAbelian.{max (u + 1) v}
      (Sheaf (S.qcSite.grothendieckTopology.over X) AddCommGrpCat.{max (u + 1) v}) := by
  have _ : PreservesLimits (forget AddCommGrpCat.{max (u + 1) v}) :=
    AddCommGrpCat.forget_preservesLimits
  have _ : EssentiallySmall.{max (u + 1) v} (Over X) :=
    EssentiallySmall.mk' (AsSmall.equiv.{u, u + 1, max (u + 1) v} (C := Over X))
  exact Sheaf.isGrothendieckAbelian_of_essentiallySmall _ AddCommGrpCat.{max (u + 1) v}

/-- Abelian sheaves on the localized quasi-compact site have enough injectives. -/
theorem enoughInjectives_qcSliceSheaf
    (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound) (X : S.category) :
    EnoughInjectives
      (Sheaf (S.qcSite.grothendieckTopology.over X) AddCommGrpCat.{max (u + 1) v}) :=
  have := isGrothendieckAbelian_qcSliceSheaf.{u, w, v} S X
  inferInstance

section ClauseOne

variable (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound) (X : S.category)
  [HasSheafify (Opens.grothendieckTopology X.obj) AddCommGrpCat.{max (u + 1) v}]
  [HasSheafify (S.zariskiTopology.over X) AddCommGrpCat.{max (u + 1) v}]

/-- **Stacks 0DCY (1), the identification `ε_{X,*}(a_X^{-1}F) = π_X^{-1}F`.** For an object `X`
of the site and an abelian sheaf `F` on the space underlying `X`, the change-of-topology direct
image of `a_X^{-1}F` is `π_X^{-1}F`. -/
def qcAbelianDirectImageTopologicalInverseImageIsoUnconditional
    (F : Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{max (u + 1) v}) :
    (qcAbelianDirectImage.{u, w, v} S X).obj
        ((qcTopologicalAbelianInverseImage.{u, w, v} S X).obj F) ≅
      (S.abelianComparisonInverseImage.{u, w, max (u + 1) v} X).obj F :=
  have := isIso_qcAbelianComparisonAdjunction_unit_app.{u, w, v} S X _
    (zariskiPullbackClass_isSheaf_qc.{u, w, v} S X _
      (zariskiPullbackClass_abelianComparisonInverseImage.{u, w, v} S X F))
  (asIso ((qcAbelianComparisonAdjunction.{u, w, v} S X).unit.app
    ((S.abelianComparisonInverseImage.{u, w, max (u + 1) v} X).obj F))).symm

end ClauseOne

section ClauseTwo

variable (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound) {X Y : S.category}
  (f : X ⟶ Y)
  [HasSheafify (S.zariskiTopology.over X) AddCommGrpCat.{max (u + 1) v}]
  [HasSheafify (S.zariskiTopology.over Y) AddCommGrpCat.{max (u + 1) v}]
  [EnoughInjectives (Sheaf (S.qcSite.grothendieckTopology.over X) AddCommGrpCat.{max (u + 1) v})]
  [EnoughInjectives (Sheaf (S.zariskiTopology.over X) AddCommGrpCat.{max (u + 1) v})]
  [HasSheafify (Opens.grothendieckTopology X.obj) AddCommGrpCat.{max (u + 1) v}]
  [HasSheafify (Opens.grothendieckTopology Y.obj) AddCommGrpCat.{max (u + 1) v}]
  [EnoughInjectives (Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{max (u + 1) v})]

/-- **Stacks 0DCY (2).** Let `f : X ⟶ Y` be a proper arrow of the site and let `F` be an abelian
sheaf on the space underlying `X`. Given the vanishing condition `(V_n)` of Stacks 0EZF (`hV`),
for every `i` the inverse image along `a_Y` of `R^i f_* F` is `R^i f_{qc,*}` of `a_X^{-1}F`. -/
def qcTopologicalHigherDirectImageIsoOfVanishing (hf : S.properMorphisms f) (i : ℕ)
    (hV : ∀ G : Sheaf (S.zariskiTopology.over X) AddCommGrpCat.{max (u + 1) v},
      S.zariskiPullbackClass.{u, w, v} X G → ∀ j : ℕ, 0 < j →
        IsZero (((qcAbelianDirectImage.{u, w, v} S X).rightDerived j).obj
          ((qcAbelianInverseImage.{u, w, v} S X).obj G)))
    (F : Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{max (u + 1) v}) :
    (qcTopologicalAbelianInverseImage.{u, w, v} S Y).obj
        (((spaceDirectImage S f AddCommGrpCat.{max (u + 1) v}).rightDerived i).obj F) ≅
      ((qcAbelianSliceDirectImage.{u, w, v} S f).rightDerived i).obj
        ((qcTopologicalAbelianInverseImage.{u, w, v} S X).obj F) :=
  have h0DCU : ((sliceDirectImage S f AddCommGrpCat.{max (u + 1) v}).rightDerived i).obj
        ((S.abelianComparisonInverseImage.{u, w, max (u + 1) v} X).obj F) ≅
      (S.abelianComparisonInverseImage.{u, w, max (u + 1) v} Y).obj
        (((spaceDirectImage S f AddCommGrpCat.{max (u + 1) v}).rightDerived i).obj F) :=
    rightDerivedZariskiBaseChangeIso.{u, w, v} S f
      (isProperMap_of_properMorphisms S f hf) F i
  have hcmp : IsIso ((qcHigherDirectImageComparison.{u, w, v} S f i).app
      ((qcTopologicalAbelianInverseImage.{u, w, v} S X).obj F)) := by
    refine isIso_qcHigherDirectImageComparison_app.{u, w, v} S f i _
      (fun q hq _ => hV _ (zariskiPullbackClass_abelianComparisonInverseImage.{u, w, v} S X F)
        q hq) ?_
    refine (Presheaf.isSheaf_of_iso_iff ((sheafToPresheaf _ _).mapIso
      (((sliceDirectImage S f AddCommGrpCat.{max (u + 1) v}).rightDerived i).mapIso
        (qcAbelianDirectImageTopologicalInverseImageIsoUnconditional.{u, w, v} S X F)))).mpr ?_
    refine zariskiPullbackClass_isSheaf_qc.{u, w, v} S Y _ ?_
    rw [zariskiPullbackClass, ObjectProperty.prop_map_iff]
    exact ⟨((spaceDirectImage S f AddCommGrpCat.{max (u + 1) v}).rightDerived i).obj F,
      trivial, ⟨h0DCU.symm⟩⟩
  (qcAbelianInverseImage.{u, w, v} S Y).mapIso (h0DCU.symm ≪≫
      ((sliceDirectImage S f AddCommGrpCat.{max (u + 1) v}).rightDerived i).mapIso
        (qcAbelianDirectImageTopologicalInverseImageIsoUnconditional.{u, w, v} S X F).symm ≪≫
      asIso ((qcHigherDirectImageComparison.{u, w, v} S f i).app
        ((qcTopologicalAbelianInverseImage.{u, w, v} S X).obj F))) ≪≫
    asIso ((qcAbelianComparisonAdjunction.{u, w, v} S Y).counit.app
      (((qcAbelianSliceDirectImage.{u, w, v} S f).rightDerived i).obj
        ((qcTopologicalAbelianInverseImage.{u, w, v} S X).obj F)))

end ClauseTwo

end Stacks.Topology.LocallyQuasiCompactZariskiSituation

end
