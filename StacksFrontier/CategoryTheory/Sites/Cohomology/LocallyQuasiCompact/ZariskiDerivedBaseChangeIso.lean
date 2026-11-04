module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.ProperDerivedImageIso
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.QcComparisonNaturality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.ZariskiDerivedProperBaseChange
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.ZariskiHigherDirectImageClass

/-!
# The Zariski derived base change map of a proper morphism is invertible

For a morphism `f : X ⟶ Y` of the locally quasi-compact Zariski site, two derived base change
maps `π_Y^{-1}Rf_* ⟶ Rf_{Zar,*}π_X^{-1}` on bounded below derived categories are constructed in
this development: `derivedComparisonBaseChangeMap`, from the mate
`abelianZariskiComparisonBaseChangeMap` of the square of direct images, and
`properDerivedImageComparison`, from the unit-square-counit composite
`abelianProperDirectImageComparison`; the second is proved invertible for proper `f` (Stacks
0DCU). This file identifies the two, first underived and then derived, so that the first is
invertible for proper `f` as well.

## Main results

* `abelianProperDirectImageComparison_eq_abelianZariskiComparisonBaseChangeMap`: the two
  underived maps agree, the unit-square-counit composite being the inverse mate.
* `properDerivedImageComparison_eq_derivedComparisonBaseChangeMap`: the two derived maps agree.
* `isIso_derivedComparisonBaseChangeMap`: the derived base change map is invertible for proper
  `f`.

## References

* [Stacks Project, Tag 0DCU](https://stacks.math.columbia.edu/tag/0DCU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace Stacks.Topology.LocallyQuasiCompactZariskiSituation

universe u w v

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable {S₀ : Set LocallyQuasiCompactHausdorff.{u}} {Bound : Cardinal.{u} → Cardinal.{u}}
  (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound) {X Y : S.category} (f : X ⟶ Y)

/-- **The two underived Zariski base change maps agree**: the unit-square-counit composite
`abelianProperDirectImageComparison` is the mate `abelianZariskiComparisonBaseChangeMap` of the
square of direct images. -/
theorem abelianProperDirectImageComparison_eq_abelianZariskiComparisonBaseChangeMap :
    abelianProperDirectImageComparison.{u, w, v} S f =
      abelianZariskiComparisonBaseChangeMap.{u, w, v} S f :=
  NatTrans.ext (funext fun F ↦ (CategoryTheory.mateEquiv_symm_app
    (S.abelianComparisonAdjunction.{u, w, max (u + 1) v} X)
    (S.abelianComparisonAdjunction.{u, w, max (u + 1) v} Y)
    (zariskiComparisonDirectImageSquareIso S f AddCommGrpCat.{max (u + 1) v}).hom F).symm)

variable [HasSheafify (Opens.grothendieckTopology X.obj) AddCommGrpCat.{max (u + 1) v}]
  [HasSheafify (Opens.grothendieckTopology Y.obj) AddCommGrpCat.{max (u + 1) v}]
  [HasSheafify (S.zariskiTopology.over X) AddCommGrpCat.{max (u + 1) v}]
  [HasSheafify (S.zariskiTopology.over Y) AddCommGrpCat.{max (u + 1) v}]
  [EnoughInjectives (Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{max (u + 1) v})]
  [EnoughInjectives (Sheaf (Opens.grothendieckTopology Y.obj) AddCommGrpCat.{max (u + 1) v})]
  [EnoughInjectives (Sheaf (S.zariskiTopology.over X) AddCommGrpCat.{max (u + 1) v})]

/-- **The two derived Zariski base change maps agree.** -/
theorem properDerivedImageComparison_eq_derivedComparisonBaseChangeMap :
    properDerivedImageComparison.{u, w, v} S f = derivedComparisonBaseChangeMap.{u, w, v} S f := by
  refine eq_derivedComparisonBaseChangeMap_of_fac.{u, w, v} S f _ ?_
  refine (properDerivedImageComparison_fac.{u, w, v} S f).trans ?_
  have h :=
    abelianProperDirectImageComparison_eq_abelianZariskiComparisonBaseChangeMap.{u, w, v} S f
  show baseChangeOnHomotopy.{u, w, v} S f ≫ _ ≫ _ = _
  simp only [baseChangeOnHomotopy, zariskiBaseChange, h, Category.assoc]
  rfl

/-- **Stacks 0DCU (7b), for the derived base change map of `ZariskiDerivedProperBaseChange`**:
for a proper `f` the Zariski derived base change map `π_Y^{-1}Rf_* ⟶ Rf_{Zar,*}π_X^{-1}` is an
isomorphism, being `properDerivedImageComparison`. -/
theorem isIso_derivedComparisonBaseChangeMap (hf : S.properMorphisms f) :
    IsIso (derivedComparisonBaseChangeMap.{u, w, v} S f) := by
  rw [← properDerivedImageComparison_eq_derivedComparisonBaseChangeMap]
  exact properDerivedImageComparison_isIso.{u, w, v} S f (isProperMap_of_properMorphisms S f hf)

end Stacks.Topology.LocallyQuasiCompactZariskiSituation

end
