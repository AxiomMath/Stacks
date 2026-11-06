module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.ProperDerivedImageIso
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.ZariskiComparisonSituationData
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.ZariskiProperBaseChange
public import StacksFrontier.Homology.DerivedIndexing.Basic
import StacksCore.Tactic.StacksAttribute

/-!
# Higher direct images along a proper arrow of sheaves pulled back from the space

Let `S` be a locally quasi-compact Zariski situation, `f : X ⟶ Y` a proper arrow of its site and
`G` an abelian sheaf on the localized Zariski site over `X` of the form `π_X^{-1}G₀`. This file
proves that every higher direct image `R^i f_{Zar,*}G` is again of that form, namely `π_Y^{-1}` of
the `i`-th higher direct image of `G₀` along the underlying continuous map. This is condition
(0EZ7) of Situation 0EZ3 for the choice of data made by Stacks 0EZI.

## Main results

All in the namespace `Stacks.Topology.LocallyQuasiCompactZariskiSituation`.

* `zariskiPullbackClass_rightDerived_sliceDirectImage`: **condition (0EZ7)** — the class `A'_X` of
  sheaves pulled back from the space is carried into `A'_Y` by every `R^i f_{Zar,*}` along a proper
  arrow `f`.

## Implementation notes

The direct image is written as `sliceDirectImage`, restriction along `Over.pullback f`, which is
the form `zariskiSlicePushforwardIso` identifies with the pushforward attached to cocontinuity of
`Over.map f`, and the form in which the derived clause of Stacks 0DCU is stated.

The statement is degreewise, in the `ℕ`-indexed `CategoryTheory.Functor.rightDerived`, whereas
Stacks 0DCU compares bounded-below derived functors, whose degreewise content is the `ℤ`-indexed
homology `H^i(R(-)(-[0]))`; the two indexings are identified by
`Stacks.DerivedIndexing.rightDerivedIso`. The local `exactDerivedSingleIso` and
`exactDerivedHomologyIso` record, for a functor whose derived unit on `D⁺` is invertible, that
`RF(M[0]) ≅ (FM)[0]` and that `F` commutes with degree-`n` homology of a derived functor; both
hypotheses hold for `π^{-1}`, which is exact.

`EnoughInjectives` for abelian sheaves on the small Zariski site of an object and on the localized
big site is not a global instance, but `enoughInjectives_sheafOpens_site` and
`enoughInjectives_zariskiSliceSheaf` prove it at every object of the situation with no hypothesis.
They are made local instances, so that the statement — which needs `HasInjectiveResolutions` on the
source of `R^i f_{Zar,*}` merely to be written down — carries no instance binder.
`HasDerivedCategory.standard` is a local instance for the same reason.

## References

* [Stacks Project, Tag 0EZI](https://stacks.math.columbia.edu/tag/0EZI)
* [Stacks Project, Tag 0EZ3](https://stacks.math.columbia.edu/tag/0EZ3)
* [Stacks Project, Tag 0DCU](https://stacks.math.columbia.edu/tag/0DCU)
* [Stacks Project, Tag 005O](https://stacks.math.columbia.edu/tag/005O)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace Stacks.Topology.LocallyQuasiCompactZariskiSituation

universe u w v

/-- For a functor whose right derived unit on `D⁺` is invertible, the derived functor of a complex
concentrated in degree zero is again concentrated in degree zero: `RF(M[0]) ≅ (FM)[0]`. -/
private def exactDerivedSingleIso
    {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory A]
    {B : Type*} [Category* B] [Abelian B] [HasDerivedCategory B]
    [EnoughInjectives A] (F : A ⥤ B) [F.Additive]
    [IsIso F.rightDerivedFunctorPlusUnith] (M : A) :
    F.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor A 0).obj M) ≅
      (DerivedCategory.Plus.singleFunctor B 0).obj (F.obj M) :=
  F.rightDerivedFunctorPlus.mapIso ((Functor.singleFunctorPlusIsoCompQh 0).app M) ≪≫
    ((asIso F.rightDerivedFunctorPlusUnith).app
      ((HomotopyCategory.Plus.singleFunctor A 0).obj M)).symm ≪≫
    (Functor.mapSingleFunctorCompQhIso F).app M

/-- For a functor which preserves homology and whose right derived unit on `D⁺` is invertible,
degree-`n` homology of `RF(M)` is `F` of degree-`n` homology of `M`. -/
private def exactDerivedHomologyIso
    {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory A]
    {B : Type*} [Category* B] [Abelian B] [HasDerivedCategory B]
    [EnoughInjectives A] (F : A ⥤ B) [F.Additive] [F.PreservesHomology]
    [IsIso F.rightDerivedFunctorPlusUnith] (M : DerivedCategory.Plus A) (n : ℤ) :
    (DerivedCategory.Plus.homologyFunctor B n).obj (F.rightDerivedFunctorPlus.obj M) ≅
      F.obj ((DerivedCategory.Plus.homologyFunctor A n).obj M) := by
  let H := DerivedCategory.Plus.homologyFunctor B n
  let HA := DerivedCategory.Plus.homologyFunctor A n
  let L := DerivedCategory.Plus.Qh.objPreimage M
  let e : DerivedCategory.Plus.Qh.obj L ≅ M := DerivedCategory.Plus.Qh.objObjPreimageIso M
  refine H.mapIso (F.rightDerivedFunctorPlus.mapIso e.symm) ≪≫ ?_ ≪≫ F.mapIso (HA.mapIso e)
  let K := (HomotopyCategory.Plus.quotient_obj_surjective L).choose
  rw [← (HomotopyCategory.Plus.quotient_obj_surjective L).choose_spec]
  exact H.mapIso ((asIso F.rightDerivedFunctorPlusUnith).app
      ((HomotopyCategory.Plus.quotient A).obj K)).symm ≪≫
    (DerivedCategory.homologyFunctor B n).mapIso
      (DerivedCategory.Qh.mapIso ((F.mapHomotopyCategoryFactors (.up ℤ)).app K.obj) ≪≫
        (DerivedCategory.quotientCompQhIso B).app _) ≪≫
    (DerivedCategory.homologyFunctorFactors B n).app _ ≪≫
    (K.obj.sc n).mapHomologyIso F ≪≫
    F.mapIso (((DerivedCategory.homologyFunctor A n).mapIso
      ((DerivedCategory.quotientCompQhIso A).app K.obj) ≪≫
      (DerivedCategory.homologyFunctorFactors A n).app K.obj).symm)

attribute [local instance] HasDerivedCategory.standard
  enoughInjectives_zariskiSliceSheaf enoughInjectives_sheafOpens_site

variable {S₀ : Set LocallyQuasiCompactHausdorff.{u}} {Bound : Cardinal.{u} → Cardinal.{u}}

/-- **Stacks 0EZI, the condition on higher direct images.** Let `f : X ⟶ Y` be a proper arrow of
the locally quasi-compact Zariski site and let `G` be an abelian sheaf on the localized Zariski
site over `X` of the form `π_X^{-1}G₀`. Then for every `i` the higher direct image `R^i f_{Zar,*}G`
is again of that form: it is `π_Y^{-1}` of the `i`-th higher direct image of `G₀` along the
continuous map underlying `f`.

This is condition (0EZ7) of Situation 0EZ3 for the data chosen by Stacks 0EZI — the proper arrows
as the class `P`, the sheaves pulled back from the space as `A'`. -/
@[stacks 0EZI "condition (0EZ7) of Situation 0EZ3: higher direct images along a proper arrow stay
in the class"]
theorem zariskiPullbackClass_rightDerived_sliceDirectImage
    (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound)
    ⦃X Y : S.category⦄ (f : X ⟶ Y) (hf : S.properMorphisms f)
    (G : Sheaf (S.zariskiTopology.over X) AddCommGrpCat.{max (u + 1) v})
    (hG : S.zariskiPullbackClass.{u, w, v} X G) (i : ℕ) :
    S.zariskiPullbackClass.{u, w, v} Y
      (((sliceDirectImage S f AddCommGrpCat.{max (u + 1) v}).rightDerived i).obj G) := by
  rw [zariskiPullbackClass, ObjectProperty.prop_map_iff] at hG ⊢
  obtain ⟨G₀, -, ⟨e⟩⟩ := hG
  let PX := S.abelianComparisonInverseImage.{u, w, max (u + 1) v} X
  let PY := S.abelianComparisonInverseImage.{u, w, max (u + 1) v} Y
  let T := topologicalPushforward.{u, w, v} S f
  let R := sliceDirectImage S f AddCommGrpCat.{max (u + 1) v}
  have : IsIso (properDerivedImageComparison.{u, w, v} S f) :=
    properDerivedImageComparison_isIso.{u, w, v} S f
      (S.stacksIsProperMap_of_properMorphisms f hf)
  let M := (DerivedCategory.Plus.singleFunctor
    (Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{max (u + 1) v}) 0).obj G₀
  let c : PY.rightDerivedFunctorPlus.obj (T.rightDerivedFunctorPlus.obj M) ≅
      R.rightDerivedFunctorPlus.obj (PX.rightDerivedFunctorPlus.obj M) :=
    (asIso (properDerivedImageComparison.{u, w, v} S f)).app M
  let H := DerivedCategory.Plus.homologyFunctor
    (Sheaf (S.zariskiTopology.over Y) AddCommGrpCat.{max (u + 1) v}) (i : ℤ)
  refine ⟨(T.rightDerived i).obj G₀, trivial, ⟨?_⟩⟩
  exact PY.mapIso ((Stacks.DerivedIndexing.rightDerivedIso T i).app G₀) ≪≫
    (exactDerivedHomologyIso PY (T.rightDerivedFunctorPlus.obj M) (i : ℤ)).symm ≪≫
    H.mapIso (c ≪≫ R.rightDerivedFunctorPlus.mapIso (exactDerivedSingleIso PX G₀)) ≪≫
    ((Stacks.DerivedIndexing.rightDerivedIso R i).app (PX.obj G₀)).symm ≪≫
    (R.rightDerived i).mapIso e

end Stacks.Topology.LocallyQuasiCompactZariskiSituation

end
