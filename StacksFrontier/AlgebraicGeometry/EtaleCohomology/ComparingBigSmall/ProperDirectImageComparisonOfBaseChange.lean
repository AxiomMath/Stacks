module

public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedFunctorSingleRightDerived
public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjective
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlusComparisons
public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactPlusHomologyComposition
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.ComparingBigSmall.DerivedProperDirectImage
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.ComparingBigSmall.ProperEtaleComparisonSituation
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsion.TorsionCohomologySingle
public import StacksFrontier.Homology.Injectives.KInjective.RightDerivedCriterion

/-!
# Higher direct images along a proper morphism, from proper base change

Let `B` be a big étale site. The comparison `AlgebraicGeometry.ProperDirectImageComparison B` of
higher direct images along proper morphisms, `R^i f_{big,*}(π_X⁻¹F) ≅ π_Y⁻¹(R^i f_{small,*}F)`
for a torsion abelian sheaf `F`, is degree `i` of Stacks 0DDJ (2). It follows from the proper base
change theorem in the form of Stacks 095T: granted that cohomology commutes with base change for
every proper morphism of schemes, the derived base change map of Stacks 0DDJ (2) is an
isomorphism at `F` placed in degree zero
(`AlgebraicGeometry.isIso_bigSmallEtaleDerivedBaseChange_app_of_cohomologyCommutesWithBaseChange`),
and its cohomology in degree `i` is the asserted isomorphism.

## Main results

* `AlgebraicGeometry.properDirectImageComparison_of_cohomologyCommutesWithBaseChange` — granted
  Stacks 095T, `AlgebraicGeometry.ProperDirectImageComparison B` holds.
* `AlgebraicGeometry.bigSmallEtaleDerivedPlusBaseChange` — the base change map
  `π_Y⁻¹(Rf_{small,*}L) ⟶ Rf_{big,*}(π_X⁻¹L)` of Stacks 0DDJ (2) on `D⁺`.
* `AlgebraicGeometry.isIso_bigSmallEtaleDerivedPlusBaseChange_of_cohomologyCommutesWithBaseChange`
  — it is an isomorphism for `f` proper and `L` with torsion cohomology sheaves, granted
  Stacks 095T.

## Implementation notes

The derived direct images on the unbounded derived categories are the total right derived
functors, which exist because abelian sheaves on the small and the big étale sites form
Grothendieck abelian categories, hence have K-injective resolutions. The cohomology of a right
derived functor at an object placed in degree zero is Mathlib's `rightDerived`, by
`Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived`, and the exact functors
`π⁻¹` commute with placing in degree zero and with cohomology.

## References

* [Stacks Project, Tag 0DDJ](https://stacks.math.columbia.edu/tag/0DDJ)
* [Stacks Project, Tag 095T](https://stacks.math.columbia.edu/tag/095T)
* [Stacks Project, Tag 0F0I](https://stacks.math.columbia.edu/tag/0F0I)
* [Stacks Project, Tag 0F0J](https://stacks.math.columbia.edu/tag/0F0J)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard smallEtaleSheaf_isGrothendieckAbelian
  bigEtaleSheaf_isGrothendieckAbelian

variable (B : BigEtaleSite.{u})

/-- **`ProperDirectImageComparison` from proper base change.** Granted Stacks 095T — cohomology
commutes with base change along every proper morphism of schemes — the higher direct images along
a proper morphism `f : X ⟶ Y` of the big étale site satisfy
`R^i f_{big,*}(π_X⁻¹F) ≅ π_Y⁻¹(R^i f_{small,*}F)` for every torsion abelian sheaf `F` on `X_étale`
and every `i`: this is degree `i` of Stacks 0DDJ (2) at `F` placed in degree zero. -/
public theorem properDirectImageComparison_of_cohomologyCommutesWithBaseChange
    (h095T : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f],
      Stacks.EtaleCohomology.CohomologyCommutesWithBaseChange.{u, 0} f) :
    ProperDirectImageComparison B := by
  intro X Y f hf F hF i
  have : IsProper (B.inclusion.map f) := hf
  let wS := B.smallPushforward f AddCommGrpCat.{u + 1}
  let wB := (Over.pullback f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
    (BigEtaleOver.topology B Y.obj Y.property) (BigEtaleOver.topology B X.obj X.property)
  have hresS := fun K => Stacks.Injectives.exists_kInjective_resolution_of_grothendieck
    (C := Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1}) K
  have hresB := fun K => Stacks.Injectives.exists_kInjective_resolution_of_grothendieck
    (C := Sheaf (BigEtaleOver.topology B X.obj X.property) AddCommGrpCat.{u + 1}) K
  have := (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective.{
      _, _, 0, _, _, 0}
    (wS.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) hresS).1
  have := (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective.{
      _, _, 0, _, _, 0}
    (wB.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) hresB).1
  let RfSmall := (wS.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).totalRightDerived
    DerivedCategory.Qh (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))
  let αSmall := (wS.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh).totalRightDerivedUnit DerivedCategory.Qh
      (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))
  let RfBig := (wB.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).totalRightDerived
    DerivedCategory.Qh (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))
  let αBig := (wB.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh).totalRightDerivedUnit DerivedCategory.Qh
      (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))
  let πX := (SmallEtale.inclusion B X.obj X.property).sheafPullback AddCommGrpCat.{u + 1}
    (SmallEtale.topology B X.obj X.property) (BigEtaleOver.topology B X.obj X.property)
  let πY := (SmallEtale.inclusion B Y.obj Y.property).sheafPullback AddCommGrpCat.{u + 1}
    (SmallEtale.topology B Y.obj Y.property) (BigEtaleOver.topology B Y.obj Y.property)
  let K := (DerivedCategory.singleFunctor _ 0).obj F
  have := isIso_bigSmallEtaleDerivedBaseChange_app_of_cohomologyCommutesWithBaseChange B f
    RfSmall RfBig αSmall αBig (h095T _) K 0 inferInstance
    (Stacks.Torsion.torsionCohomologyProperty_singleFunctor _ F hF)
  exact ⟨((Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived wB RfBig αBig hresB
      i).app (πX.obj F)).symm ≪≫
    (DerivedCategory.homologyFunctor _ (i : ℤ)).mapIso
      (RfBig.mapIso ((πX.mapDerivedCategorySingleFunctor 0).app F).symm ≪≫
        (asIso ((bigSmallEtaleDerivedBaseChange B f RfSmall RfBig αSmall αBig).app K)).symm) ≪≫
    (Stacks.DerivedFunctor.derivedHomologyIso πY (i : ℤ)).app (RfSmall.obj K) ≪≫
    πY.mapIso ((Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived wS RfSmall
      αSmall hresS i).app F)⟩

/-! ### The derived form of Stacks 0DDJ (2) on `D⁺` -/

section Plus

variable {A C : Type*} [Category A] [Abelian A] [HasDerivedCategory A] [EnoughInjectives A]
  [Category C] [Abelian C] [HasDerivedCategory C]

/-- **A bounded-below right derived functor computes an unbounded one on bounded-below objects.**
For an additive `w`, an object `L` of `D⁺` and a right derived functor `H` of `w` on the unbounded
derived categories, `ι(R⁺w L) ≅ H(ι L)`, provided K-injective resolutions exist. -/
def rightDerivedFunctorPlusιObjIso (w : A ⥤ C) [w.Additive]
    (H : DerivedCategory A ⥤ DerivedCategory C)
    (α : w.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ H)
    [H.IsRightDerivedFunctor α (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
    (hres : ∀ K : CochainComplex A ℤ, ∃ (I : CochainComplex A ℤ) (f : K ⟶ I),
      I.IsKInjective ∧ QuasiIso f)
    (L : DerivedCategory.Plus A) :
    DerivedCategory.Plus.ι.obj (w.rightDerivedFunctorPlus.obj L) ≅
      H.obj (DerivedCategory.Plus.ι.obj L) := by
  let I := (InjectiveObject.ι A).mapHomotopyCategoryPlus
  let E := I ⋙ DerivedCategory.Plus.Qh
  let K := E.objPreimage L
  let e : E.obj K ≅ L := E.objObjPreimageIso L
  have hK : CochainComplex.IsKInjective (I.obj K).obj.as := by
    obtain ⟨n, hn⟩ := (HomotopyCategory.plus_quotient_obj_iff K.obj.as).1 K.property
    have : CochainComplex.IsStrictlyGE (I.obj K).obj.as n := by
      change CochainComplex.IsStrictlyGE
        (((InjectiveObject.ι A).mapHomologicalComplex (.up ℤ)).obj K.obj.as) n
      infer_instance
    exact CochainComplex.isKInjective_of_injective _ n
  have hα := (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective
    (w.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) hres).2
      DerivedCategory.Qh H α (I.obj K).obj.as hK
  exact DerivedCategory.Plus.ι.mapIso (w.rightDerivedFunctorPlus.mapIso e.symm) ≪≫
    DerivedCategory.Plus.ι.mapIso (asIso (w.rightDerivedFunctorPlusUnit.app (I.obj K))).symm ≪≫
    (DerivedCategory.Plus.QhCompιIsoιCompQh C).app (w.mapHomotopyCategoryPlus.obj (I.obj K)) ≪≫
    DerivedCategory.Qh.mapIso
      ((Functor.mapHomotopyCategoryPlusCompιIso w).app (I.obj K)) ≪≫
    @asIso _ _ _ _ (α.app ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj (I.obj K).obj.as))
      hα ≪≫
    H.mapIso (((DerivedCategory.Plus.QhCompιIsoιCompQh A).app (I.obj K)).symm ≪≫
      DerivedCategory.Plus.ι.mapIso e)

end Plus

/-! ### The base change map of Stacks 0DDJ (2) on `D⁺` -/

section PlusBaseChange

variable {X Y : B.Scheme} (f : X ⟶ Y)
  {JX : GrothendieckTopology (BigEtaleOver B X.obj X.property)}
  {JY : GrothendieckTopology (BigEtaleOver B Y.obj Y.property)}
  (hX : BigEtaleOver.topology B X.obj X.property = JX)
  (hY : BigEtaleOver.topology B Y.obj Y.property = JY)
  [(SmallEtale.inclusion B X.obj X.property).IsContinuous
    (SmallEtale.topology B X.obj X.property) JX]
  [(SmallEtale.inclusion B Y.obj Y.property).IsContinuous
    (SmallEtale.topology B Y.obj Y.property) JY]
  [HasSheafify JX Ab.{u + 1}] [HasSheafify JY Ab.{u + 1}]
  [(Over.map f).IsCocontinuous JX JY]
  [EnoughInjectives (Sheaf JX Ab.{u + 1})]
  [((Over.map f).sheafPushforwardCocontinuous Ab.{u + 1} JX JY).Additive]
  [PreservesFiniteLimits ((SmallEtale.inclusion B X.obj X.property).sheafPullback Ab.{u + 1}
    (SmallEtale.topology B X.obj X.property) JX)]
  [PreservesFiniteColimits ((SmallEtale.inclusion B X.obj X.property).sheafPullback Ab.{u + 1}
    (SmallEtale.topology B X.obj X.property) JX)]
  [((SmallEtale.inclusion B X.obj X.property).sheafPullback Ab.{u + 1}
    (SmallEtale.topology B X.obj X.property) JX).Additive]
  [PreservesFiniteLimits ((SmallEtale.inclusion B Y.obj Y.property).sheafPullback Ab.{u + 1}
    (SmallEtale.topology B Y.obj Y.property) JY)]
  [PreservesFiniteColimits ((SmallEtale.inclusion B Y.obj Y.property).sheafPullback Ab.{u + 1}
    (SmallEtale.topology B Y.obj Y.property) JY)]
  [((SmallEtale.inclusion B Y.obj Y.property).sheafPullback Ab.{u + 1}
    (SmallEtale.topology B Y.obj Y.property) JY).Additive]

/-- **The base change map of Stacks 0DDJ (2) on `D⁺`.** For a morphism `f : X ⟶ Y` of a big étale
site and `L` in `D⁺(X_étale)`, the base change map `π_Y⁻¹(Rf_{small,*}L) ⟶ Rf_{big,*}(π_X⁻¹L)` of
the square of topoi `π_Y ∘ f_big = f_small ∘ π_X`, the derived functors being those of `D⁺` and
the topologies on the slices any topologies equal to the slice topologies. It is the canonical map
`AlgebraicGeometry.bigSmallEtaleDerivedBaseChange` of the unbounded derived categories at `L`,
read through the canonical identifications `ι(R⁺w L) ≅ Rw(ι L)` of the bounded below right
derived functors with the unbounded ones (`rightDerivedFunctorPlusιObjIso`), the inclusion `ι` of
`D⁺` being fully faithful. -/
public def bigSmallEtaleDerivedPlusBaseChange
    (L : DerivedCategory.Plus (Sheaf (SmallEtale.topology B X.obj X.property) Ab.{u + 1})) :
    ((SmallEtale.inclusion B Y.obj Y.property).sheafPullback Ab.{u + 1}
        (SmallEtale.topology B Y.obj Y.property) JY).mapDerivedCategoryPlus.obj
        ((B.smallPushforward f Ab.{u + 1}).rightDerivedFunctorPlus.obj L) ⟶
      ((Over.map f).sheafPushforwardCocontinuous Ab.{u + 1} JX JY).rightDerivedFunctorPlus.obj
        (((SmallEtale.inclusion B X.obj X.property).sheafPullback Ab.{u + 1}
          (SmallEtale.topology B X.obj X.property) JX).mapDerivedCategoryPlus.obj L) := by
  subst hX hY
  let wS := B.smallPushforward f AddCommGrpCat.{u + 1}
  let wB := (Over.pullback f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
    (BigEtaleOver.topology B Y.obj Y.property) (BigEtaleOver.topology B X.obj X.property)
  have hresS := fun K => Stacks.Injectives.exists_kInjective_resolution_of_grothendieck
    (C := Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1}) K
  have hresB := fun K => Stacks.Injectives.exists_kInjective_resolution_of_grothendieck
    (C := Sheaf (BigEtaleOver.topology B X.obj X.property) AddCommGrpCat.{u + 1}) K
  haveI := (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective
    (wS.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) hresS).1
  haveI := (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective
    (wB.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) hresB).1
  let RfSmall := (wS.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).totalRightDerived
    DerivedCategory.Qh (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))
  let αSmall := (wS.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh).totalRightDerivedUnit DerivedCategory.Qh
      (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))
  let RfBig := (wB.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).totalRightDerived
    DerivedCategory.Qh (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))
  let αBig := (wB.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh).totalRightDerivedUnit DerivedCategory.Qh
      (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))
  let πX := (SmallEtale.inclusion B X.obj X.property).sheafPullback AddCommGrpCat.{u + 1}
    (SmallEtale.topology B X.obj X.property) (BigEtaleOver.topology B X.obj X.property)
  let πY := (SmallEtale.inclusion B Y.obj Y.property).sheafPullback AddCommGrpCat.{u + 1}
    (SmallEtale.topology B Y.obj Y.property) (BigEtaleOver.topology B Y.obj Y.property)
  let e : DerivedCategory.Plus.ι.obj
        (πY.mapDerivedCategoryPlus.obj (wS.rightDerivedFunctorPlus.obj L)) ⟶
      DerivedCategory.Plus.ι.obj
        (wB.rightDerivedFunctorPlus.obj (πX.mapDerivedCategoryPlus.obj L)) :=
    πY.mapDerivedCategory.map (rightDerivedFunctorPlusιObjIso wS RfSmall αSmall hresS L).hom ≫
      (bigSmallEtaleDerivedBaseChange B f RfSmall RfBig αSmall αBig).app
        (DerivedCategory.Plus.ι.obj L) ≫
      (rightDerivedFunctorPlusιObjIso wB RfBig αBig hresB (πX.mapDerivedCategoryPlus.obj L)).inv
  exact DerivedCategory.TStructure.t.plus.fullyFaithfulι.preimage e ≫
    ((Functor.rightDerivedFunctorPlusNatIso
      ((Over.mapPullbackAdj f).sheafPushforwardCocontinuousIso Ab.{u + 1})).app _).inv

/-- **Stacks 0DDJ (2) on `D⁺`, from proper base change.** Granted Stacks 095T, for a proper
morphism `f : X ⟶ Y` of a big étale site and `L` in `D⁺(X_étale)` with torsion cohomology
sheaves, the base change map `π_Y⁻¹(Rf_{small,*}L) ⟶ Rf_{big,*}(π_X⁻¹L)`,
`AlgebraicGeometry.bigSmallEtaleDerivedPlusBaseChange`, is an isomorphism. -/
public theorem isIso_bigSmallEtaleDerivedPlusBaseChange_of_cohomologyCommutesWithBaseChange
    (h095T : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f],
      Stacks.EtaleCohomology.CohomologyCommutesWithBaseChange.{u, 0} f)
    (hf : IsProper (B.inclusion.map f))
    (L : DerivedCategory.Plus (Sheaf (SmallEtale.topology B X.obj X.property) Ab.{u + 1}))
    (hL : ∀ i : ℤ, Stacks.Torsion.torsionSheafProperty.{u + 1}
      (SmallEtale.topology B X.obj X.property)
      ((DerivedCategory.Plus.homologyFunctor _ i).obj L)) :
    IsIso (bigSmallEtaleDerivedPlusBaseChange B f hX hY L) := by
  subst hX hY
  have : IsProper (B.inclusion.map f) := hf
  let wS := B.smallPushforward f AddCommGrpCat.{u + 1}
  let wB := (Over.pullback f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
    (BigEtaleOver.topology B Y.obj Y.property) (BigEtaleOver.topology B X.obj X.property)
  have hresS := fun K => Stacks.Injectives.exists_kInjective_resolution_of_grothendieck
    (C := Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1}) K
  have hresB := fun K => Stacks.Injectives.exists_kInjective_resolution_of_grothendieck
    (C := Sheaf (BigEtaleOver.topology B X.obj X.property) AddCommGrpCat.{u + 1}) K
  have := (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective.{
      _, _, 0, _, _, 0}
    (wS.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) hresS).1
  have := (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective.{
      _, _, 0, _, _, 0}
    (wB.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) hresB).1
  let RfSmall := (wS.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).totalRightDerived
    DerivedCategory.Qh (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))
  let αSmall := (wS.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh).totalRightDerivedUnit DerivedCategory.Qh
      (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))
  let RfBig := (wB.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).totalRightDerived
    DerivedCategory.Qh (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))
  let αBig := (wB.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh).totalRightDerivedUnit DerivedCategory.Qh
      (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))
  let πX := (SmallEtale.inclusion B X.obj X.property).sheafPullback AddCommGrpCat.{u + 1}
    (SmallEtale.topology B X.obj X.property) (BigEtaleOver.topology B X.obj X.property)
  let πY := (SmallEtale.inclusion B Y.obj Y.property).sheafPullback AddCommGrpCat.{u + 1}
    (SmallEtale.topology B Y.obj Y.property) (BigEtaleOver.topology B Y.obj Y.property)
  have hK : (DerivedCategory.Plus.ι.obj L).IsGE (L.property.choose) := L.property.choose_spec
  have h0DDJ := isIso_bigSmallEtaleDerivedBaseChange_app_of_cohomologyCommutesWithBaseChange B f
    RfSmall RfBig αSmall αBig (h095T _) (DerivedCategory.Plus.ι.obj L) _ hK hL
  let e : DerivedCategory.Plus.ι.obj
        (πY.mapDerivedCategoryPlus.obj (wS.rightDerivedFunctorPlus.obj L)) ⟶
      DerivedCategory.Plus.ι.obj
        (wB.rightDerivedFunctorPlus.obj (πX.mapDerivedCategoryPlus.obj L)) :=
    πY.mapDerivedCategory.map (rightDerivedFunctorPlusιObjIso wS RfSmall αSmall hresS L).hom ≫
      (bigSmallEtaleDerivedBaseChange B f RfSmall RfBig αSmall αBig).app
        (DerivedCategory.Plus.ι.obj L) ≫
      (rightDerivedFunctorPlusιObjIso wB RfBig αBig hresB (πX.mapDerivedCategoryPlus.obj L)).inv
  have : IsIso e := @IsIso.comp_isIso _ _ _ _ _ _ _ (Functor.map_isIso _ _)
    (@IsIso.comp_isIso _ _ _ _ _ _ _ h0DDJ (Iso.isIso_inv _))
  exact @IsIso.comp_isIso _ _ _ _ _ _ _
    (DerivedCategory.TStructure.t.plus.fullyFaithfulι.preimageIso (asIso e)).isIso_hom
    inferInstance

end PlusBaseChange

end AlgebraicGeometry

end
