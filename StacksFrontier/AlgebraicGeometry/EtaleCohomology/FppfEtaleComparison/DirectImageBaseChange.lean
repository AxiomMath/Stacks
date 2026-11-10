module

public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.FppfEtaleComparison.FinitePushforwardInputs
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.ComparingBigSmall.ProperEtaleChangeOfTopology
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.ComparingBigSmall.ProperDirectImageCommutation
import StacksCore.Tactic.StacksAttribute

/-!
# Comparing fppf and étale cohomology: direct images (Stacks 0DDS)

Let `B` be a big fppf site and `(Sch/S)_étale` the étale site on the same category of schemes
(`AlgebraicGeometry.associatedBigEtaleSite`). For an object `X` write `π_X⁻¹` for the inverse
image from `X_étale` to the big étale site of `X`, `ε_X⁻¹` for the change of topology from the big
étale to the big fppf site of `X`, and `a_X⁻¹ = ε_X⁻¹ ∘ π_X⁻¹`. This file proves Stacks 0DDS:

1. `ε_{X,*}a_X⁻¹F = π_X⁻¹F` and `R^iε_{X,*}(a_X⁻¹F) = 0` for `i > 0`;
2. `a_Y⁻¹(R^if_{small,*}F) = R^if_{big,fppf,*}(a_X⁻¹F)` for `f` finite;
3. `π_X⁻¹K ⟶ Rε_{X,*}(a_X⁻¹K)` is an isomorphism for `K` in `D⁺(X_étale)`;
4. `a_Y⁻¹(Rf_{small,*}K) = Rf_{big,fppf,*}(a_X⁻¹K)` for `f` finite and `K` in `D⁺(X_étale)`;
5. the same for `f` proper and `K` in `D⁺(X_étale)` with torsion cohomology sheaves.

In (2), (4) and (5) the identification is the canonical base change map of the square of topoi
`a_Y ∘ f_{big,fppf} = f_{small} ∘ a_X` (Stacks 0DDM).

## Main definitions

* `AlgebraicGeometry.fppfSmallEtaleDerivedDirectImageBaseChange`: the base change map
  `a_Y⁻¹(Rf_{small,*}K) ⟶ Rf_{big,fppf,*}(a_X⁻¹K)` on `D⁺`.
* `AlgebraicGeometry.fppfSmallEtaleHigherDirectImageBaseChange`: the base change map
  `a_Y⁻¹(R^if_{small,*}F) ⟶ R^if_{big,fppf,*}(a_X⁻¹F)`, its cohomology in degree `i` at `F[0]`.

## Main results

* `AlgebraicGeometry.fppfSmallEtale_projectionPullback_comparison`: **Stacks 0DDS (1)**.
* `AlgebraicGeometry.isIso_fppfSmallEtaleHigherDirectImageBaseChange_of_isFinite`:
  **Stacks 0DDS (2)**.
* `AlgebraicGeometry.isIso_fppfSmallEtaleDerivedUnit`: **Stacks 0DDS (3)**.
* `AlgebraicGeometry.isIso_fppfSmallEtaleDerivedDirectImageBaseChange_of_isFinite`:
  **Stacks 0DDS (4)**.
* `AlgebraicGeometry.isIso_fppfSmallEtaleDerivedDirectImageBaseChange_of_isProper`:
  **Stacks 0DDS (5)**.

## Implementation notes

The base change map of (4) and (5) is the composite of the base change maps of the two squares
the square of `a = π ∘ ε` is pasted from: `ε_Y⁻¹` applied to the base change map
`π_Y⁻¹(Rf_{small,*}K) ⟶ Rf_{big,étale,*}(π_X⁻¹K)` of Stacks 0DDJ
(`AlgebraicGeometry.bigSmallEtaleDerivedPlusBaseChange`), followed by the base change map
`ε_Y⁻¹(Rf_{big,étale,*}K') ⟶ Rf_{big,fppf,*}(ε_X⁻¹K')` of the change of topology
(`Stacks.ComparingTopologies.derivedComparisonBaseChange`) at `K' = π_X⁻¹K`, in Situation 0EZ3 for
the fppf and étale topologies (Stacks 0F0H, `AlgebraicGeometry.fppfEtaleCohomologyComparison`).

The second factor is invertible for every `f` and every `K` by Stacks 0EZF (2), the cohomology
sheaves of `π_X⁻¹K` being in `𝒜'_X`. The first factor is invertible for `f` finite by Stacks 0DDJ
(4) and for `f` proper and `K` with torsion cohomology sheaves by Stacks 0DDJ (2). This is the
source's proof of (5) rearranged: the source compares `Rε_{Y,*}` of both sides through the same
two inputs, 0DDJ (2) and Stacks 0DDS (3), and concludes with the conservativity of `Rε_{Y,*}` on
complexes with cohomology in `𝒜_Y`; the base change map of the change of topology packages that
step (its invertibility, Stacks 0EZF (2), is proved from the vanishing conditions `(V_n)`, which
are part (1)). The base change map of (2) is the degree `i` cohomology of that of (4) at `F`
placed in degree zero.

The derived categories are those of `HasDerivedCategory.standard`, the model in which Stacks
0EZF and Stacks 0DDJ (2) are stated.

## References

* [Stacks Project, Tag 0DDS](https://stacks.math.columbia.edu/tag/0DDS)
* [Stacks Project, Tag 0DDJ](https://stacks.math.columbia.edu/tag/0DDJ)
* [Stacks Project, Tag 0EZF](https://stacks.math.columbia.edu/tag/0EZF)
* [Stacks Project, Tag 0F0H](https://stacks.math.columbia.edu/tag/0F0H)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.ComparingTopologies
open Stacks.Cohomology.Localization

universe u

namespace AlgebraicGeometry

-- Stacks 0EZF (2), `Stacks.ComparingTopologies.isIso_derivedComparisonBaseChange_app`
-- (`StacksFrontier/CategoryTheory/Sites/Cohomology/ChangeOfTopology/`
-- `HigherDirectImageVanishing.lean:89`), and Stacks 0DDJ (2),
-- `AlgebraicGeometry.isIso_bigSmallEtaleDerivedBaseChange_app_of_isProper`
-- (`ComparingBigSmall/ProperDirectImageCommutation.lean:124`), are stated in the standard model.
attribute [local instance] HasDerivedCategory.standard smallEtaleSheaf_isGrothendieckAbelian
  bigEtaleSheaf_isGrothendieckAbelian

/-! ### Invertibility of the base change map of Stacks 0DDJ on `D⁺` -/

section PlusBaseChange

variable (E : BigEtaleSite.{u}) {X Y : E.Scheme} (f : X ⟶ Y)
  {JX : GrothendieckTopology (BigEtaleOver E X.obj X.property)}
  {JY : GrothendieckTopology (BigEtaleOver E Y.obj Y.property)}
  (hX : BigEtaleOver.topology E X.obj X.property = JX)
  (hY : BigEtaleOver.topology E Y.obj Y.property = JY)
  [(SmallEtale.inclusion E X.obj X.property).IsContinuous
    (SmallEtale.topology E X.obj X.property) JX]
  [(SmallEtale.inclusion E Y.obj Y.property).IsContinuous
    (SmallEtale.topology E Y.obj Y.property) JY]
  [HasSheafify JX Ab.{u + 1}] [HasSheafify JY Ab.{u + 1}]
  [(Over.map f).IsCocontinuous JX JY]
  [EnoughInjectives (Sheaf JX Ab.{u + 1})]
  [((Over.map f).sheafPushforwardCocontinuous Ab.{u + 1} JX JY).Additive]
  [PreservesFiniteLimits ((SmallEtale.inclusion E X.obj X.property).sheafPullback Ab.{u + 1}
    (SmallEtale.topology E X.obj X.property) JX)]
  [PreservesFiniteColimits ((SmallEtale.inclusion E X.obj X.property).sheafPullback Ab.{u + 1}
    (SmallEtale.topology E X.obj X.property) JX)]
  [((SmallEtale.inclusion E X.obj X.property).sheafPullback Ab.{u + 1}
    (SmallEtale.topology E X.obj X.property) JX).Additive]
  [PreservesFiniteLimits ((SmallEtale.inclusion E Y.obj Y.property).sheafPullback Ab.{u + 1}
    (SmallEtale.topology E Y.obj Y.property) JY)]
  [PreservesFiniteColimits ((SmallEtale.inclusion E Y.obj Y.property).sheafPullback Ab.{u + 1}
    (SmallEtale.topology E Y.obj Y.property) JY)]
  [((SmallEtale.inclusion E Y.obj Y.property).sheafPullback Ab.{u + 1}
    (SmallEtale.topology E Y.obj Y.property) JY).Additive]

/-- **The base change map of Stacks 0DDJ on `D⁺` is invertible where the unbounded one is.** If
for all right derived functors `Rf_{small,*}`, `Rf_{big,*}` on the unbounded derived categories
the base change map `AlgebraicGeometry.bigSmallEtaleDerivedBaseChange` is invertible at `ι L`,
then so is the base change map `AlgebraicGeometry.bigSmallEtaleDerivedPlusBaseChange` at `L`: the
latter is the former, for the total right derived functors, read through isomorphisms. -/
theorem isIso_bigSmallEtaleDerivedPlusBaseChange_of_forall_isIso
    (L : DerivedCategory.Plus (Sheaf (SmallEtale.topology E X.obj X.property) Ab.{u + 1}))
    (h : ∀ (RfSmall : DerivedCategory (Sheaf (SmallEtale.topology E X.obj X.property) Ab.{u + 1})
        ⥤ DerivedCategory (Sheaf (SmallEtale.topology E Y.obj Y.property) Ab.{u + 1}))
      (RfBig : DerivedCategory (Sheaf (BigEtaleOver.topology E X.obj X.property) Ab.{u + 1}) ⥤
        DerivedCategory (Sheaf (BigEtaleOver.topology E Y.obj Y.property) Ab.{u + 1}))
      (αSmall : (E.smallPushforward f Ab.{u + 1}).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RfSmall)
      (αBig : ((Over.pullback f).sheafPushforwardContinuous Ab.{u + 1}
        (BigEtaleOver.topology E Y.obj Y.property)
        (BigEtaleOver.topology E X.obj X.property)).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RfBig)
      [RfSmall.IsRightDerivedFunctor αSmall (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))]
      [RfBig.IsRightDerivedFunctor αBig (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))],
      IsIso ((bigSmallEtaleDerivedBaseChange E f RfSmall RfBig αSmall αBig).app
        (DerivedCategory.Plus.ι.obj L))) :
    IsIso (bigSmallEtaleDerivedPlusBaseChange E f hX hY L) := by
  subst hX hY
  let wS := E.smallPushforward f AddCommGrpCat.{u + 1}
  let wB := (Over.pullback f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
    (BigEtaleOver.topology E Y.obj Y.property) (BigEtaleOver.topology E X.obj X.property)
  have hresS := fun K => Stacks.Injectives.exists_kInjective_resolution_of_grothendieck
    (C := Sheaf (SmallEtale.topology E X.obj X.property) AddCommGrpCat.{u + 1}) K
  have hresB := fun K => Stacks.Injectives.exists_kInjective_resolution_of_grothendieck
    (C := Sheaf (BigEtaleOver.topology E X.obj X.property) AddCommGrpCat.{u + 1}) K
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
  let πX := (SmallEtale.inclusion E X.obj X.property).sheafPullback AddCommGrpCat.{u + 1}
    (SmallEtale.topology E X.obj X.property) (BigEtaleOver.topology E X.obj X.property)
  let πY := (SmallEtale.inclusion E Y.obj Y.property).sheafPullback AddCommGrpCat.{u + 1}
    (SmallEtale.topology E Y.obj Y.property) (BigEtaleOver.topology E Y.obj Y.property)
  let e : DerivedCategory.Plus.ι.obj
        (πY.mapDerivedCategoryPlus.obj (wS.rightDerivedFunctorPlus.obj L)) ⟶
      DerivedCategory.Plus.ι.obj
        (wB.rightDerivedFunctorPlus.obj (πX.mapDerivedCategoryPlus.obj L)) :=
    πY.mapDerivedCategory.map (rightDerivedFunctorPlusιObjIso wS RfSmall αSmall hresS L).hom ≫
      (bigSmallEtaleDerivedBaseChange E f RfSmall RfBig αSmall αBig).app
        (DerivedCategory.Plus.ι.obj L) ≫
      (rightDerivedFunctorPlusιObjIso wB RfBig αBig hresB (πX.mapDerivedCategoryPlus.obj L)).inv
  have : IsIso e := @IsIso.comp_isIso _ _ _ _ _ _ _ (Functor.map_isIso _ _)
    (@IsIso.comp_isIso _ _ _ _ _ _ _ (h RfSmall RfBig αSmall αBig) (Iso.isIso_inv _))
  exact @IsIso.comp_isIso _ _ _ _ _ _ _
    (DerivedCategory.TStructure.t.plus.fullyFaithfulι.preimageIso (asIso e)).isIso_hom
    inferInstance

/-- **Stacks 0DDJ (4) on `D⁺`.** For a finite morphism `f` of a big étale site the base change
map `π_Y⁻¹(Rf_{small,*}L) ⟶ Rf_{big,*}(π_X⁻¹L)` is an isomorphism for every `L` in
`D⁺(X_étale)`. -/
theorem isIso_bigSmallEtaleDerivedPlusBaseChange_of_isFinite [IsFinite (E.inclusion.map f)]
    (L : DerivedCategory.Plus (Sheaf (SmallEtale.topology E X.obj X.property) Ab.{u + 1})) :
    IsIso (bigSmallEtaleDerivedPlusBaseChange E f hX hY L) :=
  isIso_bigSmallEtaleDerivedPlusBaseChange_of_forall_isIso E f hX hY L
    fun RfSmall RfBig αSmall αBig _ _ =>
      have := isIso_bigSmallEtaleDerivedBaseChange_of_isFinite E f RfSmall RfBig αSmall αBig
      inferInstance

/-- **Stacks 0DDJ (2) on `D⁺`.** For a proper morphism `f` of a big étale site the base change
map `π_Y⁻¹(Rf_{small,*}L) ⟶ Rf_{big,*}(π_X⁻¹L)` is an isomorphism for every `L` in
`D⁺(X_étale)` with torsion cohomology sheaves. -/
theorem isIso_bigSmallEtaleDerivedPlusBaseChange_of_isProper [IsProper (E.inclusion.map f)]
    (L : DerivedCategory.Plus (Sheaf (SmallEtale.topology E X.obj X.property) Ab.{u + 1}))
    (hL : ∀ i : ℤ, Stacks.Torsion.torsionSheafProperty.{u + 1}
      (SmallEtale.topology E X.obj X.property)
      ((DerivedCategory.Plus.homologyFunctor _ i).obj L)) :
    IsIso (bigSmallEtaleDerivedPlusBaseChange E f hX hY L) :=
  isIso_bigSmallEtaleDerivedPlusBaseChange_of_forall_isIso E f hX hY L
    fun RfSmall RfBig αSmall αBig _ _ =>
      isIso_bigSmallEtaleDerivedBaseChange_app_of_isProper E f RfSmall RfBig αSmall αBig
        (DerivedCategory.Plus.ι.obj L) _ L.property.choose_spec hL

end PlusBaseChange

/-! ### The base change maps of Stacks 0DDS -/

section Fppf

variable (B : BigFppfSite.{u})

/-- The inverse image `π_X⁻¹` into the slice topology followed by the identification of the slice
topology with a topology `J` equal to it is the inverse image `π_X⁻¹` into `J`. -/
def smallEtaleSheafPullbackTopologyEqIso (E : BigEtaleSite.{u}) (X : E.Scheme)
    {J : GrothendieckTopology (BigEtaleOver E X.obj X.property)}
    (h : BigEtaleOver.topology E X.obj X.property = J)
    [(SmallEtale.inclusion E X.obj X.property).IsContinuous
      (SmallEtale.topology E X.obj X.property) J]
    [HasSheafify J Ab.{u + 1}] :
    (SmallEtale.inclusion E X.obj X.property).sheafPullback Ab.{u + 1}
        (SmallEtale.topology E X.obj X.property) (BigEtaleOver.topology E X.obj X.property) ⋙
      (sheafEquivOfTopologyEq h Ab.{u + 1}).functor ≅
    (SmallEtale.inclusion E X.obj X.property).sheafPullback Ab.{u + 1}
      (SmallEtale.topology E X.obj X.property) J := by
  subst h
  exact Iso.refl _

variable {B}

/-- The cohomology sheaves of `π_X⁻¹L`, for `L` in `D⁺(X_étale)`, lie in the class `𝒜'_X` of
Stacks 0F0H: they are `π_X⁻¹H^n(L)`. -/
theorem fppfEtaleWeakSerre_homology_sheafPullback (X : B.Schemes)
    (L : DerivedCategory.Plus
      (Sheaf (SmallEtale.topology (associatedBigEtaleSite B) X.1 X.2) Ab.{u + 1})) (n : ℤ) :
    fppfEtaleWeakSerre B X ((DerivedCategory.Plus.homologyFunctor _ n).obj
      (((SmallEtale.inclusion (associatedBigEtaleSite B) X.1 X.2).sheafPullback Ab.{u + 1}
        (SmallEtale.topology (associatedBigEtaleSite B) X.1 X.2)
        ((associatedBigEtaleSite B).topology.over X)).mapDerivedCategoryPlus.obj L)) := by
  let π := (SmallEtale.inclusion (associatedBigEtaleSite B) X.1 X.2).sheafPullback Ab.{u + 1}
    (SmallEtale.topology (associatedBigEtaleSite B) X.1 X.2)
    ((associatedBigEtaleSite B).topology.over X)
  have e : (DerivedCategory.Plus.homologyFunctor
      (Sheaf ((associatedBigEtaleSite B).topology.over X) Ab.{u + 1}) n).obj
        (π.mapDerivedCategoryPlus.obj L) ≅
      π.obj ((DerivedCategory.Plus.homologyFunctor _ n).obj L) :=
    (π.mapDerivedCategoryHomologyIso n).app L.obj
  exact ⟨(DerivedCategory.Plus.homologyFunctor _ n).obj L,
    ⟨(smallEtaleSheafPullbackTopologyEqIso (associatedBigEtaleSite B) X
      (bigEtaleOver_topology_eq_of_obj (associatedBigEtaleSite B) X)).app _ ≪≫ e.symm⟩⟩

/-- **The base change map `a_Y⁻¹(Rf_{small,*}K) ⟶ Rf_{big,fppf,*}(a_X⁻¹K)` of Stacks 0DDS (4) and
(5).** For a morphism `f : X ⟶ Y` of the big fppf site and `K` in `D⁺(X_étale)`, the base change
map of the square of topoi `a_Y ∘ f_{big,fppf} = f_{small} ∘ a_X` of Stacks 0DDM, where
`a_X⁻¹ = ε_X⁻¹ ∘ π_X⁻¹`. It is the composite of the base change maps of the two squares that
square is pasted from: `ε_Y⁻¹` applied to the base change map
`π_Y⁻¹(Rf_{small,*}K) ⟶ Rf_{big,étale,*}(π_X⁻¹K)` of Stacks 0DDJ,
`AlgebraicGeometry.bigSmallEtaleDerivedPlusBaseChange`, followed by the base change map
`ε_Y⁻¹(Rf_{big,étale,*}π_X⁻¹K) ⟶ Rf_{big,fppf,*}(ε_X⁻¹π_X⁻¹K)` of the change of topology,
`Stacks.ComparingTopologies.derivedComparisonBaseChange`. -/
def fppfSmallEtaleDerivedDirectImageBaseChange {X Y : B.Schemes} (f : X ⟶ Y)
    (K : DerivedCategory.Plus
      (Sheaf (SmallEtale.topology (associatedBigEtaleSite B) X.1 X.2) Ab.{u + 1})) :
    (fppfBigEtaleAbelianPullback B Y).rightDerivedFunctorPlus.obj
        (((SmallEtale.inclusion (associatedBigEtaleSite B) Y.1 Y.2).sheafPullback Ab.{u + 1}
          (SmallEtale.topology (associatedBigEtaleSite B) Y.1 Y.2)
          ((associatedBigEtaleSite B).topology.over Y)).mapDerivedCategoryPlus.obj
          (((associatedBigEtaleSite B).smallPushforward f Ab.{u + 1}).rightDerivedFunctorPlus.obj
            K)) ⟶
      (overPushforward B.precoverage.toGrothendieck f).rightDerivedFunctorPlus.obj
        ((fppfBigEtaleAbelianPullback B X).rightDerivedFunctorPlus.obj
          (((SmallEtale.inclusion (associatedBigEtaleSite B) X.1 X.2).sheafPullback Ab.{u + 1}
            (SmallEtale.topology (associatedBigEtaleSite B) X.1 X.2)
            ((associatedBigEtaleSite B).topology.over X)).mapDerivedCategoryPlus.obj K)) :=
  (fppfBigEtaleAbelianPullback B Y).rightDerivedFunctorPlus.map
      (bigSmallEtaleDerivedPlusBaseChange (associatedBigEtaleSite B) f
        (bigEtaleOver_topology_eq_of_obj (associatedBigEtaleSite B) X)
        (bigEtaleOver_topology_eq_of_obj (associatedBigEtaleSite B) Y) K) ≫
    (derivedComparisonBaseChange (fppfEtaleCohomologyComparison B) f).app
      (((SmallEtale.inclusion (associatedBigEtaleSite B) X.1 X.2).sheafPullback Ab.{u + 1}
        (SmallEtale.topology (associatedBigEtaleSite B) X.1 X.2)
        ((associatedBigEtaleSite B).topology.over X)).mapDerivedCategoryPlus.obj K)

/-- The base change map `a_Y⁻¹(Rf_{small,*}K) ⟶ Rf_{big,fppf,*}(a_X⁻¹K)` is an isomorphism as
soon as its first factor, the base change map of Stacks 0DDJ on `D⁺`, is: its second factor, the
base change map of the change of topology at `π_X⁻¹K`, is invertible by Stacks 0EZF (2), the
cohomology sheaves of `π_X⁻¹K` lying in `𝒜'_X`. -/
theorem isIso_fppfSmallEtaleDerivedDirectImageBaseChange_of_isIso {X Y : B.Schemes} (f : X ⟶ Y)
    (K : DerivedCategory.Plus
      (Sheaf (SmallEtale.topology (associatedBigEtaleSite B) X.1 X.2) Ab.{u + 1}))
    (h : IsIso (bigSmallEtaleDerivedPlusBaseChange (associatedBigEtaleSite B) f
        (bigEtaleOver_topology_eq_of_obj (associatedBigEtaleSite B) X)
        (bigEtaleOver_topology_eq_of_obj (associatedBigEtaleSite B) Y) K)) :
    IsIso (fppfSmallEtaleDerivedDirectImageBaseChange f K) :=
  @IsIso.comp_isIso _ _ _ _ _ _ _ (Functor.map_isIso _ _)
    (isIso_derivedComparisonBaseChange_app (fppfEtaleCohomologyComparison B) f
      (((SmallEtale.inclusion (associatedBigEtaleSite B) X.1 X.2).sheafPullback Ab.{u + 1}
        (SmallEtale.topology (associatedBigEtaleSite B) X.1 X.2)
        ((associatedBigEtaleSite B).topology.over X)).mapDerivedCategoryPlus.obj K)
      (fppfEtaleWeakSerre_homology_sheafPullback X K))

/-- For a finite morphism `f : X ⟶ Y` of the big fppf site and `K` in `D⁺(X_étale)`,

`a_Y⁻¹(Rf_{small,*}K) = Rf_{big,fppf,*}(a_X⁻¹K)`:

the base change map `AlgebraicGeometry.fppfSmallEtaleDerivedDirectImageBaseChange` is an
isomorphism. -/
@[stacks 0DDS "(4)"]
theorem isIso_fppfSmallEtaleDerivedDirectImageBaseChange_of_isFinite {X Y : B.Schemes}
    (f : X ⟶ Y) [IsFinite (B.inclusion.map f)]
    (K : DerivedCategory.Plus
      (Sheaf (SmallEtale.topology (associatedBigEtaleSite B) X.1 X.2) Ab.{u + 1})) :
    IsIso (fppfSmallEtaleDerivedDirectImageBaseChange f K) :=
  isIso_fppfSmallEtaleDerivedDirectImageBaseChange_of_isIso f K
    (isIso_bigSmallEtaleDerivedPlusBaseChange_of_isFinite (associatedBigEtaleSite B) f
      (bigEtaleOver_topology_eq_of_obj (associatedBigEtaleSite B) X)
      (bigEtaleOver_topology_eq_of_obj (associatedBigEtaleSite B) Y) K)

/-- **Stacks 0DDS (5).** For a proper morphism `f : X ⟶ Y` of the big fppf site and `K` in
`D⁺(X_étale)` with torsion cohomology sheaves,

`a_Y⁻¹(Rf_{small,*}K) = Rf_{big,fppf,*}(a_X⁻¹K)`:

the base change map `AlgebraicGeometry.fppfSmallEtaleDerivedDirectImageBaseChange` is an
isomorphism. Its first factor is invertible by Stacks 0DDJ (2), proper base change, and its
second by Stacks 0EZF (2). -/
@[stacks 0DDS "(5)"]
theorem isIso_fppfSmallEtaleDerivedDirectImageBaseChange_of_isProper {X Y : B.Schemes}
    (f : X ⟶ Y) [IsProper (B.inclusion.map f)]
    (K : DerivedCategory.Plus
      (Sheaf (SmallEtale.topology (associatedBigEtaleSite B) X.1 X.2) Ab.{u + 1}))
    (hK : ∀ i : ℤ, Stacks.Torsion.torsionSheafProperty.{u + 1}
      (SmallEtale.topology (associatedBigEtaleSite B) X.1 X.2)
      ((DerivedCategory.Plus.homologyFunctor _ i).obj K)) :
    IsIso (fppfSmallEtaleDerivedDirectImageBaseChange f K) :=
  isIso_fppfSmallEtaleDerivedDirectImageBaseChange_of_isIso f K
    (isIso_bigSmallEtaleDerivedPlusBaseChange_of_isProper (associatedBigEtaleSite B) f
      (bigEtaleOver_topology_eq_of_obj (associatedBigEtaleSite B) X)
      (bigEtaleOver_topology_eq_of_obj (associatedBigEtaleSite B) Y) K hK)

/-- **The base change map `a_Y⁻¹(R^if_{small,*}F) ⟶ R^if_{big,fppf,*}(a_X⁻¹F)` of Stacks 0DDS
(2).** For a morphism `f : X ⟶ Y` of the big fppf site, an abelian sheaf `F` on `X_étale` and
`i : ℕ`: the degree `i` cohomology of the derived base change map
`AlgebraicGeometry.fppfSmallEtaleDerivedDirectImageBaseChange` at `F` placed in degree zero, read
through the canonical identifications `R^iw(F) = H^i(R⁺w(F[0]))`
(`Stacks.DerivedIndexing.rightDerivedIso`), `H^i(π_Y⁻¹M) = π_Y⁻¹H^i(M)`,
`H^i(R⁺ε_Y⁻¹N) = ε_Y⁻¹H^i(N)` and `R⁺ε_X⁻¹(π_X⁻¹(F[0])) = (ε_X⁻¹π_X⁻¹F)[0]` for the exact functors
`π⁻¹` and `ε⁻¹`. -/
def fppfSmallEtaleHigherDirectImageBaseChange {X Y : B.Schemes} (f : X ⟶ Y)
    (F : Sheaf (SmallEtale.topology (associatedBigEtaleSite B) X.1 X.2) Ab.{u + 1}) (i : ℕ) :
    (fppfBigEtaleAbelianPullback B Y).obj
        (((SmallEtale.inclusion (associatedBigEtaleSite B) Y.1 Y.2).sheafPullback Ab.{u + 1}
          (SmallEtale.topology (associatedBigEtaleSite B) Y.1 Y.2)
          ((associatedBigEtaleSite B).topology.over Y)).obj
          ((((associatedBigEtaleSite B).smallPushforward f Ab.{u + 1}).rightDerived i).obj F)) ⟶
      ((overPushforward B.precoverage.toGrothendieck f).rightDerived i).obj
        ((fppfBigEtaleAbelianPullback B X).obj
          (((SmallEtale.inclusion (associatedBigEtaleSite B) X.1 X.2).sheafPullback Ab.{u + 1}
            (SmallEtale.topology (associatedBigEtaleSite B) X.1 X.2)
            ((associatedBigEtaleSite B).topology.over X)).obj F)) :=
  let πX := (SmallEtale.inclusion (associatedBigEtaleSite B) X.1 X.2).sheafPullback Ab.{u + 1}
    (SmallEtale.topology (associatedBigEtaleSite B) X.1 X.2)
    ((associatedBigEtaleSite B).topology.over X)
  let πY := (SmallEtale.inclusion (associatedBigEtaleSite B) Y.1 Y.2).sheafPullback Ab.{u + 1}
    (SmallEtale.topology (associatedBigEtaleSite B) Y.1 Y.2)
    ((associatedBigEtaleSite B).topology.over Y)
  let S := fppfEtaleCohomologyComparison B
  let εX := abelianComparisonPullback S.fineCoverage S.coarseCoverage X
  let εY := abelianComparisonPullback S.fineCoverage S.coarseCoverage Y
  haveI : PreservesFiniteColimits εX := abelianComparisonPullback_preservesFiniteColimits S X
  haveI : PreservesFiniteColimits εY := abelianComparisonPullback_preservesFiniteColimits S Y
  let wS := (associatedBigEtaleSite B).smallPushforward f Ab.{u + 1}
  let Ff := overPushforward B.precoverage.toGrothendieck f
  let M := (DerivedCategory.Plus.singleFunctor _ 0).obj F
  let H := DerivedCategory.Plus.homologyFunctor
    (Sheaf (B.precoverage.toGrothendieck.over Y) Ab.{u + 1}) (i : ℤ)
  (εY.mapIso (πY.mapIso ((Stacks.DerivedIndexing.rightDerivedIso wS i).app F)) ≪≫
      εY.mapIso ((πY.mapDerivedCategoryHomologyIso (i : ℤ)).app
        (DerivedCategory.Plus.ι.obj (wS.rightDerivedFunctorPlus.obj M))).symm ≪≫
      ((Stacks.DerivedFunctor.exactRightDerivedPlusHomologyIso εY (i : ℤ)).app
        (πY.mapDerivedCategoryPlus.obj (wS.rightDerivedFunctorPlus.obj M))).symm).hom ≫
    H.map (fppfSmallEtaleDerivedDirectImageBaseChange f M) ≫
    (H.mapIso (Ff.rightDerivedFunctorPlus.mapIso
      (εX.rightDerivedFunctorPlus.mapIso
          ((Stacks.DerivedFunctor.exactMapDerivedCategoryPlusSingle πX 0).app F) ≪≫
        ((Stacks.DerivedFunctor.exactSingleFunctorRightDerivedPlusIso εX 0).app
          (πX.obj F)).symm)) ≪≫
      ((Stacks.DerivedIndexing.rightDerivedIso Ff i).app (εX.obj (πX.obj F))).symm).hom

/-- **Stacks 0DDS (2).** For a finite morphism `f : X ⟶ Y` of the big fppf site, an abelian sheaf
`F` on `X_étale` and every `i`,

`a_Y⁻¹(R^if_{small,*}F) = R^if_{big,fppf,*}(a_X⁻¹F)`:

the base change map `AlgebraicGeometry.fppfSmallEtaleHigherDirectImageBaseChange` is an
isomorphism. It is the cohomology of the derived base change map of part (4) at `F` placed in
degree zero, read through isomorphisms. -/
@[stacks 0DDS "(2)"]
theorem isIso_fppfSmallEtaleHigherDirectImageBaseChange_of_isFinite {X Y : B.Schemes}
    (f : X ⟶ Y) [IsFinite (B.inclusion.map f)]
    (F : Sheaf (SmallEtale.topology (associatedBigEtaleSite B) X.1 X.2) Ab.{u + 1}) (i : ℕ) :
    IsIso (fppfSmallEtaleHigherDirectImageBaseChange f F i) := by
  have h := isIso_fppfSmallEtaleDerivedDirectImageBaseChange_of_isFinite f
    ((DerivedCategory.Plus.singleFunctor _ 0).obj F)
  dsimp only [fppfSmallEtaleHigherDirectImageBaseChange]
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ (Iso.isIso_hom _)
    (@IsIso.comp_isIso _ _ _ _ _ _ _ (@Functor.map_isIso _ _ _ _ _ _ _ _ h) (Iso.isIso_hom _))

variable (B)

/-- **Stacks 0DDS (1).** For an object `X` of the big fppf site and an abelian sheaf `F` on
`X_étale`,

`ε_{X,*}a_X⁻¹F = π_X⁻¹F` and `R^iε_{X,*}(a_X⁻¹F) = 0` for `i > 0`:

the unit `π_X⁻¹F ⟶ ε_{X,*}ε_X⁻¹π_X⁻¹F = ε_{X,*}a_X⁻¹F` of `ε_X⁻¹ ⊣ ε_{X,*}` is an isomorphism, and
the higher right derived functors of `ε_{X,*}` vanish at `a_X⁻¹F`. -/
@[stacks 0DDS "(1)"]
theorem fppfSmallEtale_projectionPullback_comparison (X : B.Schemes)
    (F : Sheaf (SmallEtale.topology (associatedBigEtaleSite B) X.1 X.2) Ab.{u + 1}) :
    IsIso ((fppfBigEtaleAbelianAdjunction B X).unit.app ((fppfEtaleProjectionPullback B X).obj F)) ∧
      ∀ i : ℕ, 0 < i → IsZero (((fppfBigEtaleAbelianPushforward B X).rightDerived i).obj
        ((fppfSmallEtaleAbelianPullback B X).obj F)) :=
  ⟨isIso_fppfBigEtaleAbelianAdjunction_unit_app_projectionPullback B X F,
    isZero_fppfBigEtaleAbelianPushforward_rightDerived_fppfSmallEtaleAbelianPullback B X F⟩

/-- **Stacks 0DDS (3).** For an object `X` of the big fppf site and `K` in `D⁺(X_étale)` the map
`π_X⁻¹K ⟶ Rε_{X,*}(a_X⁻¹K)`, `AlgebraicGeometry.fppfSmallEtaleDerivedUnit`, is an isomorphism.
It is Stacks 0EZF (1) at `π_X⁻¹K`, which lies in `D⁺_{𝒜'_X}`. -/
@[stacks 0DDS "(3)"]
theorem isIso_fppfSmallEtaleDerivedUnit (X : B.Schemes) :
    IsIso (fppfSmallEtaleDerivedUnit B X) :=
  isIso_fppfSmallEtaleDerivedUnit_of_finite X
    fppfEtaleOverMapPushforward_preservesFiniteColimits_of_finite
    fppfEtaleWeakSerre_overMapPushforward_of_finite

end Fppf

end AlgebraicGeometry

end
