module

public import StacksFrontier.AlgebraicGeometry.DeRham.LerayHirsch.RealizationEdge
public import StacksFrontier.AlgebraicGeometry.DeRham.LerayHirsch.DeRhamComparisonAdjoint
public import StacksFrontier.AlgebraicGeometry.DeRham.LerayHirsch.HomologyPullback

/-!
# The pullback of de Rham cohomology is the pullback of classes followed by the comparison

For a commutative square `g' ≫ f = f' ≫ g` of schemes, let
`g₀ : (X', f'^{-1}𝒪_{S'}) ⟶ (X, f^{-1}𝒪_S)` be the induced morphism of inverse-image ringed
spaces. The pullback `H^m_{dR}(X/S) ⟶ H^m_{dR}(X'/S')` of [Stacks, Section 0FL6]
(`AlgebraicGeometry.Scheme.Hom.deRhamCohomologyPullback`), read in derived global sections of
modules through the comparison of the two realizations ([Stacks, Tag 01F1]), is the pullback of
classes along `g₀` (`Stacks.Cohomology.HomologyPullback.homologyPullback`) followed by the
canonical comparison `Lg₀^*Ω^•_{X/S} ⟶ Ω^•_{X'/S'}` of derived and termwise pullback of forms.

This is the shape in which the de Rham pullback meets the pullback legs of the Künneth map.

## Main definitions

* `Stacks.WeilDeRham.deRhamPullbackComparisonQ`: the comparison
  `Lg₀^*Ω^•_{X/S} ⟶ Ω^•_{X'/S'}` read at the localization functor `Q`.

## Main results

* `Stacks.WeilDeRham.homEquiv_deRhamPullbackComparisonQ`: its transpose under `Lg₀^* ⊣ Rg₀_*` is
  the canonical map `Ω^•_{X/S} ⟶ g₀_*Ω^•_{X'/S'}` followed by `g₀_* ⟶ Rg₀_*`.
* `Stacks.WeilDeRham.deRhamCohomologyPullback_eq_homologyPullback`: **the de Rham pullback is the
  pullback of classes followed by the comparison.**

## References

* [Stacks Project, Section 0FL6](https://stacks.math.columbia.edu/tag/0FL6)
* [Stacks Project, Tag 01F1](https://stacks.math.columbia.edu/tag/01F1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.DeRhamDirectImage Stacks.DeRhamBaseChange AlgebraicGeometry.ProperSmoothDeRham
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.CupProductAndDerivedPushforwardOnRingedSpaces
open Stacks.Cohomology.GlobalKunneth Stacks.Cohomology.LerayCupPairing

universe u


namespace Stacks.WeilDeRham

variable {X X' S S' : Scheme.{u}} (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S)
  (w : g' ≫ f = f' ≫ g)

/-- **The comparison `Lg₀^*Ω^•_{X/S} ⟶ Ω^•_{X'/S'}`**, read at the localization functor `Q` of
the derived category: `AlgebraicGeometry.ProperSmoothDeRham.deRhamBaseChangeComparison`
conjugated by the identification of `Q` with the localization of the homotopy category. -/
def deRhamPullbackComparisonQ :
    letI := @HasDerivedCategory.standard.{u, u + 1}
    (derivedPullback (inverseImageBaseMap g' f' f g w)).obj
        (DerivedCategory.Q.obj (deRhamComplexInt f)) ⟶
      DerivedCategory.Q.obj (deRhamComplexInt f') :=
  letI := @HasDerivedCategory.standard.{u, u + 1}
  (derivedPullback (inverseImageBaseMap g' f' f g w)).map
      ((DerivedCategory.quotientCompQhIso _).inv.app (deRhamComplexInt f)) ≫
    deRhamBaseChangeComparison g' f' f g w ≫
      (DerivedCategory.quotientCompQhIso _).hom.app (deRhamComplexInt f')

/-- **The transpose of the comparison** under `Lg₀^* ⊣ Rg₀_*` is the canonical map
`Ω^•_{X/S} ⟶ g₀_*Ω^•_{X'/S'}` followed by the comparison `g₀_* ⟶ Rg₀_*`. -/
theorem homEquiv_deRhamPullbackComparisonQ :
    letI := @HasDerivedCategory.standard.{u, u + 1}
    (derivedAdjunction (inverseImageBaseMap g' f' f g w)).homEquiv _ _
        (deRhamPullbackComparisonQ g' f' f g w) =
      DerivedCategory.Q.map (deRhamPushforwardInt g' f' f g w) ≫
        pushforwardComparisonQ (inverseImageBaseMap g' f' f g w) (deRhamComplexInt f') := by
  let := @HasDerivedCategory.standard.{u, u + 1}
  rw [deRhamPullbackComparisonQ, Adjunction.homEquiv_naturality_left,
    Adjunction.homEquiv_naturality_right]
  exact homEquiv_deRhamBaseChangeComparison_pushforwardComparisonQ g' f' f g w

/-- **The de Rham pullback is the pullback of classes followed by the comparison.** The pullback
`H^m_{dR}(X/S) ⟶ H^m_{dR}(X'/S')` of Section 0FL6, read in the realization of de Rham cohomology
by derived global sections of modules, is the pullback of classes along `g₀` of
`Stacks.Cohomology.HomologyPullback.homologyPullback` followed by `RΓ` of the comparison
`Lg₀^*Ω^•_{X/S} ⟶ Ω^•_{X'/S'}`. -/
theorem deRhamCohomologyPullback_eq_homologyPullback (m : ℤ)
    (ξ : Scheme.Hom.deRhamCohomology f m) :
    letI := @HasDerivedCategory.standard.{u, u + 1}
    (AlgebraicGeometry.SheafOfModules.deRhamCohomologyAbelianIsoDeRhamCohomology
        (Scheme.Hom.deRhamAlgebras f')
        (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras f'))
        m).hom.hom ((Scheme.Hom.deRhamCohomologyPullback g' f f' g w m).hom ξ) =
      ((DerivedCategory.homologyFunctor _ m).map ((baseSections (inverseImageBase f')).map
          (deRhamPullbackComparisonQ g' f' f g w))).hom
        (Stacks.Cohomology.HomologyPullback.homologyPullback (inverseImageBaseMap g' f' f g w)
          (DerivedCategory.Q.obj (deRhamComplexInt f)) m
          ((AlgebraicGeometry.SheafOfModules.deRhamCohomologyAbelianIsoDeRhamCohomology
            (Scheme.Hom.deRhamAlgebras f)
            (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras f))
            m).hom.hom ξ)) := by
  let := @HasDerivedCategory.standard.{u, u + 1}
  refine (deRhamCohomologyAbelianIsoDeRhamCohomology_deRhamCohomologyPullback g' f' f g w m
    ξ).trans ?_
  refine Eq.trans ?_ (Stacks.Cohomology.HomologyPullback.homologyPullback_homEquiv
    (inverseImageBaseMap g' f' f g w) (deRhamPullbackComparisonQ g' f' f g w) m _).symm
  rw [homEquiv_deRhamPullbackComparisonQ]

end Stacks.WeilDeRham

end
