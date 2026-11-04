module

public import StacksFrontier.AlgebraicGeometry.DeRham.LerayHirsch.LerayHirschIsomorphism
public import StacksFrontier.AlgebraicGeometry.DeRham.ProperSmoothAffineDeRhamModel
public import StacksFrontier.AlgebraicGeometry.DeRham.CupProduct.PullbackCupProductDerived

/-!
# Base change of `Rf_*Ω^•` along a cartesian square, on cohomology

Let

```
X' --g'--> X
|          |
f'         f
v          v
S' --g---> S
```

be a cartesian square of schemes with `f` proper and smooth. By [Stacks, Tag 0FM0] the base change
map `Lg^*Rf_*Ω^•_{X/S} ⟶ Rf'_*Ω^•_{X'/S'}` is an isomorphism
(`Stacks.DeRhamSmooth.deRhamUnboundedBaseChangeIsoOfIsPullback`). This file computes it on
cohomology: a class of `H^m_{dR}(X/S)`, read in `H^m(S, Rf_*Ω^•_{X/S})` through the Leray
identification, pulled back to `S'` and carried by the base change isomorphism, is the pullback of
de Rham cohomology along the square ([Stacks, Tag 0FL6]), read in `H^m(S', Rf'_*Ω^•_{X'/S'})`.

This is the computation the Leray--Hirsch development of the library carries out for the fibre
square of a point
(`AlgebraicGeometry.DeRhamLerayHirsch.homologyPullback_deRhamClassToDirectImage`), for an
arbitrary cartesian square; the proof is the same, through the square-generic lemmas
`AlgebraicGeometry.DeRhamLerayHirsch.lerayCohomologyIso_derivedBaseChangeMap_comp`,
`Stacks.DeRhamBaseChange.homEquiv_deRhamBaseChangeComparison_pushforwardComparisonQ` and
`Stacks.DeRhamBaseChange.deRhamCohomologyAbelianIsoDeRhamCohomology_deRhamCohomologyPullback`.

## Main results

* `Stacks.WeilDeRham.deRhamBaseChangeComparison_homologyPullback`: pullback of classes along the
  inverse-image ringed spaces followed by the canonical map of de Rham complexes is the pullback
  of de Rham cohomology along the square.
* `Stacks.WeilDeRham.lerayCohomologyIso_deRhamUnboundedBaseChange_homologyPullback`: the base
  change isomorphism on cohomology is the pullback of de Rham cohomology along the square.
* `Stacks.WeilDeRham.homologyPullback_unitCycleClass_deRhamUnboundedBaseChange`: the same for the
  value at the pulled back class of `1` of a morphism `𝒪_S[-m] ⟶ Rf_*Ω^•_{X/S}`.

## References

* [Stacks Project, Tag 0FM0](https://stacks.math.columbia.edu/tag/0FM0)
* [Stacks Project, Tag 0FL6](https://stacks.math.columbia.edu/tag/0FL6)
* [Stacks Project, Tag 0D5W](https://stacks.math.columbia.edu/tag/0D5W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.DerivedGlobalCupProduct Stacks.Cohomology.GlobalKunneth
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces Stacks.Cohomology.LerayCupPairing
open Stacks.Cohomology.HomologyPullback Stacks.Cohomology.DerivedBaseChange
open Stacks.DeRhamDirectImage AlgebraicGeometry.DeRhamCohomologyDirectImage Stacks.DeRhamBaseChange
open AlgebraicGeometry.ProperSmoothDeRham
open scoped Stacks.StandardDerivedModel

universe u

namespace Stacks.WeilDeRham

variable {X X' S S' : Scheme.{u}} (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S)

/-- **The canonical map of de Rham complexes along a commutative square, on cohomology.** The
pullback of a class along `g₀ : (X', f'^{-1}𝒪_{S'}) ⟶ (X, f^{-1}𝒪_S)` followed by the canonical
map `Lg₀^*Ω^•_{X/S} ⟶ Ω^•_{X'/S'}` is the pullback of de Rham cohomology along the square
([Stacks, Tag 0FL6]), in the realization by derived global sections of modules. -/
theorem deRhamBaseChangeComparison_homologyPullback (w : g' ≫ f = f' ≫ g) (m : ℤ)
    (z : cohomologyModule (DerivedCategory.Q.obj (deRhamCochainComplex f)) m) :
    ((DerivedCategory.homologyFunctor _ m).map ((baseSections _).map
        ((derivedPullback (inverseImageBaseMap g' f' f g w)).map
            ((DerivedCategory.quotientCompQhIso _).inv.app (deRhamComplexInt f)) ≫
          deRhamBaseChangeComparison g' f' f g w ≫
          (DerivedCategory.quotientCompQhIso _).hom.app (deRhamComplexInt f')))).hom
        (homologyPullback (inverseImageBaseMap g' f' f g w) _ m z) =
      deRhamPullbackSquare g' f' f g w m z := by
  refine (homologyPullback_homEquiv (inverseImageBaseMap g' f' f g w) _ m z).trans ?_
  have hadj : (derivedAdjunction (inverseImageBaseMap g' f' f g w)).homEquiv _ _
      ((derivedPullback (inverseImageBaseMap g' f' f g w)).map
          ((DerivedCategory.quotientCompQhIso _).inv.app (deRhamComplexInt f)) ≫
        deRhamBaseChangeComparison g' f' f g w ≫
        (DerivedCategory.quotientCompQhIso _).hom.app (deRhamComplexInt f')) =
      DerivedCategory.Q.map (deRhamPushforwardInt g' f' f g w) ≫
        Stacks.Cohomology.CupProductAndDerivedPushforwardOnRingedSpaces.pushforwardComparisonQ
          (inverseImageBaseMap g' f' f g w) (deRhamComplexInt f') := by
    rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
    exact homEquiv_deRhamBaseChangeComparison_pushforwardComparisonQ g' f' f g w
  rw [hadj]
  have h := deRhamCohomologyAbelianIsoDeRhamCohomology_deRhamCohomologyPullback g' f' f g w m
    ((AlgebraicGeometry.SheafOfModules.deRhamCohomologyAbelianIsoDeRhamCohomology
      (Scheme.Hom.deRhamAlgebras f)
      (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras f)) m).inv.hom
      z)
  erw [Iso.inv_hom_id_apply] at h
  exact h.symm

variable (hsq : IsPullback g' f' f g) [IsProper f] [Smooth f]

/-- **[Stacks, Tag 0FM0] on cohomology.** A class `z` of `H^m(X, Ω^•_{X/S})`, read in
`H^m(S, Rf_*Ω^•_{X/S})` through the Leray identification, pulled back to `S'` and carried by the
base change isomorphism `Lg^*Rf_*Ω^•_{X/S} ≅ Rf'_*Ω^•_{X'/S'}`, is, read in
`H^m(X', Ω^•_{X'/S'})`, the pullback of `z` along the square. -/
theorem lerayCohomologyIso_deRhamUnboundedBaseChange_homologyPullback (m : ℤ)
    (z : cohomologyModule (DerivedCategory.Q.obj (deRhamCochainComplex f)) m) :
    (lerayCohomologyIso (inverseImageBaseProjection f')
        (DerivedCategory.Q.obj (deRhamCochainComplex f')) m).hom
      (((DerivedCategory.homologyFunctor _ m).map ((baseSections _).map
        (Stacks.DeRhamSmooth.deRhamUnboundedBaseChangeIsoOfIsPullback f g g' f' hsq).hom)).hom
        (homologyPullback g.toLRSHom.toShHom (derivedDeRhamDirectImageUnbounded f) m
          ((lerayCohomologyIso (inverseImageBaseProjection f)
            (DerivedCategory.Q.obj (deRhamCochainComplex f)) m).inv z))) =
      deRhamPullbackSquare g' f' f g hsq.w m z :=
  (DeRhamLerayHirsch.lerayCohomologyIso_derivedBaseChangeMap_comp
    (inverseImageBaseMap g' f' f g hsq.w) (inverseImageBaseProjection f')
    (inverseImageBaseProjection f) g.toLRSHom.toShHom
    (inverseImageBaseMap_comp_inverseImageBaseProjection _ _ f _ hsq.w)
    ((DerivedCategory.quotientCompQhIso _).inv.app (deRhamComplexInt f))
    (deRhamBaseChangeComparison g' f' f g hsq.w)
    ((DerivedCategory.quotientCompQhIso _).hom.app (deRhamComplexInt f')) m z).trans
    (deRhamBaseChangeComparison_homologyPullback g' f' f g hsq.w m z)

/-- **The value of a morphism `𝒪_S[-m] ⟶ Rf_*Ω^•_{X/S}` after base change.** For
`a : 𝒪_S[-m] ⟶ Rf_*Ω^•_{X/S}`, the pullback to `S'` of the class of `1`, carried by `Lg^*a` and
the base change isomorphism, is, read in `H^m(X', Ω^•_{X'/S'})`, the pullback along the square
of the value of `a` at the class of `1`, read in `H^m(X, Ω^•_{X/S})`. -/
theorem homologyPullback_unitCycleClass_deRhamUnboundedBaseChange (m : ℤ)
    (a : DerivedCategory.Q.obj (unitComplex S.toRingedSpace m) ⟶
      derivedDeRhamDirectImageUnbounded f) :
    (lerayCohomologyIso (inverseImageBaseProjection f')
        (DerivedCategory.Q.obj (deRhamCochainComplex f')) m).hom
      (((DerivedCategory.homologyFunctor _ m).map ((baseSections _).map
        ((derivedPullback g.toLRSHom.toShHom).map a ≫
          (Stacks.DeRhamSmooth.deRhamUnboundedBaseChangeIsoOfIsPullback f g g' f' hsq).hom))).hom
        (homologyPullback g.toLRSHom.toShHom _ m (unitCycleClass S.toRingedSpace m))) =
      deRhamPullbackSquare g' f' f g hsq.w m
        ((lerayCohomologyIso (inverseImageBaseProjection f)
          (DerivedCategory.Q.obj (deRhamCochainComplex f)) m).hom
          (evalUnit (derivedDeRhamDirectImageUnbounded f) m a)) := by
  have h := lerayCohomologyIso_deRhamUnboundedBaseChange_homologyPullback g' f' f g hsq m
    ((lerayCohomologyIso (inverseImageBaseProjection f)
      (DerivedCategory.Q.obj (deRhamCochainComplex f)) m).hom
      (evalUnit (derivedDeRhamDirectImageUnbounded f) m a))
  rw [Iso.hom_inv_id_apply] at h
  refine Eq.trans ?_ h
  refine congrArg (lerayCohomologyIso (inverseImageBaseProjection f')
    (DerivedCategory.Q.obj (deRhamCochainComplex f')) m).hom ?_
  refine (map_map_comp_apply (baseSections _) (DerivedCategory.homologyFunctor _ m) _ _ _).trans ?_
  exact congrArg _ (homologyPullback_naturality g.toLRSHom.toShHom a m _).symm

end Stacks.WeilDeRham

end
