module

public import StacksFrontier.AlgebraicGeometry.Divisors.IdealSheafPullbackComap
public import StacksFrontier.AlgebraicGeometry.Divisors.NormalSheaf

/-!
# The normal sheaf of the inverse image of an effective Cartier divisor

Let `q : X ⟶ Y` be a morphism of schemes and let `D ⊆ Y` be an effective Cartier divisor whose
pullback is defined, that is, whose scheme-theoretic inverse image `q^{-1}D` is again an
effective Cartier divisor (`Stacks.Divisors.IsPullbackDefined`, [Stacks, Tag 01WV]). Write
`ψ : q^{-1}D ⟶ D` for the restriction of `q` to the two closed subschemes. Then

`𝒩_{q^{-1}D / X} ≅ ψ^* 𝒩_{D/Y}`.

## Main definitions

* `Stacks.Divisors.comapSubschemeMap'`: the restriction of `q` to the two closed subschemes.

## Main results

* `Stacks.Divisors.normalSheafComapIso`: **the identification above.**

## Implementation notes

Nothing is asked of `q` beyond the hypothesis that the inverse image of `D` is again an effective
Cartier divisor; in particular `q` need not be flat.

`Stacks.Divisors.comapSubschemeMap'` duplicates `Stacks.Divisors.comapSubschemeMap` without its
étale hypothesis on `q`; the two should be deduplicated by moving the general one here.

## References

* [Stacks Project, Tag 0B3P](https://stacks.math.columbia.edu/tag/0B3P)
* [Stacks Project, Tag 01WV](https://stacks.math.columbia.edu/tag/01WV)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory RingedSpaceModuleAdjunction
open Stacks.SheafOfModules.TensorStalkRingedSpace (ringStalk)

universe u

namespace Stacks.Divisors

variable {X Y : Scheme.{u}} (q : X ⟶ Y) (D : Y.IdealSheafData)

/-- **The restriction of `q : X ⟶ Y` to the closed subschemes cut out by `q^{-1}D` and `D`.**
This is the lower edge of the commutative square of `Stacks.Divisors.comap_subschemeι_comm`. -/
abbrev comapSubschemeMap' : (D.comap q).subscheme ⟶ D.subscheme :=
  Scheme.IdealSheafData.subschemeMap (D.comap q) D q (D.le_map_comap q)

/-- **The normal sheaf of the inverse image of an effective Cartier divisor is the pullback of
the normal sheaf**, along the restriction of `q` to the two closed subschemes. -/
def normalSheafComapIso [IsEffectiveCartierDivisor D] (hD : IsPullbackDefined q D) :
    normalSheaf (D.comap q).subschemeι ≅
      (modulePullback (comapSubschemeMap' q D).toLRSHom.toShHom).obj
        (normalSheaf D.subschemeι) :=
  haveI : IsEffectiveCartierDivisor (D.comap q) := hD
  have _h₁ : ∀ x : X.toRingedSpace.carrier, IsLocalRing (ringStalk X.toRingedSpace x) :=
    fun x => X.isLocalRing x
  have _h₂ : ∀ y : Y.toRingedSpace.carrier, IsLocalRing (ringStalk Y.toRingedSpace y) :=
    fun y => Y.isLocalRing y
  have _hI : Stacks.SheafOfModules.IsInvertible Y.sheaf.obj
      (structureSheafRing Y.toRingedSpace).property (Eta.idealSheaf D) :=
    Stacks.InvertibleBridge.stacksIsInvertible_of_algebraicGeometryIsInvertible
  normalSheafIsoInvertibleSheaf (D.comap q) ≪≫
    (modulePullback (D.comap q).subschemeι.toLRSHom.toShHom).mapIso
      (Stacks.SheafOfModules.dualSheafIso _ _ (pullbackIdealSheafComapIso q D hD).symm ≪≫
        dualPullbackIsoOfPullbackStalkFormula q.toLRSHom.toShHom
          (Stacks.RingedSpace.pullbackStalkFormula _) (Eta.idealSheaf D)) ≪≫
    ((modulePullbackComp (D.comap q).subschemeι.toLRSHom.toShHom
      q.toLRSHom.toShHom).app _).symm ≪≫
    (modulePullbackCongr (comap_subschemeι_comm_toShHom q D)).app _ ≪≫
    (modulePullbackComp (comapSubschemeMap' q D).toLRSHom.toShHom
      D.subschemeι.toLRSHom.toShHom).app _ ≪≫
    (modulePullback (comapSubschemeMap' q D).toLRSHom.toShHom).mapIso
      (normalSheafIsoInvertibleSheaf D).symm

end Stacks.Divisors

end
