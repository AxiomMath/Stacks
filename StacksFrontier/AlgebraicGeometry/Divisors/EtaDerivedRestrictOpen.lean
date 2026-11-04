module

public import StacksFrontier.AlgebraicGeometry.Divisors.EtaDerivedPullbackComparison
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RelativeTorIndependentBaseChange
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RestrictTarget

/-!
# The derived décalage commutes with restriction along an open immersion

Let `X` be a scheme, let `D ⊆ X` be an effective Cartier divisor with ideal sheaf `I = ℐ_D` and
let `j : W ⟶ X` be an open immersion.  The preimage `j⁻¹D` of the divisor is again an effective
Cartier divisor — an open immersion is flat — and

`(Lη_I K)|_W ≅ Lη_{I|_W}(K|_W)`

in `D(𝒪_W)`, for every object `K` of `D(𝒪_X)` presented by a complex of `I`-torsion-free
`𝒪_X`-modules, which every object is.

This is the special case of [Stacks, Tag 0F9X] at the open immersion `j`.  It is not
a new theorem: an open immersion is flat, so the flat case of that tag,
`Stacks.Divisors.Eta.derivedEtaPullbackIso`, applies to it; what this file adds is the passage
from derived pullback to restriction, which is
`AlgebraicGeometry.Scheme.Modules.derivedRestrictIsoDerivedPullback`.  The composite is the
identification that the chart-level comparison
`AlgebraicGeometry.ComplexAndDivisorSituation.ChartDecalage` of
`StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.GoodTripleEtaPerfect` needs on its
left-hand side, and that no declaration previously stated.

The open immersion is left arbitrary rather than taken to be the inclusion `U.ι` of an open
subscheme because the chart-level comparison needs the statement twice: once at `U.ι`, and once
at the isomorphism `U ≅ Spec Γ(X, U)` of an affine chart, which is an open immersion but not
the inclusion of an open of `Spec Γ(X, U)`.

## Main definitions

* `Stacks.Divisors.Eta.derivedEtaRestrictOpenIso`: **`(Lη_I K)|_W ≅ Lη_{I|_W}(K|_W)`**, for `K`
  presented by a complex of `I`-torsion-free modules.
* `Stacks.Divisors.Eta.derivedEtaRestrictOpenObjIso`: the same at an arbitrary object of
  `D(𝒪_X)`.
* `Stacks.Divisors.Eta.derivedEtaRestrictModulesObjIso`: the same at the inclusion of an open
  subscheme, written at the
  `AlgebraicGeometry.RingedSpace.PseudoCoherence.restrictModules` spelling of restriction, which
  is the one the local criterion for perfectness is phrased in.

## Main results

* `Stacks.Divisors.Eta.isEffectiveCartierDivisor_comap_of_isOpenImmersion`: the preimage of an
  effective Cartier divisor under an open immersion is an effective Cartier divisor, registered
  as an instance so that `Lη_{I|_W}` is available without a hypothesis.

## Implementation notes

The three exactness-and-monomorphy instance binders of
`Stacks.Divisors.Eta.derivedEtaPullbackIso` are discharged from flatness of the open immersion,
exactly as in `AlgebraicGeometry.ComplexAndDivisorSituation.derivedEtaPullbackIso`:
`RingedSpaceModuleAdjunction.preservesFiniteLimits_modulePullback_of_isFlat`,
`RingedSpaceModuleAdjunction.preservesColimits_modulePullback` and
`Stacks.IdealTorsion.Eta.mono_pullbackIdealIncl`.  The functors
`Stacks.IdealTorsion.Eta.etaPullbackModules` and
`RingedSpaceModuleAdjunction.modulePullback` are equal by definition but have different head
symbols, so the colimit-preservation instance is carried across by `change`.

The object is presented by a complex of `I`-torsion-free modules, the shape in which
`Stacks.Divisors.Eta.derivedEtaPullbackIso` is stated; this is no restriction, since every
object of `D(𝒪_X)` admits such a presentation by
`Stacks.Divisors.Eta.exists_torsionFreeComplex_iso`.

## References

* [Stacks Project, Tag 0F9X](https://stacks.math.columbia.edu/tag/0F9X)
* [Stacks Project, Tag 0F8Q](https://stacks.math.columbia.edu/tag/0F8Q)
* [Stacks Project, Tag 01WV](https://stacks.math.columbia.edu/tag/01WV)
* [Stacks Project, Tag 02OO](https://stacks.math.columbia.edu/tag/02OO)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace Stacks.Divisors.Eta

variable {X : Scheme.{u}} (D : X.IdealSheafData)
  [Stacks.Divisors.IsEffectiveCartierDivisor D] {W : Scheme.{u}} (j : W ⟶ X)
  [AlgebraicGeometry.IsOpenImmersion j]

/-- **The preimage of an effective Cartier divisor under an open immersion is an effective
Cartier divisor.**  An open immersion is flat, so this is Stacks tag 02OO (6) through
`Stacks.Divisors.isPullbackDefined_of_flat`.  It is an instance so that the décalage by the
preimage ideal sheaf is available with no hypothesis. -/
instance isEffectiveCartierDivisor_comap_of_isOpenImmersion :
    Stacks.Divisors.IsEffectiveCartierDivisor (D.comap j) :=
  Stacks.Divisors.isPullbackDefined_of_flat j D ‹_›

/-- **The derived décalage commutes with restriction along an open immersion:**
`(Lη_I K)|_W ≅ Lη_{I|_W}(K|_W)` in `D(𝒪_W)`, where `I = ℐ_D` is the ideal sheaf of an effective
Cartier divisor `D ⊆ X`, `j : W ⟶ X` is an open immersion, and `K = [G^•]` is presented by a
complex `G^•` of `I`-torsion-free `𝒪_X`-modules.

An open immersion is flat, so this is the flat case of [Stacks, Tag 0F9X],
`Stacks.Divisors.Eta.derivedEtaPullbackIso`, conjugated on each side by
`AlgebraicGeometry.Scheme.Modules.derivedRestrictIsoDerivedPullback`, which identifies
restriction to an open subscheme with the derived pullback along the open immersion. -/
def derivedEtaRestrictOpenIso
    (K : CochainComplex
      (Stacks.IdealTorsion.Eta.TorsionFreeModule X.toRingedSpace (idealSheafι D)) ℤ) :
    (AlgebraicGeometry.Scheme.Modules.restrictFunctor j).mapDerivedCategory.obj
        ((@Stacks.IdealTorsion.Eta.derivedEta X.toRingedSpace (idealSheaf D) (idealSheafι D)
            (mono_idealSheafι D) (isInvertible_idealSheaf D)
            (hasTorsionFreeResolutions D)).obj
          (DerivedCategory.Q.obj
            ((Stacks.IdealTorsion.Eta.torsionFreeComplex X.toRingedSpace
              (idealSheafι D)).obj K))) ≅
      (@Stacks.IdealTorsion.Eta.derivedEta W.toRingedSpace
          (idealSheaf (D.comap j)) (idealSheafι (D.comap j))
          (mono_idealSheafι (D.comap j)) (isInvertible_idealSheaf (D.comap j))
          (hasTorsionFreeResolutions (D.comap j))).obj
        ((AlgebraicGeometry.Scheme.Modules.restrictFunctor j).mapDerivedCategory.obj
          (DerivedCategory.Q.obj
            ((Stacks.IdealTorsion.Eta.torsionFreeComplex X.toRingedSpace
              (idealSheafι D)).obj K))) :=
  have hflat : AlgebraicGeometry.IsFlat j.toLRSHom.toShHom :=
    fun x => AlgebraicGeometry.Flat.stalkMap j x
  letI : PreservesFiniteLimits
      (Stacks.IdealTorsion.Eta.etaPullbackModules j.toLRSHom.toShHom) :=
    RingedSpaceModuleAdjunction.preservesFiniteLimits_modulePullback_of_isFlat
      j.toLRSHom.toShHom hflat
  letI : PreservesColimits
      (RingedSpaceModuleAdjunction.modulePullback j.toLRSHom.toShHom) :=
    RingedSpaceModuleAdjunction.preservesColimits_modulePullback j.toLRSHom.toShHom
  letI : PreservesFiniteColimits
      (Stacks.IdealTorsion.Eta.etaPullbackModules j.toLRSHom.toShHom) := by
    change PreservesFiniteColimits
      (RingedSpaceModuleAdjunction.modulePullback j.toLRSHom.toShHom)
    infer_instance
  letI : Mono (Stacks.IdealTorsion.Eta.pullbackIdealIncl j.toLRSHom.toShHom
      (idealSheaf D) (idealSheafι D)) :=
    @Stacks.IdealTorsion.Eta.mono_pullbackIdealIncl _ _ j.toLRSHom.toShHom hflat
      (idealSheaf D) (idealSheafι D) (mono_idealSheafι D)
  (AlgebraicGeometry.Scheme.Modules.derivedRestrictIsoDerivedPullback j).app _ ≪≫
    derivedEtaPullbackIso j D hflat K ≪≫
    (@Stacks.IdealTorsion.Eta.derivedEta W.toRingedSpace
        (idealSheaf (D.comap j)) (idealSheafι (D.comap j))
        (mono_idealSheafι (D.comap j)) (isInvertible_idealSheaf (D.comap j))
        (hasTorsionFreeResolutions (D.comap j))).mapIso
      ((AlgebraicGeometry.Scheme.Modules.derivedRestrictIsoDerivedPullback j).app _).symm

/-- **The derived décalage commutes with restriction along an open immersion, at an arbitrary
object:** `(Lη_I K)|_W ≅ Lη_{I|_W}(K|_W)` in `D(𝒪_W)` for every object `K` of `D(𝒪_X)`.

`Stacks.Divisors.Eta.derivedEtaRestrictOpenIso` read at a complex of `I`-torsion-free modules
presenting `K`, which `Stacks.Divisors.Eta.exists_torsionFreeComplex_iso` supplies, and
conjugated by that presentation on both sides. -/
def derivedEtaRestrictOpenObjIso (L : DerivedCategory X.Modules) :
    (AlgebraicGeometry.Scheme.Modules.restrictFunctor j).mapDerivedCategory.obj
        ((derivedEtaData D).functor.obj L) ≅
      (derivedEtaData (D.comap j)).functor.obj
        ((AlgebraicGeometry.Scheme.Modules.restrictFunctor j).mapDerivedCategory.obj L) :=
  (AlgebraicGeometry.Scheme.Modules.restrictFunctor j).mapDerivedCategory.mapIso
      ((derivedEtaData D).functor.mapIso
        (exists_torsionFreeComplex_iso D L).choose_spec.some.symm) ≪≫
    derivedEtaRestrictOpenIso D j (exists_torsionFreeComplex_iso D L).choose ≪≫
    (derivedEtaData (D.comap j)).functor.mapIso
      ((AlgebraicGeometry.Scheme.Modules.restrictFunctor j).mapDerivedCategory.mapIso
        (exists_torsionFreeComplex_iso D L).choose_spec.some)

/-- **The derived décalage commutes with restriction to an open subscheme**, written at the
`AlgebraicGeometry.RingedSpace.PseudoCoherence.restrictModules` spelling of restriction that the

local criterion for perfectness, and with it the chart-level comparison
`AlgebraicGeometry.ComplexAndDivisorSituation.ChartDecalage`, is phrased in.

This is `Stacks.Divisors.Eta.derivedEtaRestrictOpenObjIso` carried across
`AlgebraicGeometry.RingedSpace.derivedRestrictModulesIsoRestrictFunctor`; the ringed-space
restriction and Mathlib's restriction along `U.ι` are the same pushforward along the functor on
opens, so the two induced functors on derived categories are identified. -/
def derivedEtaRestrictModulesObjIso (U : X.Opens) (L : DerivedCategory X.Modules) :
    (AlgebraicGeometry.RingedSpace.PseudoCoherence.restrictModules X.toRingedSpace
          U).mapDerivedCategory.obj ((derivedEtaData D).functor.obj L) ≅
      (derivedEtaData (D.comap U.ι)).functor.obj
        ((AlgebraicGeometry.RingedSpace.PseudoCoherence.restrictModules X.toRingedSpace
          U).mapDerivedCategory.obj L) :=
  letI r : (AlgebraicGeometry.RingedSpace.PseudoCoherence.restrictModules X.toRingedSpace
      U).mapDerivedCategory ≅
      (AlgebraicGeometry.Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory :=
    AlgebraicGeometry.RingedSpace.derivedRestrictModulesIsoRestrictFunctor X U
  r.app _ ≪≫ derivedEtaRestrictOpenObjIso D U.ι L ≪≫
    (derivedEtaData (D.comap U.ι)).functor.mapIso (r.app L).symm

end Stacks.Divisors.Eta

end
