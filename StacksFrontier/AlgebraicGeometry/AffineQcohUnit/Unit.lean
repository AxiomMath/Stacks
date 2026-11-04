module

public import StacksFrontier.AlgebraicGeometry.PushforwardColimits.Counit

/-!
# The unit of Stacks Tag 01SB is invertible at every quasi-coherent module

Let `f : X ⟶ S` be an affine morphism of schemes.  This file discharges the hypothesis `hunit`
of `Stacks.AlgebraicGeometry.AffineQcohEquivalence.isEquivalence_affineQuasicoherentPushforward`:
the unit of the adjunction of Stacks Tag 01SB is invertible at every quasi-coherent
`f_* 𝒪_X`-module.

It is the companion of
`Stacks.AlgebraicGeometry.PushforwardColimits.isIso_counit_app_of_isQuasicoherent` and runs along
the same two steps.  Invertibility of the unit is local on `S` by
`Stacks.AlgebraicGeometry.QcohRestrictEquiv.isIso_unit_of_isIso_unit_affineOpens`, which reduces
the statement to the unit at `f ∣_ V` for `V` an affine open of `S`; and over such a `V` the
restricted module has a *global* presentation, so
`Stacks.AlgebraicGeometry.PushforwardColimits.isIso_unit_app_of_presentation` applies.

## Main results

* `Stacks.AlgebraicGeometry.AffineQcohUnit.isIso_unit_app_of_isQuasicoherent`: **the unit of the
  adjunction of Stacks Tag 01SB is invertible at every quasi-coherent module**, for an affine
  morphism.

## Where the presentation comes from

The counit and the unit need presentations of two different modules, and that is the only
difference between the two arguments.  For the counit the module is an `𝒪_U`-module for `U` an
affine open of `X`, so
`Stacks.AlgebraicGeometry.AffinePushforward.nonempty_presentation_of_isoSpec` produces the
presentation directly.  For the unit the module is
`(SheafOfModules.pushforward (Stacks.AlgebraicGeometry.AffineQcohRestriction.restrictCompareRing
f V)).obj G`, a module over the restriction of `f_* 𝒪_X` to `V`; that is a sheaf of rings and not
the structure sheaf of a scheme, so `nonempty_presentation_of_isoSpec` does not apply to it.

What does apply is `Stacks.AlgebraicGeometry.RestrictEquivalence.presentationOfIsoSpec`: on an
affine scheme, a module over a quasi-coherent algebra which is quasi-coherent after restriction of
scalars has a global presentation.  Its two hypotheses here are the quasi-coherence of
`f_* 𝒪_X` as a module over itself and the quasi-coherence of the restricted `G` after restriction
of scalars, both of which
`Stacks.AlgebraicGeometry.RestrictEquivalence.isQuasicoherent_pullbackModules` already assembles
for the hypothesis `hL`; this file assembles them once more for the unit.

A statement of the same kind is `Stacks.AlgebraicGeometry.QcohLimits.presentationOverAffine`,
but it lives on the slice site `Over V` rather than on the opens of the open subscheme `V`.
`presentationOfIsoSpec` is the `Opens V` form of the same statement, obtained by replaying the
argument over an open subscheme rather than by identifying the two sites; it is proved in
`StacksFrontier/AlgebraicGeometry/RestrictEquivalence/Basic.lean`, which
`StacksFrontier/AlgebraicGeometry/PushforwardColimits/Counit.lean` itself imports.  So no identification of `Over V` with the opens of `V` is needed
for Tag 01SB, and none is made here.

## References

* [Stacks Project, Tag 01SB](https://stacks.math.columbia.edu/tag/01SB)
* [Stacks Project, Tag 0H88](https://stacks.math.columbia.edu/tag/0H88)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry

universe u

noncomputable section

namespace Stacks.AlgebraicGeometry.AffineQcohUnit

open Stacks.AlgebraicGeometry.AffineQcohPushforward
open Stacks.AlgebraicGeometry.AffineQcohEquivalence
open Stacks.AlgebraicGeometry.AffineQcohRestriction

attribute [local instance] Topology.IsOpenEmbedding.functor_isContinuous

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- For an affine morphism `f : X ⟶ S`, an affine open `V` of `S` and a quasi-coherent
`f_* 𝒪_X`-module `G`, the restriction of `G` to `V` — retyped as a module over the direct image
of `𝒪_{f ⁻¹ᵁ V}` along `f ∣_ V` — has a global presentation.  The restriction is quasi-coherent
after restriction of scalars by
`Stacks.AlgebraicGeometry.RestrictEquivalence.isQuasicoherent_pushforward_restrictCompareRing`
followed by Stacks Tag 0H88 on the affine scheme `V`, and `f ∣_ V` is a morphism of affine
schemes, so
`Stacks.AlgebraicGeometry.RestrictEquivalence.presentationOfIsoSpec` produces the
presentation. -/
def presentationPushforwardRestrictCompareRing [IsAffineHom f]
    (G : SheafOfModules.{u} (pushforwardRing f.base X.ringCatSheaf))
    (hG : ((SheafOfModules.restrictScalars f.toRingCatSheafHom).obj G).IsQuasicoherent)
    {V : S.Opens} (hV : IsAffineOpen V) :
    ((SheafOfModules.pushforward.{u} (restrictCompareRing f V)).obj G).Presentation := by
  have hVa : IsAffine (V : S.Opens).toScheme := hV
  have hUa : IsAffine (f ⁻¹ᵁ V).toScheme := hV.preimage f
  have haff : IsAffineHom (resPreimage f V) :=
    @isAffineHom_of_isAffine _ _ (resPreimage f V) hUa hVa
  have hNres : ((SheafOfModules.restrictScalars (resPreimage f V).toRingCatSheafHom).obj
      ((SheafOfModules.pushforward.{u} (restrictCompareRing f V)).obj G)).IsQuasicoherent :=
    @QcohOverAlgebra.isQuasicoherent_restrictScalars_pushforwardModules _ _
      (resPreimage f V) haff _
      (RestrictEquivalence.isQuasicoherent_pushforward_restrictCompareRing f V G hG)
  exact RestrictEquivalence.presentationOfIsoSpec (resPreimage f V).toRingCatSheafHom hV.isoSpec
    (@isQuasicoherent_restrictScalars_pushforwardRing _ _ (resPreimage f V) haff) _ hNres

/-- **The unit of the adjunction of Stacks Tag 01SB is invertible at every quasi-coherent
module.**  For an affine morphism `f : X ⟶ S`, invertibility of the unit is local on `S`, and
over an affine open `V` of `S` the restriction of the module has a global presentation by
`presentationPushforwardRestrictCompareRing`, so
`Stacks.AlgebraicGeometry.PushforwardColimits.isIso_unit_app_of_presentation` applies.  This is
the hypothesis `hunit` of
`Stacks.AlgebraicGeometry.AffineQcohEquivalence.isEquivalence_affineQuasicoherentPushforward`. -/
theorem isIso_unit_app_of_isQuasicoherent [IsAffineHom f]
    (G : SheafOfModules.{u} (pushforwardRing f.base X.ringCatSheaf)) (hG : G.IsQuasicoherent) :
    IsIso ((pullbackPushforwardAdjunction f).unit.app G) := by
  have hqcG : ((SheafOfModules.restrictScalars f.toRingCatSheafHom).obj G).IsQuasicoherent :=
    have := hG
    QcohOverAlgebra.isQuasicoherent_restrictScalars_pushforwardModules f G
  refine QcohRestrictEquiv.isIso_unit_of_isIso_unit_affineOpens f G fun U ↦ ?_
  have hV : IsAffine (U : S.Opens).toScheme := U.2
  have hU : IsAffine (f ⁻¹ᵁ (U : S.Opens)).toScheme := U.2.preimage f
  have haff : IsAffineHom (resPreimage f (U : S.Opens)) :=
    @isAffineHom_of_isAffine _ _ (resPreimage f (U : S.Opens)) hU hV
  exact @PushforwardColimits.isIso_unit_app_of_presentation _ _ _ haff _
    (presentationPushforwardRestrictCompareRing f G hqcG U.2)

end Stacks.AlgebraicGeometry.AffineQcohUnit

end

end
