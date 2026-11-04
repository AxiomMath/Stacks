module

public import StacksFrontier.AlgebraicGeometry.PushforwardColimits.Unit
public import StacksFrontier.AlgebraicGeometry.QcohRestrictEquiv.PushforwardRestrict
public import StacksFrontier.AlgebraicGeometry.RestrictEquivalence.Basic

/-!
# The counit of Stacks Tag 01SB is invertible at every quasi-coherent module

Let `f : X ⟶ S` be an affine morphism of schemes.  This file discharges the hypothesis `hcounit`
of `Stacks.AlgebraicGeometry.AffineQcohEquivalence.isEquivalence_affineQuasicoherentPushforward`:
the counit of the adjunction of Stacks Tag 01SB is invertible at every quasi-coherent
`𝒪_X`-module.

The two inputs are already available.  Invertibility of the counit is local on `S` by
`Stacks.AlgebraicGeometry.QcohRestrictEquiv.isIso_counit_of_isIso_counit_affineOpens`, which
reduces the statement to the counit at `f ∣_ V` for `V` an affine open of `S`; and over such a
`V` the preimage `f ⁻¹ᵁ V` is affine, so the restricted module — quasi-coherent by
`Stacks.AlgebraicGeometry.RestrictEquivalence.isQuasicoherent_restrictOver_structureSheaf` — has
a *global* presentation by
`Stacks.AlgebraicGeometry.AffinePushforward.nonempty_presentation_of_isoSpec`, and
`Stacks.AlgebraicGeometry.PushforwardColimits.isIso_counit_app_of_presentation` applies.

## Main results

* `Stacks.AlgebraicGeometry.PushforwardColimits.isIso_counit_app_of_isQuasicoherent`: **the
  counit of the adjunction of Stacks Tag 01SB is invertible at every quasi-coherent module**, for
  an affine morphism.

## What is not done

The companion hypothesis `hunit` is *not* proved here.  Its local form is available —
`Stacks.AlgebraicGeometry.PushforwardColimits.isIso_unit_app_of_presentation` gives the unit at
any `f_* 𝒪_X`-module admitting a global presentation, and
`Stacks.AlgebraicGeometry.QcohRestrictEquiv.isIso_unit_of_isIso_unit_affineOpens` reduces the
global statement to affine opens of `S` — but what is missing is the presentation itself: for `V`
an affine open of `S` one needs a `SheafOfModules.Presentation` of
`(SheafOfModules.pushforward (Stacks.AlgebraicGeometry.AffineQcohRestriction.restrictCompareRing
f V)).obj G`, a module over the restriction of `f_* 𝒪_X`, which is a sheaf of rings and not the
structure sheaf of a scheme; `nonempty_presentation_of_isoSpec` does not apply to it.  The
corresponding statement for a quasi-coherent algebra is
`Stacks.AlgebraicGeometry.QcohLimits.presentationOverAffine`, but that produces a presentation on
the slice site `Over V` rather than on the site of opens of the open subscheme `V`, and the two
spellings are not identified anywhere in this repository.

That presentation is the *only* thing missing: granted a term of type
`((SheafOfModules.pushforward (restrictCompareRing f V)).obj G).Presentation` for every affine
open `V` of `S` and every quasi-coherent `G`, the hypothesis `hunit` follows by
`isIso_unit_of_isIso_unit_affineOpens` together with `isIso_unit_app_of_presentation` at
`resPreimage f V`, which is an affine morphism of affine schemes.

## References

* [Stacks Project, Tag 01SB](https://stacks.math.columbia.edu/tag/01SB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry

universe u

noncomputable section

namespace Stacks.AlgebraicGeometry.PushforwardColimits

open Stacks.AlgebraicGeometry.AffineQcohPushforward
open Stacks.AlgebraicGeometry.AffineQcohEquivalence
open Stacks.AlgebraicGeometry.AffineQcohRestriction

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- **The counit of the adjunction of Stacks Tag 01SB is invertible at every quasi-coherent
module.**  For an affine morphism `f : X ⟶ S`, invertibility of the counit is local on `S`, and
over an affine open `V` of `S` the preimage `f ⁻¹ᵁ V` is affine, so the restriction of the module
has a global presentation and `isIso_counit_app_of_presentation` applies.  This is the hypothesis
`hcounit` of
`Stacks.AlgebraicGeometry.AffineQcohEquivalence.isEquivalence_affineQuasicoherentPushforward`. -/
theorem isIso_counit_app_of_isQuasicoherent [IsAffineHom f]
    (M : SheafOfModules.{u} X.ringCatSheaf) (hM : M.IsQuasicoherent) :
    IsIso ((pullbackPushforwardAdjunction f).counit.app M) := by
  refine QcohRestrictEquiv.isIso_counit_of_isIso_counit_affineOpens f M fun U ↦ ?_
  have hV : IsAffine (U : S.Opens).toScheme := U.2
  have hU : IsAffine (f ⁻¹ᵁ (U : S.Opens)).toScheme := U.2.preimage f
  have hN : ((restrictOver (f ⁻¹ᵁ (U : S.Opens)) X.ringCatSheaf).obj M).IsQuasicoherent :=
    RestrictEquivalence.isQuasicoherent_restrictOver_structureSheaf
      (f ⁻¹ᵁ (U : S.Opens)) M hM
  have haff : IsAffineHom (resPreimage f (U : S.Opens)) :=
    @isAffineHom_of_isAffine _ _ (resPreimage f (U : S.Opens)) hU hV
  exact @isIso_counit_app_of_presentation _ _ _ haff _
    (@AffinePushforward.nonempty_presentation_of_isoSpec _ _
      (@Scheme.isoSpec (f ⁻¹ᵁ (U : S.Opens)).toScheme hU) _ hN).some

end Stacks.AlgebraicGeometry.PushforwardColimits

end

end
