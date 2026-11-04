module

public import StacksFrontier.AlgebraicGeometry.Locality.Hxy
public import StacksFrontier.AlgebraicGeometry.DiagonalQuotientPresentation.Basic

/-!
# The shape-2 generator formula is instantiable at the diagonal: the three inputs

`StacksFrontier.AlgebraicGeometry.Locality.Hxy` leaves
`Stacks.Tag08S2Locality.conormalAffineSectionsIsoCotangent_apply_of_image` with one hypothesis,
`hy`. This file checks — by construction, not by inspection — that every *other* input that
statement needs exists at the diagonal of an arbitrary morphism of schemes, over the ambient chart
of an affine open `U` lying over an affine open `V` of the base. So the only thing standing
between [Stacks, Tag 08S2] and the sheaf-side formula is `hy`, and after that the
module-structure step.

## Main results

* the open of the coborder factorization at which the formula is read is
  `Stacks.LeibnizDerivation.chart f U`, **by `rfl`**
  (`Stacks.LeibnizDerivation.coborderRange_ι_preimage_ambientChart`).
  So the section `y₀` the formula wants is literally
  `Stacks.LeibnizDerivation.deltaIdealSection f U b`, with no transport.
* `Stacks.Tag08S2Locality.diagonal_hVeq`: the transport `hVeq` of the preimage open that the
  formula carries, at the diagonal. Both sides are `U`, by
  `Stacks.LeibnizDerivation.diagonal_preimage_ambientChart` and
  `Stacks.LeibnizDerivation.chart_preimage`.
* `Stacks.Tag08S2Locality.exists_diagonalIdealSection_ambient`: **the section `x₀` of the ideal
  sheaf of the diagonal over the ambient chart named by `p₂^♯ b − p₁^♯ b`.** This is the `x₀` of
  `hxy_of_image`, and the element naming it is *exactly* the one
  `Stacks.DiagonalCotangentTransport.exists_addEquiv_kaehlerCotangentChart` states its generator
  formula at — so the two halves of [Stacks, Tag 08S2] meet at one named ring element.

## What is checked here, and why it is not obvious

The diagonal of a morphism of schemes is an immersion, not a closed immersion, and the part (2)
machinery of [Stacks, Tag 01R3] is stated for an immersion with a closed-immersion factorization.
Two things could therefore have gone wrong and do not:

* the formula reads the quotient generator over `i.coborderRange.ι ⁻¹ᵁ V`, and nothing *said* that
  this is the chart `Stacks.LeibnizDerivation.cls` is defined through. It is, definitionally
  (`Stacks.LeibnizDerivation.coborderRange_ι_preimage_ambientChart`), so the two developments'
  opens agree with no bridge at all;
* `x₀` has to be a section of the ideal sheaf of the **diagonal itself**, not of its coborder
  factorization `Stacks.LeibnizDerivation.quotientMap`'s `i.liftCoborder`. The tree's
  `Stacks.LeibnizDerivation.app_deltaAt_eq_zero` is about the factorization; what is needed is the
  same statement for `pullback.diagonal f`, and
  `Stacks.LeibnizDerivation.app_delta_eq_zero` supplies it from the two projections retracting the
  diagonal (`AlgebraicGeometry.pullback.diagonal_fst` and `diagonal_snd`) with no affineness
  hypothesis. `Stacks.Conormal.AffineCotangent.Sections.exists_idealSheaf_section_iff` then
  produces the section.

## What is not done

* **`hy` at the diagonal.** With the three inputs above it is the identity
  `V₀.topIso.inv (ι y₀) = ((i.coborderRange.ι ∣_ V).app ⊤) (V.topIso.inv (ι x₀))` for
  `V₀ = chart f U` — after `Stacks.Conormal.Tag01R3Generators.image_restrictIdealSectionTop` has
  been applied on the right and its `⊤`-analogue on the left. By
  `AlgebraicGeometry.morphismRestrict_app` and `AlgebraicGeometry.Scheme.Opens.ι_appIso` being
  `Iso.refl`, that reduces to `Stacks.LeibnizDerivation.deltaAt f U b` being the comorphism of
  `i.coborderRange.ι` applied to `p₂^♯ b − p₁^♯ b`, which is
  `AlgebraicGeometry.Scheme.Hom.appLE_comp` bookkeeping on the two projections.
* **The module-structure step**, and therefore no clause of [Stacks, Tag 08S2]:
  `Stacks.Conormal.CotangentAppIso.conormalAffineSectionsIsoCotangent` is
  `Γ(X ×_S X, ambientChart f U)`-linear while
  `Stacks.LeibnizDerivation.kaehlerToConormal` lives in `ModuleCat Γ(X, U)`, and
  `Stacks.LeibnizDerivation.surjective_diagRes_appTop` is what bridges them.
  `Stacks.LeibnizDerivation.existsUnique_affineConormalIsoKaehler_iff_isIso` closes both labels
  after that.

**No `stacks` attribute is attached**, and none should be: nothing here is an assertion of either
tag.

## Universe situation

A single universe `u`, as in the tagged statements.

## References

* [Stacks Project, Tag 08S2](https://stacks.math.columbia.edu/tag/08S2)
* [Stacks Project, Tag 01R3](https://stacks.math.columbia.edu/tag/01R3)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction

universe u

namespace Stacks.Tag08S2Locality

variable {X S : Scheme.{u}} (f : X ⟶ S) (U : X.Opens)

/-- **The transport `hVeq` at the diagonal.** Both sides are `U`. -/
theorem diagonal_hVeq :
    pullback.diagonal f ⁻¹ᵁ Stacks.LeibnizDerivation.ambientChart f U =
      (pullback.diagonal f).liftCoborder ⁻¹ᵁ
        ((pullback.diagonal f).coborderRange.ι ⁻¹ᵁ
          Stacks.LeibnizDerivation.ambientChart f U) :=
  (Stacks.LeibnizDerivation.diagonal_preimage_ambientChart f U).trans
    (Stacks.LeibnizDerivation.chart_preimage f U).symm

/-- **The section of the ideal sheaf of the diagonal over the ambient chart named by
`p₂^♯ b − p₁^♯ b`.** This is the `x₀` of `Stacks.Tag08S2Locality.hxy_of_image` at the diagonal,
and the ring element naming it is the one
`Stacks.DiagonalCotangentTransport.exists_addEquiv_kaehlerCotangentChart` states its generator
formula at.

The two projections retract the diagonal, so `Stacks.LeibnizDerivation.app_delta_eq_zero` kills
the difference, and
`Stacks.Conormal.AffineCotangent.Sections.exists_idealSheaf_section_iff` turns that into the
section. Nothing is affine, Noetherian or quasi-compact, and `f` is arbitrary. -/
theorem exists_diagonalIdealSection_ambient (b : Γ(X, U)) :
    ∃ x₀ : (Stacks.ClosedImmersion.idealSheaf
        (pullback.diagonal f).toLRSHom.toShHom).val.obj
          (.op (Stacks.LeibnizDerivation.ambientChart f U)),
      ((kernel.ι (SheafOfModules.unitToPushforwardObjUnit (structureSheafHom
          (pullback.diagonal f).toLRSHom.toShHom))).val.app
          (.op (Stacks.LeibnizDerivation.ambientChart f U))).hom x₀ =
        ((pullback.snd f f).appLE U (Stacks.LeibnizDerivation.ambientChart f U)
            (Stacks.LeibnizDerivation.ambientChart_le_snd_preimage f U)).hom b -
          ((pullback.fst f f).appLE U (Stacks.LeibnizDerivation.ambientChart f U)
            (Stacks.LeibnizDerivation.ambientChart_le_fst_preimage f U)).hom b :=
  (Stacks.Conormal.AffineCotangent.Sections.exists_idealSheaf_section_iff
    (pullback.diagonal f) (Stacks.LeibnizDerivation.ambientChart f U) _).2
    (Stacks.LeibnizDerivation.app_delta_eq_zero (pullback.diagonal f)
      (pullback.diagonal_fst f) (pullback.diagonal_snd f) U
      (Stacks.LeibnizDerivation.ambientChart f U)
      (Stacks.LeibnizDerivation.ambientChart_le_fst_preimage f U)
      (Stacks.LeibnizDerivation.ambientChart_le_snd_preimage f U) b)

end Stacks.Tag08S2Locality

end
