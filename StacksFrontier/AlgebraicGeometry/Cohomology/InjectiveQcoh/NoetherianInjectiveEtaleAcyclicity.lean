module

public import StacksFrontier.AlgebraicGeometry.Cohomology.InjectiveQcoh.ArtinianPresentationChart
public import StacksFrontier.AlgebraicGeometry.Cohomology.InjectiveQcoh.InjectiveEtaleAcyclicity
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeQuasicoherentSubobjectExtensionAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompact
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentPushforwardQcqs
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentSeparator
import StacksCore.Tactic.StacksAttribute

/-!
# Acyclicity of an injective quasi-coherent module on a Noetherian algebraic space

Let `X` be a Noetherian algebraic space over a scheme `S` and let `𝒥` be an injective object of
the category `QCoh(𝒪_X)` of quasi-coherent modules on the small étale site of `X`.  Then
`H^p(U, 𝒥|_U) = 0` for `p > 0` and every quasi-compact and quasi-separated algebraic space `U`
étale over `X`.  This is Stacks 09TL, part (1), here reduced to one input, Stacks 07U6 at an
affine surjective étale chart `j : W ⟶ X` of Stacks 03H6: that `j_*` preserves filtered colimits
of quasi-coherent modules.  That input is proved in
`StacksFrontier/AlgebraicGeometry/Cohomology/InjectiveQcoh/UnconditionalArtinianPresentation.lean`,
which states Stacks 09TJ and Stacks 09TL, part (1), without it.

## Main results

* `AlgebraicGeometry.Space.chartArtinianPresentation_of_isAffine`: the four inputs of
  `AlgebraicGeometry.Space.ChartArtinianPresentation` at an affine locally Noetherian chart of a
  quasi-separated algebraic space, three of them discharged and the fourth assumed.
* `AlgebraicGeometry.Space.isZero_etaleRestrictionCohomology_of_injective_of_pushforwardColimits`:
  **Stacks 09TL, part (1)**, granted that one input.

## Implementation notes

The cohomology `H^p(U, -|_U)` is `AlgebraicGeometry.Space.etaleRestrictionCohomology`, the `p`-th
right derived functor of global sections of `𝒪_U`-modules on the small étale ringed site of `U`
precomposed with étale restriction along `g : U ⟶ X`; this is the arrangement of
`StacksFrontier/AlgebraicGeometry/Cohomology/InjectiveQcoh/EtaleAcyclicity.lean`, where the
universes are discussed.

Of the four fields of `AlgebraicGeometry.Space.ChartArtinianPresentation`, which is the
hypothesis of the chart reduction of Stacks 09TJ
(`AlgebraicGeometry.Space.exists_filtered_colimit_artinian_pushforwards_retract`):

* `pushforwardQuasicoherent`, Stacks 03M9 for the chart, is
  `AlgebraicGeometry.Space.isQuasicoherentOnSite_modulePushforward_of_qcqs`.  It asks that the
  chart morphism be quasi-compact and quasi-separated, and both are automatic here rather than
  assumed: the source of the chart is an affine scheme, hence a quasi-compact and quasi-separated
  algebraic space, and the target `X` is quasi-separated, so Stacks 073B, parts (1) and (2)
  (`AlgebraicGeometry.Space.isQuasiCompact_of_isQuasiCompactSpace` and
  `AlgebraicGeometry.Space.isQuasiSeparated_of_isAbsolutelyQuasiSeparated_source`) apply.
* `enoughInjectives`, Stacks 077V for the chart, is
  `AlgebraicGeometry.Space.quasicoherentSheaves_enoughInjectives`.
* `artinianPresentation`, Stacks 09TI at the chart, is
  `AlgebraicGeometry.Space.exists_filtered_colimit_artinian_pushforwards_of_isAffine`, which
  produces the colimit isomorphic to the given injective object; an isomorphism is in particular
  a retract.
* `pushforwardPreservesFilteredColimits`, Stacks 07U6 for the chart read in `QCoh`, is the one
  field carried as a hypothesis here.  It is proved in `UnconditionalArtinianPresentation.lean`
  of this directory, which imports this file, as
`AlgebraicGeometry.Space.preservesFilteredColimitsOfSize_chartQuasicoherentPushforward_of_isAffine`.

The retract of Stacks 09TJ is then turned into the vanishing by
`AlgebraicGeometry.Space.isZero_etaleRestrictionCohomology_of_retract_colimit`: the colimit is
computed in all modules by Stacks 03M1, étale restriction preserves it, Stacks 073E in the form
`AlgebraicGeometry.Space.isZero_rightDerived_globalSectionsFunctor_of_isColimit` reduces the
vanishing to the terms of the diagram, those vanish by the Artinian case
`AlgebraicGeometry.Space.isZero_etaleRestrictionCohomology_of_isArtinianPushforward`, and a
retract of a zero object is zero.  No colimit-preservation of `H^p(U, -|_U)` is assumed.

Part (2) of Stacks 09TL, the vanishing `R^p f_*𝒥 = 0` for `f : X ⟶ Y` with `Y` quasi-separated,
is not stated here.

## References

* [Stacks Project, Tag 09TL](https://stacks.math.columbia.edu/tag/09TL)
* [Stacks Project, Tag 09TJ](https://stacks.math.columbia.edu/tag/09TJ)
* [Stacks Project, Tag 09TI](https://stacks.math.columbia.edu/tag/09TI)
* [Stacks Project, Tag 07U6](https://stacks.math.columbia.edu/tag/07U6)
* [Stacks Project, Tag 03M9](https://stacks.math.columbia.edu/tag/03M9)
* [Stacks Project, Tag 077V](https://stacks.math.columbia.edu/tag/077V)
* [Stacks Project, Tag 073B](https://stacks.math.columbia.edu/tag/073B)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.SiteModules

attribute [local instance 5000] SheafOfModules.instAbelian

noncomputable section

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The inputs of Stacks 09TJ at an affine locally Noetherian chart**, three of the four
discharged.  Let `X` be a quasi-separated algebraic space and `j : W ⟶ X` a morphism from an
affine locally Noetherian scheme of the site.  Granted Stacks 07U6 for `j` read in the
quasi-coherent categories, the chart carries an
`AlgebraicGeometry.Space.ChartArtinianPresentation`. -/
theorem chartArtinianPresentation_of_isAffine (hZ : B.Contains (⊤_ Scheme.{u}))
    {X : AlgebraicSpaces B S hS} (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
    (W : BigFppfOver B S hS) (j : schemeSpace W ⟶ X)
    (hWaff : IsAffine ((BigFppfOver.toScheme B S hS).obj W))
    (hWnoeth : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj W))
    (hChartFilteredColimits : ∀ hqc : ∀ M : QuasicoherentSheaves.{u, u} B S hS
        (schemeSpace W).1 (schemeSpace W).2,
        ((modulePushforward B S hS j).obj M.obj).IsQuasicoherentOnSite,
      PreservesFilteredColimitsOfSize.{u, u}
        (chartQuasicoherentPushforward B S hS j hqc)) :
    ChartArtinianPresentation B S hS X (schemeSpace W) j := by
  have hjqc : IsQuasiCompact B S hS j.hom :=
    isQuasiCompact_of_isQuasiCompactSpace B S hS hZ X.2 hXqs
      (isQuasiCompactSpace_yoneda_of_isAffine B S hS W hWaff) j.hom
  have hjqs : IsQuasiSeparated B S hS j.hom :=
    isQuasiSeparated_of_isAbsolutelyQuasiSeparated_source B S hS hZ (schemeSpace W).2
      (isAbsolutelyQuasiSeparated_of_isAffineSpace B S hS hZ
        (isAffineSpace_yoneda B S hS W hWaff)) j.hom
  refine
    { pushforwardQuasicoherent := fun M =>
        isQuasicoherentOnSite_modulePushforward_of_qcqs B S hS j hjqc hjqs M.obj M.property
      enoughInjectives := quasicoherentSheaves_enoughInjectives B S hS _ _
      pushforwardPreservesFilteredColimits := hChartFilteredColimits _
      artinianPresentation := ?_ }
  intro JY hJY
  have := hJY
  obtain ⟨I, inst, hfilt, D, c, hart, hc, ⟨e⟩⟩ :=
    exists_filtered_colimit_artinian_pushforwards_of_isAffine B S hS W hWaff hWnoeth JY
  exact ⟨I, inst, hfilt, D, c, hart, hc,
    ⟨{ i := e.inv, r := e.hom, retract := e.inv_hom_id }⟩⟩

attribute [local instance] hasInjectiveResolutions_modules enoughInjectives_modules in
/-- For `X` a Noetherian algebraic space over a scheme `S` of a big fppf site and `𝒥` an
injective object of `QCoh(𝒪_X)`, the cohomology `H^p(U, 𝒥|_U)` vanishes for `p > 0` and every
quasi-compact quasi-separated algebraic space `U` étale over `X`, provided the direct image
along an affine surjective étale chart of `X` preserves filtered colimits of quasi-coherent
modules.  The unconditional form is
`AlgebraicGeometry.Space.isZero_etaleRestrictionCohomology_of_injective_of_isNoetherian`. -/
theorem isZero_etaleRestrictionCohomology_of_injective_of_pushforwardColimits
    (hZ : B.Contains (⊤_ Scheme.{u})) {X U : AlgebraicSpaces B S hS}
    (hX : IsNoetherian B S hS hZ X.1)
    (hChartFilteredColimits : ∀ (W : BigFppfOver B S hS) (j : schemeSpace W ⟶ X),
      IsAffine ((BigFppfOver.toScheme B S hS).obj W) →
      IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj W) →
      (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf j.hom →
      IsEtale B S hS j.hom →
      ∀ hqc : ∀ M : QuasicoherentSheaves.{u, u} B S hS
          (schemeSpace W).1 (schemeSpace W).2,
          ((modulePushforward B S hS j).obj M.obj).IsQuasicoherentOnSite,
        PreservesFilteredColimitsOfSize.{u, u}
          (chartQuasicoherentPushforward B S hS j hqc))
    (J : QuasicoherentSheaves.{u, u} B S hS X.1 X.2) [Injective J]
    (g : U ⟶ X) (hg : IsEtale B S hS g.hom)
    (hUqc : IsQuasiCompactSpace B S hS U.1)
    (hUqs : IsAbsolutelyQuasiSeparated B S hS hZ U.1)
    (p : ℕ) (hp : 0 < p) :
    IsZero ((etaleRestrictionCohomology B S hS g hg p).obj J) := by
  obtain ⟨I, inst, hfilt, D, c, hart, ⟨hc⟩, ⟨r⟩⟩ :=
    exists_filtered_colimit_artinian_pushforwards_retract B S hS hZ X hX
      (fun W j hWaff hWnoeth hWsurj hWet =>
        chartArtinianPresentation_of_isAffine B S hS hZ hX.2.1 W j hWaff hWnoeth
          (hChartFilteredColimits W j hWaff hWnoeth hWsurj hWet)) J
  let := inst
  let := hfilt
  exact isZero_etaleRestrictionCohomology_of_retract_colimit B S hS hZ hX.2.1 g hg hUqc hUqs
    p hp J D c hart hc r

end AlgebraicGeometry.Space

end

end
