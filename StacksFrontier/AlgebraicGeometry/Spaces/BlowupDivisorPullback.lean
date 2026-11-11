module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Blowup.ReesSituationComparison
public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.RegularPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.AdmissibleBlowup
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupFinality
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupRelativeProj
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartIdealSheafPreimage
public import StacksFrontier.AlgebraicGeometry.Spaces.EffectiveCartierEtaleEquiv
import StacksFrontier.AlgebraicGeometry.Spaces.BlowupEquivalenceRelationClosed
import StacksFrontier.AlgebraicGeometry.Spaces.EffectiveCartierPullbackCriteria
import StacksFrontier.AlgebraicGeometry.Spaces.EtalePermanence
import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlas

/-!
# Every effective Cartier divisor pulls back along the blowup of an algebraic space

Let `S` be a scheme contained in a big fppf site `B`, let `X` be an algebraic space over `S`, let
`Z ⊆ X` be a closed subspace and let `b : X' ⟶ X` be the blowing up of `X` along `Z` of Stacks
085Q.  Stacks 085X says that for *every* effective Cartier divisor `D` on `X` — not only for the
centre `Z` — the pullback `b⁻¹(D)` is defined in the sense of Stacks 083Y, that is, `b⁻¹(D)` is
again an effective Cartier divisor.

## Main results

* `AlgebraicGeometry.Space.isPullbackDefined_blowUpAlongHom`: **Stacks 085X** for the blowup of
  Stacks 085Q.
* `Stacks.Blowup.isEffectiveCartierDivisor_comap_relativeProjToBase`: the scheme-level input,
  Stacks 0809 for the relative `Proj` of `Stacks.Blowup.reesSituation`.

## The shape of the proof

The source reduces Stacks 085X, through Stacks 085R and 083C, to the statement that a
nonzerodivisor of a ring `A` stays a nonzerodivisor in an affine blowup algebra `A[I/a]`.  The
route taken here is the same reduction with the scheme-level consequence of that algebra fact
used wholesale, exactly as
`AlgebraicGeometry.Space.isEffectiveCartierDivisor_exceptionalDivisor_blowUpAlong` does for
Stacks 085T part (2).  Four inputs meet.

1. **One surjective étale chart suffices.** Stacks 083C (2) ⟹ (1),
   `AlgebraicGeometry.Space.isEffectiveCartierDivisor_of_hasEffectiveCartierEtaleCover`, reduces
   effective Cartier-ness of `b⁻¹(D)` to effective Cartier-ness of its inverse image on a single
   surjective étale scheme chart of `X'`.
2. **The construction provides such a chart.** The blowup is glued from the relative `Proj` `P_U`
   of the Rees algebra of `𝓘_Z|_U` on the presenting scheme `U` of an étale presentation of `X`,
   and `AlgebraicGeometry.Space.RelativeProjGlueingData.chart` is a surjective étale chart
   `P_U ⟶ X'` whose composite with `b` is `P_U ⟶ U ⟶ X`.
3. **The inverse image of `D` on `U` is an effective Cartier divisor on the scheme `U`.** This is
   Stacks 083C (1) ⟹ (3),
   `AlgebraicGeometry.Space.hasEffectiveCartierEtalePullbacks_of_isEffectiveCartier`, at the
   chart `U ⟶ X` of the presentation.  This is the step at which effective Cartier-ness of `D` on
   `X` is used, and the only one; the centre `Z` plays no part in it.
4. **For a scheme it is Stacks 0809.** `AlgebraicGeometry.isPullbackDefined_blowUpToBase` says
   that every effective Cartier divisor on a scheme has a defined pullback along the blowup of
   that scheme in a quasi-coherent ideal.  It is proved for `AlgebraicGeometry.blowUp`, whereas
   the chart `P_U ⟶ U` is the relative `Proj` of `Stacks.Blowup.reesSituation`; the two are
   identified over the base by `Stacks.Blowup.reesSituationBlowUpIso`, and an isomorphism is
   flat, so Stacks 02OO (6) transports the statement.  That transport is
   `Stacks.Blowup.isEffectiveCartierDivisor_comap_relativeProjToBase` below.

So the ideal sheaf of `b⁻¹(D) ×_{X'} P_U` on `P_U` is the inverse image along `P_U ⟶ U` of the
ideal sheaf of `D ×_X U` on `U`, by `AlgebraicGeometry.Space.schemeKer_snd_preimage` and
`AlgebraicGeometry.Space.schemeKer_snd_comp`, and that inverse image is an effective Cartier
divisor by (3) and (4).

## Implementation notes

The blowup is the constructed one of Stacks 085Q,
`AlgebraicGeometry.Space.blowUpAlongHom`, and the parameters `P`, `hcU`, `hcR` and `heq` are
the ones that construction is built from: an étale presentation of `X`, two containment
conditions on the big fppf site, and the normalisation and cocycle conditions making the two
projections of the relative `Proj`s an internal equivalence relation.  None of them appears in
the conclusion beyond naming the blowup, and no part of the assertion of Stacks 085X is assumed:
the only hypothesis on `D` is that it is an effective Cartier divisor on `X`, which is the
source's hypothesis.

The closed-subscheme presentation that Stacks 083C (2) asks for is supplied by
`AlgebraicGeometry.Space.ker_eq_iff_exists_closedSubschemePresentation` applied to the ideal
sheaf of the canonical base change of `b⁻¹(D)` to the chart, which is an object of the site
because the inclusion of a closed subspace is relatively representable.  So no further
containment assumption on the big fppf site is made.

Stacks 085X for a blowup named by its universal property, `AlgebraicGeometry.Space.IsBlowupAlong`,
is `AlgebraicGeometry.Space.isPullbackDefined_of_isBlowupAlong` below: such a blowup is
isomorphic over the base to the constructed one by Stacks 085U.  With the construction data
supplied for every centre it is
`AlgebraicGeometry.Space.IsBlowupAlong.isPullbackDefined_of_isEffectiveCartierDivisor` of
`StacksFrontier/AlgebraicGeometry/Spaces/BlowupAnyCentre.lean`.

## References

* [Stacks Project, Tag 085X](https://stacks.math.columbia.edu/tag/085X)
* [Stacks Project, Tag 085Q](https://stacks.math.columbia.edu/tag/085Q)
* [Stacks Project, Tag 083Y](https://stacks.math.columbia.edu/tag/083Y)
* [Stacks Project, Tag 083C](https://stacks.math.columbia.edu/tag/083C)
* [Stacks Project, Tag 0809](https://stacks.math.columbia.edu/tag/0809)
* [Stacks Project, Tag 02OO](https://stacks.math.columbia.edu/tag/02OO)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace Stacks.Blowup

/-- **Stacks 0809 for the relative `Proj` of `Stacks.Blowup.reesSituation`.** The inverse image
of an effective Cartier divisor `D` on a scheme `X` along the structure morphism of the relative
`Proj` of the Rees algebra of a quasi-coherent ideal sheaf `I` of `X` is again an effective
Cartier divisor.

This is `AlgebraicGeometry.isPullbackDefined_blowUpToBase` — Stacks 0809 for
`AlgebraicGeometry.blowUp`, the blowup every geometric fact about blowups of schemes in this
repository is proved for — transported along `Stacks.Blowup.reesSituationBlowUpIso`: the
comparison is an isomorphism *over the base*, so the two inverse-image ideals differ by pullback
along an isomorphism, and an isomorphism is flat
(`Stacks.Divisors.isPullbackDefined_of_flat`, Stacks 02OO (6)).

No `@[stacks]` attribute is attached: Stacks 0809 is already claimed by
`AlgebraicGeometry.isPullbackDefined_blowUpToBase`, and this is that result moved to the model
of the Rees algebra out of which the blowup of an algebraic space is glued. -/
public theorem isEffectiveCartierDivisor_comap_relativeProjToBase {X : Scheme.{u}}
    (I D : X.IdealSheafData) (hD : Stacks.Divisors.IsEffectiveCartierDivisor D) :
    Stacks.Divisors.IsEffectiveCartierDivisor
      (D.comap (Stacks.RelativeProj.Situation.relativeProjToBase
        (Stacks.Blowup.reesSituation I))) := by
  rw [← reesSituationBlowUpIso_hom_blowUpToBase I, Scheme.IdealSheafData.comap_comp]
  exact Stacks.Divisors.isPullbackDefined_of_flat (reesSituationBlowUpIso I).hom
    (D.comap (AlgebraicGeometry.blowUpToBase I))
    (AlgebraicGeometry.isPullbackDefined_blowUpToBase I D hD)

end Stacks.Blowup

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### Transport of pullback-definedness along an isomorphism over the base -/

/-- **Definedness of the pullback of a closed subspace transports along an isomorphism over the
base.**  Let `D ⊆ X` be a closed subspace of an algebraic space, let `g : Y' ⟶ X` be a morphism
along which the pullback of `D` is defined in the sense of Stacks 083Y, and let `e : Y ≅ Y'` be
an isomorphism of algebraic spaces with `e.hom ≫ g = f`.  Then the pullback of `D` along `f` is
defined as well.

The inverse image of `D` along `f = e.hom ≫ g` is the inverse image along `e.hom` of the
inverse image along `g`, so the statement is the pullback of an effective Cartier divisor along
an isomorphism.  An isomorphism is étale (`AlgebraicGeometry.Space.isEtale_of_isIso`) and étale
morphisms are flat (`AlgebraicGeometry.Space.isFlat_of_isEtale`), so Stacks 02OO (6) for
algebraic spaces, `AlgebraicGeometry.Space.isPullbackDefined_of_isFlat`, supplies it; nothing
beyond that descent is used.

This is the shape in which the consequences of the uniqueness of blowups need it: a result
proved for one blowup of `X` in a closed subspace crosses
`AlgebraicGeometry.Space.IsBlowupAlong.exists_iso` to any other. -/
theorem isPullbackDefined_of_iso_over {X Y Y' : AlgebraicSpaces B S hS} (e : Y ≅ Y')
    {f : Y ⟶ X} {g : Y' ⟶ X} (he : e.hom ≫ g = f) (D : ClosedSubspaces B S hS X.1)
    (hD : IsPullbackDefined B S hS g D) :
    IsPullbackDefined B S hS f D := by
  have hpull : IsPullbackDefined B S hS e.hom (preimageClosedSubspace g D) :=
    isPullbackDefined_of_isFlat B S hS e.hom _ hD
      (isFlat_of_isEtale B S hS (isEtale_of_isIso B S hS e.hom.hom))
  refine isEffectiveCartierDivisor_of_subfunctor_eq ?_ hpull
  change D.1.preimage f.hom = (D.1.preimage g.hom).preimage e.hom.hom
  rw [← Subfunctor.preimage_comp D.1 e.hom.hom g.hom,
    ← ObjectProperty.FullSubcategory.comp_hom, he]

/-! ### Stacks 085X -/

variable {X : AlgebraicSpaces B S hS} [HasSheafify (BigFppfOver.topology B S hS) (Type u)]
  (Z : ClosedSubspaces B S hS X.obj) (P : Presentation B S hS X.obj X.property)
  (hcU : B.Contains (reesChartSituation (centreIdeal Z)
      (isCartesianOnAffineCharts_centreIdeal Z) P).relativeProj)
  (hcR : B.Contains (reesRelationSituation (centreIdeal Z)
      (isCartesianOnAffineCharts_centreIdeal Z) P).relativeProj)
  (heq : CategoryTheory.IsEquivalenceRelation
      ((Over.post B.inclusion).map (reesProjTarget (centreIdeal Z)
        (isCartesianOnAffineCharts_centreIdeal Z) P hcU hcR))
      ((Over.post B.inclusion).map (reesProjSource (centreIdeal Z)
        (isCartesianOnAffineCharts_centreIdeal Z) P hcU hcR)))
  (hcRR : B.Contains (reesDoubleSituation (centreIdeal Z)
      (isCartesianOnAffineCharts_centreIdeal Z) P).relativeProj)

/-- **Stacks 085X.** Let `X` be an algebraic space over a scheme `S`, let `Z ⊆ X` be a closed
subspace and let `b : X' ⟶ X` be the blowing up of `X` along `Z` of Stacks 085Q.  Then for every
effective Cartier divisor `D` on `X` the pullback `b⁻¹(D)` is defined in the sense of Stacks
083Y: the inverse image of `D` along `b` is again an effective Cartier divisor, on `X'`.

By Stacks 083C (2) ⟹ (1) it is enough to see this on one surjective étale scheme chart of `X'`,
and the construction supplies one: the relative `Proj` `P_U` of the Rees algebra of `𝓘_Z|_U` on
the presenting scheme `U` of the étale presentation, whose composite with `b` is `P_U ⟶ U ⟶ X`.
The inverse image of `b⁻¹(D)` there is therefore the inverse image along `P_U ⟶ U` of the closed
subscheme `D ×_X U` of `U`, which is an effective Cartier divisor on `U` by Stacks 083C
(1) ⟹ (3); and for a scheme the inverse image of an effective Cartier divisor along a blowup is
an effective Cartier divisor by Stacks 0809.

The parameters `P`, `hcU`, `hcR` and `heq` are the ones the blowup of Stacks 085Q is built from
and only name the blowup; the hypothesis on `D` is the source's own. -/
@[stacks 085X "for the blowup of Stacks 085Q: with no assumed inputs beyond the \
construction data P, hcU, hcR and heq naming the blowup, every effective Cartier divisor on an \
algebraic space has a defined pullback along it"]
theorem isPullbackDefined_blowUpAlongHom (D : ClosedSubspaces B S hS X.obj)
    (hD : IsEffectiveCartierDivisor B S hS X D) :
    IsPullbackDefined B S hS (blowUpAlongHom Z P hcU hcR heq) D := by
  set d := reesGlueingData (centreIdeal Z) (isCartesianOnAffineCharts_centreIdeal Z)
    P hcU hcR heq with hd
  have hchartE : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) d.chart := d.chart_etale
  have hchartS : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) d.chart := d.chart_surjective
  have hproj : (BigFppfOver.toScheme B S hS).map d.projChartHom =
      (reesChartSituation (centreIdeal Z)
        (isCartesianOnAffineCharts_centreIdeal Z) P).relativeProjToBase := rfl
  have hker : ((BigFppfOver.toScheme B S hS).map
        ((preimageClosedSubspace (blowUpAlongHom Z P hcU hcR heq) D).2.2.rep.snd d.chart)).ker =
      ((BigFppfOver.toScheme B S hS).map (D.2.2.rep.snd (d.chart ≫ d.toBase))).ker :=
    schemeKer_snd_preimage B S hS (blowUpAlongHom Z P hcU hcR heq) D
      ⟨CostructuredArrow.mk d.chart, hchartE⟩
  rw [d.chart_comp_toBase, schemeKer_snd_comp B S hS D d.presentation.toSpace d.projChartHom,
    hproj] at hker
  have hDU : Stacks.Divisors.IsEffectiveCartierDivisor
      ((BigFppfOver.toScheme B S hS).map (D.2.2.rep.snd d.presentation.toSpace)).ker :=
    (isSchemeEffectiveCartierPullback_iff B S hS X D d.presentation.U
      d.presentation.toSpace).1
      (hasEffectiveCartierEtalePullbacks_of_isEffectiveCartier B S hS X D hD
        d.presentation.U d.presentation.toSpace
        (isEtale_of_presheaf_etale B S hS d.presentation.etale))
  have hcartier : Stacks.Divisors.IsEffectiveCartierDivisor
      ((((BigFppfOver.toScheme B S hS).map (D.2.2.rep.snd d.presentation.toSpace)).ker).comap
        ((reesChartSituation (centreIdeal Z)
          (isCartesianOnAffineCharts_centreIdeal Z) P).relativeProjToBase)) :=
    Stacks.Blowup.isEffectiveCartierDivisor_comap_relativeProjToBase
      (reesChartIdeal (centreIdeal Z) (isCartesianOnAffineCharts_centreIdeal Z) P) _ hDU
  refine isEffectiveCartierDivisor_of_hasEffectiveCartierEtaleCover B S hS _ _
    ⟨d.projChart, d.chart, isEtale_of_presheaf_etale B S hS hchartE,
      isSurjective_of_presheafSurjective B S hS d.chart hchartS, ?_⟩
  obtain ⟨R, j, e, hmap, hran⟩ :=
    (ker_eq_iff_exists_closedSubschemePresentation B S hS (blowUpAlong Z P hcU hcR heq)
      (preimageClosedSubspace (blowUpAlongHom Z P hcU hcR heq) D) d.projChart d.chart _).1 rfl
  exact ⟨_, R, j, e, by rw [hker]; exact hcartier, hmap, hran⟩

include P hcU hcR hcRR in
/-- **Stacks 085X, for an arbitrary blowup.**  Let `X` be an algebraic space over a scheme `S`,
let `Z ⊆ X` be a closed subspace and let `b : X' ⟶ X` be *a* blowup of `X` in `Z`, in the sense
of the universal property of Stacks 085U.  Then for every effective Cartier divisor `D` on `X`
the pullback `b⁻¹(D)` is defined in the sense of Stacks 083Y.

This is the source's statement: nothing distinguishes `b` beyond being a blowup of `X` in a
closed subspace, and `D` is an arbitrary effective Cartier divisor.  A blowup in a fixed centre
is unique up to isomorphism over the base,
`AlgebraicGeometry.Space.IsBlowupAlong.exists_iso`, and the blowup of Stacks 085Q is one,
`AlgebraicGeometry.Space.isBlowupAlong_blowUpAlongHom'` (Stacks 085U); so `b` is isomorphic over
`X` to the constructed blowup, for which
`AlgebraicGeometry.Space.isPullbackDefined_blowUpAlongHom` gives the conclusion; and that
conclusion crosses the isomorphism by
`AlgebraicGeometry.Space.isPullbackDefined_of_iso_over`.

The parameters `P`, `hcU`, `hcR` and `hcRR` are those of the construction of Stacks 085Q, used
only to produce the blowup `b` is compared against; none of them occurs in the conclusion. -/
@[stacks 085X "the source statement, for any b which is a blowup of X in a closed subspace in \
the sense of the Stacks 085U universal property; with no assumed inputs apart from the Stacks \
085Q construction data P, hcU, hcR and hcRR, which does not occur in the conclusion"]
theorem isPullbackDefined_of_isBlowupAlong {X' : AlgebraicSpaces B S hS} {b : X' ⟶ X}
    (hb : IsBlowupAlong B S hS Z b) (D : ClosedSubspaces B S hS X.obj)
    (hD : IsEffectiveCartierDivisor B S hS X D) :
    IsPullbackDefined B S hS b D := by
  obtain ⟨e, he⟩ := hb.exists_iso (isBlowupAlong_blowUpAlongHom' Z P hcU hcR hcRR)
  exact isPullbackDefined_of_iso_over e he D
    (isPullbackDefined_blowUpAlongHom Z P hcU hcR
      (isEquivalenceRelation_post_reesProj (centreIdeal Z)
        (isCartesianOnAffineCharts_centreIdeal Z) P hcU hcR hcRR) D hD)

end AlgebraicGeometry.Space

end
