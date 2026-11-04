module

public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.InverseImageCentre
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupCentreCartier
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupUniversalLift
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatFieldCover

/-!
# The blowup of an algebraic space is final among the objects making the centre Cartier

Let `S` be a scheme, let `X` be an algebraic space over `S` and let `Z ⊆ X` be a closed
subspace.  Tag 085U says that the blowing up `b : X' ⟶ X` of `Z` in `X` is a final object of the
category `𝒞` of those `Y ⟶ X` whose inverse image of `Z` is an effective Cartier divisor on `Y`.
The membership half — that `b` is an object of `𝒞` — is
`AlgebraicGeometry.Space.isEffectiveCartierDivisor_exceptionalDivisor'` in
`StacksFrontier/AlgebraicGeometry/Spaces/BlowupCentreCartier.lean`.  This file proves the
**finality** half, that every object of `𝒞` admits a unique morphism to `b` over `X`, and
assembles the two into the tag.

## Main results

* `Stacks.Blowup.existsUnique_hom_relativeProj_reesSituation`: **the mapping-in property of the
  relative `Proj` of the explicit Rees algebra sheaf of a scheme.**  Tag 0806 for the blowup of
  a scheme, transported along the comparison of the three constructions of that blowup, in the
  form of a unique lift over the base.
* `AlgebraicGeometry.Space.existsUnique_hom_relativeProj_blowUpGlueingData`: the unique lift of
  an étale scheme chart of `X` that factors through the presenting scheme of the presentation
  the blowup is built from.  This is the previous statement read through the cartesian chart
  square of the glueing datum.
* `AlgebraicGeometry.Space.exists_adapted_chart`: every algebraic space over `X` has a
  surjective étale scheme chart which maps to the presenting scheme compatibly with `X`.
* `AlgebraicGeometry.Space.existsUnique_hom_blowUpAlong'`: **the finality half of Tag 085U.**
  Every algebraic space over `X` on which the inverse image of `Z` is an effective Cartier
  divisor admits exactly one morphism to the blowup over `X`.
* `AlgebraicGeometry.Space.isBlowupAlong_blowUpAlongHom'`: **Tag 085U.** The blowing up
  `b : X' ⟶ X` of `X` along `Z` is a final object of `𝒞`.
* `AlgebraicGeometry.Space.existsUnique_lift_blowUpAlongHom'`: Tag 085U as the lifting property
  its consumers use.

## Implementation notes

**Finality is inherited from the scheme level through the chart square, not reproved.**  The
source proves finality by producing the classifying morphism from the mapping-in property of
relative `Proj` and then arguing uniqueness from separatedness of `b` together with
scheme-theoretic density of the complement of the exceptional divisor.  Neither input is needed
here.  The blowup is `AlgebraicGeometry.Space.RelativeProjGlueingData.relativeProj` of the Rees
glueing datum, and `AlgebraicGeometry.Space.RelativeProjGlueingData.isPullback_chart_toBase`
says that `P_U = X' ×_X U` for the presenting scheme `U` of the presentation.  So for a scheme
chart `V` of an algebraic space `Y` over `X` which comes with a morphism `w : V ⟶ U` over `X`,
the morphisms `V ⟶ X'` over `X` correspond *bijectively* to the morphisms `V ⟶ P_U` over `w`,
and those are classified — existence and uniqueness at once — by Tag 0806 for the scheme `U`.
Uniqueness on such a chart is therefore the scheme-level uniqueness, which is where the
separatedness and density arguments already live.

**Why an arbitrary `Y` reduces to such a chart.**  The atlas of `Y` need not map to `U`, but
`AlgebraicGeometry.Space.Presentation.toSpace` of `X` is relatively representable, so its base
change along `h_{U₀} ⟶ Y ⟶ X` is a scheme `V` which is again a surjective étale chart of `Y`
and which does map to `U`.  Its kernel pair `V ×_Y V` is a scheme because the diagonal of `Y`
is representable, and the two composites `V ×_Y V ⇉ V ⟶ X'` agree by the uniqueness just
described, applied on `V ×_Y V` with the morphism to `U` taken along *one* of the two
projections — this is the point at which it matters that the uniqueness statement is about all
lifts of a fixed morphism to `X`, not only about those compatible with a chosen factorisation
through `U`.  Unique descent along the atlas,
`AlgebraicGeometry.existsUnique_desc_of_surjective_etale_atlas`, then produces the morphism
`Y ⟶ X'` and simultaneously makes it unique.

**The two constructions of the blowup of a scheme.**  Tag 0806 is proved in the library for
`AlgebraicGeometry.blowUp`, the relative `Proj` of the *chosen* Rees algebra datum, whereas the
blowup of an algebraic space is glued from `Stacks.Blowup.reesSituation`, the situation of the
*explicit* Rees algebra sheaf.  `Stacks.Blowup.reesSituationBlowUpIso` identifies the two over
the base, and the unique-lift property transports along it.  It carries no divisor or density
content.

## References

* [Stacks Project, Tag 085U](https://stacks.math.columbia.edu/tag/085U)
* [Stacks Project, Tag 085Q](https://stacks.math.columbia.edu/tag/085Q)
* [Stacks Project, Tag 084C](https://stacks.math.columbia.edu/tag/084C)
* [Stacks Project, Tag 083C](https://stacks.math.columbia.edu/tag/083C)
* [Stacks Project, Tag 0263](https://stacks.math.columbia.edu/tag/0263)
* [Stacks Project, Tag 0262](https://stacks.math.columbia.edu/tag/0262)
* [Stacks Project, Tag 0806](https://stacks.math.columbia.edu/tag/0806)
* [Stacks Project, Tag 01OG](https://stacks.math.columbia.edu/tag/01OG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.Blowup

variable {X : AlgebraicGeometry.Scheme.{u}} (I : X.IdealSheafData)

/-- **The mapping-in property of the relative `Proj` of the Rees algebra sheaf, Tag 0806.**  Let
`I` be a quasi-coherent ideal sheaf on a scheme `X` and let `q : W ⟶ X` be a morphism along
which `I` pulls back to an effective Cartier divisor.  Then there is exactly one morphism from
`W` to the relative `Proj` of `Stacks.Blowup.reesSituation I` over `X`.

This is Tag 0806 for `AlgebraicGeometry.blowUp`, in the unique-lift form
`AlgebraicGeometry.blowUpLift`, transported along `Stacks.Blowup.reesSituationBlowUpIso`.
Unconditional. -/
theorem existsUnique_hom_relativeProj_reesSituation {W : AlgebraicGeometry.Scheme.{u}}
    (q : W ⟶ X) (hq : Stacks.Divisors.IsEffectiveCartierDivisor (I.comap q)) :
    ∃! g : W ⟶ (reesSituation I).relativeProj,
      g ≫ (reesSituation I).relativeProjToBase = q := by
  have he := reesSituationBlowUpIso_hom_blowUpToBase I
  refine ⟨AlgebraicGeometry.blowUpLift I q hq ≫ (reesSituationBlowUpIso I).inv, ?_,
    fun g hg => ?_⟩
  · dsimp only
    rw [← he]
    erw [Category.assoc, Iso.inv_hom_id_assoc]
    exact AlgebraicGeometry.blowUpLift_comp I q hq
  · rw [Iso.eq_comp_inv]
    refine AlgebraicGeometry.blowUpLift_unique I q hq _ ?_
    dsimp only at hg ⊢
    rw [Category.assoc, he]
    exact hg

end Stacks.Blowup

namespace AlgebraicGeometry.Space

open AlgebraicGeometry

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **A morphism of schemes over `S` is a morphism of the big fppf category over `S`.**  A
morphism between the underlying schemes of two objects of the site which commutes with their
structure morphisms to `S` is the image of a morphism of the site; see
`AlgebraicGeometry.Space.toScheme_map_siteHomOfScheme`. -/
def siteHomOfScheme {V W : BigFppfOver B S hS}
    (h : (BigFppfOver.toScheme B S hS).obj V ⟶ (BigFppfOver.toScheme B S hS).obj W)
    (hw : h ≫ B.inclusion.map W.hom = B.inclusion.map V.hom) : V ⟶ W :=
  Over.homMk (ObjectProperty.homMk h) (ObjectProperty.hom_ext _ hw)

/-- The morphism of schemes underlying `AlgebraicGeometry.Space.siteHomOfScheme` is the one it
was built from. -/
theorem toScheme_map_siteHomOfScheme {V W : BigFppfOver B S hS}
    (h : (BigFppfOver.toScheme B S hS).obj V ⟶ (BigFppfOver.toScheme B S hS).obj W)
    (hw : h ≫ B.inclusion.map W.hom = B.inclusion.map V.hom) :
    (BigFppfOver.toScheme B S hS).map (siteHomOfScheme h hw) = h :=
  rfl

variable {X : AlgebraicSpaces B S hS}
  [HasSheafify (BigFppfOver.topology B S hS) (Type u)]
  (Z : ClosedSubspaces B S hS X.obj) (P : Presentation B S hS X.obj X.property)
  (hcU : B.Contains (reesChartSituation (centreIdeal Z)
      (isCartesianOnAffineCharts_centreIdeal Z) P).relativeProj)
  (hcR : B.Contains (reesRelationSituation (centreIdeal Z)
      (isCartesianOnAffineCharts_centreIdeal Z) P).relativeProj)
  (hcRR : B.Contains (reesDoubleSituation (centreIdeal Z)
      (isCartesianOnAffineCharts_centreIdeal Z) P).relativeProj)

omit [HasSheafify (BigFppfOver.topology B S hS) (Type u)] in
/-- **The ideal sheaf of the inverse image of the centre on an object of the site over the
presenting scheme.**  For a morphism `w : V ⟶ U` of the site into the presenting scheme of a
presentation of `X`, the sheaf of ideals of the inverse image of the centre along
`V ⟶ U ⟶ X` is the inverse image along `w` of the Rees chart ideal, the sheaf of ideals whose
Rees algebra the blowup is the relative `Proj` of.

This is `AlgebraicGeometry.Space.ker_rep_snd_eq_reesChartIdeal` together with the composition
rule `AlgebraicGeometry.Space.schemeKer_snd_comp` for inverse images on charts. -/
theorem ker_rep_snd_comp_presentation_toSpace {V : BigFppfOver B S hS} (w : V ⟶ P.U) :
    ((BigFppfOver.toScheme B S hS).map (Z.2.2.rep.snd (yoneda.map w ≫ P.toSpace))).ker =
      (reesChartIdeal (centreIdeal Z) (isCartesianOnAffineCharts_centreIdeal Z) P).comap
        ((BigFppfOver.toScheme B S hS).map w) :=
  (schemeKer_snd_comp B S hS Z P.toSpace w).trans
    (congrArg (fun J => J.comap ((BigFppfOver.toScheme B S hS).map w))
      (ker_rep_snd_eq_reesChartIdeal B S hS X Z P))

omit [HasSheafify (BigFppfOver.topology B S hS) (Type u)] in
/-- **The Rees chart ideal pulls back to an effective Cartier divisor on a chart adapted to the
presentation.**  Let `y : Y ⟶ X` be a morphism of algebraic spaces along which the centre `Z`
pulls back to an effective Cartier divisor, let `a : h_V ⟶ Y` be an étale scheme chart of `Y`
and let `w : V ⟶ U` be a morphism into the presenting scheme with `V ⟶ U ⟶ X` equal to
`V ⟶ Y ⟶ X`.  Then the inverse image of the Rees chart ideal along `w` is an effective Cartier
divisor on the scheme `V`.

The chart condition of Tag 083C, available on *every* étale chart by
`AlgebraicGeometry.Space.hasEffectiveCartierEtalePullbacks_of_isEffectiveCartier`, is a
condition on the ideal sheaf of the inverse image of the divisor by
`AlgebraicGeometry.Space.isSchemeEffectiveCartierPullback_iff_ker`, and that ideal sheaf is
computed by `AlgebraicGeometry.Space.ker_rep_snd_comp_presentation_toSpace`. -/
theorem isEffectiveCartierDivisor_comap_reesChartIdeal_of_chart {Y : AlgebraicSpaces B S hS}
    (y : Y ⟶ X) (hy : IsPullbackDefined B S hS y Z) {V : BigFppfOver B S hS} (w : V ⟶ P.U)
    (a : yoneda.obj V ⟶ Y.obj) (ha : IsEtale B S hS a)
    (hsq : yoneda.map w ≫ P.toSpace = a ≫ y.hom) :
    Stacks.Divisors.IsEffectiveCartierDivisor
      ((reesChartIdeal (centreIdeal Z) (isCartesianOnAffineCharts_centreIdeal Z) P).comap
        ((BigFppfOver.toScheme B S hS).map w)) := by
  have hci : _root_.AlgebraicGeometry.IsClosedImmersion
      ((BigFppfOver.toScheme B S hS).map (Z.2.2.rep.snd (yoneda.map w ≫ P.toSpace))) :=
    Z.2.2.property_snd _
  have hj : (Z.1.preimage y.hom).preimage a =
      Subfunctor.range (yoneda.map (Z.2.2.rep.snd (yoneda.map w ≫ P.toSpace))) := by
    rw [← Subfunctor.preimage_comp, ← hsq]
    exact preimage_eq_range_rep_snd B S hS X Z V (yoneda.map w ≫ P.toSpace)
  have hpull : HasEffectiveCartierEtalePullbacks B S hS Y
      ⟨Z.1.preimage y.hom,
        isClosedSubspace_preimage B S hS y.hom Z.1 X.2 Y.2 Z.2⟩ :=
    hasEffectiveCartierEtalePullbacks_of_isEffectiveCartier B S hS Y _ hy
  have hker := (isSchemeEffectiveCartierPullback_iff_ker B S hS Y
    ⟨Z.1.preimage y.hom, isClosedSubspace_preimage B S hS y.hom Z.1 X.2 Y.2 Z.2⟩ V _ a
    (Z.2.2.rep.snd (yoneda.map w ≫ P.toSpace)) hj).1 (hpull V a ha)
  rwa [ker_rep_snd_comp_presentation_toSpace Z P w] at hker

/-- **The unique lift of a chart adapted to the presentation.**  Let `w : V ⟶ U` be a morphism
of the site into the presenting scheme of the presentation the blowup is built from, and suppose
the inverse image of the Rees chart ideal along `w` is an effective Cartier divisor on the
scheme `V`.  Then there is exactly one morphism from `h_V` to the blowup whose composite with
the structure morphism of the blowup is `V ⟶ U ⟶ X`.

The chart square `AlgebraicGeometry.Space.RelativeProjGlueingData.isPullback_chart_toBase`
exhibits `P_U` as `X' ×_X U`, so such morphisms correspond to morphisms `V ⟶ P_U` over `w`;
Yoneda identifies those with morphisms of the site, the forgetful functor to schemes with
morphisms of schemes over `U`, and
`Stacks.Blowup.existsUnique_hom_relativeProj_reesSituation` classifies those. -/
theorem existsUnique_hom_relativeProj_blowUpGlueingData {V : BigFppfOver B S hS} (w : V ⟶ P.U)
    (hEC : Stacks.Divisors.IsEffectiveCartierDivisor
      ((reesChartIdeal (centreIdeal Z) (isCartesianOnAffineCharts_centreIdeal Z) P).comap
        ((BigFppfOver.toScheme B S hS).map w))) :
    ∃! l : yoneda.obj V ⟶ (blowUpGlueingData Z P hcU hcR hcRR).relativeProj,
      l ≫ (blowUpGlueingData Z P hcU hcR hcRR).toBase = yoneda.map w ≫ P.toSpace := by
  have hpb : IsPullback (blowUpGlueingData Z P hcU hcR hcRR).chart
      (yoneda.map (blowUpGlueingData Z P hcU hcR hcRR).projChartHom)
      (blowUpGlueingData Z P hcU hcR hcRR).toBase P.toSpace :=
    (blowUpGlueingData Z P hcU hcR hcRR).isPullback_chart_toBase
  have hπ : (BigFppfOver.toScheme B S hS).map
      (blowUpGlueingData Z P hcU hcR hcRR).projChartHom =
      (reesChartSituation (centreIdeal Z)
        (isCartesianOnAffineCharts_centreIdeal Z) P).relativeProjToBase := rfl
  obtain ⟨gs, hgs, hgsu⟩ :=
    Stacks.Blowup.existsUnique_hom_relativeProj_reesSituation
      (reesChartIdeal (centreIdeal Z) (isCartesianOnAffineCharts_centreIdeal Z) P)
      ((BigFppfOver.toScheme B S hS).map w) hEC
  have hwS : (BigFppfOver.toScheme B S hS).map w ≫ B.inclusion.map P.U.hom =
      B.inclusion.map V.hom :=
    (B.inclusion.map_comp w.left P.U.hom).symm.trans (congrArg B.inclusion.map (Over.w w))
  have hgsS : gs ≫ B.inclusion.map (blowUpGlueingData Z P hcU hcR hcRR).projChart.hom =
      B.inclusion.map V.hom :=
    (Category.assoc gs ((reesChartSituation (centreIdeal Z)
        (isCartesianOnAffineCharts_centreIdeal Z) P).relativeProjToBase)
        (B.inclusion.map P.U.hom)).symm.trans
      ((congrArg (fun k => k ≫ B.inclusion.map P.U.hom) hgs).trans hwS)
  obtain ⟨ws, hwsg⟩ :
      ∃ ws : V ⟶ (blowUpGlueingData Z P hcU hcR hcRR).projChart,
        (BigFppfOver.toScheme B S hS).map ws = gs :=
    ⟨siteHomOfScheme gs hgsS, rfl⟩
  have hwsπ : ws ≫ (blowUpGlueingData Z P hcU hcR hcRR).projChartHom = w := by
    refine BigFppfOver.map_toScheme_injective B S hS ?_
    show (BigFppfOver.toScheme B S hS).map
      (ws ≫ (blowUpGlueingData Z P hcU hcR hcRR).projChartHom) =
      (BigFppfOver.toScheme B S hS).map w
    rw [Functor.map_comp, hwsg, hπ]
    exact hgs
  have hws2 : yoneda.map ws ≫
      yoneda.map (blowUpGlueingData Z P hcU hcR hcRR).projChartHom = yoneda.map w :=
    (yoneda.map_comp ws (blowUpGlueingData Z P hcU hcR hcRR).projChartHom).symm.trans
      (congrArg yoneda.map hwsπ)
  have hmain : (yoneda.map ws ≫ (blowUpGlueingData Z P hcU hcR hcRR).chart) ≫
      (blowUpGlueingData Z P hcU hcR hcRR).toBase = yoneda.map w ≫ P.toSpace :=
    (Category.assoc (yoneda.map ws) (blowUpGlueingData Z P hcU hcR hcRR).chart
        (blowUpGlueingData Z P hcU hcR hcRR).toBase).trans
      ((congrArg (fun k => yoneda.map ws ≫ k)
          (blowUpGlueingData Z P hcU hcR hcRR).chart_comp_toBase).trans
        ((Category.assoc (yoneda.map ws)
              (yoneda.map (blowUpGlueingData Z P hcU hcR hcRR).projChartHom)
              P.toSpace).symm.trans
          (congrArg (fun k => k ≫ P.toSpace) hws2)))
  have huniq : ∀ l : yoneda.obj V ⟶ (blowUpGlueingData Z P hcU hcR hcRR).relativeProj,
      l ≫ (blowUpGlueingData Z P hcU hcR hcRR).toBase = yoneda.map w ≫ P.toSpace →
        l = yoneda.map ws ≫ (blowUpGlueingData Z P hcU hcR hcRR).chart := by
    intro l hl
    obtain ⟨gt, hgtm⟩ : ∃ gt : V ⟶ (blowUpGlueingData Z P hcU hcR hcRR).projChart,
        yoneda.map gt = hpb.lift l (yoneda.map w) hl :=
      ⟨yoneda.preimage _, yoneda.map_preimage _⟩
    have hgtπ : gt ≫ (blowUpGlueingData Z P hcU hcR hcRR).projChartHom = w := by
      refine yoneda.map_injective ?_
      rw [Functor.map_comp, hgtm]
      exact hpb.lift_snd l (yoneda.map w) hl
    have hgtS : (BigFppfOver.toScheme B S hS).map gt ≫
        (reesChartSituation (centreIdeal Z)
          (isCartesianOnAffineCharts_centreIdeal Z) P).relativeProjToBase =
        (BigFppfOver.toScheme B S hS).map w :=
      (congrArg (fun k => (BigFppfOver.toScheme B S hS).map gt ≫ k) hπ).symm.trans
        ((((BigFppfOver.toScheme B S hS).map_comp gt
            (blowUpGlueingData Z P hcU hcR hcRR).projChartHom).symm).trans
          (congrArg (BigFppfOver.toScheme B S hS).map hgtπ))
    have hgteq : gt = ws :=
      BigFppfOver.map_toScheme_injective B S hS
        ((hgsu _ hgtS).trans hwsg.symm)
    refine Eq.trans (hpb.lift_fst l (yoneda.map w) hl).symm ?_
    exact congrArg (fun k => k ≫ (blowUpGlueingData Z P hcU hcR hcRR).chart)
      (hgtm.symm.trans (congrArg yoneda.map hgteq))
  exact ⟨yoneda.map ws ≫ (blowUpGlueingData Z P hcU hcR hcRR).chart, hmain, huniq⟩

omit [HasSheafify (BigFppfOver.topology B S hS) (Type u)] in
/-- **Every algebraic space over `X` has a surjective étale scheme chart adapted to a
presentation of `X`.**  For a morphism `y : Y ⟶ X` of algebraic spaces there are an object `V`
of the site, a morphism `w : V ⟶ U` into the presenting scheme of the presentation and a
surjective étale chart `a : h_V ⟶ Y` with `V ⟶ U ⟶ X` equal to `V ⟶ Y ⟶ X`.

Take any atlas `h_{U₀} ⟶ Y` of `Y` and base change the atlas of the presentation along
`h_{U₀} ⟶ Y ⟶ X`: the atlas of a presentation is relatively representable, so the base change
is again an object of the site, and it is surjective and étale over `U₀` because those
properties are tested after every representable base change. -/
theorem exists_adapted_chart {Y : AlgebraicSpaces B S hS} (y : Y ⟶ X) :
    ∃ (V : BigFppfOver B S hS) (w : V ⟶ P.U) (a : yoneda.obj V ⟶ Y.obj),
      (MorphismProperty.inverseImage (@AlgebraicGeometry.Surjective.{u} :
          MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)).presheaf a ∧
        (MorphismProperty.inverseImage (@AlgebraicGeometry.Etale.{u} :
            MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)).presheaf a ∧
          yoneda.map w ≫ P.toSpace = a ≫ y.hom := by
  obtain ⟨U₀, f₀, hf₀s, hf₀e⟩ := Y.property.exists_atlas
  have hrep : yoneda.relativelyRepresentable P.toSpace := P.etale.rep
  have hsqV : IsPullback (yoneda.map (hrep.fst' (f₀ ≫ y.hom)))
      (yoneda.map (hrep.snd (f₀ ≫ y.hom))) P.toSpace (f₀ ≫ y.hom) :=
    hrep.isPullback' (f₀ ≫ y.hom)
  have hδe : AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map
      (hrep.snd (f₀ ≫ y.hom))) :=
    P.etale.property (f₀ ≫ y.hom) _ _ hsqV
  have hδs : AlgebraicGeometry.Surjective ((BigFppfOver.toScheme B S hS).map
      (hrep.snd (f₀ ≫ y.hom))) :=
    P.surjective.property (f₀ ≫ y.hom) _ _ hsqV
  have hbcS : MorphismProperty.IsStableUnderBaseChange
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u}) := inferInstance
  have hmulS : MorphismProperty.IsStableUnderComposition
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsMultiplicative.toIsStableUnderComposition
  have hinvS : MorphismProperty.IsStableUnderComposition
      (MorphismProperty.inverseImage (@AlgebraicGeometry.Surjective.{u} :
        MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)) :=
    MorphismProperty.IsStableUnderComposition.inverseImage _
  have hscS : MorphismProperty.IsStableUnderComposition
      ((MorphismProperty.inverseImage (@AlgebraicGeometry.Surjective.{u} :
        MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)).presheaf) := inferInstance
  refine ⟨hrep.pullback (f₀ ≫ y.hom), hrep.fst' (f₀ ≫ y.hom),
    yoneda.map (hrep.snd (f₀ ≫ y.hom)) ≫ f₀, ?_, ?_, ?_⟩
  · exact MorphismProperty.comp_mem _ _ _
      (presheaf_yoneda_map_of_inverseImage B S hS hbcS _ hδs) hf₀s
  · exact etale_comp_of_scheme B S hS _ f₀ hδe hf₀e
  · exact hsqV.w.trans (Category.assoc _ _ _).symm

/-- **The finality half of Stacks 085U.**  Every algebraic space `Y` over `X` on which the
inverse image of the centre `Z` is an effective Cartier divisor admits exactly one morphism to
the blowup `X'` of `X` along `Z` commuting with the morphisms to `X`.

The atlas of `Y` is replaced by the adapted chart of
`AlgebraicGeometry.Space.exists_adapted_chart`, which is still a surjective étale scheme chart
of `Y` and now maps to the presenting scheme; on it
`AlgebraicGeometry.Space.existsUnique_hom_relativeProj_blowUpGlueingData` gives the lift and
its uniqueness, the same uniqueness identifies the two restrictions of the lift to the kernel
pair, and `AlgebraicGeometry.existsUnique_desc_of_surjective_etale_atlas` descends it to `Y`
and makes it unique there. -/
theorem existsUnique_hom_blowUpAlong' {Y : AlgebraicSpaces B S hS} (y : Y ⟶ X)
    (hy : IsPullbackDefined B S hS y Z) :
    ∃! l : Y.obj ⟶ (blowUpGlueingData Z P hcU hcR hcRR).relativeProj,
      l ≫ (blowUpGlueingData Z P hcU hcR hcRR).toBase = y.hom := by
  have hlift : ∀ {V : BigFppfOver B S hS} (w : V ⟶ P.U) (a : yoneda.obj V ⟶ Y.obj),
      IsEtale B S hS a → yoneda.map w ≫ P.toSpace = a ≫ y.hom →
      ∃! l : yoneda.obj V ⟶ (blowUpGlueingData Z P hcU hcR hcRR).relativeProj,
        l ≫ (blowUpGlueingData Z P hcU hcR hcRR).toBase = yoneda.map w ≫ P.toSpace :=
    fun w a ha hsq => existsUnique_hom_relativeProj_blowUpGlueingData Z P hcU hcR hcRR w
      (isEffectiveCartierDivisor_comap_reesChartIdeal_of_chart Z P y hy w a ha hsq)
  obtain ⟨V, w, a, has, hae, hsq⟩ := exists_adapted_chart P y
  obtain ⟨lV, hlV, hlVu⟩ := hlift w a (isEtale_of_presheaf_etale B S hS hae) hsq
  have hrepa : yoneda.relativelyRepresentable a :=
    Functor.relativelyRepresentable.of_diag Y.property.diagonal_representable a
  have hKpb : IsPullback (yoneda.map (hrepa.fst' a)) (yoneda.map (hrepa.snd a)) a a :=
    hrepa.isPullback' a
  have hk₁e : AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map (hrepa.fst' a)) :=
    hae.property a (yoneda.map (hrepa.snd a)) (hrepa.fst' a) hKpb.flip
  have hk₁a : (MorphismProperty.inverseImage (@AlgebraicGeometry.Etale.{u} :
      MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)).presheaf
      (yoneda.map (hrepa.fst' a) ≫ a) :=
    etale_comp_of_scheme B S hS _ a hk₁e hae
  have hsqK : yoneda.map (hrepa.fst' a ≫ w) ≫ P.toSpace =
      (yoneda.map (hrepa.fst' a) ≫ a) ≫ y.hom := by
    rw [Functor.map_comp, Category.assoc, Category.assoc, hsq]
  obtain ⟨lK, hlK, hlKu⟩ := hlift (hrepa.fst' a ≫ w) (yoneda.map (hrepa.fst' a) ≫ a)
    (isEtale_of_presheaf_etale B S hS hk₁a) hsqK
  have hk : yoneda.map (hrepa.fst' a) ≫ lV = yoneda.map (hrepa.snd a) ≫ lV := by
    have e₁ : (yoneda.map (hrepa.fst' a) ≫ lV) ≫
        (blowUpGlueingData Z P hcU hcR hcRR).toBase =
        yoneda.map (hrepa.fst' a ≫ w) ≫ P.toSpace := by
      rw [Category.assoc, hlV, Functor.map_comp, Category.assoc]
    have e₂ : (yoneda.map (hrepa.snd a) ≫ lV) ≫
        (blowUpGlueingData Z P hcU hcR hcRR).toBase =
        yoneda.map (hrepa.fst' a ≫ w) ≫ P.toSpace := by
      rw [Category.assoc, hlV, Functor.map_comp, Category.assoc, hsq, ← Category.assoc,
        ← Category.assoc, hKpb.w]
    rw [hlKu _ e₁, hlKu _ e₂]
  have hkb : yoneda.map (hrepa.fst' a) ≫ a ≫ y.hom =
      yoneda.map (hrepa.snd a) ≫ a ≫ y.hom := by
    rw [← Category.assoc, ← Category.assoc, hKpb.w]
  obtain ⟨c, hc, hcu⟩ := AlgebraicGeometry.existsUnique_desc_of_surjective_etale_atlas
    B S hS Y.property.isSheaf a hKpb has hae
    (blowUpGlueingData Z P hcU hcR hcRR).isAlgebraicSpace_relativeProj.isSheaf lV hk
  obtain ⟨b₀, hb₀, hbu⟩ := AlgebraicGeometry.existsUnique_desc_of_surjective_etale_atlas
    B S hS Y.property.isSheaf a hKpb has hae X.property.isSheaf (a ≫ y.hom) hkb
  have hmain : c ≫ (blowUpGlueingData Z P hcU hcR hcRR).toBase = y.hom := by
    have hca : a ≫ c ≫ (blowUpGlueingData Z P hcU hcR hcRR).toBase = a ≫ y.hom := by
      rw [← Category.assoc, hc, hlV, hsq]
    rw [hbu (c ≫ (blowUpGlueingData Z P hcU hcR hcRR).toBase) hca, hbu y.hom rfl]
  have huniq : ∀ l : Y.obj ⟶ (blowUpGlueingData Z P hcU hcR hcRR).relativeProj,
      l ≫ (blowUpGlueingData Z P hcU hcR hcRR).toBase = y.hom → l = c := by
    intro l hl
    have hal : (a ≫ l) ≫ (blowUpGlueingData Z P hcU hcR hcRR).toBase =
        yoneda.map w ≫ P.toSpace := by
      rw [Category.assoc, hl, hsq]
    exact hcu l (hlVu (a ≫ l) hal)
  exact ⟨c, hmain, huniq⟩

/-- **Stacks 085U.**  The blowing up `b : X' ⟶ X` of an algebraic space `X` along a closed
subspace `Z ⊆ X` is a final object of the category `𝒞` of algebraic spaces over `X` on which the
inverse image of `Z` is an effective Cartier divisor.

Membership in `𝒞` is
`AlgebraicGeometry.Space.isEffectiveCartierDivisor_exceptionalDivisor'` and finality is
`AlgebraicGeometry.Space.existsUnique_hom_blowUpAlong'`; the two are assembled by
`AlgebraicGeometry.Space.isBlowupAlong_of_existsUnique_lift`.  The hypotheses are exactly the
data the construction of Tag 085Q itself takes — an étale presentation `P` of `X`, the universe
choice `HasSheafify` for the quotient presheaf, and the three `B.Contains` side conditions on
the relative `Proj`s which `AlgebraicGeometry.Space.relativeProjChartOfSituation` already asks
for; nothing is assumed about `Z` beyond being a closed subspace, and in particular no
separatedness or density input is used.

This declaration alone carries Tag 085U.  Both halves are recovered from it by projection —
membership as `AlgebraicGeometry.Space.IsBlowupAlong.isPullbackDefined`, which is
`AlgebraicGeometry.Space.isEffectiveCartierDivisor_exceptionalDivisor'` up to unfolding
`AlgebraicGeometry.Space.exceptionalDivisor'`, and finality as
`AlgebraicGeometry.Space.IsBlowupAlong.existsUnique_lift`, which is
`AlgebraicGeometry.Space.existsUnique_lift_blowUpAlongHom'` — so neither of those two is
registered. -/
@[stacks 085U "the blowup of an algebraic space along a closed subspace is a final object of \
the category of those Y over X whose inverse image of the centre is an effective Cartier \
divisor; both halves, membership and finality"]
theorem isBlowupAlong_blowUpAlongHom' :
    IsBlowupAlong B S hS Z (blowUpAlongHom' Z P hcU hcR hcRR) := by
  refine isBlowupAlong_of_existsUnique_lift
    (isEffectiveCartierDivisor_exceptionalDivisor' Z P hcU hcR hcRR) fun Y y hy => ?_
  obtain ⟨l, hl, hlu⟩ := existsUnique_hom_blowUpAlong' Z P hcU hcR hcRR y hy
  have h1 : (ObjectProperty.homMk l : Y ⟶ blowUpAlong' Z P hcU hcR hcRR) ≫
      blowUpAlongHom' Z P hcU hcR hcRR = y :=
    ObjectProperty.hom_ext _ hl
  have h2 : ∀ m : Y ⟶ blowUpAlong' Z P hcU hcR hcRR,
      m ≫ blowUpAlongHom' Z P hcU hcR hcRR = y →
        m = (ObjectProperty.homMk l : Y ⟶ blowUpAlong' Z P hcU hcR hcRR) := by
    intro m hm
    exact ObjectProperty.hom_ext _
      (hlu m.hom (congrArg (fun k : Y ⟶ X => k.hom) hm))
  exact ⟨ObjectProperty.homMk l, h1, h2⟩

/-- **The finality half of Stacks 085U, as a lifting property of the blowup morphism.**  For
every morphism `y : Y ⟶ X` of algebraic spaces along which the inverse image of the centre `Z`
is an effective Cartier divisor there is exactly one morphism `Y ⟶ X'` whose composite with the
blowing up `b : X' ⟶ X` of `X` along `Z` is `y`.

This is `AlgebraicGeometry.Space.existsUnique_hom_blowUpAlong'` read in the category of
algebraic spaces over `S`, which is how the consumers of Tag 085U use finality.  Tag 085U is
registered on `AlgebraicGeometry.Space.isBlowupAlong_blowUpAlongHom'`, of which this statement
is the projection `AlgebraicGeometry.Space.IsBlowupAlong.existsUnique_lift`, so it carries no
tag of its own. -/
theorem existsUnique_lift_blowUpAlongHom' {Y : AlgebraicSpaces B S hS} (y : Y ⟶ X)
    (hy : IsPullbackDefined B S hS y Z) :
    ∃! l : Y ⟶ blowUpAlong' Z P hcU hcR hcRR, l ≫ blowUpAlongHom' Z P hcU hcR hcRR = y :=
  (isBlowupAlong_blowUpAlongHom' Z P hcU hcR hcRR).existsUnique_lift y hy

end AlgebraicGeometry.Space

end
