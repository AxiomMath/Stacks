module

public import StacksFrontier.AlgebraicGeometry.Blowup.ReesProjChartAway
public import StacksFrontier.AlgebraicGeometry.DivisorFlatPullback.Basic

/-!
# An ideal sheaf on the standard blowup chart, read on the degree-one `Proj` chart

`StacksFrontier/AlgebraicGeometry/Blowup/ReesProjChartAway.lean` identifies the standard affine
chart `Stacks.BlowUpChartCover.chart I U a` of the blowup with the degree-one standard open of
the chart of the relative `Proj` of the Rees algebra, through the ring isomorphism
`Stacks.Blowup.chartAwayEquiv`. This file transports an ideal sheaf along that identification:
the ideal of a quasi-coherent ideal sheaf of the blowup on the standard chart at `a`, read in
`Γ(X, U)[I/a]`, is the image under `chartAwayEquiv` of its ideal on the degree-one `Proj` chart.

That is the shape in which the chart criterion
`Stacks.BlowUpChartCover.comap_idealSheafDataOfHom_eq_exceptionalIdeal_pow_mul_iff` meets the
`Proj`-side computation of the ideal of a closed subscheme of a relative `Proj`.

## Main results

* `Stacks.Blowup.map_chartΓIso_ideal_eq_specMap`: the ideal on the standard blowup chart,
  read in `Γ(X, U)[I/a]`, is the ideal of the inverse image of the ideal sheaf along that
  chart.
* `Stacks.Blowup.map_chartΓIso_ideal_eq_map_chartAwayEquiv`: **the ideal on the standard
  blowup chart is the image of the ideal on the degree-one `Proj` chart.**

## Implementation notes

Both sides are obtained from the ideal of the ideal sheaf on one and the same affine open of the
blowup — the image of the chart — by `Stacks.IdealSheaf.ideal_comap_appLE`, and the two
restriction maps differ exactly by `chartAwayEquiv`, because
`Stacks.Blowup.specMap_chartAwayEquiv_awayChart` says the two charts differ by `Spec` of it.
The identification of `(Spec.map χ).appTop` with `χ` read through the two canonical
identifications of global sections of a spectrum is
`AlgebraicGeometry.Scheme.ΓSpecIso_naturality`.

The proofs here are written in term mode, through `congrArg` with an explicitly typed function
and through the private lemma `ideal_map_hom_comp`, rather than by `rw`. Rewriting with
`Stacks.BlowUpChartCover.chartΓIso_hom_eq` abstracts a motive over a morphism out of
`Γ(blowUp I, chartOpen I U a)`, and type-checking that motive exhausts the heartbeat budget in
either direction; supplying the function to `congrArg` instead means no motive is ever
abstracted. For the same reason the whole of `Spec Γ(X, U)[I/a]` is named as an affine open by
`isAffineOpen_top_chartRing` rather than written inline as `AlgebraicGeometry.isAffineOpen_top _`,
and the `le` argument of `Scheme.Hom.appLE` is spelled out as the same literal term that
`chartΓIso_hom_eq` uses.

## References

* [Stacks Project, Tag 0804](https://stacks.math.columbia.edu/tag/0804)

## Not done here

No Stacks tag is claimed: this is bookkeeping along an identification of charts, not a labelled
assertion of the source.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjBridge

universe u

namespace Stacks.Blowup

variable {X : Scheme.{u}} (I : X.IdealSheafData) (U : X.affineOpens) (a : I.ideal U)

/-- The whole of `Spec Γ(X, U)[I/a]` is an affine open of it. Named, rather than written as
`AlgebraicGeometry.isAffineOpen_top _`, because solving that underscore by unification against
the chart's source exhausts the heartbeat budget. -/
public theorem isAffineOpen_top_chartRing :
    IsAffineOpen (⊤ : (Spec (.of (Stacks.BlowUpChartCover.chartRing I U a))).Opens) :=
  AlgebraicGeometry.isAffineOpen_top _

/-- The whole of `Spec` of the degree-one `Proj` chart's coordinate ring is an affine open of
it. Named for the same reason as `Stacks.Blowup.isAffineOpen_top_chartRing`. -/
public theorem isAffineOpen_top_chartAway :
    IsAffineOpen (⊤ : (Spec (.of (HomogeneousLocalization.Away
      (((reesSheafGradedAlgebra I).toGradedAlgebra).grading (chartSite U))
      (reesSheafDegreeOne I U a)))).Opens) :=
  AlgebraicGeometry.isAffineOpen_top _

/-- Pushing an ideal forward along a composite of ring morphisms is pushing it forward along
each in turn. Stated once, for abstract objects of `CommRingCat`, so that it can be applied by
unification against the goal: rewriting with `CommRingCat.hom_comp` and `Ideal.map_map` inside
the proofs below would instead force a motive over the blowup's sections, which is unaffordable.
-/
private theorem ideal_map_hom_comp {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T)
    (J : Ideal R) :
    Ideal.map (f ≫ g).hom J = Ideal.map g.hom (Ideal.map f.hom J) := by
  rw [Ideal.map_map, CommRingCat.hom_comp]

/-- **The ideal of an ideal sheaf on the standard chart at `a`**, transported to
`Γ(X, U)[I/a]`, is the ideal of its inverse image along that chart, read on the whole of
`Spec Γ(X, U)[I/a]`. -/
public theorem map_chartΓIso_ideal_eq_specMap
    (Z : (AlgebraicGeometry.blowUp I).IdealSheafData) :
    Ideal.map (Stacks.BlowUpChartCover.chartΓIso I U a).hom.hom
        (Z.ideal (Stacks.BlowUpChartCover.chartOpen I U a)) =
      Ideal.map (Scheme.ΓSpecIso
          (.of (Stacks.BlowUpChartCover.chartRing I U a))).hom.hom
        ((Z.comap (Stacks.BlowUpChartCover.chart I U a)).ideal
          ⟨⊤, isAffineOpen_top_chartRing I U a⟩) := by
  have h1 : (Z.comap (Stacks.BlowUpChartCover.chart I U a)).ideal
        ⟨⊤, isAffineOpen_top_chartRing I U a⟩ =
      (Z.ideal (Stacks.BlowUpChartCover.chartOpen I U a)).map
        ((Stacks.BlowUpChartCover.chart I U a).appLE
          (Stacks.BlowUpChartCover.chartOpen I U a).1 ⊤
          (le_of_eq (Scheme.Hom.preimage_opensRange
            (Stacks.BlowUpChartCover.chart I U a)).symm)).hom :=
    Stacks.IdealSheaf.ideal_comap_appLE Z (Stacks.BlowUpChartCover.chart I U a)
      (Stacks.BlowUpChartCover.chartOpen I U a) ⟨⊤, isAffineOpen_top_chartRing I U a⟩
      (le_of_eq (Scheme.Hom.preimage_opensRange
        (Stacks.BlowUpChartCover.chart I U a)).symm)
  rw [h1]
  exact Eq.trans
    (congrArg (fun k : Γ(AlgebraicGeometry.blowUp I,
          (Stacks.BlowUpChartCover.chartOpen I U a).1) ⟶
        CommRingCat.of (Stacks.BlowUpChartCover.chartRing I U a) =>
      Ideal.map k.hom (Z.ideal (Stacks.BlowUpChartCover.chartOpen I U a)))
      (Stacks.BlowUpChartCover.chartΓIso_hom_eq I U a))
    (ideal_map_hom_comp _ _ _)

/-- The global sections of `Spec` of a ring isomorphism, read through the canonical
identifications of the global sections of the two spectra, is that isomorphism. -/
public theorem map_ΓSpecIso_map_specMap_appLE {R S : CommRingCat.{u}} (χ : R ⟶ S)
    (J : Ideal Γ(Spec R, ⊤)) :
    Ideal.map (Scheme.ΓSpecIso S).hom.hom
        (Ideal.map ((Spec.map χ).appLE ⊤ ⊤ le_rfl).hom J) =
      Ideal.map χ.hom (Ideal.map (Scheme.ΓSpecIso R).hom.hom J) := by
  rw [Ideal.map_map, Ideal.map_map, ← CommRingCat.hom_comp, ← CommRingCat.hom_comp]
  refine congrArg (fun k : Γ(Spec R, ⊤) ⟶ S => Ideal.map k.hom J) ?_
  rw [show (Spec.map χ).appLE ⊤ ⊤ le_rfl = (Spec.map χ).appTop from
      Scheme.Hom.appLE_eq_app (Spec.map χ),
    Scheme.ΓSpecIso_naturality]

/-- **An ideal sheaf of the blowup, read on the standard chart at `a` and on the degree-one
`Proj` chart.** Its ideal on the standard chart, transported to `Γ(X, U)[I/a]` by
`Stacks.BlowUpChartCover.chartΓIso`, is the image under `Stacks.Blowup.chartAwayEquiv` of its
ideal on the degree-one `Proj` chart. -/
public theorem map_chartΓIso_ideal_eq_map_chartAwayEquiv
    (Z : (AlgebraicGeometry.blowUp I).IdealSheafData) :
    Ideal.map (Stacks.BlowUpChartCover.chartΓIso I U a).hom.hom
        (Z.ideal (Stacks.BlowUpChartCover.chartOpen I U a)) =
      Ideal.map (chartAwayEquiv I U a).toRingHom
        (Ideal.map (Scheme.ΓSpecIso (.of (HomogeneousLocalization.Away
            (((reesSheafGradedAlgebra I).toGradedAlgebra).grading (chartSite U))
            (reesSheafDegreeOne I U a)))).hom.hom
          ((Z.comap (awayChart I U a)).ideal
            ⟨⊤, isAffineOpen_top_chartAway I U a⟩)) := by
  have hcomap : Z.comap (Stacks.BlowUpChartCover.chart I U a) =
      (Z.comap (awayChart I U a)).comap
        (Spec.map (CommRingCat.ofHom (chartAwayEquiv I U a).toRingHom)) := by
    rw [← Scheme.IdealSheafData.comap_comp, specMap_chartAwayEquiv_awayChart]
  have h2 : ((Z.comap (awayChart I U a)).comap
          (Spec.map (CommRingCat.ofHom (chartAwayEquiv I U a).toRingHom))).ideal
        ⟨⊤, isAffineOpen_top_chartRing I U a⟩ =
      ((Z.comap (awayChart I U a)).ideal ⟨⊤, isAffineOpen_top_chartAway I U a⟩).map
        ((Spec.map (CommRingCat.ofHom (chartAwayEquiv I U a).toRingHom)).appLE
          ⊤ ⊤ le_rfl).hom :=
    Stacks.IdealSheaf.ideal_comap_appLE (Z.comap (awayChart I U a))
      (Spec.map (CommRingCat.ofHom (chartAwayEquiv I U a).toRingHom))
      ⟨⊤, isAffineOpen_top_chartAway I U a⟩
      ⟨⊤, isAffineOpen_top_chartRing I U a⟩ le_rfl
  refine Eq.trans (map_chartΓIso_ideal_eq_specMap I U a Z) ?_
  refine Eq.trans (congrArg (Ideal.map (Scheme.ΓSpecIso
      (.of (Stacks.BlowUpChartCover.chartRing I U a))).hom.hom)
    ((congrArg (fun K : (Spec (.of (Stacks.BlowUpChartCover.chartRing I U a))).IdealSheafData =>
      K.ideal ⟨⊤, isAffineOpen_top_chartRing I U a⟩) hcomap).trans h2)) ?_
  exact map_ΓSpecIso_map_specMap_appLE _ _

end Stacks.Blowup

end
