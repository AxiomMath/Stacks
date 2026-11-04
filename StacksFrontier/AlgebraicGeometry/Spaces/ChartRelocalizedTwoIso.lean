module

public import StacksFrontier.AlgebraicGeometry.Stacks.FlatFppfRinged
public import StacksFrontier.AlgebraicGeometry.Recovery04IH.LocalizedToposMorphismLocallyRinged
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartLocalizationInverseRingedToposTwoIso
public import StacksFrontier.CategoryTheory.Sites.Modules.Localization.RingedToposRelocalizedMorphism

/-!
# The relocalized morphism as a morphism of the small étale ringed topoi of two charts

Let `X` and `Y` be algebraic spaces over a scheme `S` contained in a big fppf site `B`, let
`ψ` be a morphism of their small étale ringed topoi, let `T` be an étale scheme chart of `X`,
`V` one of `Y`, and `s : h_T ⟶ ψ⁻¹h_V` a section. [Stacks Project, Tag 04J8] attaches to these a
morphism of the localizations at `h_T` and `h_V`; this file conjugates it into a morphism of the
small étale ringed topoi of the two charts and records the square that relates it to `ψ`.

## Main definitions

* `AlgebraicGeometry.Space.chartRelocalized`: the conjugated relocalized morphism.

## Main results

* `AlgebraicGeometry.Space.isLocallyRinged_chartRelocalized`: it is locally ringed when `ψ` is.
* `AlgebraicGeometry.Space.chartRelocalizedRestrictionTwoIso`: the chartwise comparison square, for
  an arbitrary morphism `ψ` of small étale ringed topoi and an arbitrary section `s`,
  pushed down to the ringed topos of `Y`.  It is *not*
  `AlgebraicGeometry.Space.chartRelocalizedTwoIso` of
  `StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleChartRelocalization.lean`, which is
  Stacks 04M5 proper: that one is stated over the localization, for the morphism of
  small étale ringed topoi of a morphism of spaces and the section corresponding to a
  chart morphism `g`.

## References

* [Stacks Project, Tag 04I6](https://stacks.math.columbia.edu/tag/04I6)
* [Stacks Project, Tag 04IE](https://stacks.math.columbia.edu/tag/04IE)
* [Stacks Project, Tag 04J8](https://stacks.math.columbia.edu/tag/04J8)
* [Stacks Project, Tag 04KL](https://stacks.math.columbia.edu/tag/04KL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] AlgebraicGeometry.hasSheafCompose_forget_ringCat
  AlgebraicGeometry.hasSheafCompose_forget_commRingCat
  Stacks.hasSheafCompose_forget₂_commRingCat

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X Y : AlgebraicSpaces B S hS)
    (ψ : RingedToposHom (smallEtaleRingedTopos B S hS X) (smallEtaleRingedTopos B S hS Y))
    (T : SmallEtale B S hS X.1) (V : SmallEtale B S hS Y.1)
    (s : smallEtaleChartSheaf B S hS X T ⟶
      ψ.toToposHom.inverseImage.obj (smallEtaleChartSheaf B S hS Y V))

/-- **The relocalized morphism of [Stacks Project, Tag 04J8], conjugated into a morphism of the
small étale ringed topoi of two charts.**

Given a morphism `ψ` of the small étale ringed topoi of `X` and `Y`, an étale scheme chart `T`
of `X`, an étale scheme chart `V` of `Y` and a section `s : h_T ⟶ ψ⁻¹h_V`, Stacks 04J8 gives a
morphism `(ψ_s, ψ_s^♯)` of the localizations at `h_T` and `h_V`.  Composing it on both sides
with the identifications of those localizations with the small étale ringed topoi of the charts
turns it into a morphism of the small étale ringed topoi of `T` and `V`. -/
noncomputable def chartRelocalized :
    RingedToposHom (smallEtaleRingedTopos B S hS (chartSpace B S hS X T))
      (smallEtaleRingedTopos B S hS (chartSpace B S hS Y V)) :=
  RingedToposHom.comp
    (X := smallEtaleRingedTopos B S hS (chartSpace B S hS X T))
    (Y := (smallEtaleRingedTopos B S hS Y).localizedRingedTopos (smallEtaleChartSheaf B S hS Y V))
    (Z := smallEtaleRingedTopos B S hS (chartSpace B S hS Y V))
    (chartLocalizationRingedToposInverse B S hS Y V)
    (RingedToposHom.comp
      (X := smallEtaleRingedTopos B S hS (chartSpace B S hS X T))
      (Y := (smallEtaleRingedTopos B S hS X).localizedRingedTopos (smallEtaleChartSheaf B S hS X T))
      (Z := (smallEtaleRingedTopos B S hS Y).localizedRingedTopos (smallEtaleChartSheaf B S hS Y V))
      (ψ.relocalized s)
      (chartLocalizationRingedToposHom B S hS X T))

/-- **The conjugated relocalized morphism is locally ringed when `ψ` is.**  The relocalization is
locally ringed by [Stacks Project, Tag 04J8] and both identifications are, so this is
`AlgebraicGeometry.RingedToposHom.isLocallyRinged_comp` twice. -/
theorem isLocallyRinged_chartRelocalized (hψ : ψ.IsLocallyRinged) :
    (chartRelocalized B S hS X Y ψ T V s).IsLocallyRinged := by
  unfold chartRelocalized
  apply RingedToposHom.isLocallyRinged_comp
  · exact isLocallyRinged_chartLocalizationRingedToposInverse B S hS Y V
  · apply RingedToposHom.isLocallyRinged_comp
    · exact ψ.isLocallyRinged_relocalized (smallEtaleChartSheaf B S hS Y V) s hψ
    · exact isLocallyRinged_chartLocalizationRingedToposHom B S hS X T

/-- **THE CHARTWISE COMPARISON: the conjugated relocalized morphism, followed down to the small
étale ringed topos of `Y`, is 2-isomorphic to `ψ` after the chart of `X`.**

This is the square that makes the chartwise data of [Stacks Project, Tag 04KL] compatible with
`ψ`, and it is assembled from three squares:

* `AlgebraicGeometry.Space.chartLocalizationInverseRestrictionTwoIso`, which replaces the chart
  of `Y` after the inverse identification by the localization morphism of
  [Stacks Project, Tag 04IE];
* `AlgebraicGeometry.RingedToposHom.relocalizedRingedSquare`, which is the commutativity of
  [Stacks Project, Tag 04J8]'s localization square as a square of ringed topoi;
* `AlgebraicGeometry.Space.chartLocalizationRestrictionTwoIso`, which replaces the localization
  morphism of `X` after the identification by the chart of `X`.

The remaining steps are reassociations. -/
noncomputable def chartRelocalizedRestrictionTwoIso :
    RingedToposHom.TwoIso
      (A := smallEtaleRingedTopos B S hS (chartSpace B S hS X T))
      (B := smallEtaleRingedTopos B S hS Y)
      (RingedToposHom.comp
        (X := smallEtaleRingedTopos B S hS (chartSpace B S hS X T))
        (Y := smallEtaleRingedTopos B S hS (chartSpace B S hS Y V))
        (Z := smallEtaleRingedTopos B S hS Y)
        (smallEtaleRestrictionRingedToposHom B S hS (chartToSpace B S hS Y V)
          (isEtale_chartToSpace B S hS Y V))
        (chartRelocalized B S hS X Y ψ T V s))
      (RingedToposHom.comp
        (X := smallEtaleRingedTopos B S hS (chartSpace B S hS X T))
        (Y := smallEtaleRingedTopos B S hS X)
        (Z := smallEtaleRingedTopos B S hS Y)
        ψ
        (smallEtaleRestrictionRingedToposHom B S hS (chartToSpace B S hS X T)
          (isEtale_chartToSpace B S hS X T))) :=
  (RingedToposHom.TwoIso.associator
      (RingedToposHom.comp
        (X := smallEtaleRingedTopos B S hS (chartSpace B S hS X T))
        (Y := (smallEtaleRingedTopos B S hS X).localizedRingedTopos
          (smallEtaleChartSheaf B S hS X T))
        (Z := (smallEtaleRingedTopos B S hS Y).localizedRingedTopos
          (smallEtaleChartSheaf B S hS Y V))
        (ψ.relocalized s)
        (chartLocalizationRingedToposHom B S hS X T))
      (chartLocalizationRingedToposInverse B S hS Y V)
      (smallEtaleRestrictionRingedToposHom B S hS (chartToSpace B S hS Y V)
        (isEtale_chartToSpace B S hS Y V))).trans
    ((RingedToposHom.TwoIso.whiskerLeft
        (RingedToposHom.comp
          (X := smallEtaleRingedTopos B S hS (chartSpace B S hS X T))
          (Y := (smallEtaleRingedTopos B S hS X).localizedRingedTopos
            (smallEtaleChartSheaf B S hS X T))
          (Z := (smallEtaleRingedTopos B S hS Y).localizedRingedTopos
            (smallEtaleChartSheaf B S hS Y V))
          (ψ.relocalized s)
          (chartLocalizationRingedToposHom B S hS X T))
        (chartLocalizationInverseRestrictionTwoIso B S hS Y V)).trans
      ((RingedToposHom.TwoIso.associator
          (chartLocalizationRingedToposHom B S hS X T)
          (ψ.relocalized s)
          (RingedTopos.localizationMorphism (smallEtaleRingedTopos B S hS Y)
            (smallEtaleChartSheaf B S hS Y V))).trans
        ((RingedToposHom.TwoIso.whiskerLeft
            (chartLocalizationRingedToposHom B S hS X T)
            (ψ.relocalizedRingedSquare s)).trans
          ((RingedToposHom.TwoIso.associator
              (chartLocalizationRingedToposHom B S hS X T)
              (RingedTopos.localizationMorphism (smallEtaleRingedTopos B S hS X)
                (smallEtaleChartSheaf B S hS X T))
              ψ).symm.trans
            (RingedToposHom.TwoIso.whiskerRight
              (chartLocalizationRestrictionTwoIso B S hS X T).symm ψ)))))

end AlgebraicGeometry.Space

end
