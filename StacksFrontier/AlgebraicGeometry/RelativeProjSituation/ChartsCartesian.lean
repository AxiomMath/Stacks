module

public import StacksFrontier.AlgebraicGeometry.RelativeProjSituation.MapBaseChange
public import StacksFrontier.AlgebraicGeometry.RelativeProjSituation.SituationData
public import StacksFrontier.AlgebraicGeometry.RelativeProj.Charts.Descent

/-!
# Tag 01NO for a situation

`Stacks.RelativeProj.Situation.ChartsCartesian` is the content of Stacks tag 01NO for a relative
`Proj` situation: for affine opens `U ≤ V` of the base, the irrelevant ideal of `𝒜(U)` is covered
by that of `𝒜(V)`, and the comparison morphism `Proj 𝒜(U) ⟶ Proj 𝒜(V)` is an open immersion onto
the part of `Proj 𝒜(V)` lying over `U`. `Stacks.RelativeProj.Situation.chartsCartesian` proves it
for every situation.

`Stacks.RelativeProj.Situation.ChartsCartesian.of_isPullback` derives the same condition from
three statements about rings read through `Spec`:

* that the irrelevant ideal of `𝒜(U)` is covered by that of `𝒜(V)`;
* that `Spec (𝒜(U)₀)` is the base change of `Spec (𝒜(V)₀)` along `U ⟶ V`;
* that `Spec (Away 𝒜(U) (f a))` is the base change of `Spec (Away 𝒜(V) a)` along
  `Spec (𝒜(U)₀) ⟶ Spec (𝒜(V)₀)` for every homogeneous `a` of positive degree
  (`Stacks.Proj.IsBaseChangeOnCharts`).

## Main definitions

* `Stacks.RelativeProj.Situation.chartZero` is the structure morphism
  `Spec (𝒜(U)₀) ⟶ U` of a chart, so that the chart morphism
  `Stacks.RelativeProj.chartToOpen` factors as `Proj 𝒜(U) ⟶ Spec (𝒜(U)₀) ⟶ U`.

## Main results

* `Stacks.RelativeProj.Situation.chartsCartesian`: **Tag 01NO for every situation.**
* `Stacks.RelativeProj.Situation.data_chartsCartesian` and
  `Stacks.RelativeProj.Situation.relativeProj_data_chartsCartesian`: the resulting gluing datum
  and relative `Proj` are `Stacks.RelativeProj.Situation.chartData` and
  `Stacks.RelativeProj.Situation.relativeProj`.
* `Stacks.RelativeProj.Situation.chartZero_homOfLE`: the degree-zero chart morphisms are
  morphisms over the base.
* `Stacks.RelativeProj.Situation.isPullback_chartZero`: the degree-zero base-change square is
  cartesian as soon as the image of `Spec (𝒜(U)₀) ⟶ Spec (𝒜(V)₀)` is the part lying over `U`.
* `Stacks.RelativeProj.Situation.ChartsCartesian.of_isPullback`: **Tag 01NO for a situation whose
  graded algebra base changes on affine opens.**

## References

* [Stacks Project, Tag 01I9](https://stacks.math.columbia.edu/tag/01I9)
* [Stacks Project, Tag 01N2](https://stacks.math.columbia.edu/tag/01N2)
* [Stacks Project, Tag 01NO](https://stacks.math.columbia.edu/tag/01NO)
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite HomogeneousIdeal Graded

universe u

namespace Stacks.RelativeProj.Situation

variable (s : Situation.{u})

/-- **The degree-zero chart morphism** `Spec (𝒜(U)₀) ⟶ U`: `Spec` of the degree-zero
identification `Γ(S, U) ⟶ 𝒜(U)₀`, followed by the affine identification of `U` with
`Spec Γ(S, U)`. By `Stacks.RelativeProj.Situation.chartToOpen_eq` the chart morphism
`Stacks.RelativeProj.chartToOpen` of a situation is the structure morphism of `Proj` to
`Spec (𝒜(U)₀)` followed by this. -/
public def chartZero (U : s.base.affineOpens) :
    Spec (CommRingCat.of (s.chartGrading U 0)) ⟶ U.1.toScheme :=
  Spec.map (s.baseHom U.1) ≫ (isAffineOpen U).isoSpec.inv

/-- The chart morphism of a situation factors through `Spec` of the degree-zero part. -/
public theorem chartToOpen_eq (U : s.base.affineOpens) :
    chartToOpen (s.chartGrading) U (s.baseHom U.1) =
      Proj.toSpecZero (s.chartGrading U) ≫ s.chartZero U :=
  (Category.assoc _ _ _).symm

/-- **The degree-zero chart morphisms are morphisms over the base.** For affine opens `U ≤ V`,
`Spec` of the degree-zero component of the restriction map is a morphism over the inclusion
`U ⟶ V`. -/
public theorem chartZero_homOfLE {U V : s.base.affineOpens} (h : U ≤ V) :
    Spec.map (CommRingCat.ofHom (s.gradedRestrict h).gradedZeroRingHom) ≫ s.chartZero V =
      s.chartZero U ≫ s.base.homOfLE h := by
  rw [chartZero, chartZero, Category.assoc,
    isoSpec_inv_homOfLE (isAffineOpen U) (isAffineOpen V) h, ← Spec.map_comp_assoc,
    ← Spec.map_comp_assoc]
  exact congrArg (fun k ↦ Spec.map k ≫ (isAffineOpen V).isoSpec.inv)
    (s.baseHom_gradedRestrict h).symm

/-- The degree-zero base-change square of an inclusion of affine opens is cartesian as soon as
`Spec (𝒜(U)₀) ⟶ Spec (𝒜(V)₀)` is an open immersion whose image is the part lying over `U`. -/
public theorem isPullback_chartZero {U V : s.base.affineOpens} (h : U ≤ V)
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom (s.gradedRestrict h).gradedZeroRingHom))]
    (hr : (Spec.map (CommRingCat.ofHom (s.gradedRestrict h).gradedZeroRingHom)).opensRange =
      s.chartZero V ⁻¹ᵁ (s.base.homOfLE h).opensRange) :
    IsPullback (s.chartZero U)
      (Spec.map (CommRingCat.ofHom (s.gradedRestrict h).gradedZeroRingHom))
      (s.base.homOfLE h) (s.chartZero V) :=
  IsOpenImmersion.isPullback _ _ _ _ (s.chartZero_homOfLE h) hr.symm

/-- **Tag 01NO for a situation whose graded algebra base changes on affine opens.** The three
hypotheses are the degreewise surjectivity of the base-change comparison, that `Spec (𝒜(U)₀)` is
the base change of `Spec (𝒜(V)₀)` along `U ⟶ V`, and that the standard affine charts of
`Proj 𝒜(U)` are the base changes of those of `Proj 𝒜(V)`. -/
public theorem ChartsCartesian.of_isPullback
    (hirr : ∀ {U V : s.base.affineOpens} (h : U ≤ V),
      (s.chartGrading U)₊ ≤ ((s.chartGrading V)₊).map (s.gradedRestrict h))
    (hzero : ∀ {U V : s.base.affineOpens} (h : U ≤ V),
      IsPullback (s.chartZero U)
        (Spec.map (CommRingCat.ofHom (s.gradedRestrict h).gradedZeroRingHom))
        (s.base.homOfLE h) (s.chartZero V))
    (hcharts : ∀ {U V : s.base.affineOpens} (h : U ≤ V),
      Stacks.Proj.IsBaseChangeOnCharts (s.gradedRestrict h)) :
    s.ChartsCartesian where
  irrelevant_le h := hirr h
  isOpenImmersion_map h :=
    have : IsOpenImmersion
        (Spec.map (CommRingCat.ofHom (s.gradedRestrict h).gradedZeroRingHom)) :=
      MorphismProperty.of_isPullback (hzero h) inferInstance
    AlgebraicGeometry.Proj.isOpenImmersion_map (hirr h) (hcharts h)
  opensRange_map h := by
    have h₀ : IsOpenImmersion
        (Spec.map (CommRingCat.ofHom (s.gradedRestrict h).gradedZeroRingHom)) :=
      MorphismProperty.of_isPullback (hzero h) inferInstance
    have h₁ := AlgebraicGeometry.Proj.isOpenImmersion_map (hirr h) (hcharts h)
    rw [AlgebraicGeometry.Proj.opensRange_map (hirr h) (hcharts h),
      IsOpenImmersion.opensRange_eq_preimage_opensRange (hzero h), chartToOpen_eq,
      Scheme.Hom.comp_preimage]

/-! ### Tag 01NO for every situation, from the chart descent -/

/-- The graded restriction homomorphism `Stacks.RelativeProj.Situation.gradedSectionRestriction`
is `Stacks.RelativeProj.Situation.gradedRestrict`. -/
public theorem gradedSectionRestriction_eq_gradedRestrict {U V : s.base.Opens} (h : U ≤ V) :
    gradedSectionRestriction s U V h = s.gradedRestrict h := rfl

/-- The degree-zero identification `Stacks.RelativeProj.Situation.sectionRingZeroMap` is
`Stacks.RelativeProj.Situation.baseHom`. -/
public theorem sectionRingZeroMap_eq_baseHom (U : s.base.Opens) :
    sectionRingZeroMap s U = s.baseHom U := rfl

/-- The chart structure morphism `Stacks.RelativeProj.Situation.projInclusionToOpen` is the chart
structure morphism `Stacks.RelativeProj.chartToOpen` of the family of section rings. -/
public theorem projInclusionToOpen_eq_chartToOpen (U : s.base.affineOpens) :
    projInclusionToOpen s U.1 U.2 = chartToOpen (s.chartGrading) U (s.baseHom U.1) := rfl

/-- **Tag 01NO for every relative `Proj` situation.** For every inclusion `U ≤ V` of affine opens
of the base, the irrelevant ideal of `𝒜(U)` is covered by that of `𝒜(V)`, and the resulting
comparison morphism `Proj 𝒜(U) ⟶ Proj 𝒜(V)` is an open immersion onto the part of `Proj 𝒜(V)`
lying over `U`. -/
public theorem chartsCartesian : s.ChartsCartesian where
  irrelevant_le {U V} h := irrelevant_le_map_gradedSectionRestriction s U.1 V.1 h U.2 V.2
  isOpenImmersion_map {U V} h := isOpenImmersion_projInclusionMap s h U.2 V.2
  opensRange_map {U V} h := projInclusionToOpen_preimage_eq_opensRange s h U.2 V.2

/-- The gluing datum of a situation, built from
`Stacks.RelativeProj.Situation.chartsCartesian`, is `Stacks.RelativeProj.Situation.chartData`. -/
public theorem data_chartsCartesian : s.data s.chartsCartesian = chartData s := rfl

/-- The relative `Proj` of a situation, built from
`Stacks.RelativeProj.Situation.chartsCartesian`, is
`Stacks.RelativeProj.Situation.relativeProj`. -/
public theorem relativeProj_data_chartsCartesian :
    (s.data s.chartsCartesian).relativeProj = relativeProj s := rfl

end Stacks.RelativeProj.Situation

end
