module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartIdealSheafSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartSchemePoints
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealZeroLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.EtaleTopos

/-!
# The support of the chartwise sheaf of ideals is the preimage of the zero locus

Let `X` be an algebraic space over a scheme `S` contained in a big fppf site `B`, let
`ℐ ⊆ 𝒪_X` be a sheaf of ideals on its small étale site which is cartesian on affine charts, and
let `A` be an étale scheme chart of `X`.  Two closed subsets of the chart's scheme are in play:

* the support of the Zariski sheaf of ideals
  `AlgebraicGeometry.Space.idealSheafDataOfChart` which the chart inherits, over whose
  complement [Stacks, Tag 01YB] is stated;
* the preimage of the zero locus `|V(ℐ)|` of `AlgebraicGeometry.Space.idealZeroLocus`, over
  whose complement `U = X ∖ V(ℐ)` the canonical map of [Stacks, Tag 07UM] is stated.

`StacksFrontier/AlgebraicGeometry/Spaces/IdealComplementChartOpen.lean` proves that a Zariski open
off the support maps into the unit locus of `ℐ`.  **This file proves the converse**, so that the
two complements coincide: a point of the chart's scheme whose point of `X` lies in the unit locus
of `ℐ` lies off the support.

The mechanism is the one the library already uses for the sections of `ℐⁿ𝒢` over a chart of `U`
(`AlgebraicGeometry.Space.idealPowSubmodule_obj_pc_eq_top`): a sheaf of ideals has *local
membership*, so it is the whole structure sheaf over an étale chart as soon as the charts over
that chart on which it is the whole structure sheaf are jointly surjective, and that joint
surjectivity is exactly what membership in the unit locus provides at each point.  No descent of
the unit ideal along an étale covering is needed: the unit section is descended, not the ideal.

## Main definitions

* `AlgebraicGeometry.Space.chartUnitLocusPreimage` is the preimage in the chart's scheme of the
  unit locus of `ℐ`, taken along `AlgebraicGeometry.Space.chartSchemeToPoints`.

## Main results

* `AlgebraicGeometry.Space.isOpen_chartUnitLocusPreimage`: that preimage is open, the unit locus
  being open and the comparison of the points of a representable with the points of the
  representing scheme being a homeomorphism.
* `AlgebraicGeometry.Space.obj_eq_top_of_forall_mem_chartUnitLocusPreimage`: **an étale chart all
  of whose points lie over the unit locus carries the unit ideal of sections of `ℐ`.**  This is
  the local-membership step, and it is what replaces the missing descent.
* `AlgebraicGeometry.Space.obj_openChart_eq_top_of_subset`: consequently `ℐ` is the whole
  structure sheaf over the étale chart cut out by a Zariski open contained in that preimage.
* `AlgebraicGeometry.Space.mem_support_compl_of_mem_chartUnitLocusPreimage`: **the converse
  direction** — a point of the chart's scheme lying over the unit locus lies off the support of
  the chartwise sheaf of ideals.
* `AlgebraicGeometry.Space.support_compl_eq_chartUnitLocusPreimage`: **the two complements
  coincide**, as subsets of the chart's scheme.
* `AlgebraicGeometry.Space.exists_mem_support_compl_chartSchemeToPoints_eq`: on a chart which is
  surjective on points, every point of the unit locus is the point of a point of the chart's
  scheme lying off the support.  This is the form in which the charts cut out by the Zariski
  opens off the support are seen to cover `U = X ∖ V(ℐ)`.

## Implementation notes

**The passage between the two descriptions of a point of the chart is
`AlgebraicGeometry.Space.chartSchemeToPoints`**, the point of `X` carried by a point of the
chart's scheme, rather than `AlgebraicGeometry.Space.pointsMap` of a point of the represented
presheaf.  The two are interchanged by
`AlgebraicGeometry.Space.chartSchemeToPoints_eq_pointsMap_pointsEquivScheme_symm`, and the first
is the one that composes with a morphism of charts without a comparison of point sets, by
`AlgebraicGeometry.Space.chartSchemeToPoints_map`; that is what makes the statement about the
chart cut out by a Zariski open a statement about the open, with no point juggling.

**Only one affine neighbourhood is chosen, and it is chosen inside the preimage.**  Membership
off the support is tested on affine opens — `mem_support_compl_iff_exists_affineOpen` — so the
openness of the preimage is used exactly once, to put an affine open between the point and the
preimage; the affine basis of a scheme is `AlgebraicGeometry.Scheme.isBasis_affineOpens`.

No hypothesis beyond cartesianness of `ℐ` on affine charts is carried, and that only because
`AlgebraicGeometry.Space.idealSheafDataOfChart` needs it to exist; the statements before the
support appears carry none.

## References

* [Stacks Project, Tag 07UM](https://stacks.math.columbia.edu/tag/07UM)
* [Stacks Project, Tag 01YB](https://stacks.math.columbia.edu/tag/01YB)
* [Stacks Project, Tag 03BX](https://stacks.math.columbia.edu/tag/03BX)
* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS)
    (I : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule)

/-! ### The preimage of the unit locus in a chart's scheme -/

/-- The preimage in the scheme of an étale chart of the unit locus of `ℐ`: the points of the
chart's scheme whose point of `X` lies in the unit locus. -/
def chartUnitLocusPreimage (A : SmallEtale B S hS X.1) : Set (chartScheme A) :=
  chartSchemeToPoints B S hS X.1 A ⁻¹' idealUnitLocus B S hS X I

/-- Membership in the preimage of the unit locus is membership of the point of `X` which the
point of the chart's scheme determines. -/
theorem mem_chartUnitLocusPreimage_iff (A : SmallEtale B S hS X.1) (x : chartScheme A) :
    x ∈ chartUnitLocusPreimage B S hS X I A ↔
      chartSchemeToPoints B S hS X.1 A x ∈ idealUnitLocus B S hS X I := Iff.rfl

/-- A point of the scheme of an étale chart lies over the unit locus exactly when the
corresponding point of the represented presheaf maps into it. -/
theorem mem_chartUnitLocusPreimage_iff_pointsMap (A : SmallEtale B S hS X.1)
    (x : chartScheme A) :
    x ∈ chartUnitLocusPreimage B S hS X I A ↔
      pointsMap B S hS (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj A)) A.obj.hom
          ((pointsEquivScheme B S hS ((SmallEtale.toOver B S hS X.1).obj A)).symm x) ∈
        idealUnitLocus B S hS X I := by
  rw [chartUnitLocusPreimage, Set.mem_preimage,
    chartSchemeToPoints_eq_pointsMap_pointsEquivScheme_symm]

/-- The preimage of the unit locus is the image, under the comparison of the points of the
represented presheaf with the points of the chart's scheme, of the preimage of the unit locus
there. -/
theorem chartUnitLocusPreimage_eq_image (A : SmallEtale B S hS X.1) :
    chartUnitLocusPreimage B S hS X I A =
      pointsToScheme B S hS ((SmallEtale.toOver B S hS X.1).obj A) ''
        (pointsMap B S hS (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj A)) A.obj.hom ⁻¹'
          idealUnitLocus B S hS X I) := by
  ext x
  refine ⟨fun hx => ⟨_, (mem_chartUnitLocusPreimage_iff_pointsMap B S hS X I A x).1 hx, ?_⟩, ?_⟩
  · exact (pointsEquivScheme B S hS ((SmallEtale.toOver B S hS X.1).obj A)).apply_symm_apply x
  · rintro ⟨y, hy, rfl⟩
    refine (mem_chartUnitLocusPreimage_iff_pointsMap B S hS X I A _).2 ?_
    have hyx : (pointsEquivScheme B S hS ((SmallEtale.toOver B S hS X.1).obj A)).symm
        (pointsToScheme B S hS ((SmallEtale.toOver B S hS X.1).obj A) y) = y :=
      (pointsEquivScheme B S hS ((SmallEtale.toOver B S hS X.1).obj A)).symm_apply_apply y
    rw [hyx]
    exact hy

/-- **The preimage of the unit locus in the scheme of an étale chart is open.**  The unit locus
is open by `AlgebraicGeometry.Space.isOpen_idealUnitLocus`, the map on points induced by the
chart is continuous by clause (2) of Stacks 03BX, and the comparison of the points of a
represented presheaf with the points of the representing scheme identifies the two topologies. -/
theorem isOpen_chartUnitLocusPreimage (A : SmallEtale B S hS X.1) :
    IsOpen (chartUnitLocusPreimage B S hS X I A) := by
  have hopen : IsOpen (pointsMap B S hS
      (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj A)) A.obj.hom ⁻¹'
        idealUnitLocus B S hS X I) :=
    (continuous_pointsMap B S hS A.obj.hom).isOpen_preimage _ (isOpen_idealUnitLocus B S hS X I)
  rw [isOpen_pointTopology_yoneda_iff_isOpen_image] at hopen
  rw [chartUnitLocusPreimage_eq_image]
  exact hopen

/-! ### A chart lying over the unit locus carries the unit ideal -/


/-- **The charts on which `ℐ` is the whole structure sheaf cover an étale chart all of whose
points lie over the unit locus.**  A covering sieve of the small étale site is one whose arrows
are jointly surjective on points, and membership in the unit locus produces, at each point, a
chart over the given one on which `ℐ` is the whole structure sheaf together with a point above
it. -/
private theorem unitSieve_mem_topology_of_forall (P : SmallEtale B S hS X.1)
    (h : ∀ x : chartScheme P, x ∈ chartUnitLocusPreimage B S hS X I P) :
    unitSieve B S hS X I P ∈ SmallEtale.topology B S hS X.1 P := by
  rw [SmallEtale.mem_topology_iff_exists_mem_range]
  intro x
  obtain ⟨W, g, hW, w, hw⟩ := (mem_idealUnitLocus_iff_exists_over B S hS X I P
    ((pointsEquivScheme B S hS ((SmallEtale.toOver B S hS X.1).obj P)).symm x)).1
      ((mem_chartUnitLocusPreimage_iff_pointsMap B S hS X I P x).1 (h x))
  refine ⟨W, g, hW, pointsToScheme B S hS ((SmallEtale.toOver B S hS X.1).obj W) w, ?_⟩
  rw [← pointsToScheme_pointsMap_yoneda, hw]
  exact (pointsEquivScheme B S hS ((SmallEtale.toOver B S hS X.1).obj P)).apply_symm_apply x

/-- **An étale chart all of whose points lie over the unit locus of `ℐ` carries the unit ideal of
sections of `ℐ`.**

A sheaf of ideals has local membership, so the unit section lies in it over the chart as soon as
its restrictions along a covering sieve do; and the charts on which `ℐ` is the whole structure
sheaf form such a sieve.  This is the step which replaces a descent of the unit ideal along an
étale covering: what is descended is the unit *section*. -/
theorem obj_eq_top_of_forall_mem_chartUnitLocusPreimage (P : SmallEtale B S hS X.1)
    (h : ∀ x : chartScheme P, x ∈ chartUnitLocusPreimage B S hS X I P) :
    I.obj (op P) = ⊤ := by
  refine eq_top_iff.2 fun z _ => I.isSheaf z ?_
  refine (SmallEtale.topology B S hS X.1).superset_covering ?_
    (unitSieve_mem_topology_of_forall B S hS X I P h)
  intro Y g hg
  exact hg.ge Submodule.mem_top

/-! ### The chart cut out by a Zariski open inside the preimage -/

/-- The point of `X` carried by a point of the chart cut out by a Zariski open is the point
carried by its image in the ambient chart's scheme. -/
private theorem chartSchemeToPoints_ι_openChart (A : SmallEtale B S hS X.1)
    (V : (chartScheme A).Opens) (x : chartScheme (openChart B S hS X.1 A V)) :
    chartSchemeToPoints B S hS X.1 A (V.ι x) =
      chartSchemeToPoints B S hS X.1 (openChart B S hS X.1 A V) x := by
  have h := chartSchemeToPoints_map B S hS X.1 (openChartInclusion B S hS X.1 A V) x
  rw [toScheme_map_toOver_map_openChartInclusion] at h
  exact h

/-- Every point of the étale chart cut out by a Zariski open contained in the preimage of the
unit locus lies over the unit locus: pushing a point along the inclusion of the open does not
change the point of `X` it determines. -/
theorem forall_mem_chartUnitLocusPreimage_openChart (A : SmallEtale B S hS X.1)
    {V : (chartScheme A).Opens}
    (hV : (V : Set (chartScheme A)) ⊆ chartUnitLocusPreimage B S hS X I A)
    (x : chartScheme (openChart B S hS X.1 A V)) :
    x ∈ chartUnitLocusPreimage B S hS X I (openChart B S hS X.1 A V) := by
  have hmem := (mem_chartUnitLocusPreimage_iff B S hS X I A _).1
    (hV ((Scheme.Opens.range_ι V).le ⟨x, rfl⟩))
  rwa [mem_chartUnitLocusPreimage_iff, ← chartSchemeToPoints_ι_openChart]

/-- **`ℐ` is the whole structure sheaf over the étale chart cut out by a Zariski open of the
chart's scheme contained in the preimage of the unit locus.** -/
theorem obj_openChart_eq_top_of_subset (A : SmallEtale B S hS X.1)
    {V : (chartScheme A).Opens}
    (hV : (V : Set (chartScheme A)) ⊆ chartUnitLocusPreimage B S hS X I A) :
    I.obj (op (openChart B S hS X.1 A V)) = ⊤ :=
  obj_eq_top_of_forall_mem_chartUnitLocusPreimage B S hS X I _
    (forall_mem_chartUnitLocusPreimage_openChart B S hS X I A hV)

/-- **A point of the chart's scheme lying over the unit locus has an affine open neighbourhood
over whose étale chart `ℐ` is the whole structure sheaf.**  The preimage of the unit locus is
open and the affine opens are a basis. -/
theorem exists_affineOpen_obj_openChart_eq_top (A : SmallEtale B S hS X.1) (x : chartScheme A)
    (hx : x ∈ chartUnitLocusPreimage B S hS X I A) :
    ∃ V : (chartScheme A).affineOpens,
      x ∈ V.1 ∧ I.obj (op (openChart B S hS X.1 A V.1)) = ⊤ := by
  obtain ⟨V, hVmem, hxV, hVle⟩ :=
    Opens.isBasis_iff_nbhd.mp (chartScheme A).isBasis_affineOpens
      (show x ∈ (⟨chartUnitLocusPreimage B S hS X I A,
        isOpen_chartUnitLocusPreimage B S hS X I A⟩ : (chartScheme A).Opens) from hx)
  exact ⟨⟨V, hVmem⟩, hxV,
    obj_openChart_eq_top_of_subset B S hS X I A (fun _ hy => hVle hy)⟩

/-! ### The support and the preimage of the zero locus -/

variable (hI : IsCartesianOnAffineCharts I.toSheafOfModules)

/-- **The converse direction: a point of the chart's scheme lying over the unit locus of `ℐ` lies
off the support of the chartwise sheaf of ideals.**

This needs no descent of the unit ideal from an étale chart to a Zariski open: an affine open
neighbourhood inside the preimage of the unit locus cuts out an étale chart carrying the unit
ideal by `AlgebraicGeometry.Space.obj_openChart_eq_top_of_subset`, and an affine open carrying
the unit ideal misses the support. -/
theorem mem_support_compl_of_mem_chartUnitLocusPreimage (A : SmallEtale B S hS X.1)
    (x : chartScheme A) (hx : x ∈ chartUnitLocusPreimage B S hS X I A) :
    x ∈ ((idealSheafDataOfChart B S hS X I hI A).support.compl : (chartScheme A).Opens) :=
  (mem_support_compl_iff_exists_affineOpen B S hS X I hI A x).2
    (exists_affineOpen_obj_openChart_eq_top B S hS X I A x hx)

/-- A point of the chart's scheme lying off the support of the chartwise sheaf of ideals lies
over the unit locus of `ℐ`: it has an affine open neighbourhood whose étale chart carries the
unit ideal, and that chart witnesses membership in the unit locus. -/
theorem mem_chartUnitLocusPreimage_of_mem_support_compl (A : SmallEtale B S hS X.1)
    (x : chartScheme A)
    (hx : x ∈ ((idealSheafDataOfChart B S hS X I hI A).support.compl :
      (chartScheme A).Opens)) :
    x ∈ chartUnitLocusPreimage B S hS X I A := by
  obtain ⟨V, hxV, hV⟩ := (mem_support_compl_iff_exists_affineOpen B S hS X I hI A x).1 hx
  obtain ⟨x', hx'⟩ := (Scheme.Opens.range_ι V.1).ge hxV
  have h2 : chartSchemeToPoints B S hS X.1 A x =
      chartSchemeToPoints B S hS X.1 (openChart B S hS X.1 A V.1) x' := by
    subst hx'
    exact chartSchemeToPoints_ι_openChart B S hS X A V.1 x'
  have hunit : chartSchemeToPoints B S hS X.1 (openChart B S hS X.1 A V.1) x' ∈
      idealUnitLocus B S hS X I := by
    refine ⟨openChart B S hS X.1 A V.1, hV,
      (pointsEquivScheme B S hS
        ((SmallEtale.toOver B S hS X.1).obj (openChart B S hS X.1 A V.1))).symm x', ?_⟩
    exact (chartSchemeToPoints_eq_pointsMap_pointsEquivScheme_symm B S hS X.1
      (openChart B S hS X.1 A V.1) x').symm
  rw [mem_chartUnitLocusPreimage_iff, h2]
  exact hunit

/-- **The complement of the support of the chartwise sheaf of ideals is the preimage of the unit
locus of `ℐ`**, as subsets of the chart's scheme.  Equivalently, the support is the preimage of
the zero locus `|V(ℐ)|`: this is the identification under which [Stacks, Tag 01YB] on the chart's
scheme is a statement about the restriction to the chart of `U = X ∖ V(ℐ)`. -/
theorem support_compl_eq_chartUnitLocusPreimage (A : SmallEtale B S hS X.1) :
    (((idealSheafDataOfChart B S hS X I hI A).support.compl : (chartScheme A).Opens) :
        Set (chartScheme A)) =
      chartUnitLocusPreimage B S hS X I A :=
  Set.eq_of_subset_of_subset
    (fun x hx => mem_chartUnitLocusPreimage_of_mem_support_compl B S hS X I hI A x hx)
    (fun x hx => mem_support_compl_of_mem_chartUnitLocusPreimage B S hS X I hI A x hx)

/-- **On a chart which is surjective on points, every point of the unit locus of `ℐ` comes from a
point of the chart's scheme lying off the support.**

This is the form in which the étale charts of `U = X ∖ V(ℐ)` cut out by the Zariski opens of the
chart's scheme off the support are seen to cover `U`: the single chart cut out by the complement
of the support is surjective onto the points of `U`. -/
theorem exists_mem_support_compl_chartSchemeToPoints_eq (A : SmallEtale B S hS X.1)
    (hA : Function.Surjective (pointsMap B S hS
      (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj A)) A.obj.hom))
    {z : points B S hS X.1} (hz : z ∈ idealUnitLocus B S hS X I) :
    ∃ x : chartScheme A,
      x ∈ ((idealSheafDataOfChart B S hS X I hI A).support.compl : (chartScheme A).Opens) ∧
        chartSchemeToPoints B S hS X.1 A x = z := by
  obtain ⟨x, hx⟩ := surjective_chartSchemeToPoints B S hS X.1 A hA z
  refine ⟨x, mem_support_compl_of_mem_chartUnitLocusPreimage B S hS X I hI A x ?_, hx⟩
  exact Set.mem_preimage.2 (hx ▸ hz)

end AlgebraicGeometry.Space

end
