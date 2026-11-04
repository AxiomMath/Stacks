module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Properties.Dimension
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.EtalePermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.LocalRingDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresented
public import StacksFrontier.Topology.Irreducible.GenericPoints

/-!
# Codimension-zero points of an algebraic space

A point of an algebraic space has codimension zero — its local ring has Krull dimension zero —
exactly when a point above it in some étale scheme chart is the generic point of an irreducible
component, and then this holds for every point above it in every étale scheme chart. For a
representable algebraic space it is the ordinary topological condition on the space of points.

## Main results

* `AlgebraicGeometry.Space.localRingDimension_eq_zero_iff_exists_etale_genericPoint`: the
  condition tested on one étale scheme chart.
* `AlgebraicGeometry.Space.localRingDimension_eq_zero_iff_all_etale_genericPoints`: the
  condition tested on every étale scheme chart.
* `AlgebraicGeometry.Space.localRingDimension_eq_zero_iff_genericPoint_of_iso` and
  `AlgebraicGeometry.Space.localRingDimension_eq_zero_iff_genericPoint_of_isRepresentable`: for
  a represented algebraic space the condition is membership in the generic points of the space
  of points.
* `AlgebraicGeometry.Space.codimensionZeroPoints_dense`: the points of codimension zero are
  dense.

## Implementation notes

The dimension of the local ring at a point is `AlgebraicGeometry.Space.localRingDimension` of
Tag 04NA, computed on an étale scheme chart; that the chart may be chosen freely is Tag 0BAM.
Translating the chart value to a topological condition is
`AlgebraicGeometry.ringKrullDim_stalk_eq_zero_iff_mem_genericPoints`, which holds for any
scheme.

Étaleness of a chart appears in two equivalent forms: `AlgebraicGeometry.Space.IsEtale` of
Tag 03FR, which is the form the statements below use, and the relatively representable étale
property, which is the form `AlgebraicGeometry.Space.HasChartLocalRingDimension` uses. The two
agree for a morphism out of a representable presheaf by
`AlgebraicGeometry.Space.isEtale_iff_presheaf_of_yoneda`.

The point set carries the topology of Tag 03BX, made a local instance here. In the
representable case the isomorphism of presheaves and the identification of the points of a
represented presheaf with the points of the representing scheme are both homeomorphisms, so
they match up generic points; the chart is the isomorphism itself, which is étale.

Density is inherited from the scheme: the generic points of the irreducible components of a
sober space are dense, the points of an étale scheme atlas are homeomorphic to the points of
the atlas, and the atlas is surjective and continuous on points, so the image of that dense
set is dense and consists of codimension-zero points.

## References

* [Stacks Project, Tag 0BAQ](https://stacks.math.columbia.edu/tag/0BAQ)
* [Stacks Project, Tag 0BAR](https://stacks.math.columbia.edu/tag/0BAR)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **Stacks 0BAQ, conditions (1) and (2).** A point of an algebraic space has a local ring of
dimension zero exactly when some étale scheme chart has, above it, a generic point of an
irreducible component. -/
@[stacks 0BAQ "condition (2)"]
theorem localRingDimension_eq_zero_iff_exists_etale_genericPoint
    (hF : IsAlgebraicSpace B S hS F) (x : points B S hS F) :
    localRingDimension B S hS x = 0 ↔
      ∃ (U : BigFppfOver B S hS) (a : yoneda.obj U ⟶ F)
        (u : (BigFppfOver.toScheme B S hS).obj U),
        IsEtale B S hS a ∧ ChartPoint B S hS U a u x ∧
          u ∈ genericPoints ((BigFppfOver.toScheme B S hS).obj U) := by
  rw [localRingDimension_eq_iff_hasChartLocalRingDimension B S hS hF x 0]
  exact exists_congr fun U => exists_congr fun a => exists_congr fun u =>
    and_congr (isEtale_iff_presheaf_of_yoneda B S hS a).symm
      (and_congr_right' (ringKrullDim_stalk_eq_zero_iff_mem_genericPoints _ _))

/-- **Stacks 0BAQ, conditions (1) and (3).** A point of an algebraic space has a local ring of
dimension zero exactly when every point above it in every étale scheme chart is the generic
point of an irreducible component. -/
@[stacks 0BAQ "condition (3)"]
theorem localRingDimension_eq_zero_iff_all_etale_genericPoints
    (hF : IsAlgebraicSpace B S hS F) (x : points B S hS F) :
    localRingDimension B S hS x = 0 ↔
      ∀ (U : BigFppfOver B S hS) (a : yoneda.obj U ⟶ F)
        (u : (BigFppfOver.toScheme B S hS).obj U),
        IsEtale B S hS a → ChartPoint B S hS U a u x →
          u ∈ genericPoints ((BigFppfOver.toScheme B S hS).obj U) := by
  rw [localRingDimension_eq_iff_hasChartLocalRingDimension B S hS hF x 0]
  constructor
  · rintro ⟨U, a, u, ha, hxu, hdim⟩ V b v hb hv
    exact (ringKrullDim_stalk_eq_zero_iff_mem_genericPoints _ _).mp
      ((hasChartLocalRingDimension_iff_allChartsLocalRingDimension B S hS hF x 0).mp
        ⟨U, a, u, ha, hxu, hdim⟩ V b v ((isEtale_iff_presheaf_of_yoneda B S hS b).mp hb) hv)
  · intro hall
    refine (hasChartLocalRingDimension_iff_allChartsLocalRingDimension B S hS hF x 0).mpr ?_
    intro U a u ha hxu
    exact (ringKrullDim_stalk_eq_zero_iff_mem_genericPoints _ _).mpr
      (hall U a u ((isEtale_iff_presheaf_of_yoneda B S hS a).mpr ha) hxu)

/-- **Stacks 0BAQ, the representable case.** For an algebraic space presented as a presheaf
isomorphic to a representable one, a point has a local ring of dimension zero exactly when it
is the generic point of an irreducible component of the space of points. -/
theorem localRingDimension_eq_zero_iff_genericPoint_of_iso (hF : IsAlgebraicSpace B S hS F)
    (U : BigFppfOver B S hS) (e : yoneda.obj U ≅ F) (x : points B S hS F) :
    localRingDimension B S hS x = 0 ↔ x ∈ genericPoints (points B S hS F) := by
  obtain ⟨p, rfl⟩ : ∃ p, pointsMap B S hS (yoneda.obj U) e.hom p = x :=
    ⟨(pointsHomeomorphOfIso B S hS e).symm x,
      (pointsHomeomorphOfIso B S hS e).apply_symm_apply x⟩
  have hchart := chartPoint_pointsToScheme B S hS U e.hom p
  have hgen : pointsMap B S hS (yoneda.obj U) e.hom p ∈ genericPoints (points B S hS F) ↔
      pointsToScheme B S hS U p ∈
        genericPoints ((BigFppfOver.toScheme B S hS).obj U) :=
    ((pointsHomeomorphOfIso B S hS e).mem_genericPoints_iff p).trans
      ((schemePointsHomeomorph B S hS U).mem_genericPoints_iff p).symm
  exact ⟨fun hdim => hgen.mpr
      ((localRingDimension_eq_zero_iff_all_etale_genericPoints B S hS hF _).mp hdim
        U e.hom _ (isEtale_of_isIso B S hS e.hom) hchart),
    fun hx => (localRingDimension_eq_zero_iff_exists_etale_genericPoint B S hS hF _).mpr
      ⟨U, e.hom, _, isEtale_of_isIso B S hS e.hom, hchart, hgen.mp hx⟩⟩

/-- **Stacks 0BAQ, the representable case.** For a representable algebraic space, a point has a
local ring of dimension zero exactly when it is the generic point of an irreducible component
of the space of points. -/
@[stacks 0BAQ "representable case", ega "I 2.4.3"]
theorem localRingDimension_eq_zero_iff_genericPoint_of_isRepresentable
    (hF : IsAlgebraicSpace B S hS F) (hrep : F.IsRepresentable) (x : points B S hS F) :
    localRingDimension B S hS x = 0 ↔ x ∈ genericPoints (points B S hS F) :=
  let : F.IsRepresentable := hrep
  localRingDimension_eq_zero_iff_genericPoint_of_iso B S hS hF F.reprX F.reprW x

/-- **Stacks 0BAR.** The points of codimension zero of an algebraic space are dense in its
space of points. -/
@[stacks 0BAR]
theorem codimensionZeroPoints_dense (hF : IsAlgebraicSpace B S hS F) :
    Dense {x : points B S hS F | localRingDimension B S hS x = 0} := by
  obtain ⟨U, f, hsurj, hetale⟩ := hF.exists_atlas
  have hf : IsEtale B S hS f := (isEtale_iff_presheaf_of_yoneda B S hS f).mpr hetale
  have hdense : Dense ((schemePointsHomeomorph B S hS U).symm ''
      genericPoints ((BigFppfOver.toScheme B S hS).obj U)) :=
    (schemePointsHomeomorph B S hS U).symm.surjective.denseRange.dense_image
      (schemePointsHomeomorph B S hS U).symm.continuous
      (dense_iff_closure_eq.mpr genericPoints.closure)
  refine ((surjective_iff_surjective_pointsMap B S hS F hF U f).mp hsurj).denseRange.dense_of_mapsTo
    (continuous_pointsMap B S hS f) hdense ?_
  rintro y ⟨z, hz, rfl⟩
  refine (localRingDimension_eq_zero_iff_exists_etale_genericPoint B S hS hF _).mpr
    ⟨U, f, _, hf, chartPoint_pointsToScheme B S hS U f _, ?_⟩
  have hzeq : pointsToScheme B S hS U ((schemePointsHomeomorph B S hS U).symm z) = z :=
    (schemePointsHomeomorph B S hS U).apply_symm_apply z
  rwa [hzeq]

end AlgebraicGeometry.Space

end
