module

public import StacksFrontier.AlgebraicGeometry.Spaces.FpqcSourceLocalityTransfer
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.QuasiFiniteLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Descent.Germ.EtaleLocalCriterion
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.Fibre
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.Locus
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineEtaleEnlargementOfOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.CodimensionZeroPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.QuasiSeparatedVeryReasonable
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.RelativeConditionComparisons
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.RelativeDecency
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.VeryReasonableImpliesReasonable
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartAtPointOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.FieldFibreDiscreteDecent
public import StacksFrontier.AlgebraicGeometry.Spaces.FieldFibreEquivalences
public import StacksFrontier.AlgebraicGeometry.Spaces.FieldFibreFiniteDecent
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactPoints
public import StacksFrontier.AlgebraicGeometry.Descent.FiniteFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Limits.AffineFromFiniteSurjective
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.GenericallyFinite
public import StacksFrontier.AlgebraicGeometry.Properties.GenericPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.EtaleSourceDecency
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartLocality
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteAffineProper
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteFlatChartRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralFiniteTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompact
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SpecialCoverings
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsMono
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparationCancellation
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosedPermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiCoverAffineAtlas

/-!
# Quasi-finiteness of a morphism of algebraic spaces over a codimension-zero point

Let `f : X ⟶ Y` be a morphism of algebraic spaces over `S` which is locally of finite type and
let `y` be a point of codimension zero of `Y`, meaning that the local ring of `Y` at `y` has
dimension zero (Stacks 04NA). The fibre of `f` above `y` consists of points of codimension
zero exactly when `f` is quasi-finite at every point above `y`, and it is enough to test
quasi-finiteness at the codimension-zero points above `y`. This is **Stacks 0BBB**.

## Main results

* `AlgebraicGeometry.Space.isQuasiFiniteAt_iff_forall_quasiFiniteAt_chart`: quasi-finiteness
  of a morphism of algebraic spaces at a point is quasi-finiteness of the induced morphism of
  schemes in every pointed pair of étale charts at that point.
* `AlgebraicGeometry.Space.quasiFiniteAt_over_codimensionZeroPoint_tfae`: **Stacks 0BBB**.
* `AlgebraicGeometry.Space.finite_fieldFiber_iff_quasiFiniteAt_fiber`: **Stacks 0ACZ**,
  conditions (1) and (2): for a quasi-separated morphism of finite type, the field fibre over
  a field-valued point of the target has finitely many points exactly when the morphism is
  quasi-finite at every point above the point represented.
* `AlgebraicGeometry.Space.finite_fieldFiber_iff_finite_setFiber_of_decent`: **Stacks 0ACZ**,
  condition (4): for a decent target, the field fibre has finitely many points exactly when
  the set-theoretic fibre is finite.
* `AlgebraicGeometry.Space.exists_isOpenSubspace_isFinite_pullback_snd_of_finite_fieldFiber`:
  **Stacks 0ACZ**, conditions (1) and (2) imply condition (3): a finite field fibre over a
  point of codimension zero gives an open subspace of the target containing that point over
  which the morphism becomes finite.
* `AlgebraicGeometry.Space.isQuasiFiniteAt_of_isFinite_pullback_snd`: **Stacks 0ACZ**,
  condition (3) implies condition (2): finiteness over an open subspace of the target makes
  the morphism quasi-finite at every point above a point of that subspace.
* `AlgebraicGeometry.Space.finite_fieldFiber_iff_exists_isOpenSubspace_isFinite_pullback_snd`:
  **Stacks 0ACZ**, conditions (1) and (3), which closes the equivalence of the source's first
  three conditions over a point of codimension zero.

## Implementation notes

The three conditions of the source are compared by reduction to the corresponding statement
for schemes, Stacks 0BAH, in a pointed pair of étale charts. Two translations make that
reduction work. On the one hand a point of an algebraic space has local ring of dimension zero
exactly when its chart points are generic points of the chart (Stacks 0BAQ). On the other hand
quasi-finiteness of `f` at a point, Stacks 03XJ part (2), is quasi-finiteness of the morphism
of charts at the corresponding chart point: both are the germ-level property induced by being
locally of finite type and locally quasi-finite, the first through Stacks 04RF and the second
because the quasi-finite locus of a morphism of schemes is open (Stacks 01TI). The property is
étale local on the source and target by Stacks 04R3, which is what Stacks 04RF needs.

Condition (3) of Stacks 0ACZ is reached through the affine quotient of a finite étale
equivalence relation. An affine étale chart of the target at the codimension-zero point is
shrunk, using Stacks 02NW, until both the affine atlas of the base change and its kernel pair
are finite over it; the atlas is then finite over the base change by fppf descent, so the base
change is a scheme by Stacks 07S6 and an affine one by Stacks 01ZT, Chevalley's theorem on
finite surjections onto a scheme. The source's own route through Stacks 07VS — affineness of
the target of a finite surjection of algebraic spaces — is avoided, that statement not being
available.

The pointed pair of étale charts at a point is produced by lifting an atlas of the target
along the morphism (Stacks 02X1) and choosing a field-valued point of the source chart above
the point (Stacks 03H5). Replacing the field-valued representative of such a pair by the
canonical representative of another point of the same source chart gives a pair at the image
of that point, which is how a statement about all points of a fibre in the chart becomes a
statement about all points of the fibre of `f`.

## References

* [Stacks Project, Tag 0ACZ](https://stacks.math.columbia.edu/tag/0ACZ)
* [Stacks Project, Tag 0BBB](https://stacks.math.columbia.edu/tag/0BBB)
* [Stacks Project, Tag 01ZT](https://stacks.math.columbia.edu/tag/01ZT)
* [Stacks Project, Tag 01ZV](https://stacks.math.columbia.edu/tag/01ZV)
* [Stacks Project, Tag 02NW](https://stacks.math.columbia.edu/tag/02NW)
* [Stacks Project, Tag 07S6](https://stacks.math.columbia.edu/tag/07S6)
* [Stacks Project, Tag 0BAH](https://stacks.math.columbia.edu/tag/0BAH)
* [Stacks Project, Tag 0BAQ](https://stacks.math.columbia.edu/tag/0BAQ)
* [Stacks Project, Tag 01TI](https://stacks.math.columbia.edu/tag/01TI)
* [Stacks Project, Tag 04NA](https://stacks.math.columbia.edu/tag/04NA)
* [Stacks Project, Tag 04R3](https://stacks.math.columbia.edu/tag/04R3)
* [Stacks Project, Tag 04RF](https://stacks.math.columbia.edu/tag/04RF)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

set_option synthInstance.maxHeartbeats 400000 in
-- `inferInstance` for `HasPullbacks` on presheaves over the big fppf site is a deep instance search
/-- Pullbacks of presheaves on the big fppf site over `S` (instance search times out
without this shortcut). -/
local instance hasPullbacks_presheaf_genericallyFinite :
    CategoryTheory.Limits.HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

local instance (priority := high) hasPullback_presheaf_genericallyFinite
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    CategoryTheory.Limits.HasLimit (CategoryTheory.Limits.cospan f g) :=
  CategoryTheory.Limits.HasLimitsOfShape.has_limit _

set_option synthInstance.maxHeartbeats 400000 in
-- `HasLimitsOfShape (Discrete J)` on presheaves over the big fppf site is a deep instance search
/-- Discrete limits of presheaves on the big fppf site over `S` (instance search times out
without this shortcut). -/
local instance (priority := high) hasDiscreteLimits_presheaf_genericallyFinite (J : Type) :
    CategoryTheory.Limits.HasLimitsOfShape (CategoryTheory.Discrete J)
      ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

section Charts

variable {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- The scheme point selected by a pointed pair of étale charts is the one underlying its
field-valued representative. -/
lemma sourcePoint_eq_schemePoint {f : X ⟶ Y} {x : points B S hS X}
    (c : EtaleChartAtPoint B S hS f x) :
    c.sourcePoint B S hS = schemePoint B S hS c.U c.representative := by
  change (BigFppfOver.toScheme B S hS).map c.representative.value c.point = _
  rw [Subsingleton.elim c.point (IsLocalRing.closedPoint c.representative.carrier)]
  rfl

/-- The point of the source chart selected by a pointed pair of étale charts lies above the
specified point of the algebraic space. -/
private lemma chartPoint_sourcePoint {f : X ⟶ Y} {x : points B S hS X}
    (c : EtaleChartAtPoint B S hS f x) :
    ChartPoint B S hS c.U c.a (c.sourcePoint B S hS) x :=
  ⟨c.representative, (sourcePoint_eq_schemePoint B S hS c).symm, c.maps_to⟩

/-- The image in the target chart of the representative of a pointed pair of étale charts maps to
the image of the specified point in the target algebraic space. -/
private lemma pointsMap_map_representative {f : X ⟶ Y} {x : points B S hS X}
    (c : EtaleChartAtPoint B S hS f x) :
    pointsMap B S hS (yoneda.obj c.V) c.b
      ((FieldValuedPoint.map B S hS (yoneda.obj c.U) (yoneda.map c.h) c.representative).class B S hS
        (yoneda.obj c.V)) = pointsMap B S hS X f x := by
  change pointsMap B S hS (yoneda.obj c.V) c.b (pointsMap B S hS (yoneda.obj c.U)
    (yoneda.map c.h) (c.representative.class B S hS (yoneda.obj c.U))) = _
  rw [← pointsMap_comp_apply, c.comm, pointsMap_comp_apply, c.maps_to]

/-- The image in the target chart of the point selected by a pointed pair of étale charts lies
above the image of the specified point. -/
lemma chartPoint_map_sourcePoint {f : X ⟶ Y} {x : points B S hS X}
    (c : EtaleChartAtPoint B S hS f x) :
    ChartPoint B S hS c.V c.b
      ((BigFppfOver.toScheme B S hS).map c.h (c.sourcePoint B S hS))
      (pointsMap B S hS X f x) := by
  refine ⟨FieldValuedPoint.map B S hS (yoneda.obj c.U) (yoneda.map c.h) c.representative, ?_, ?_⟩
  · rw [schemePoint_map_yoneda, sourcePoint_eq_schemePoint]
  · exact pointsMap_map_representative B S hS c

/-- A point of the source chart of a pointed pair of étale charts whose image in the target
chart is the selected point maps to the same point of the target algebraic space. -/
private lemma pointsMap_chartPoint_eq {f : X ⟶ Y} {x : points B S hS X}
    (c : EtaleChartAtPoint B S hS f x)
    (z : (BigFppfOver.toScheme B S hS).obj c.U)
    (hz : (BigFppfOver.toScheme B S hS).map c.h z =
      (BigFppfOver.toScheme B S hS).map c.h (c.sourcePoint B S hS)) :
    pointsMap B S hS X f (pointsMap B S hS (yoneda.obj c.U) c.a
        ((schemePointRepresentative B S hS c.U z).class B S hS (yoneda.obj c.U))) =
      pointsMap B S hS X f x := by
  classical
  let q := schemePointRepresentative B S hS c.U z
  let qV := FieldValuedPoint.map B S hS (yoneda.obj c.U) (yoneda.map c.h) q
  let q₀ := FieldValuedPoint.map B S hS (yoneda.obj c.U) (yoneda.map c.h) c.representative
  have hsame : pointsToScheme B S hS c.V (qV.class B S hS (yoneda.obj c.V)) =
      pointsToScheme B S hS c.V (q₀.class B S hS (yoneda.obj c.V)) := by
    change schemePoint B S hS c.V qV = schemePoint B S hS c.V q₀
    rwa [schemePoint_map_yoneda, schemePoint_map_yoneda, ← sourcePoint_eq_schemePoint,
      schemePointRepresentative_point]
  have hclass : qV.class B S hS (yoneda.obj c.V) = q₀.class B S hS (yoneda.obj c.V) :=
    (pointsEquivScheme B S hS c.V).injective hsame
  calc pointsMap B S hS X f (pointsMap B S hS (yoneda.obj c.U) c.a
          (q.class B S hS (yoneda.obj c.U)))
      = pointsMap B S hS (yoneda.obj c.U) (c.a ≫ f) (q.class B S hS (yoneda.obj c.U)) :=
        (pointsMap_comp_apply B S hS c.a f _).symm
    _ = pointsMap B S hS (yoneda.obj c.U) (yoneda.map c.h ≫ c.b)
          (q.class B S hS (yoneda.obj c.U)) := by rw [c.comm]
    _ = pointsMap B S hS (yoneda.obj c.V) c.b (qV.class B S hS (yoneda.obj c.V)) :=
        pointsMap_comp_apply B S hS (yoneda.map c.h) c.b _
    _ = pointsMap B S hS X f x := by rw [hclass, pointsMap_map_representative]

/-- Every point of an algebraic space carries a pointed pair of étale charts for a morphism
out of it. -/
private lemma nonempty_etaleChartAtPoint (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) (x : points B S hS X) :
    Nonempty (EtaleChartAtPoint B S hS f x) := by
  obtain ⟨V, b, hbSurj, hbEtale⟩ := hY.exists_atlas
  obtain ⟨U, a, h, hcomm, haSurj, haEtale⟩ :=
    exists_surjective_etale_presentation_lift B S hS hX hY f V b hbSurj hbEtale
  obtain ⟨z, hz⟩ := (surjective_iff_surjective_pointsMap B S hS X hX U a).mp haSurj x
  obtain ⟨p, hp⟩ := Quot.exists_rep z
  exact ⟨{ U := U, V := V, a := a, b := b, h := h
           a_etale := haEtale, b_etale := hbEtale, comm := hcomm.symm
           representative := p, point := IsLocalRing.closedPoint p.carrier
           maps_to := by rw [← hp] at hz; exact hz }⟩

/-- The morphism of schemes in a pointed pair of étale charts of a morphism locally of finite type
is locally of finite type. -/
private lemma locallyOfFiniteType_map_chart {f : X ⟶ Y} (hf : IsLocallyOfFiniteType B S hS f)
    {x : points B S hS X} (c : EtaleChartAtPoint B S hS f x) :
    LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map c.h) :=
  hf c.U c.V c.a c.b c.h c.a_etale c.b_etale c.comm

/-- If `y` has local ring of dimension zero, the image in the target chart of the point selected
by a pointed pair of étale charts at a point above `y` is a generic point. -/
private lemma map_sourcePoint_mem_genericPoints (hY : IsAlgebraicSpace B S hS Y)
    {y : points B S hS Y} (hy : localRingDimension B S hS y = 0) {f : X ⟶ Y}
    {x : points B S hS X} (c : EtaleChartAtPoint B S hS f x) (hxy : pointsMap B S hS X f x = y) :
    (BigFppfOver.toScheme B S hS).map c.h (c.sourcePoint B S hS) ∈
      genericPoints ((BigFppfOver.toScheme B S hS).obj c.V) :=
  (localRingDimension_eq_zero_iff_all_etale_genericPoints B S hS hY y).mp hy
    c.V c.b _ ((isEtale_iff_presheaf_of_yoneda B S hS c.b).mpr c.b_etale)
    (hxy ▸ chartPoint_map_sourcePoint B S hS c)

/-- Quasi-finiteness of a morphism of algebraic spaces at a point, Stacks 03XJ part (2), is
quasi-finiteness of the induced morphism of schemes at the selected point in every pointed
pair of étale charts at that point. -/
theorem isQuasiFiniteAt_iff_forall_quasiFiniteAt_chart (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) (hf : IsLocallyOfFiniteType B S hS f)
    (x : points B S hS X) :
    IsQuasiFiniteAt B S hS f x ↔
      ∀ c : EtaleChartAtPoint B S hS f x,
        quasiFiniteAt ((BigFppfOver.toScheme B S hS).map c.h) (c.sourcePoint B S hS) := by
  have hP := locallyOfFiniteType_inf_locallyQuasiFinite_isEtaleLocalOnSourceAndTarget.{u}
  have hiff := holdsOnEveryEtaleChartAtPoint_iff_exists_open B S hS
    ((@LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u}) ⊓
      (@LocallyQuasiFinite.{u} : MorphismProperty Scheme.{u})) hP hX hY f x
  constructor
  · intro hx c
    have := locallyOfFiniteType_map_chart B S hS hf c
    obtain ⟨U, hU, hqf, hmem⟩ := hx.exists_mem_range_pointsMap
    exact (quasiFiniteAt_iff_hasRepresentativeWithProperty _ _).mpr
      (hiff.mpr ⟨U, hU, hmem, hqf⟩ c)
  · intro hall
    obtain ⟨U, hU, hmem, hqf⟩ := hiff.mp fun c ↦ by
      have := locallyOfFiniteType_map_chart B S hS hf c
      exact (quasiFiniteAt_iff_hasRepresentativeWithProperty _ _).mp (hall c)
    obtain ⟨x', hx'⟩ := hmem
    exact ⟨U, hU, x', hx', hqf⟩

end Charts

/-- **Stacks 0BBB.** Let `f : X ⟶ Y` be a morphism of algebraic spaces over `S` locally of
finite type and let `y` be a point of `Y` whose local ring has dimension zero. The following
are equivalent: every point of `X` above `y` has local ring of dimension zero; `f` is
quasi-finite at every point above `y`; and `f` is quasi-finite at every point above `y` whose
local ring has dimension zero. -/
@[stacks 0BBB]
theorem quasiFiniteAt_over_codimensionZeroPoint_tfae
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) (hf : IsLocallyOfFiniteType B S hS f)
    (y : points B S hS Y) (hy : localRingDimension B S hS y = 0) :
    List.TFAE [
      ∀ x : points B S hS X, pointsMap B S hS X f x = y →
        localRingDimension B S hS x = 0,
      ∀ x : points B S hS X, pointsMap B S hS X f x = y → IsQuasiFiniteAt B S hS f x,
      ∀ x : points B S hS X, localRingDimension B S hS x = 0 →
        pointsMap B S hS X f x = y → IsQuasiFiniteAt B S hS f x] := by
  classical
  let T := BigFppfOver.toScheme B S hS
  tfae_have 1 → 2 := by
    intro h1 x hxy
    refine (isQuasiFiniteAt_iff_forall_quasiFiniteAt_chart B S hS hX hY f hf x).mpr fun c ↦ ?_
    have hft := locallyOfFiniteType_map_chart B S hS hf c
    have hη := map_sourcePoint_mem_genericPoints B S hS hY hy c hxy
    have hfibre : T.map c.h ⁻¹' {T.map c.h (c.sourcePoint B S hS)} ⊆
        genericPoints (T.obj c.U) := by
      intro z hz
      have hdim : localRingDimension B S hS (pointsMap B S hS (yoneda.obj c.U) c.a
          ((schemePointRepresentative B S hS c.U z).class B S hS (yoneda.obj c.U))) = 0 :=
        h1 _ ((pointsMap_chartPoint_eq B S hS c z hz).trans hxy)
      exact (localRingDimension_eq_zero_iff_all_etale_genericPoints B S hS hX _).mp hdim
        c.U c.a z ((isEtale_iff_presheaf_of_yoneda B S hS c.a).mpr c.a_etale)
        ⟨schemePointRepresentative B S hS c.U z,
          schemePointRepresentative_point B S hS c.U z, rfl⟩
    have htfae := quasiFiniteAt_over_genericPoint_tfae (T.map c.h)
      (T.map c.h (c.sourcePoint B S hS)) hη
    have h2 : ∀ z : T.obj c.U, T.map c.h z = T.map c.h (c.sourcePoint B S hS) →
        quasiFiniteAt (T.map c.h) z := (htfae.out 1 2).mp hfibre
    exact h2 _ rfl
  tfae_have 2 → 3 := fun h2 x _ hxy ↦ h2 x hxy
  tfae_have 3 → 1 := by
    intro h3 x hxy
    obtain ⟨c⟩ := nonempty_etaleChartAtPoint B S hS hX hY f x
    have hft := locallyOfFiniteType_map_chart B S hS hf c
    have hη := map_sourcePoint_mem_genericPoints B S hS hY hy c hxy
    have hscheme : ∀ z : T.obj c.U, z ∈ genericPoints (T.obj c.U) →
        T.map c.h z = T.map c.h (c.sourcePoint B S hS) →
        quasiFiniteAt (T.map c.h) z := by
      intro z hzgen hz
      let q := schemePointRepresentative B S hS c.U z
      let xz := pointsMap B S hS (yoneda.obj c.U) c.a (q.class B S hS (yoneda.obj c.U))
      have hchart : ChartPoint B S hS c.U c.a z xz :=
        ⟨q, schemePointRepresentative_point B S hS c.U z, rfl⟩
      have hdimz : localRingDimension B S hS xz = 0 :=
        (localRingDimension_eq_zero_iff_exists_etale_genericPoint B S hS hX xz).2
          ⟨c.U, c.a, z, (isEtale_iff_presheaf_of_yoneda B S hS c.a).mpr c.a_etale,
            hchart, hzgen⟩
      have hxyz : pointsMap B S hS X f xz = y := (pointsMap_chartPoint_eq B S hS c z hz).trans hxy
      let cz : EtaleChartAtPoint B S hS f xz :=
        { U := c.U, V := c.V, a := c.a, b := c.b, h := c.h
          a_etale := c.a_etale, b_etale := c.b_etale, comm := c.comm
          representative := q, point := IsLocalRing.closedPoint q.carrier
          maps_to := rfl }
      have hsrc : cz.sourcePoint B S hS = z := by
        change T.map q.value (IsLocalRing.closedPoint q.carrier) = z
        exact schemePointRepresentative_point B S hS c.U z
      have := (isQuasiFiniteAt_iff_forall_quasiFiniteAt_chart B S hS hX hY f hf xz).mp
        (h3 xz hdimz hxyz) cz
      rwa [hsrc] at this
    have htfae := quasiFiniteAt_over_genericPoint_tfae (T.map c.h)
      (T.map c.h (c.sourcePoint B S hS)) hη
    have hfibre : T.map c.h ⁻¹' {T.map c.h (c.sourcePoint B S hS)} ⊆
        genericPoints (T.obj c.U) := (htfae.out 3 1).mp hscheme
    exact (localRingDimension_eq_zero_iff_exists_etale_genericPoint B S hS hX x).2
      ⟨c.U, c.a, c.sourcePoint B S hS,
        (isEtale_iff_presheaf_of_yoneda B S hS c.a).mpr c.a_etale,
        chartPoint_sourcePoint B S hS c, hfibre rfl⟩
  tfae_finish

/-! ### Generic finiteness: Stacks 0ACZ -/

section GenericFiniteness

open CategoryTheory.Limits

attribute [local instance] pointTopology

variable {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **Stacks 03M5.** A quasi-separated morphism of algebraic spaces over `S` is decent: it is
very reasonable, hence reasonable, hence decent. -/
private theorem decent_of_quasiSeparated (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) (hqs : IsQuasiSeparated B S hS f) :
    IsDecent B S hS f :=
  isDecent_of_isReasonable B S hS hX hY f
    (isReasonable_of_isVeryReasonable B S hS hX hY
      (isVeryReasonable_of_isQuasiSeparated B S hS hX hY hqs))

/-- Every point of the field fibre `X_k` of `f : X ⟶ Y` over a field-valued point `p` of `Y`
maps to the point of `|Y|` represented by `p`. -/
private theorem pullback_point_maps_to_fieldPoint (f : X ⟶ Y)
    (p : FieldValuedPoint B S hS Y)
    (z : points B S hS (pullback f (yonedaEquiv.symm p.value))) :
    pointsMap B S hS X f
      (pointsMap B S hS (pullback f (yonedaEquiv.symm p.value))
        (pullback.fst f (yonedaEquiv.symm p.value)) z) =
      p.class B S hS Y := by
  let g := yonedaEquiv.symm p.value
  change pointsMap B S hS X f
      (pointsMap B S hS (pullback f g) (pullback.fst f g) z) = p.class B S hS Y
  induction z using Quot.inductionOn with
  | h w =>
      let wb := FieldValuedPoint.map B S hS (pullback f g) (pullback.snd f g) w
      let wx := FieldValuedPoint.map B S hS (pullback f g) (pullback.fst f g) w
      have hbg : pointsMap B S hS (yoneda.obj (p.siteObject B S hS Y)) g
          (wb.class B S hS _) = p.class B S hS Y := by
        apply FieldValuedPoint.class_eq_class_of_hasCommonExtension
        refine ⟨FieldValuedPoint.map B S hS (yoneda.obj (p.siteObject B S hS Y)) g wb,
          FieldValuedPoint.dominates_refl B S hS Y _, ?_⟩
        refine ⟨wb.value, ?_⟩
        change Y.map wb.value.op p.value =
          (FieldValuedPoint.map B S hS (yoneda.obj (p.siteObject B S hS Y)) g wb).value
        rfl
      have hmaps : pointsMap B S hS X f (wx.class B S hS _) =
          pointsMap B S hS (yoneda.obj (p.siteObject B S hS Y)) g
            (wb.class B S hS _) := by
        calc
          _ = pointsMap B S hS (pullback f g)
                (pullback.fst f g ≫ f) (w.class B S hS _) :=
              (pointsMap_comp_apply B S hS (pullback.fst f g) f (w.class B S hS _)).symm
          _ = pointsMap B S hS (pullback f g)
                (pullback.snd f g ≫ g) (w.class B S hS _) :=
              congrArg (fun k ↦ pointsMap B S hS (pullback f g) k
                (w.class B S hS _)) (pullback.condition (f := f) (g := g))
          _ = pointsMap B S hS (yoneda.obj (p.siteObject B S hS Y)) g
                (wb.class B S hS _) :=
              pointsMap_comp_apply B S hS (pullback.snd f g) g (w.class B S hS _)
      rw [hbg] at hmaps
      rw [pointsMap_class, pointsMap_class]
      simpa [wx] using hmaps

/-- If the set-theoretic fibre of `f : X ⟶ Y` over a field-valued point `p` of `Y` is empty,
then the field fibre `X_k` has no points at all, so its point set is finite. -/
private theorem finite_fieldFibre_of_empty_setFibre (f : X ⟶ Y)
    (p : FieldValuedPoint B S hS Y) (hne : ¬ (setFibre B S hS f p).Nonempty) :
    (Set.univ : Set (points B S hS (pullback f (yonedaEquiv.symm p.value)))).Finite := by
  have hemp : (Set.univ : Set (points B S hS
      (pullback f (yonedaEquiv.symm p.value)))) = ∅ := by
    ext z
    simp only [Set.mem_univ, Set.mem_empty_iff_false, iff_false]
    intro _
    apply hne
    refine ⟨pointsMap B S hS (pullback f (yonedaEquiv.symm p.value))
      (pullback.fst f (yonedaEquiv.symm p.value)) z, ?_⟩
    simpa [setFibre] using pullback_point_maps_to_fieldPoint B S hS f p z
  rw [hemp]
  exact Set.finite_empty

/-- **Stacks 0ACK, condition (8) implies condition (4).** Let
`f : X ⟶ Y` be a morphism of algebraic spaces over `S` of finite type and let `p` be a
field-valued point of `Y`. If `f` is quasi-finite at
every point of `|X|` above the point represented by `p`, then the field fibre `X_k` has
finitely many points: its point space is discrete by Stacks 0ACK, conditions (5) and (8), and
compact because `X_k ⟶ Spec(k)` is a quasi-compact base change of `f`. -/
private theorem finite_fieldFiber_of_quasiFiniteAt (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) (p : FieldValuedPoint B S hS Y)
    (hft : IsFiniteType B S hS f)
    (hqf : ∀ x : points B S hS X, pointsMap B S hS X f x = p.class B S hS Y →
      IsQuasiFiniteAt B S hS f x) :
    (Set.univ : Set (points B S hS (pullback f (yonedaEquiv.symm p.value)))).Finite := by
  have hF : IsAlgebraicSpace B S hS (fieldFibre B S hS f p) :=
    isAlgebraicSpace_pullback B S hS f (yonedaEquiv.symm p.value) hX
      (isAlgebraicSpace_yoneda B S hS (p.siteObject B S hS Y)) hY
  have hdisc : DiscreteTopology (points B S hS (fieldFibre B S hS f p)) :=
    (isDiscreteFieldFibrePoints_iff_isQuasiFiniteAboveFieldValuedPoint B S hS hX hY hft.1
      p).2 fun x hx ↦ hqf x hx
  have hcompact : CompactSpace (points B S hS (fieldFibre B S hS f p)) :=
    (isQuasiCompactSpace_iff_compactSpace_points B S hS (fieldFibre B S hS f p) hF).1
      (IsQuasiCompactSpace.of_iso B S hS
        (hft.2 _ (isAlgebraicSpace_yoneda B S hS (p.siteObject B S hS Y))
          (isQuasiCompact_yoneda_of_compact B S hS _ (by
            change CompactSpace (Spec (.of p.carrier))
            infer_instance)) (yonedaEquiv.symm p.value))
        (pullbackSymmetry (yonedaEquiv.symm p.value) f))
  have : Finite (points B S hS (fieldFibre B S hS f p)) := finite_of_compact_of_discrete
  exact Set.toFinite Set.univ

/-- **Stacks 0ACK, condition (8) implies condition (4).** The previous lemma, phrased for a
point `y` of `|Y|` represented by `p`. -/
private theorem finite_fieldFiber_of_quasiFiniteAt_on_fiber (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) (p : FieldValuedPoint B S hS Y)
    (hft : IsFiniteType B S hS f) (y : points B S hS Y) (hp : p.class B S hS Y = y)
    (hqf : ∀ x : points B S hS X, pointsMap B S hS X f x = y →
      IsQuasiFiniteAt B S hS f x) :
    Set.Finite (Set.univ : Set (points B S hS
      (pullback f (yonedaEquiv.symm p.value)))) := by
  exact finite_fieldFiber_of_quasiFiniteAt B S hS hX hY f p hft
    fun x hx ↦ hqf x (by simpa [hp] using hx)

/-- **Stacks 0ACZ, conditions (1) and (2).** Let `f : X ⟶ Y` be a quasi-separated morphism of
algebraic spaces over `S` of finite type and let `p` be a field-valued representative of a
point `y` of `|Y|`. The field fibre `X_k` has finitely many points exactly when `f` is
quasi-finite at every point of `|X|` above `y`. -/
@[stacks 0ACZ "conditions (1) and (2)"]
theorem finite_fieldFiber_iff_quasiFiniteAt_fiber (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) (hqs : IsQuasiSeparated B S hS f)
    (hft : IsFiniteType B S hS f) (y : points B S hS Y)
    (p : FieldValuedPoint B S hS Y) (hp : p.class B S hS Y = y) :
    Set.Finite (Set.univ : Set (points B S hS
        (pullback f (yonedaEquiv.symm p.value)))) ↔
      ∀ x : points B S hS X, pointsMap B S hS X f x = y →
        IsQuasiFiniteAt B S hS f x := by
  refine ⟨fun hfinite x hxy ↦ ?_,
    finite_fieldFiber_of_quasiFiniteAt_on_fiber B S hS hX hY f p hft y hp⟩
  have hxset : x ∈ setFibre B S hS f p := by
    change pointsMap B S hS X f x = p.class B S hS Y
    rw [hxy, hp]
  exact (isDiscreteFieldFibrePoints_iff_isQuasiFiniteAboveFieldValuedPoint
    B S hS hX hY hft.1 p).1 (discreteTopology_points_fieldFibre_of_finite_of_isDecent
      B S hS hX hY f p hft.1 (decent_of_quasiSeparated B S hS hX hY f hqs) hfinite) x hxset

/-- **Stacks 0ACZ, condition (4) for a decent target.** Let `f : X ⟶ Y` be a quasi-separated
morphism of algebraic spaces over `S` of finite type with `Y` a decent algebraic space, and
let `p` be a field-valued representative of a point `y` of `|Y|`. The field fibre `X_k` has
finitely many points exactly when the set-theoretic fibre `f^{-1}({y}) ⊂ |X|` is finite. -/
@[stacks 0ACZ "condition (4) for a decent target"]
theorem finite_fieldFiber_iff_finite_setFiber_of_decent (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) (hqs : IsQuasiSeparated B S hS f)
    (hft : IsFiniteType B S hS f) (hdecent : IsDecentSpace B S hS Y)
    (y : points B S hS Y) (p : FieldValuedPoint B S hS Y)
    (hp : p.class B S hS Y = y) :
    Set.Finite (Set.univ : Set (points B S hS
        (pullback f (yonedaEquiv.symm p.value)))) ↔
      Set.Finite {x : points B S hS X | pointsMap B S hS X f x = y} := by
  refine ⟨fun hfield ↦ by
    simpa [setFibre, hp] using finite_setFibre_of_finite_fieldFibre B S hS hX hY f p hfield,
    fun hset ↦ ?_⟩
  exact finite_univ_points_fieldFibre_of_finite_setFibre_of_isDecent B S hS hX hY f p hft.1
    (isDecentSpace_of_isDecent B S hS hX hY f hdecent (decent_of_quasiSeparated B S hS hX hY f hqs))
    hdecent (by simpa [setFibre, hp] using hset)

end GenericFiniteness

/-! ### Finiteness over an open neighbourhood of a codimension-zero point: Stacks 0ACZ (3) -/

section OpenNeighborhood

open CategoryTheory.Limits

attribute [local simp] pullback.lift_fst pullback.lift_snd
  pullback.lift_fst_assoc pullback.lift_snd_assoc
attribute [local instance] MorphismProperty.relative_isStableUnderBaseChange


/-- An étale morphism of schemes is locally of finite type.

Kept as a named wrapper rather than inlined as `inferInstance` at the use sites: synthesising
`LocallyOfFiniteType g` from scratch exhausts `synthInstance.maxHeartbeats`, whereas applying
this lemma only has to synthesise `Etale g`, which the callers already have. -/
theorem locallyOfFiniteType_of_etale {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Etale f] : LocallyOfFiniteType f := inferInstance

attribute [local instance] BigFppfSite.hasPullbacks_schemes

attribute [local instance] AlgebraicGeometry.preservesPullbacks_bigFppfOverToScheme

/-- If a property `P` of morphisms of schemes is stable under base change, then so is the property
of morphisms in `BigFppfOver B S hS` whose image under `BigFppfOver.toScheme` satisfies `P`. -/
theorem inverseImage_stableUnderBaseChange
    (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange] :
    (P.inverseImage (BigFppfOver.toScheme B S hS)).IsStableUnderBaseChange := by
  constructor
  intro X Y Z W f g h k hpb hk
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := P) (hpb.map (BigFppfOver.toScheme B S hS)) hk

attribute [local instance] inverseImage_stableUnderBaseChange

private theorem finite_preimage_singleton_of_quasiFiniteAt
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] [QuasiCompact f] (y : Y)
    (hqf : ∀ x : X, f x = y → f.QuasiFiniteAt x) :
    (f ⁻¹' ({y} : Set Y)).Finite := by
  refine (f.isCompact_preimage_singleton y).finite ?_
  rw [isDiscrete_iff_discreteTopology, discreteTopology_iff_isOpen_singleton]
  rintro ⟨x, rfl⟩
  rw [← (f.fiberHomeo (f x)).symm.isOpen_image, Set.image_singleton]
  exact Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber.mp (hqf x rfl)

private theorem exists_affine_open_finite_of_quasiFiniteAt_fiber
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] [QuasiCompact f]
    [QuasiSeparated f] (η : Y) (hη : η ∈ genericPoints Y)
    (hqf : ∀ x : X, f x = η → f.QuasiFiniteAt x) :
    ∃ V : Y.affineOpens, η ∈ V.1 ∧ _root_.AlgebraicGeometry.IsFinite (f ∣_ V.1) :=
  (AlgebraicGeometry.finite_preimage_singleton_iff_exists_affine_open_isFinite_restrict
    f η hη).mp (finite_preimage_singleton_of_quasiFiniteAt f η hqf)



/-- An algebraic space with a surjective étale chart whose kernel-pair projection is a finite
morphism of schemes has a finite chart. Made public because
`StacksFrontier.AlgebraicGeometry.Spaces.FiniteOverDenseOpenSubspace` had its own copy of this
statement and proof; that copy is deleted. -/
theorem finite_of_finite_etale_kernelPair
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X)
    (U : BigFppfOver B S hS) (g : yoneda.obj U ⟶ X)
    (hgsurj : (MorphismProperty.inverseImage (@Surjective.{u})
      (BigFppfOver.toScheme B S hS)).presheaf g)
    (hget : (MorphismProperty.inverseImage (@Etale.{u})
      (BigFppfOver.toScheme B S hS)).presheaf g)
    (hfin : _root_.AlgebraicGeometry.IsFinite ((BigFppfOver.toScheme B S hS).map
      (hget.1.snd g))) :
    IsFinite B S hS g := by
  let : MorphismProperty.IsLocalAtTarget
      (@_root_.AlgebraicGeometry.IsFinite.{u}) Scheme.fppfPrecoverage :=
    AlgebraicGeometry.isFinite_isLocalAtTarget_fpqc.of_le
      Scheme.fppfPrecoverage_le_fpqcPrecoverage
  have hrel := (presheaf_inverseImage_iff_atlas_snd
    B S hS (@_root_.AlgebraicGeometry.IsFinite.{u}) g hget.1 U g hgsurj hget).mpr hfin
  exact (isFinite_iff_representable B S hS g
    (isAlgebraicSpace_yoneda B S hS U) hX).mpr ⟨hget.1, hrel⟩

private theorem finite_of_finite_surjective_affine_cover
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X)
    (U V : BigFppfOver B S hS)
    (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U))
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V))
    (g : yoneda.obj U ⟶ X) (f : X ⟶ yoneda.obj V)
    (hgfin : IsFinite B S hS g)
    (hgsurj : (MorphismProperty.inverseImage (@Surjective.{u})
      (BigFppfOver.toScheme B S hS)).presheaf g)
    (hgetale : (MorphismProperty.inverseImage (@Etale.{u})
      (BigFppfOver.toScheme B S hS)).presheaf g)
    (hft : IsLocallyOfFiniteType B S hS f)
    (hcomp : _root_.AlgebraicGeometry.IsFinite ((BigFppfOver.toScheme B S hS).map
      (yoneda.preimage (g ≫ f)))) :
    IsFinite B S hS f := by
  let := inverseImage_stableUnderBaseChange B S hS (@Surjective.{u})
  let := inverseImage_stableUnderBaseChange B S hS (@_root_.AlgebraicGeometry.IsFinite.{u})
  let T := BigFppfOver.toScheme B S hS
  let : IsAffine (T.obj U) := hU
  have hgrel := (isFinite_iff_representable B S hS g
    (isAlgebraicSpace_yoneda B S hS U) hX).mp hgfin
  have hget : (MorphismProperty.inverseImage (@Etale.{u}) T).presheaf g := hgetale
  have hflf : (MorphismProperty.inverseImage
      (@Stacks.Morphisms.IsFiniteLocallyFree.{u} : MorphismProperty Scheme.{u}) T).presheaf g := by
    refine ⟨hget.1, fun a b ξ fst snd hpb ↦ ?_⟩
    have h1 : _root_.AlgebraicGeometry.IsFinite (T.map snd) := hgrel.2.2 ξ fst snd hpb
    have h2 : Etale (T.map snd) := hget.2 ξ fst snd hpb
    exact (Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation
      (T.map snd)).mpr ⟨h1, inferInstance, inferInstance⟩
  have hrepX : X.IsRepresentable :=
    isRepresentable_of_surjectiveEtale_finiteLocallyFree_of_isImmersion B S hS
      (Z := U) (𝟙 ((BigFppfOver.toScheme B S hS).obj U)) hX g hflf hgsurj hget
  obtain ⟨W, ⟨e⟩⟩ : ∃ W : BigFppfOver B S hS, Nonempty (X ≅ yoneda.obj W) :=
    ⟨X.reprX, ⟨X.reprW.symm⟩⟩
  let k : U ⟶ W := yoneda.preimage (g ≫ e.hom)
  let l : W ⟶ V := yoneda.preimage (e.inv ≫ f)
  have hk : yoneda.map k = g ≫ e.hom := yoneda.map_preimage _
  have hl : yoneda.map l = e.inv ≫ f := yoneda.map_preimage _
  have hkl : k ≫ l = yoneda.preimage (g ≫ f) := by
    apply yoneda.map_injective
    simp [Functor.map_comp, hk, hl]
  have hksurj : Surjective (T.map k) := by
    apply (MorphismProperty.relative_map_iff (F := yoneda)
      (P := MorphismProperty.inverseImage (@Surjective.{u}) T)).mp
    rw [hk]
    exact MorphismProperty.RespectsIso.postcomp _ e.hom g hgsurj
  have hkfin : _root_.AlgebraicGeometry.IsFinite (T.map k) := by
    apply (MorphismProperty.relative_map_iff (F := yoneda)
      (P := MorphismProperty.inverseImage
        (@_root_.AlgebraicGeometry.IsFinite.{u}) T)).mp
    rw [hk]
    exact MorphismProperty.RespectsIso.postcomp _ e.hom g hgrel.2
  have : _root_.AlgebraicGeometry.IsFinite (T.map k) := hkfin
  have : Surjective (T.map k) := hksurj
  have hW : IsAffine (T.obj W) :=
    Stacks.AffineFromFiniteSurjective.isAffine_of_finite_surjective (T.map k)
  have hle : (MorphismProperty.inverseImage (@Etale.{u}) T).presheaf e.inv := by
    simpa using MorphismProperty.RespectsIso.postcomp _ e.inv (𝟙 _)
      (presheaf_etale_id B S hS W)
  have hlft : LocallyOfFiniteType (T.map l) := by
    apply hft W V e.inv (𝟙 _) l hle (presheaf_etale_id B S hS V)
    simpa using hl
  have hklfin : _root_.AlgebraicGeometry.IsFinite (T.map k ≫ T.map l) := by
    rw [← Functor.map_comp, hkl]
    exact hcomp
  let : IsAffine (T.obj W) := hW
  let : IsAffine (T.obj V) := hV
  let : Surjective (T.map k) := hksurj
  let : LocallyOfFiniteType (T.map l) := hlft
  let : _root_.AlgebraicGeometry.IsFinite (T.map k ≫ T.map l) := hklfin
  let : _root_.AlgebraicGeometry.UniversallyClosed (T.map l) :=
    _root_.AlgebraicGeometry.UniversallyClosed.of_comp_surjective (T.map k) (T.map l)
  let : _root_.AlgebraicGeometry.IsProper (T.map l) := ⟨⟩
  have hlfin : _root_.AlgebraicGeometry.IsFinite (T.map l) :=
    _root_.AlgebraicGeometry.IsFinite.iff_isProper_and_isAffineHom.mpr
      ⟨inferInstance, inferInstance⟩
  have hlrel : (MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.IsFinite.{u}) T).presheaf
      (yoneda.map l) := (MorphismProperty.relative_map_iff (F := yoneda)).mpr hlfin
  have hfrel : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsFinite.{u}) T).presheaf f := by
    have := MorphismProperty.RespectsIso.precomp _ e.hom (yoneda.map l) hlrel
    simpa [hl] using this
  exact (isFinite_iff_representable B S hS f hX
    (isAlgebraicSpace_yoneda B S hS V)).mpr ⟨hfrel.1, hfrel⟩

private theorem etale_presheaf_comp
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : (MorphismProperty.inverseImage (@Etale.{u})
      (BigFppfOver.toScheme B S hS)).presheaf f)
    (hg : (MorphismProperty.inverseImage (@Etale.{u})
      (BigFppfOver.toScheme B S hS)).presheaf g) :
    (MorphismProperty.inverseImage (@Etale.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (f ≫ g) := by
  let T := BigFppfOver.toScheme B S hS
  let P := MorphismProperty.inverseImage (@Etale.{u}) T
  let : MorphismProperty.IsStableUnderComposition (@Etale.{u}) := ⟨by
    intro X Y Z f g hf hg
    let := hf
    let := hg
    exact inferInstance⟩
  let : P.IsStableUnderComposition := MorphismProperty.IsStableUnderComposition.inverseImage T
  let : P.presheaf.IsStableUnderComposition := MorphismProperty.relative_isStableUnderComposition P
  exact MorphismProperty.comp_mem _ _ _ hf hg

private theorem exists_affine_etale_generic_chart
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY : IsAlgebraicSpace B S hS Y)
    (y : points B S hS Y)
    (hy : localRingDimension B S hS y = 0) :
    ∃ (U : BigFppfOver B S hS) (g : yoneda.obj U ⟶ Y)
      (v : (BigFppfOver.toScheme B S hS).obj U),
      IsAffine ((BigFppfOver.toScheme B S hS).obj U) ∧
      (MorphismProperty.inverseImage (@Etale.{u})
        (BigFppfOver.toScheme B S hS)).presheaf g ∧
      ChartPoint B S hS U g v y ∧
      v ∈ genericPoints ((BigFppfOver.toScheme B S hS).obj U) := by
  obtain ⟨I, W, hW, hatlas⟩ :=
    exists_zariski_cover_affine_etale_atlas B S hS Y hY
  have hcover := (isZariskiCover_iff_iUnion_points
    B S hS Y hY I W hW.1).mp hW
  obtain ⟨i, x, hx⟩ := Set.mem_iUnion.mp (hcover.symm ▸ Set.mem_univ y)
  obtain ⟨U, a, _, hU, hasurj, haet, _, _⟩ := hatlas i
  obtain ⟨z, hz⟩ := (presheafSurjective_iff_isSurjective_yoneda
    B S hS (W i).toFunctor (hW.1 i).1 U a).mp hasurj x
  obtain ⟨p, rfl⟩ := Quot.exists_rep z
  let g := a ≫ (W i).ι
  let v := schemePoint B S hS U p
  let T := BigFppfOver.toScheme B S hS
  let P := MorphismProperty.inverseImage (@Etale.{u}) T
  have hi : P.presheaf (W i).ι := by
    apply MorphismProperty.relative_monotone (P :=
      MorphismProperty.inverseImage (@AlgebraicGeometry.IsOpenImmersion.{u}) T)
      (P' := P) _ _ (hW.1 i).2
    intro A C m hm
    let : AlgebraicGeometry.IsOpenImmersion (T.map m) := hm
    exact (inferInstance : Etale (T.map m))
  have hg : P.presheaf g := etale_presheaf_comp B S hS a (W i).ι haet hi
  have hchart : ChartPoint B S hS U g v y := by
    refine ⟨p, rfl, ?_⟩
    change pointsMap B S hS (yoneda.obj U) (a ≫ (W i).ι)
      (p.class B S hS _) = y
    rw [pointsMap_comp]
    exact (congrArg (pointsMap B S hS (W i).toFunctor (W i).ι) hz).trans hx
  refine ⟨U, g, v, hU, hg, hchart, ?_⟩
  apply (localRingDimension_eq_zero_iff_all_etale_genericPoints
    B S hS hY y).mp hy U g v _ hchart
  intro A φ hφ
  exact etale_presheaf_comp B S hS φ g hφ hg

private theorem exists_finite_open_of_finite_etale_pullback
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y)
    (f : X ⟶ Y) (y : points B S hS Y)
    (U : BigFppfOver B S hS) (g : yoneda.obj U ⟶ Y)
    (hg : (MorphismProperty.inverseImage (@Etale.{u})
      (BigFppfOver.toScheme B S hS)).presheaf g)
    (hy : y ∈ Set.range (pointsMap B S hS (yoneda.obj U) g))
    (hfin : IsFinite B S hS (pullback.snd f g)) :
    ∃ V : Subfunctor Y,
      IsOpenSubspace B S hS V ∧
      y ∈ Set.range (pointsMap B S hS V.toFunctor V.ι) ∧
      IsFinite B S hS (pullback.snd f V.ι) := by
  let hU := isAlgebraicSpace_yoneda B S hS U
  let := (pointTopologyFamily B S hS).topology Y hY
  let := (pointTopologyFamily B S hS).topology (yoneda.obj U) hU
  have hopen : IsOpen (Set.range (pointsMap B S hS (yoneda.obj U) g)) := by
    simpa only [Set.image_univ] using
      (pointTopologyFamily B S hS).etale_isOpenMap hY U g hg
        Set.univ isOpen_univ
  obtain ⟨⟨V, hV⟩, hVr⟩ :
      ∃ W : {G : Subfunctor Y // IsOpenSubspace B S hS G},
        Set.range (pointsMap B S hS W.1.toFunctor W.1.ι) =
          Set.range (pointsMap B S hS (yoneda.obj U) g) := by
    refine ⟨(openSubspacesOrderIso B S hS Y hY).symm ⟨_, hopen⟩, ?_⟩
    have h := openSubspacesOrderIso_apply B S hS Y hY
      ((openSubspacesOrderIso B S hS Y hY).symm ⟨_, hopen⟩)
    rw [OrderIso.apply_symm_apply] at h
    exact h.symm
  let q := factorThroughEtaleImage B S hS hY U g V hV hVr
  have hq : q ≫ V.ι = g :=
    factorThroughEtaleImage_comp B S hS hY U g V hV hVr
  refine ⟨V, hV, hVr.symm ▸ hy, ?_⟩
  let hP := isAlgebraicSpace_pullback B S hS f V.ι hX hV.1 hY
  apply (isFinite_iff_etaleLocal B S hS (pullback.snd f V.ι)
    hP hV.1).mpr
  refine ⟨U, q,
    surjective_factor_through_etaleImage B S hS U g V hV hVr q hq,
    etale_factor_through_etaleImage B S hS U g hg V hV q hq, ?_⟩
  have hrel0 := (isFinite_iff_representable B S hS
    (pullback.snd f g) (isAlgebraicSpace_pullback B S hS f g hX hU hY)
    hU).mp hfin |>.2
  let e0 := pullback.congrHom (rfl : f = f) hq
  have he0 : e0.hom ≫ pullback.snd f g = pullback.snd f (q ≫ V.ι) := by
    simp [e0, pullback.congrHom_hom]
  have hrel := MorphismProperty.RespectsIso.precomp _ e0.hom _ hrel0
  rw [he0] at hrel
  have hrel' := MorphismProperty.RespectsIso.precomp _
    (pullbackLeftPullbackSndIso f V.ι q).hom _ hrel
  rw [pullbackLeftPullbackSndIso_hom_snd] at hrel'
  exact (isFinite_iff_representable B S hS
    (pullback.snd (pullback.snd f V.ι) q)
    (isAlgebraicSpace_pullback B S hS (pullback.snd f V.ι) q
      hP hU hV.1) hU).mpr ⟨hrel'.1, hrel'⟩

section

private theorem schemePointRepresentative_class_eq
    (U : BigFppfOver B S hS)
    (p : FieldValuedPoint B S hS (yoneda.obj U)) :
    (schemePointRepresentative B S hS U
      (schemePoint B S hS U p)).class B S hS (yoneda.obj U) =
      p.class B S hS (yoneda.obj U) := by
  let T := (BigFppfOver.toScheme B S hS).obj U
  let z := schemePoint B S hS U p
  let q := schemePointRepresentative B S hS U z
  let hp := AlgebraicGeometry.Space.toSchemeFieldValuedPoint B S hS U p
  let hq := AlgebraicGeometry.Space.toSchemeFieldValuedPoint B S hS U q
  have hpx : hp.point = z := rfl
  have hcx : (AlgebraicGeometry.FieldValuedPoint.canonical T z).point = z :=
    Scheme.fromSpecResidueField_apply z _
  obtain ⟨φ, hφ, -⟩ :=
    (AlgebraicGeometry.FieldValuedPoint.canonical_isSmallest z) hp (hpx.trans hcx.symm)
  have hqmap : hq.map = (AlgebraicGeometry.FieldValuedPoint.canonical T z).map := by
    let kobj : B.Schemes := B.obj (B.residueField_spec_contains U.left.property z)
    change B.inclusion.map (B.inclusion.preimage (X := kobj) (Y := U.left)
      (T.fromSpecResidueField z)) = T.fromSpecResidueField z
    rw [B.inclusion.map_preimage]
  let φ' : B.inclusion.obj
      (p.siteObject B S hS (yoneda.obj U)).left ⟶
      B.inclusion.obj (q.siteObject B S hS (yoneda.obj U)).left := by
    change Spec (.of p.carrier) ⟶ Spec (.of q.carrier)
    exact φ
  let fbase := B.inclusion.preimage φ'
  have hleft : fbase ≫ q.value.left = p.value.left := by
    apply B.inclusion.map_injective
    rw [B.inclusion.map_comp, B.inclusion.map_preimage]
    change φ' ≫ B.inclusion.map q.value.left = B.inclusion.map p.value.left
    have hqleft : B.inclusion.map q.value.left = hq.map := rfl
    have hpleft : hp.map = B.inclusion.map p.value.left := rfl
    have htemp : φ' ≫ B.inclusion.map q.value.left = hp.map := by
      rw [hqleft, hqmap, show φ' = φ from rfl]
      exact hφ
    rw [hpleft] at htemp
    exact htemp
  have hbase : fbase ≫ (q.siteObject B S hS (yoneda.obj U)).hom =
      (p.siteObject B S hS (yoneda.obj U)).hom := by
    calc
      fbase ≫ (q.siteObject B S hS (yoneda.obj U)).hom =
          fbase ≫ (q.value.left ≫ U.hom) := by
        rw [q.value.w]
        rfl
      _ = (fbase ≫ q.value.left) ≫ U.hom := (Category.assoc _ _ _).symm
      _ = p.value.left ≫ U.hom := by rw [hleft]
      _ = (p.siteObject B S hS (yoneda.obj U)).hom := by
        rw [p.value.w]
        rfl
  let f : p.siteObject B S hS (yoneda.obj U) ⟶ q.siteObject B S hS (yoneda.obj U) :=
    Over.homMk fbase hbase
  have hdom : FieldValuedPoint.Dominates B S hS (yoneda.obj U) p q := by
    refine ⟨f, ?_⟩
    change f ≫ q.value = p.value
    exact Over.OverMorphism.ext hleft
  exact (FieldValuedPoint.class_eq_class_of_hasCommonExtension B S hS (yoneda.obj U)
    ⟨p, FieldValuedPoint.dominates_refl B S hS (yoneda.obj U) p, hdom⟩).symm

end

private theorem locallyQuasiFinite_near_of_germ_hasRepresentative
    {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X)
    (r : AlgebraicGeometry.MorphismOfGerms.Representative
      ⟨X, x⟩ ⟨Y, f x⟩)
    (hr : AlgebraicGeometry.MorphismOfGerms.mk r =
      MorphismOfGerms.ofSchemeHom f x)
    (hqf : LocallyQuasiFinite r.hom) :
    ∃ W : X.Opens, x ∈ W ∧ LocallyQuasiFinite (W.ι ≫ f) := by
  let r0 : AlgebraicGeometry.MorphismOfGerms.Representative
      ⟨X, x⟩ ⟨Y, f x⟩ :=
    { source := ⊤, mem_source := by simp, hom := X.topIso.hom ≫ f,
      map_point := rfl }
  have heq : r.AgreeNear r0 :=
    AlgebraicGeometry.MorphismOfGerms.mk_eq_mk_iff.mp hr
  obtain ⟨W, hxW, hWr, hWr0, heq⟩ := heq
  let : LocallyQuasiFinite r.hom := hqf
  have hW : LocallyQuasiFinite (W.ι ≫ f) := by
    have hh : LocallyQuasiFinite (X.homOfLE hWr ≫ r.hom) := inferInstance
    rw [heq] at hh
    simpa [r0] using hh
  exact ⟨W, hxW, hW⟩

private theorem quasiFiniteAt_of_locallyQuasiFinite_near
    {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X)
    (W : X.Opens) (hxW : x ∈ W)
    (hW : LocallyQuasiFinite (W.ι ≫ f)) : f.QuasiFiniteAt x := by
  let := hW
  have h : (W.ι ≫ f).QuasiFiniteAt ⟨x, hxW⟩ := (W.ι ≫ f).quasiFiniteAt _
  exact (Scheme.Hom.quasiFiniteAt_comp_iff_of_isOpenImmersion
    (f := W.ι) (g := f) (x := ⟨x, hxW⟩)).mp h

private theorem quasiFiniteAt_on_chart
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y)
    (f : X ⟶ Y)
    (U V : BigFppfOver B S hS)
    (a : yoneda.obj U ⟶ X) (b : yoneda.obj V ⟶ Y) (k : U ⟶ V)
    (ha : (MorphismProperty.inverseImage (@Etale.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (hb : (MorphismProperty.inverseImage (@Etale.{u})
      (BigFppfOver.toScheme B S hS)).presheaf b)
    (hk : yoneda.map k ≫ b = a ≫ f)
    (x : (BigFppfOver.toScheme B S hS).obj U)
    (hqf : IsQuasiFiniteAt B S hS f
      (pointsMap B S hS (yoneda.obj U) a
        (schemePointRepresentative B S hS U x).class)) :
    ((BigFppfOver.toScheme B S hS).map k).QuasiFiniteAt x := by
  let P : MorphismProperty Scheme.{u} := (@LocallyOfFiniteType.{u}) ⊓ (@LocallyQuasiFinite.{u})
  have hP := locallyOfFiniteType_inf_locallyQuasiFinite_isEtaleLocalOnSourceAndTarget
  have hc := (holdsOnEveryEtaleChartAtPoint_iff_exists_open
    B S hS P hP hX hY f _).mpr (by
      obtain ⟨O, hO, x', hx', hOqf⟩ := hqf
      exact ⟨O, hO, ⟨x', hx'⟩, hOqf⟩)
  let p := schemePointRepresentative B S hS U x
  let c : EtaleChartAtPoint B S hS f
      (pointsMap B S hS (yoneda.obj U) a p.class) :=
    { U := U, V := V, a := a, b := b, h := k,
      a_etale := ha, b_etale := hb, comm := hk,
      representative := p, point := IsLocalRing.closedPoint p.carrier, maps_to := rfl }
  obtain ⟨r, hr, _, hqf⟩ := hc c
  obtain ⟨W, hxW, hW⟩ := locallyQuasiFinite_near_of_germ_hasRepresentative _ _ r hr hqf
  have hc' := quasiFiniteAt_of_locallyQuasiFinite_near _ _ W hxW hW
  have hx : c.sourcePoint B S hS = x := schemePointRepresentative_point B S hS U x
  rwa [hx] at hc'

private theorem schemePointRepresentative_natural
    {U V : BigFppfOver B S hS} (k : U ⟶ V)
    (x : (BigFppfOver.toScheme B S hS).obj U) :
    pointsMap B S hS (yoneda.obj U) (yoneda.map k)
      (schemePointRepresentative B S hS U x).class =
      (schemePointRepresentative B S hS V
        ((BigFppfOver.toScheme B S hS).map k x)).class := by
  let p := schemePointRepresentative B S hS U x
  let q := FieldValuedPoint.map B S hS (yoneda.obj U) (yoneda.map k) p
  change q.class B S hS _ = _
  rw [← schemePointRepresentative_class_eq B S hS V q]
  have hq : schemePoint B S hS V q =
      (BigFppfOver.toScheme B S hS).map k
        (schemePoint B S hS U p) := rfl
  rw [hq, schemePointRepresentative_point]

/-- The canonical field-valued representative of a point of a chart above `y` has class `y`. -/
private theorem pointsMap_schemePointRepresentative_class
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {U : BigFppfOver B S hS} {a : yoneda.obj U ⟶ Y}
    {v : (BigFppfOver.toScheme B S hS).obj U} {y : points B S hS Y}
    (hv : ChartPoint B S hS U a v y) :
    pointsMap B S hS (yoneda.obj U) a (schemePointRepresentative B S hS U v).class = y := by
  obtain ⟨p, hp, hpy⟩ := hv
  rw [← hp, schemePointRepresentative_class_eq]
  exact hpy

private theorem quasiFiniteAt_fiber_on_chart
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y)
    (f : X ⟶ Y) (y : points B S hS Y)
    (hqf : ∀ x, pointsMap B S hS X f x = y →
      IsQuasiFiniteAt B S hS f x)
    (U V : BigFppfOver B S hS)
    (a : yoneda.obj U ⟶ X) (b : yoneda.obj V ⟶ Y) (k : U ⟶ V)
    (ha : (MorphismProperty.inverseImage (@Etale.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (hb : (MorphismProperty.inverseImage (@Etale.{u})
      (BigFppfOver.toScheme B S hS)).presheaf b)
    (hk : yoneda.map k ≫ b = a ≫ f)
    (v : (BigFppfOver.toScheme B S hS).obj V)
    (hv : ChartPoint B S hS V b v y) :
    ∀ x, (BigFppfOver.toScheme B S hS).map k x = v →
      ((BigFppfOver.toScheme B S hS).map k).QuasiFiniteAt x := by
  intro x hx
  apply quasiFiniteAt_on_chart B S hS hX hY f U V a b k ha hb hk x
  apply hqf
  change (pointsMap B S hS X f ∘
    pointsMap B S hS (yoneda.obj U) a) _ = y
  rw [← pointsMap_comp, ← hk, pointsMap_comp]
  change pointsMap B S hS (yoneda.obj V) b
    (pointsMap B S hS (yoneda.obj U) (yoneda.map k) _) = y
  rw [schemePointRepresentative_natural, hx]
  exact pointsMap_schemePointRepresentative_class B S hS hv

private theorem isFinite_restrict_of_le
    {X Y : Scheme.{u}} (f : X ⟶ Y) {W V : Y.Opens}
    (hWV : W ≤ V) (hfin : _root_.AlgebraicGeometry.IsFinite (f ∣_ V)) :
    _root_.AlgebraicGeometry.IsFinite (f ∣_ W) := by
  let a := X.homOfLE (f.preimage_mono hWV)
  let b := Y.homOfLE hWV
  have ho : IsPullback (a ≫ (f ⁻¹ᵁ V).ι) (f ∣_ W) f (b ≫ V.ι) := by
    simpa [a, b] using (isPullback_morphismRestrict f W).flip
  have hp : IsPullback a (f ∣_ W) (f ∣_ V) b := ho.of_right
    (by simp [a, b, ← cancel_mono V.ι]) (isPullback_morphismRestrict f V).flip
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := @_root_.AlgebraicGeometry.IsFinite) hp hfin

private theorem exists_affine_open_two_finite_restrictions
    {U R V : Scheme.{u}} (k : U ⟶ V) (l : R ⟶ V)
    [IsAffine V] [LocallyOfFiniteType k] [QuasiCompact k] [QuasiSeparated k]
    [LocallyOfFiniteType l] [QuasiCompact l] [QuasiSeparated l]
    (v : V) (hv : v ∈ genericPoints V)
    (hk : ∀ x, k x = v → k.QuasiFiniteAt x)
    (hl : ∀ x, l x = v → l.QuasiFiniteAt x) :
    ∃ W : V.affineOpens, v ∈ W.1 ∧ _root_.AlgebraicGeometry.IsFinite (k ∣_ W.1) ∧
      _root_.AlgebraicGeometry.IsFinite (l ∣_ W.1) := by
  obtain ⟨W, hvW, hkW⟩ := exists_affine_open_finite_of_quasiFiniteAt_fiber k v hv hk
  obtain ⟨Z, hvZ, hlZ⟩ := exists_affine_open_finite_of_quasiFiniteAt_fiber l v hv hl
  refine ⟨⟨W.1 ⊓ Z.1, ?_⟩, ⟨hvW, hvZ⟩,
    isFinite_restrict_of_le k inf_le_left hkW,
    isFinite_restrict_of_le l inf_le_right hlZ⟩
  exact W.2.inf Z.2

private theorem kernelPair_of_restriction
    {C : Type*} [Category C]
    {R U X V R' U' X' W : C}
    {s t : R ⟶ U} {g : U ⟶ X} {f : X ⟶ V}
    {i : W ⟶ V} {r : R' ⟶ R} {u : U' ⟶ U} {x : X' ⟶ X}
    {s' t' : R' ⟶ U'} {g' : U' ⟶ X'} {f' : X' ⟶ W}
    (hR : IsPullback s t g g)
    (hU : IsPullback u (g' ≫ f') (g ≫ f) i)
    (hX : IsPullback x f' f i)
    (hR' : IsPullback r (t' ≫ g' ≫ f') (t ≫ g ≫ f) i)
    (hg : u ≫ g = g' ≫ x)
    (hs : s' ≫ u = r ≫ s) (ht : r ≫ t = t' ≫ u)
    (hsg : s' ≫ g' = t' ≫ g') : IsPullback s' t' g' g' := by
  have hUg : IsPullback u g' g x := hU.of_bot hg hX
  have hRt : IsPullback r t' t u := by
    apply IsPullback.of_bot (t := hU) _ ht
    simpa only [Category.assoc] using hR'
  have houter : IsPullback (s' ≫ u) t' g (g' ≫ x) := by
    rw [hs, ← hg]
    exact hRt.paste_horiz hR
  exact houter.of_right hsg hUg


attribute [local instance] Stacks.Morphisms.isFinite_respectsIso

private theorem property_snd_of_isPullbacks
    {C : Type*} [Category C] (P : MorphismProperty C) [P.RespectsIso]
    {A A' U V Y : C} {s : A ⟶ U} {t : A ⟶ V}
    {s' : A' ⟶ U} {t' : A' ⟶ V} {f : U ⟶ Y} {g : V ⟶ Y}
    (h : IsPullback s t f g) (h' : IsPullback s' t' f g) (ht' : P t') : P t := by
  have hh := MorphismProperty.RespectsIso.precomp P (h.isoIsPullback U V h').hom t' ht'
  simpa using hh

/-- The base change `pullback.snd f g : X ×_Y Z ⟶ Z` of a morphism `f : X ⟶ Y` of algebraic spaces
that is locally of finite type is locally of finite type. -/
theorem locallyOfFiniteType_pullback_snd
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y)
    (hZ : IsAlgebraicSpace B S hS Z)
    (f : X ⟶ Y) (g : Z ⟶ Y)
    (hf : IsLocallyOfFiniteType B S hS f) :
    IsLocallyOfFiniteType B S hS (pullback.snd f g) := by
  let X' : AlgebraicGeometry.AlgebraicSpaces B S hS := ⟨X, hX⟩
  let Y' : AlgebraicGeometry.AlgebraicSpaces B S hS := ⟨Y, hY⟩
  let Z' : AlgebraicGeometry.AlgebraicSpaces B S hS := ⟨Z, hZ⟩
  let f' : X' ⟶ Y' := ObjectProperty.homMk f
  let g' : Z' ⟶ Y' := ObjectProperty.homMk g
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := fun {A D : AlgebraicGeometry.AlgebraicSpaces B S hS} (q : A ⟶ D) =>
      IsLocallyOfFiniteType B S hS q.hom)
    (AlgebraicGeometry.AlgebraicSpaces.isPullback_fiberProduct B S hS f' g') hf

private theorem finite_of_finite_kernelPair
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X)
    (U R : BigFppfOver B S hS) (g : yoneda.obj U ⟶ X)
    (hs : (MorphismProperty.inverseImage (@Surjective.{u})
      (BigFppfOver.toScheme B S hS)).presheaf g)
    (he : (MorphismProperty.inverseImage (@Etale.{u})
      (BigFppfOver.toScheme B S hS)).presheaf g)
    (s t : R ⟶ U) (hpb : IsPullback (yoneda.map s) (yoneda.map t) g g)
    (ht : _root_.AlgebraicGeometry.IsFinite ((BigFppfOver.toScheme B S hS).map t)) :
    IsFinite B S hS g := by
  let := inverseImage_stableUnderBaseChange B S hS (@_root_.AlgebraicGeometry.IsFinite.{u})
  apply finite_of_finite_etale_kernelPair B S hS hX U g hs he
  let P := MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.IsFinite.{u})
    (BigFppfOver.toScheme B S hS)
  apply (MorphismProperty.relative_map_iff (F := yoneda) (P := P)).mp
  exact property_snd_of_isPullbacks P.presheaf (he.1.isPullback g) hpb
    ((MorphismProperty.relative_map_iff (F := yoneda) (P := P)).mpr ht)

private theorem finite_pullback_of_finite_atlas_restrictions
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X)
    (U R V W : BigFppfOver B S hS)
    (g : yoneda.obj U ⟶ X) (f : X ⟶ yoneda.obj V)
    (k : U ⟶ V) (hk : yoneda.map k = g ≫ f)
    (s t : R ⟶ U) (hpb : IsPullback (yoneda.map s) (yoneda.map t) g g)
    (hs : (MorphismProperty.inverseImage (@Surjective.{u})
      (BigFppfOver.toScheme B S hS)).presheaf g)
    (he : (MorphismProperty.inverseImage (@Etale.{u})
      (BigFppfOver.toScheme B S hS)).presheaf g)
    (hf : IsLocallyOfFiniteType B S hS f)
    (i : W ⟶ V)
    (hW : IsAffine ((BigFppfOver.toScheme B S hS).obj W))
    (hkfin : _root_.AlgebraicGeometry.IsFinite
      ((BigFppfOver.toScheme B S hS).map (pullback.snd k i)))
    (hrfin : _root_.AlgebraicGeometry.IsFinite ((BigFppfOver.toScheme B S hS).map
      (pullback.snd (t ≫ k) i))) :
    IsFinite B S hS (pullback.snd f (yoneda.map i)) := by
  let := inverseImage_stableUnderBaseChange B S hS (@_root_.AlgebraicGeometry.IsFinite.{u})
  let T := BigFppfOver.toScheme B S hS
  have hst : s ≫ k = t ≫ k := by
    apply yoneda.map_injective
    simp only [Functor.map_comp, hk, ← Category.assoc]
    rw [hpb.w]
  let U' := pullback k i
  let R' := pullback (t ≫ k) i
  let u : U' ⟶ U := pullback.fst k i
  let r : R' ⟶ R := pullback.fst (t ≫ k) i
  let k' : U' ⟶ W := pullback.snd k i
  let l' : R' ⟶ W := pullback.snd (t ≫ k) i
  let s' : R' ⟶ U' := pullback.lift (r ≫ s) l' (by
    simp only [Category.assoc, hst, r, l', pullback.condition])
  let t' : R' ⟶ U' := pullback.lift (r ≫ t) l' (by
    simp only [Category.assoc, r, l', pullback.condition])
  let X' := pullback f (yoneda.map i)
  let x : X' ⟶ X := pullback.fst f (yoneda.map i)
  let f' : X' ⟶ yoneda.obj W := pullback.snd f (yoneda.map i)
  let g' : yoneda.obj U' ⟶ X' := pullback.lift (yoneda.map u ≫ g) (yoneda.map k') (by
    rw [Category.assoc, ← hk, ← Functor.map_comp, ← Functor.map_comp]
    exact congrArg yoneda.map (pullback.condition))
  have hUg : IsPullback (yoneda.map u) g' g x := by
    apply IsPullback.of_bot (t := IsPullback.of_hasPullback f (yoneda.map i))
    · simpa [u, k', g', hk, Functor.map_comp] using
        (IsPullback.of_hasPullback k i).map yoneda
    · simp [g']
  have hX' := isAlgebraicSpace_pullback B S hS f (yoneda.map i) hX
    (isAlgebraicSpace_yoneda B S hS W)
    (isAlgebraicSpace_yoneda B S hS V)
  have hsg : yoneda.map s' ≫ g' = yoneda.map t' ≫ g' := by
    apply pullback.hom_ext
    · simp only [g', pullback.lift_fst, Category.assoc]
      rw [← Category.assoc, ← Functor.map_comp]
      rw [show s' ≫ u = r ≫ s from pullback.lift_fst _ _ _]
      rw [Functor.map_comp, Category.assoc, hpb.w]
      simp only [← Functor.map_comp_assoc,
        show t' ≫ u = r ≫ t from pullback.lift_fst _ _ _]
    · simp only [g', Category.assoc, pullback.lift_snd]
      rw [← Functor.map_comp, ← Functor.map_comp]
      rw [show s' ≫ k' = l' from pullback.lift_snd _ _ _,
        show t' ≫ k' = l' from pullback.lift_snd _ _ _]
  have hR' : IsPullback (yoneda.map s') (yoneda.map t') g' g' := by
    apply kernelPair_of_restriction (f := f) (i := yoneda.map i)
      (r := yoneda.map r) (u := yoneda.map u) (x := x) (f' := f') hpb
    · simpa [g', f', u, k', hk, Functor.map_comp] using
        (IsPullback.of_hasPullback k i).map yoneda
    · exact IsPullback.of_hasPullback f (yoneda.map i)
    · have htf : yoneda.map t' ≫ g' ≫ f' = yoneda.map l' := by
        simp only [g', f', pullback.lift_snd]
        rw [← Functor.map_comp, show t' ≫ k' = l' from pullback.lift_snd _ _ _]
      rw [htf]
      simpa only [Functor.map_comp, hk, Category.assoc] using
        (IsPullback.of_hasPullback (t ≫ k) i).map yoneda
    · simp [g', x]
    · simp [s', u, r, ← Functor.map_comp]
    · simp [t', u, r, ← Functor.map_comp]
    · exact hsg
  have hs' : (MorphismProperty.inverseImage (@Surjective.{u}) T).presheaf g' :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hUg hs
  have he' : (MorphismProperty.inverseImage (@Etale.{u}) T).presheaf g' :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hUg he
  let : _root_.AlgebraicGeometry.IsFinite (T.map k') := hkfin
  let : IsAffine (T.obj W) := hW
  let : _root_.AlgebraicGeometry.IsFinite (T.map t' ≫ T.map k') := by
    rw [← Functor.map_comp, show t' ≫ k' = l' from pullback.lift_snd _ _ _]
    exact hrfin
  have htfin : _root_.AlgebraicGeometry.IsFinite (T.map t') :=
    _root_.AlgebraicGeometry.IsFinite.of_comp (T.map t') (T.map k')
  have hgfin := finite_of_finite_kernelPair B S hS hX' U' R' g' hs' he' s' t' hR' htfin
  apply finite_of_finite_surjective_affine_cover B S hS hX' U' W
    (isAffine_of_isAffineHom (T.map k')) hW g' f' hgfin hs' he'
    (locallyOfFiniteType_pullback_snd B S hS hX
      (isAlgebraicSpace_yoneda B S hS V)
      (isAlgebraicSpace_yoneda B S hS W) f (yoneda.map i) hf)
  have hcomp : yoneda.preimage (g' ≫ f') = k' := by
    apply yoneda.map_injective
    simp [g', f']
  simpa only [hcomp] using hkfin

private theorem exists_finite_etale_chart
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y)
    (f : X ⟶ Y) (hqs : IsQuasiSeparated B S hS f)
    (hft : IsFiniteType B S hS f)
    (y : points B S hS Y)
    (hqf : ∀ x, pointsMap B S hS X f x = y →
      IsQuasiFiniteAt B S hS f x)
    (V : BigFppfOver B S hS) (a : yoneda.obj V ⟶ Y)
    (v : (BigFppfOver.toScheme B S hS).obj V)
    (hVaff : IsAffine ((BigFppfOver.toScheme B S hS).obj V))
    (ha : (MorphismProperty.inverseImage (@Etale.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (hv : ChartPoint B S hS V a v y)
    (hvgeneric : v ∈ genericPoints ((BigFppfOver.toScheme B S hS).obj V)) :
    ∃ (W : BigFppfOver B S hS) (b : yoneda.obj W ⟶ Y),
      (MorphismProperty.inverseImage (@Etale.{u})
        (BigFppfOver.toScheme B S hS)).presheaf b ∧
      y ∈ Set.range (pointsMap B S hS (yoneda.obj W) b) ∧
      IsFinite B S hS (pullback.snd f b) := by
  let := inverseImage_stableUnderBaseChange B S hS (@_root_.AlgebraicGeometry.IsFinite.{u})
  let := inverseImage_stableUnderBaseChange B S hS (@Etale.{u})
  let T := BigFppfOver.toScheme B S hS
  let : IsAffine (T.obj V) := hVaff
  let hV := isAlgebraicSpace_yoneda B S hS V
  let Z := pullback f a
  let f0 : Z ⟶ yoneda.obj V := pullback.snd f a
  let j : Z ⟶ X := pullback.fst f a
  have hZ := isAlgebraicSpace_pullback B S hS f a hX hV hY
  have hZqc : IsQuasiCompactSpace B S hS Z :=
    isQuasiCompactSpace_of_iso B S hS (pullbackSymmetry a f)
      (hft.2 _ hV (isQuasiCompact_yoneda_of_compact B S hS V inferInstance) a)
  obtain ⟨U, g, hUaff, hgsurj, hget⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover
      B S hS Z hZ).mp hZqc
  let : IsAffine (T.obj U) := hUaff
  let hU := isAlgebraicSpace_yoneda B S hS U
  have hge : (MorphismProperty.inverseImage (@Etale.{u}) T).presheaf g := by
    simpa using hget U (𝟙 _) (presheaf_etale_id B S hS U)
  have hje : (MorphismProperty.inverseImage (@Etale.{u}) T).presheaf j :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback f a).flip ha
  have hf0 := locallyOfFiniteType_pullback_snd B S hS hX hY hV f a hft.1
  have hqs0 := isQuasiSeparated_pullback
    B S hS f a hqs
  let k : U ⟶ V := yoneda.preimage (g ≫ f0)
  have hk : yoneda.map k = g ≫ f0 := yoneda.map_preimage _
  let : LocallyOfFiniteType (T.map k) := hf0 U V g (𝟙 _) k hge
    (presheaf_etale_id B S hS V) (by simpa using hk)
  have hkgqc : IsQuasiCompact B S hS (g ≫ f0) := by
    rw [← hk]
    exact AlgebraicGeometry.Space.quasiCompact_schemeMap_isQuasiCompact B S hS k inferInstance
  have hgqc := isQuasiCompact_of_comp_of_isQuasiSeparated
    B S hS g f0 hU hV hkgqc hqs0
  have hgqs : IsQuasiSeparated B S hS g := by
    refine isQuasiSeparated_of_comp B S hS g f0 ?_
    rw [← hk]
    exact (isQuasiSeparated_yoneda_map_iff
      B S hS k).mpr inferInstance
  let R := hge.1.pullback g
  let s : R ⟶ U := hge.1.fst' g
  let t : R ⟶ U := hge.1.snd g
  have hpb : IsPullback (yoneda.map s) (yoneda.map t) g g := hge.1.isPullback' g
  have hRqc : IsQuasiCompactSpace B S hS (yoneda.obj R) :=
    isQuasiCompactSpace_of_iso B S hS
      (hpb.isoIsPullback _ _ (IsPullback.of_hasPullback g g)).symm
      (hgqc _ hU (isQuasiCompact_yoneda_of_compact B S hS U inferInstance) g)
  let : CompactSpace (T.obj R) := compact_of_isQuasiCompact_yoneda B S hS R hRqc
  let : Etale (T.map t) := hge.2 g (yoneda.map s) t hpb
  let : QuasiSeparated (T.map t) :=
    (isQuasiSeparated_yoneda_map_iff B S hS t).mp
      (isQuasiSeparated_of_isPullback B S hS hpb hgqs)
  let l : R ⟶ V := t ≫ k
  let : LocallyOfFiniteType (T.map l) := by
    dsimp only [l]
    rw [Functor.map_comp]
    exact locallyOfFiniteType_comp (hf := locallyOfFiniteType_of_etale (T.map t))
      (T.map t) (T.map k)
  let : QuasiSeparated (T.map l) := by dsimp [l]; rw [Functor.map_comp]; infer_instance
  let : QuasiCompact (T.map l) := (quasiCompact_iff_compactSpace _).mpr inferInstance
  have hgj := etale_presheaf_comp B S hS g j hge hje
  have hkj : yoneda.map k ≫ a = (g ≫ j) ≫ f := by
    rw [hk]
    simp [f0, j, Category.assoc, pullback.condition]
  have hkqf := quasiFiniteAt_fiber_on_chart B S hS hX hY f y hqf
    U V (g ≫ j) a k hgj ha hkj v hv
  have htgj : (MorphismProperty.inverseImage (@Etale.{u}) T).presheaf
      (yoneda.map t ≫ g ≫ j) := etale_presheaf_comp B S hS (yoneda.map t) (g ≫ j)
        ((MorphismProperty.relative_map_iff (F := yoneda)).mpr
          (inferInstance : Etale (T.map t))) hgj
  have hlqf := quasiFiniteAt_fiber_on_chart B S hS hX hY f y hqf
    R V (yoneda.map t ≫ g ≫ j) a l htgj ha
    (by simp [l, Functor.map_comp, Category.assoc, hkj]) v hv
  obtain ⟨O, hvO, hkO, hlO⟩ := exists_affine_open_two_finite_restrictions
    (T.map k) (T.map l) v hvgeneric hkqf hlqf
  let W := opensSiteObject B S hS V O.1
  let i : W ⟶ V := opensSiteObjectInclusion B S hS V O.1
  have hi : T.map i = O.1.ι := map_opensSiteObjectInclusion B S hS V O.1
  have hW : IsAffine (T.obj W) := O.2
  have hfinsnd : ∀ {A : BigFppfOver B S hS} (m : A ⟶ V),
      _root_.AlgebraicGeometry.IsFinite (T.map m ∣_ O.1) →
        _root_.AlgebraicGeometry.IsFinite (T.map (pullback.snd m i)) := fun m hm ↦
    property_snd_of_isPullbacks
      (@_root_.AlgebraicGeometry.IsFinite.{u} : MorphismProperty Scheme.{u})
      ((IsPullback.of_hasPullback m i).map T)
      (by rw [hi]; exact (isPullback_morphismRestrict (T.map m) O.1).flip) hm
  have hkfin := hfinsnd k hkO
  have hlfin := hfinsnd l hlO
  have hfin := finite_pullback_of_finite_atlas_restrictions B S hS hZ U R V W
    g f0 k hk s t hpb hgsurj hge hf0 i hW hkfin hlfin
  let b := yoneda.map i ≫ a
  have hie : Etale (T.map i) := by
    have ho : Etale O.1.ι := inferInstance
    rw [hi]
    exact ho
  have hb : (MorphismProperty.inverseImage (@Etale.{u}) T).presheaf b :=
    etale_presheaf_comp B S hS _ _
      ((MorphismProperty.relative_map_iff (F := yoneda)).mpr hie) ha
  refine ⟨W, b, hb, ?_, ?_⟩
  · let w : T.obj W := ⟨v, hvO⟩
    have hw : T.map i w = v := by rw [hi]; rfl
    refine ⟨(schemePointRepresentative B S hS W w).class, ?_⟩
    rw [pointsMap_comp]
    change pointsMap B S hS (yoneda.obj V) a
      (pointsMap B S hS (yoneda.obj W) (yoneda.map i) _) = y
    rw [schemePointRepresentative_natural, hw]
    exact pointsMap_schemePointRepresentative_class B S hS hv
  · have hfinrel := (isFinite_iff_representable B S hS
      (pullback.snd f0 (yoneda.map i))
      (isAlgebraicSpace_pullback B S hS f0 (yoneda.map i)
        hZ (isAlgebraicSpace_yoneda B S hS W) hV)
      (isAlgebraicSpace_yoneda B S hS W)).mp hfin |>.2
    have hh := MorphismProperty.RespectsIso.precomp _
      (pullbackLeftPullbackSndIso f a (yoneda.map i)).inv _ hfinrel
    rw [pullbackLeftPullbackSndIso_inv_snd_snd] at hh
    exact (isFinite_iff_representable B S hS (pullback.snd f b)
      (isAlgebraicSpace_pullback B S hS f b hX
        (isAlgebraicSpace_yoneda B S hS W) hY)
      (isAlgebraicSpace_yoneda B S hS W)).mpr ⟨hh.1, hh⟩


/-- **Stacks 0ACZ, conditions (1) and (2) imply condition (3).** Let `f : X ⟶ Y` be a
quasi-separated morphism of algebraic spaces over `S` of finite type, let `y` be a point of
`|Y|` whose local ring has dimension zero and let `p` be a field-valued representative of `y`
with field of definition `k`. If the field fibre `X_k = X ×_Y Spec(k)` has finitely many
points then there is an open subspace `V ⊂ Y` with `y ∈ |V|` whose base change
`V ×_Y X ⟶ V` is finite.

An affine étale chart `V ⟶ Y` at `y` may be chosen so that `y` comes from a generic point `v`
of `V` (Stacks 0BAQ). Over an affine étale atlas `U` of `V ×_Y X` the two morphisms
`U ⟶ V` and `U ×_{V ×_Y X} U ⟶ V` are quasi-finite above `v` (Stacks 0BBB), so both become
finite after shrinking `V` to an affine open neighbourhood of `v` (Stacks 02NW). The relation
being finite over the atlas makes the atlas finite over the shrunk chart, and the chart being
affine with a finite surjective atlas makes `V ×_Y X` an affine scheme (Stacks 01ZT), over
which finiteness is properness together with affineness. Descending along the étale chart
produces the open subspace of `Y`. -/
@[stacks 0ACZ "conditions (1) and (2) imply condition (3)"]
theorem exists_isOpenSubspace_isFinite_pullback_snd_of_finite_fieldFiber
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y)
    (f : X ⟶ Y)
    (hqs : IsQuasiSeparated B S hS f)
    (hft : IsFiniteType B S hS f)
    (y : points B S hS Y)
    (p : FieldValuedPoint B S hS Y)
    (hp : p.class B S hS Y = y)
    (hy : localRingDimension B S hS y = 0) :
    Set.Finite (Set.univ : Set (points B S hS
      (pullback f (yonedaEquiv.symm p.value)))) →
    ∃ V : Subfunctor Y,
        IsOpenSubspace B S hS V ∧
        y ∈ Set.range (pointsMap B S hS V.toFunctor V.ι) ∧
        IsFinite B S hS (pullback.snd f V.ι) := by
  intro hfield
  have hqf := (finite_fieldFiber_iff_quasiFiniteAt_fiber
    B S hS hX hY f hqs hft y p hp).mp hfield
  have hchart : ∃ (U : BigFppfOver B S hS) (g : yoneda.obj U ⟶ Y),
      (MorphismProperty.inverseImage (@Etale.{u})
        (BigFppfOver.toScheme B S hS)).presheaf g ∧
      y ∈ Set.range (pointsMap B S hS (yoneda.obj U) g) ∧
      IsFinite B S hS (pullback.snd f g) := by
    obtain ⟨V, a, v, hVaff, ha, hv, hvgeneric⟩ :=
      exists_affine_etale_generic_chart B S hS hY y hy
    exact exists_finite_etale_chart B S hS hX hY f hqs hft y hqf
      V a v hVaff ha hv hvgeneric
  obtain ⟨U, g, hg, hgy, hgf⟩ := hchart
  exact exists_finite_open_of_finite_etale_pullback B S hS hX hY f y U g hg hgy hgf

/-- **Stacks 0ACZ, condition (3) implies condition (2).** Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S` which is locally of finite type and let `V ⊂ Y` be an open subspace
containing a point `y` of `|Y|` in its point set. If the base change `V ×_Y X ⟶ V` is finite
then `f` is quasi-finite at every point of `|X|` above `y`.

A finite morphism is quasi-finite (Stacks 04NY), so `V ×_Y X ⟶ V` is quasi-finite at every
point of its source; a point of `|X|` above `y` lifts to `|V ×_Y X|` (Stacks 03H4), and
quasi-finiteness at a point passes to and from a base change (Stacks 0ABM). -/
@[stacks 0ACZ "condition (3) implies condition (2)"]
theorem isQuasiFiniteAt_of_isFinite_pullback_snd
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y)
    (f : X ⟶ Y)
    (hlft : IsLocallyOfFiniteType B S hS f)
    (y : points B S hS Y)
    (V : Subfunctor Y)
    (hV : IsOpenSubspace B S hS V)
    (hyV : y ∈ Set.range (pointsMap B S hS V.toFunctor V.ι))
    (hfin : IsFinite B S hS (pullback.snd f V.ι))
    (x : points B S hS X)
    (hxy : pointsMap B S hS X f x = y) :
    IsQuasiFiniteAt B S hS f x := by
  have hP : IsAlgebraicSpace B S hS (pullback f V.ι) :=
    isAlgebraicSpace_pullback B S hS f V.ι hX hV.1 hY
  have hsq : IsPullback (pullback.snd f V.ι) (pullback.fst f V.ι) V.ι f :=
    (IsPullback.of_hasPullback f V.ι).flip
  have hlqf : IsLocallyQuasiFinite B S hS (pullback.snd f V.ι) :=
    (isQuasiFinite_of_isFinite B S hS (pullback.snd f V.ι) hP hV.1 hfin).1
  obtain ⟨v, hv⟩ := hyV
  obtain ⟨w, -, hwx⟩ :=
    exists_point_of_isPullback_presheaf B S hS hsq v x (hv.trans hxy.symm)
  have hqfw : IsQuasiFiniteAt B S hS f
      (pointsMap B S hS (pullback f V.ι) (pullback.fst f V.ι) w) :=
    (isQuasiFiniteAt_iff_of_isPullback B S hS hsq hX hY hV.1 hlft w).mp
      (isQuasiFiniteAt_of_isLocallyQuasiFinite B S hS hP hlqf w)
  rwa [hwx] at hqfw

/-- **Stacks 0ACZ, conditions (1) and (3).** Let `f : X ⟶ Y` be a quasi-separated morphism of
algebraic spaces over `S` of finite type, let `y` be a point of `|Y|` whose local ring has
dimension zero and let `p` be a field-valued representative of `y`. The field fibre `X_k` has
finitely many points exactly when there is an open subspace `V ⊂ Y` with `y ∈ |V|` whose base
change `V ×_Y X ⟶ V` is finite.

Together with `AlgebraicGeometry.Space.finite_fieldFiber_iff_quasiFiniteAt_fiber` this closes
the equivalence of the source's conditions (1), (2) and (3). -/
@[stacks 0ACZ "conditions (1) and (3)"]
theorem finite_fieldFiber_iff_exists_isOpenSubspace_isFinite_pullback_snd
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y)
    (f : X ⟶ Y)
    (hqs : IsQuasiSeparated B S hS f)
    (hft : IsFiniteType B S hS f)
    (y : points B S hS Y)
    (p : FieldValuedPoint B S hS Y)
    (hp : p.class B S hS Y = y)
    (hy : localRingDimension B S hS y = 0) :
    Set.Finite (Set.univ : Set (points B S hS
        (pullback f (yonedaEquiv.symm p.value)))) ↔
      ∃ V : Subfunctor Y,
        IsOpenSubspace B S hS V ∧
        y ∈ Set.range (pointsMap B S hS V.toFunctor V.ι) ∧
        IsFinite B S hS (pullback.snd f V.ι) := by
  refine ⟨exists_isOpenSubspace_isFinite_pullback_snd_of_finite_fieldFiber
    B S hS hX hY f hqs hft y p hp hy, ?_⟩
  rintro ⟨V, hV, hyV, hfin⟩
  exact (finite_fieldFiber_iff_quasiFiniteAt_fiber B S hS hX hY f hqs hft y p hp).mpr
    fun x hxy ↦ isQuasiFiniteAt_of_isFinite_pullback_snd B S hS hX hY f hft.1 y V hV hyV
      hfin x hxy

end OpenNeighborhood

end Space

end AlgebraicGeometry

end
