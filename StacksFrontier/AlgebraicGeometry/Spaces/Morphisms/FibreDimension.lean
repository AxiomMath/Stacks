module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.Germ.TranscendenceDegreeFinite
public import StacksFrontier.AlgebraicGeometry.F6Rank128.FiberDimension
public import StacksFrontier.AlgebraicGeometry.FibreDimensionBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.FibreDimensionBaseChange.Composite
public import StacksFrontier.AlgebraicGeometry.FibreDimensionBaseChange.LocalRing
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.Openness
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.QuasiFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.Dimension
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.FiberLocalRingDimensionChart
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat.AtAPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.FpqcOpenSubspaceDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenImmersionCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceImage
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresented
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.FormalGlueingCovering
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeDimensionAtPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeDimensionOpenness
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeDimensionQuasiFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.Support.CompatibleEtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.TranscendenceDegreeChart
import StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteLocusOnCharts

/-!
# Morphisms and dimensions of fibres of algebraic spaces

Stacks 04NM attaches three numbers to a point `x` of a morphism `f : X ⟶ Y` of algebraic spaces
over a scheme `S`: the relative dimension of `f` at `x`, the dimension of the local ring of the
fibre of `f` at `x`, and the transcendence degree of `x` over `f x`. This file develops the
basic theory of the first of them: the dimension formula relating the three (Stacks 04NQ), the
behaviour of all three along a composite (Stacks 04NR), the
behaviour of all three under base change (Stacks 04NS), the topology of the
bounded-relative-dimension locus (Stacks 04NT and Stacks 04NU), the characterization of local
quasi-finiteness by relative dimension `0` (Stacks 04NV) and the resulting canonical locally
quasi-finite open subspace of the source (Stacks 04NW), of which Stacks 06LS is a consequence.

## Main definitions

* `AlgebraicGeometry.Space.locallyQuasiFinitePart` is the canonical open subspace of the source
  of a morphism locally of finite type over which that morphism is locally quasi-finite.

## Main results

* `AlgebraicGeometry.Space.exists_hasRelativeDimensionAt`: every point of the source of a
  morphism of algebraic spaces has a relative dimension there.
* `AlgebraicGeometry.Space.hasRelativeDimensionAt_zero_of_dimensionAtPoint_eq_zero`: a morphism
  whose target has subsingleton underlying scheme has relative dimension `0` wherever the source
  has dimension `0`. Stated for the morphism itself rather than for a point of a pullback, which
  is what a space already over the spectrum of a field needs — the pullback form forces an
  identification `X ≅ X ×_{h_T} Spec k` and a `dimensionAtPoint` transport along it.
* `AlgebraicGeometry.Space.isQuasiFiniteAt_of_dimensionAtPoint_eq_zero_of_subsingleton`: the same
  hypothesis gives quasi-finiteness at a point of the base change.
* `Space.relativeDimensionAt_eq_fiberLocalRingDimension_add_transcendenceDegreeAt` is Stacks
  04NQ: the relative dimension at a point is the dimension of the local ring of the fibre there
  plus the transcendence degree of the point over its image.
* `AlgebraicGeometry.Space.hasRelativeDimensionAt_comp_le_add` and
  `AlgebraicGeometry.Space.exists_hasRelativeDimensionAt_comp_le_add` are part (1) of Stacks
  04NR: the relative dimension at a point of a composite is at most the sum of the two relative
  dimensions.
* `AlgebraicGeometry.Space.hasRelativeDimensionAt_comp_of_isFlatAt_fibre` is part (2) of Stacks
  04NR: that bound is attained when the morphism of field-valued fibres over the image point is
  flat at a point above the given one;
  `AlgebraicGeometry.Space.hasRelativeDimensionAt_comp_of_isFlatAt` is the special case in which
  the first morphism itself is flat at the point.
* `AlgebraicGeometry.Space.hasTranscendenceDegreeAt_comp` is part (3) of Stacks 04NR: the
  transcendence degree at a point of a composite is the sum of the two transcendence degrees.
* `AlgebraicGeometry.Space.hasRelativeDimensionAt_iff_of_isPullback` is part (1) of Stacks
  04NS: relative dimension at a point is invariant under base change.
* `AlgebraicGeometry.Space.exists_fiberLocalRingDimension_add_eq_of_isPullback`
  is part (2) of Stacks 04NS: under base change the dimension gained by the local ring of the
  fibre at a point is the transcendence degree lost there, the common difference being
  nonnegative;
  `AlgebraicGeometry.Space.fiberLocalRingDimension_le_of_isPullback` and
  `AlgebraicGeometry.Space.transcendenceDegreeAt_le_of_isPullback` are the two inequalities it
  implies.
* `AlgebraicGeometry.Space.exists_point_preserving_fiberLocalRingDimension_and_trdeg`
  is part (3) of Stacks 04NS: a point of the source and a point of the new base with the same
  image have a common lift at which that common difference vanishes.
* `AlgebraicGeometry.Space.isRetrocompact_setOf_exists_hasRelativeDimensionAt_le` is Stacks
  04NU: the locus where the relative dimension is at most `n` is retrocompact when the morphism
  is locally of finite presentation. That this locus is open is Stacks 04NT,
  `AlgebraicGeometry.Space.isOpen_setOf_hasRelativeDimensionAt_le`, which this file imports and
  uses.
* Stacks 04NV, that a morphism locally of finite type is locally quasi-finite exactly when it
  has relative dimension `0` everywhere, is
  `AlgebraicGeometry.Space.isLocallyQuasiFinite_iff_forall_hasRelativeDimensionAt_zero`, which
  this file imports and uses; it needs no algebraicity hypothesis and is not restated here.
* `AlgebraicGeometry.Space.mem_range_pointsMap_locallyQuasiFinitePart_iff`,
  `AlgebraicGeometry.Space.isLocallyQuasiFinite_locallyQuasiFinitePart`,
  `AlgebraicGeometry.Space.exists_one_le_hasRelativeDimensionAt_of_not_mem_locallyQuasiFinitePart`,
  `AlgebraicGeometry.Space.le_locallyQuasiFinitePart` and
  `AlgebraicGeometry.Space.locallyQuasiFinitePart_preimage_of_isPullback` are Stacks 04NW: the
  canonical open subspace is locally quasi-finite over the target, is the largest such open
  subspace, has relative dimension at least `1` at every point outside it, and its formation
  commutes with arbitrary base change.
* `AlgebraicGeometry.Space.isQuasiFiniteAt_of_dimensionAtPoint_fiber_eq_zero` is Stacks 06LS: a
  zero-dimensional point of a field-valued fibre lies over the quasi-finite locus.

## Implementation notes

All three invariants of Stacks 04NM are chart conditions on germs of schemes, so each statement
here is reduced to a statement about a morphism of schemes at a point by evaluating the chart
condition on one pointed étale chart (Stacks 04NC) and reading the germ property off the
morphism of charts. What the germ conditions say about that morphism of schemes is recorded by
three bridges — `AlgebraicGeometry.hasFiberDimensionAt_ofSchemeHom_iff`,
`AlgebraicGeometry.hasFiberLocalRingDimension_ofSchemeHom_iff` and
`AlgebraicGeometry.MorphismOfGerms.hasResidueFieldTranscendenceDegree_ofSchemeHom_iff` — each
of which says that the germ condition is the corresponding numerical statement about the scheme
morphism: the morphism restricted to the whole source is a representative of its own germ, and
every other representative is an open restriction of it near the point, which changes neither
the fibre nor the residue field there.

With the three numbers thus identified, Stacks 04NQ is the dimension formula of Stacks 02FX,
parts (1) and (2) of Stacks 04NR are the corresponding parts of Stacks 02JS, part (3) of Stacks
04NR is additivity of the transcendence degree of a tower of residue fields (Stacks 030H), the
three parts of Stacks 04NS are the three parts of Stacks 02FY, and Stacks 04NT and Stacks 04NU
are Stacks 02FZ and Stacks 02G0 transported along a surjective étale chart, which is
continuous, open and surjective on points by Stacks 03BX and Stacks 03H5.

The three parts of Stacks 04NS all read on one pair of compatible pointed charts, produced by
`AlgebraicGeometry.Space.exists_etaleChartAtPoint_pair_of_isPullback` from the compatible étale
charts of a fibre product; part (2) is stated with the common difference as an explicit summand
rather than as a difference, which is what makes its nonnegativity part of the statement
instead of an extra clause about truncated subtraction in `ℕ∞`.

All three parts of Stacks 04NR read on one commuting pair of chart morphisms, produced by
`AlgebraicGeometry.Space.exists_compatible_etale_charts_comp`; for parts (1) and (2) the
comparison of all three relative dimensions, and of flatness at the point, with the
corresponding germ conditions on those chart morphisms is
`AlgebraicGeometry.Space.exists_chartMorphisms_reading_comp`. The flatness hypothesis of part
(2) refers to the fibres over a field-valued representative of the image point, which are
presented by two cartesian squares rather than by chosen fibre-product objects; the relative
dimensions are carried to those fibres by part (1) of Stacks 04NS, so the general case follows
from the case of a morphism which is itself flat at the point.

Stacks 04NV identifies the chart condition for relative dimension `0` with the chart condition
for the germ form of local quasi-finiteness, which is quasi-finiteness at a point by Stacks
040Z; on a chart both are Stacks 0397. The canonical open subspace of Stacks 04NW is then the
open set of Stacks 04NT for `n = 0`, read as an open subspace through the order isomorphism of
Stacks 03BZ, and its base-change compatibility is part (1) of Stacks 04NS on points.

The bounded-dimension locus is written as the set of points at which *some* dimension value
`d ≤ n` is attained, rather than by a dimension function: the invariants of Stacks 04NM are
predicates, and quantifying over their values existentially is what makes the locus meaningful
without first proving that a value exists at every point.

## References

* [Stacks Project, Tag 04NQ](https://stacks.math.columbia.edu/tag/04NQ)
* [Stacks Project, Tag 04NR](https://stacks.math.columbia.edu/tag/04NR)
* [Stacks Project, Tag 04NS](https://stacks.math.columbia.edu/tag/04NS)
* [Stacks Project, Tag 04NT](https://stacks.math.columbia.edu/tag/04NT)
* [Stacks Project, Tag 04NU](https://stacks.math.columbia.edu/tag/04NU)
* [Stacks Project, Tag 04NV](https://stacks.math.columbia.edu/tag/04NV)
* [Stacks Project, Tag 04NW](https://stacks.math.columbia.edu/tag/04NW)
* [Stacks Project, Tag 06LS](https://stacks.math.columbia.edu/tag/06LS)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-! ### The dimension of the local ring of a fibre, read on a morphism of schemes -/

/-! ### The dimension of a fibre, read on a morphism of schemes -/

/-- Restricting a morphism of schemes to an open subscheme does not change the local dimension
of the fibre through a point of that open. -/
private theorem fiberDimension_comp_openImmersion {U X Y : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (f : X ⟶ Y) (x : U) :
    topologicalKrullDimAt ((j ≫ f).fiber ((j ≫ f) x)) ((j ≫ f).asFiber x) =
      topologicalKrullDimAt (f.fiber (f (j x))) (f.asFiber (j x)) := by
  have : Etale j := HasRingHomProperty.of_isOpenImmersion RingHom.Etale.containsIdentities
  have : Etale (𝟙 Y) := inferInstance
  exact topologicalKrullDimAt_fiber_eq_of_etale_square (j ≫ f) j (𝟙 Y) f (by simp) x

/-! ### The residue-field transcendence degree, read on a morphism of schemes -/

namespace MorphismOfGerms

/-- The residue-field transcendence degree of the germ of a composite of morphisms of schemes
is the sum of the degrees of the germs of its two factors: the three residue fields form a
tower, and the transcendence degree of a tower is additive (Stacks 030H). -/
@[sga "6 X 1.5" "partial"]
private theorem hasResidueFieldTranscendenceDegree_comp_ofSchemeHom {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) (r s : ℕ∞)
    (hr : HasResidueFieldTranscendenceDegree r (ofSchemeHom f x))
    (hs : HasResidueFieldTranscendenceDegree s (ofSchemeHom g (f x))) :
    HasResidueFieldTranscendenceDegree (r + s) (ofSchemeHom (f ≫ g) x) := by
  let _ : Algebra (Y.residueField (f x)) (X.residueField x) :=
    (f.residueFieldMap x).hom.toAlgebra
  let _ : Algebra (Z.residueField (g (f x))) (Y.residueField (f x)) :=
    (g.residueFieldMap (f x)).hom.toAlgebra
  let _ : Algebra (Z.residueField (g (f x))) (X.residueField x) :=
    ((f ≫ g).residueFieldMap x).hom.toAlgebra
  have _ : IsScalarTower (Z.residueField (g (f x))) (Y.residueField (f x))
      (X.residueField x) := IsScalarTower.of_algebraMap_eq fun z => by
    change ((f ≫ g).residueFieldMap x).hom z =
      (f.residueFieldMap x).hom ((g.residueFieldMap (f x)).hom z)
    rw [Scheme.residueFieldMap_comp]
    rfl
  have hadd := trdeg_add_eq (Z.residueField (g (f x))) (Y.residueField (f x))
    (A := X.residueField x)
  refine (hasResidueFieldTranscendenceDegree_ofSchemeHom_iff (f ≫ g) x (r + s)).mpr ?_
  change Cardinal.toENat (Algebra.trdeg (Z.residueField (g (f x))) (X.residueField x)) = r + s
  rw [← hadd, map_add,
    (hasResidueFieldTranscendenceDegree_ofSchemeHom_iff g (f x) s).mp hs,
    (hasResidueFieldTranscendenceDegree_ofSchemeHom_iff f x r).mp hr, add_comm]

end MorphismOfGerms

/-- Reading the transcendence degree of the residue-field extension of a morphism of schemes at
a point is compatible with replacing that point by an equal one. -/
private theorem trdeg_residueField_congr_point {X Y : Scheme.{u}} (f : X ⟶ Y) {x x' : X}
    (h : x = x') :
    letI := (f.residueFieldMap x).hom.toAlgebra
    letI := (f.residueFieldMap x').hom.toAlgebra
    Algebra.trdeg (Y.residueField (f x)) (X.residueField x) =
      Algebra.trdeg (Y.residueField (f x')) (X.residueField x') := by
  subst h
  rfl

/-! ### Fibres over a subsingleton target -/

/-- When the target is a subsingleton the scheme-theoretic fibre of a morphism of schemes is
the whole source, so the local dimension of the fibre is the local dimension of the source. -/
private theorem topologicalKrullDimAt_fiber_eq_of_subsingleton {U V : Scheme.{u}}
    [Subsingleton V] (q : U ⟶ V) (x : U) :
    topologicalKrullDimAt (q.fiber (q x)) (q.asFiber x) = topologicalKrullDimAt U x := by
  let s : Set U := q ⁻¹' {q x}
  have hs : s = Set.univ := by
    ext z
    simp only [Set.mem_univ, iff_true]
    exact Subsingleton.elim _ _
  have hxs : x ∈ s := rfl
  let e₁ := q.fiberHomeo (q x)
  let e₂ : ↥s ≃ₜ U := (Homeomorph.setCongr hs).trans (Homeomorph.Set.univ U)
  let e : q.fiber (q x) ≃ₜ U := e₁.trans e₂
  have hfi : e₁ (q.asFiber x) = ⟨x, hxs⟩ := Subtype.ext (Scheme.Hom.fiberι_asFiber q x)
  have hp : e (q.asFiber x) = x := by
    dsimp only [e, e₂, Homeomorph.trans_apply]
    rw [hfi]
    change ((Homeomorph.setCongr hs) (⟨x, hxs⟩ : s) : Set.univ) = x
    rfl
  rw [topologicalKrullDimAt_eq_of_homeomorph e (q.asFiber x), hp]

/-- The germ of a morphism of schemes with a subsingleton target has fibre dimension `0` at a
point at which the source has local dimension `0`. -/
private theorem hasFiberDimensionAt_zero_of_subsingleton {U V : Scheme.{u}} [Subsingleton V]
    (q : U ⟶ V) (x : U) (hdim : topologicalKrullDimAt U x = 0) :
    HasFiberDimensionAt 0 (MorphismOfGerms.ofSchemeHom q x) := by
  refine (hasFiberDimensionAt_ofSchemeHom_iff q x 0).2 ?_
  rw [topologicalKrullDimAt_fiber_eq_of_subsingleton, hdim]
  rfl

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for pullbacks of presheaves on the big fppf site over `S` is slow
/-- Pullbacks of presheaves on the big fppf site over `S` (instance search times out
without this shortcut). -/
private instance hasPullbacks_presheaf_fibreDimension :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

/-- Pullbacks of presheaves on the big fppf site over `S` (instance search times out without
this shortcut). -/
private instance (priority := high) hasPullback_presheaf_fibreDimension
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-- Every point of the source of a morphism of algebraic spaces over `S` has a relative
dimension. On a pointed étale chart at the point (Stacks 04NC) the relative dimension is the
local dimension of the fibre of the chart map, and that is not `⊥`, because the point lies in
every open neighbourhood whose dimension the defining infimum ranges over.

No finite-type hypothesis is needed: the invariant of Stacks 04NM is defined for an arbitrary
morphism. -/
theorem exists_hasRelativeDimensionAt (hF : IsAlgebraicSpace B S hS F)
    (hG : IsAlgebraicSpace B S hS G) (f : F ⟶ G) (x : points B S hS F) :
    ∃ d : ℕ∞, HasRelativeDimensionAt d B S hS f x := by
  obtain ⟨c⟩ := exists_etaleChartAtPoint B S hS hF hG f x
  let f₀ := (BigFppfOver.toScheme B S hS).map c.h
  let z := c.sourcePoint B S hS
  have hne := topologicalKrullDimAt_ne_bot (f₀.asFiber z)
  refine ⟨(topologicalKrullDimAt (f₀.fiber (f₀ z)) (f₀.asFiber z)).unbot hne, ?_⟩
  refine (holdsOnEveryEtaleChartAtPoint_iff_of_chart B S hS (@HasFiberDimensionAt.{u} _)
    (fiberDimensionAt_isEtaleLocalOnSourceAndTarget _) f x c).2 ?_
  rw [hasFiberDimensionAt_ofSchemeHom_iff, WithBot.coe_unbot]

/-- **Stacks 04NQ.** For a morphism of algebraic spaces over `S` which is locally of finite
type, the relative dimension at a point is the dimension of the local ring of the fibre there
plus the transcendence degree of the point over its image.

The three invariants of Stacks 04NM are chart conditions, so all three are read off one pointed
étale chart at the point (Stacks 04NC); on the resulting morphism of schemes the identity is
the dimension formula of Stacks 02FX. -/
@[stacks 04NQ]
theorem relativeDimensionAt_eq_fiberLocalRingDimension_add_transcendenceDegreeAt
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G)
    (f : F ⟶ G) (x : points B S hS F) (hf : IsLocallyOfFiniteType B S hS f)
    (d e r : ℕ∞) (hd : HasRelativeDimensionAt d B S hS f x)
    (he : HasFiberLocalRingDimension e B S hS hF hG f x)
    (hr : HasTranscendenceDegreeAt B S hS f x r) : d = e + r := by
  obtain ⟨c⟩ := exists_etaleChartAtPoint B S hS hF hG f x
  let f₀ := (BigFppfOver.toScheme B S hS).map c.h
  let u := c.sourcePoint B S hS
  have : LocallyOfFiniteType f₀ :=
    hf c.U c.V c.a c.b c.h c.a_etale c.b_etale c.comm
  let _ : Algebra (((BigFppfOver.toScheme B S hS).obj c.V).residueField (f₀ u))
      (((BigFppfOver.toScheme B S hS).obj c.U).residueField u) :=
    (f₀.residueFieldMap u).hom.toAlgebra
  have hdim : topologicalKrullDimAt (f₀.fiber (f₀ u)) (f₀.asFiber u) = (d : WithBot ℕ∞) :=
    (hasFiberDimensionAt_ofSchemeHom_iff f₀ u d).mp (hd c)
  have hloc : ringKrullDim ((f₀.fiber (f₀ u)).presheaf.stalk (f₀.asFiber u)) =
      (e : WithBot ℕ∞) :=
    (hasFiberLocalRingDimension_ofSchemeHom_iff f₀ u e).mp (he c)
  have htr : Cardinal.toENat (Algebra.trdeg
      (((BigFppfOver.toScheme B S hS).obj c.V).residueField (f₀ u))
      (((BigFppfOver.toScheme B S hS).obj c.U).residueField u)) = r :=
    (MorphismOfGerms.hasResidueFieldTranscendenceDegree_ofSchemeHom_iff f₀ u r).mp (hr c)
  have hformula := topologicalKrullDimAt_fiber_eq_krullDimOfRing_stalk_add_trdeg f₀ u
  rw [hdim, hloc, htr] at hformula
  exact_mod_cast hformula

/-- **Additivity of the transcendence degree at a point**, part (3) of Stacks 04NR. For
composable morphisms `f : X ⟶ Y` and `g : Y ⟶ Z` of algebraic spaces over `S` and a point `x`
of `X`, the transcendence degree of `x` over its image under `f ≫ g` is the sum of the
transcendence degree of `x` over `f x` and of `f x` over `g (f x)`.

Compatible étale charts for the composite
(`AlgebraicGeometry.Space.exists_compatible_etale_charts_comp`) read all three transcendence
degrees on a single commuting pair of chart morphisms `α` and `β` of the site; on the resulting
morphisms of schemes the three residue fields form a tower and the transcendence degree of a
tower is additive.

The source assumes `f` and `g` locally of finite type; that is not needed, neither for the
chart comparison nor for the tower identity. -/
@[stacks 04NR "part (3): additivity of the transcendence degree"]
theorem hasTranscendenceDegreeAt_comp {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hZ : IsAlgebraicSpace B S hS Z) (f : X ⟶ Y) (g : Y ⟶ Z) (x : points B S hS X)
    (r s : ℕ∞) (hr : HasTranscendenceDegreeAt B S hS f x r)
    (hs : HasTranscendenceDegreeAt B S hS g (pointsMap B S hS X f x) s) :
    HasTranscendenceDegreeAt B S hS (f ≫ g) x (r + s) := by
  obtain ⟨U, V, W, a, b, c, α, β, u, v, w, _, _, _, _, _, _, _, _, _, hαu, _, _, _,
    _, _, _, htα, htβ, htcomp⟩ :=
    exists_compatible_etale_charts_comp B S hS hX hY hZ f g x
  obtain ⟨p, rfl⟩ := Quot.exists_rep u
  let T := BigFppfOver.toScheme B S hS
  let t : Spec (.of p.carrier) := IsLocalRing.closedPoint p.carrier
  let pV := FieldValuedPoint.map B S hS (yoneda.obj U) (yoneda.map α) p
  have hpV : pV.class B S hS (yoneda.obj V) = v := hαu
  subst hpV
  let cα := etaleChartAtPointOfId B S hS U V α p t
  let cβ := etaleChartAtPointOfId B S hS V W β pV t
  let cαβ := etaleChartAtPointOfId B S hS U W (α ≫ β) p t
  let u₀ : T.obj U := cα.sourcePoint B S hS
  have hβsource : cβ.sourcePoint B S hS = T.map α u₀ :=
    schemePoint_map_yoneda B S hS α p
  have hα : MorphismOfGerms.HasResidueFieldTranscendenceDegree r
      (MorphismOfGerms.ofSchemeHom (T.map α) u₀) :=
    (holdsOnEveryEtaleChartAtPoint_iff_of_chart B S hS
      (@MorphismOfGerms.HasResidueFieldTranscendenceDegree.{u} r)
      (MorphismOfGerms.residueFieldTranscendenceDegree_isEtaleLocalOnSourceAndTarget r)
      (yoneda.map α) (p.class B S hS (yoneda.obj U)) cα).mp ((htα r).mp hr)
  have hβ : MorphismOfGerms.HasResidueFieldTranscendenceDegree s
      (MorphismOfGerms.ofSchemeHom (T.map β) (T.map α u₀)) := by
    rw [← hβsource]
    exact (holdsOnEveryEtaleChartAtPoint_iff_of_chart B S hS
      (@MorphismOfGerms.HasResidueFieldTranscendenceDegree.{u} s)
      (MorphismOfGerms.residueFieldTranscendenceDegree_isEtaleLocalOnSourceAndTarget s)
      (yoneda.map β) (pV.class B S hS (yoneda.obj V)) cβ).mp ((htβ s).mp hs)
  refine (htcomp (r + s)).mpr ((holdsOnEveryEtaleChartAtPoint_iff_of_chart B S hS
    (@MorphismOfGerms.HasResidueFieldTranscendenceDegree.{u} (r + s))
    (MorphismOfGerms.residueFieldTranscendenceDegree_isEtaleLocalOnSourceAndTarget (r + s))
    (yoneda.map (α ≫ β)) (p.class B S hS (yoneda.obj U)) cαβ).mpr ?_)
  change MorphismOfGerms.HasResidueFieldTranscendenceDegree (r + s)
    (MorphismOfGerms.ofSchemeHom (T.map (α ≫ β)) u₀)
  rw [T.map_comp]
  exact MorphismOfGerms.hasResidueFieldTranscendenceDegree_comp_ofSchemeHom
    (T.map α) (T.map β) u₀ r s hα hβ

/-- **Compatible étale charts for a composite, read on the chart morphisms.** Two composable
morphisms of algebraic spaces over `S` which are locally of finite type, together with a point
`x` of the source, admit chart morphisms `α` and `β` of the site and a point `u₀` of the source
chart over `x` such that the induced morphisms of schemes are locally of finite type and the
relative dimension of each of `f`, `g` and `f ≫ g` at the corresponding point is the germ-level
fibre dimension of the corresponding morphism of schemes at `u₀`; flatness of `f` at `x`
becomes flatness of the germ of the first chart morphism.

Compatible étale charts (`AlgebraicGeometry.Space.exists_compatible_etale_charts_comp`) give
the charts and the three comparisons of relative dimensions; a field-valued representative of
`x` turns each chart morphism into a pointed chart of itself
(`AlgebraicGeometry.Space.etaleChartAtPointOfId`), on which the chart condition of Stacks 04NC
is the germ property at the selected scheme point. -/
private theorem exists_chartMorphisms_reading_comp {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hZ : IsAlgebraicSpace B S hS Z) (f : X ⟶ Y) (g : Y ⟶ Z) (x : points B S hS X)
    (hf : IsLocallyOfFiniteType B S hS f) (hg : IsLocallyOfFiniteType B S hS g) :
    ∃ (U V W : BigFppfOver B S hS) (α : U ⟶ V) (β : V ⟶ W)
        (u₀ : (BigFppfOver.toScheme B S hS).obj U),
      LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map α) ∧
      LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map β) ∧
      (∀ d : ℕ∞, HasRelativeDimensionAt d B S hS f x ↔
        HasFiberDimensionAt d
          (MorphismOfGerms.ofSchemeHom ((BigFppfOver.toScheme B S hS).map α) u₀)) ∧
      (∀ d : ℕ∞, HasRelativeDimensionAt d B S hS g (pointsMap B S hS X f x) ↔
        HasFiberDimensionAt d (MorphismOfGerms.ofSchemeHom
          ((BigFppfOver.toScheme B S hS).map β)
          ((BigFppfOver.toScheme B S hS).map α u₀))) ∧
      (∀ d : ℕ∞, HasRelativeDimensionAt d B S hS (f ≫ g) x ↔
        HasFiberDimensionAt d (MorphismOfGerms.ofSchemeHom
          ((BigFppfOver.toScheme B S hS).map α ≫
            (BigFppfOver.toScheme B S hS).map β) u₀)) ∧
      (IsFlatAt B S hS f x → MorphismOfGerms.IsFlat
        (MorphismOfGerms.ofSchemeHom ((BigFppfOver.toScheme B S hS).map α) u₀)) := by
  obtain ⟨U, V, W, a, b, c, α, β, u, v, w, _, haEtale, _, hbEtale, _, hcEtale,
      hcommF, hcommG, hu, hαu, _, _, _, hdimF, hdimG, hdimComp, _, _, _⟩ :=
    exists_compatible_etale_charts_comp B S hS hX hY hZ f g x
  obtain ⟨p, rfl⟩ := Quot.exists_rep u
  let T := BigFppfOver.toScheme B S hS
  let t : Spec (.of p.carrier) := IsLocalRing.closedPoint p.carrier
  let pV := FieldValuedPoint.map B S hS (yoneda.obj U) (yoneda.map α) p
  have hpV : pV.class B S hS (yoneda.obj V) = v := hαu
  subst hpV
  let cα := etaleChartAtPointOfId B S hS U V α p t
  let cβ := etaleChartAtPointOfId B S hS V W β pV t
  let cαβ := etaleChartAtPointOfId B S hS U W (α ≫ β) p t
  let chartF : EtaleChartAtPoint B S hS f x :=
    { U := U, V := V, a := a, b := b, h := α
      a_etale := haEtale, b_etale := hbEtale, comm := hcommF
      representative := p, point := t, maps_to := hu }
  let u₀ : T.obj U := cα.sourcePoint B S hS
  have hβsource : cβ.sourcePoint B S hS = T.map α u₀ :=
    schemePoint_map_yoneda B S hS α p
  have hftα : LocallyOfFiniteType (T.map α) := hf U V a b α haEtale hbEtale hcommF
  have hftβ : LocallyOfFiniteType (T.map β) := hg V W b c β hbEtale hcEtale hcommG
  refine ⟨U, V, W, α, β, u₀, hftα, hftβ, fun d => ?_, fun d => ?_, fun d => ?_, fun hflat => ?_⟩
  · exact (hdimF d).trans (holdsOnEveryEtaleChartAtPoint_iff_of_chart B S hS
      (@HasFiberDimensionAt.{u} d) (fiberDimensionAt_isEtaleLocalOnSourceAndTarget d)
      (yoneda.map α) (p.class B S hS (yoneda.obj U)) cα)
  · exact (hdimG d).trans ((holdsOnEveryEtaleChartAtPoint_iff_of_chart B S hS
      (@HasFiberDimensionAt.{u} d) (fiberDimensionAt_isEtaleLocalOnSourceAndTarget d)
      (yoneda.map β) (pV.class B S hS (yoneda.obj V)) cβ).trans
      (by rw [hβsource]; exact Iff.rfl))
  · refine (hdimComp d).trans ((holdsOnEveryEtaleChartAtPoint_iff_of_chart B S hS
      (@HasFiberDimensionAt.{u} d) (fiberDimensionAt_isEtaleLocalOnSourceAndTarget d)
      (yoneda.map (α ≫ β)) (p.class B S hS (yoneda.obj U)) cαβ).trans ?_)
    change HasFiberDimensionAt d (MorphismOfGerms.ofSchemeHom (T.map (α ≫ β)) u₀) ↔ _
    rw [T.map_comp]
  · exact hflat chartF

/-- **Stacks 04NR, part (1).** For composable morphisms of algebraic spaces over `S` which are
locally of finite type, the relative dimension of the composite at a point is at most the sum of
the relative dimension of the first morphism there and of the second morphism at the image
point.

Compatible étale charts for the composite read all three relative dimensions as fibre
dimensions of a pair of composable morphisms of schemes at one point, where the inequality is
part of Stacks 02JS. -/
@[stacks 04NR "part (1): the relative dimension of a composite is at most the sum"]
theorem hasRelativeDimensionAt_comp_le_add {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hZ : IsAlgebraicSpace B S hS Z) (f : X ⟶ Y) (g : Y ⟶ Z) (x : points B S hS X)
    (hf : IsLocallyOfFiniteType B S hS f) (hg : IsLocallyOfFiniteType B S hS g) (d e n : ℕ∞)
    (hd : HasRelativeDimensionAt d B S hS f x)
    (he : HasRelativeDimensionAt e B S hS g (pointsMap B S hS X f x))
    (hn : HasRelativeDimensionAt n B S hS (f ≫ g) x) : n ≤ d + e := by
  obtain ⟨U, V, W, α, β, u₀, hftα, hftβ, hbF, hbG, hbComp, -⟩ :=
    exists_chartMorphisms_reading_comp B S hS hX hY hZ f g x hf hg
  let T := BigFppfOver.toScheme B S hS
  have : LocallyOfFiniteType (T.map α) := hftα
  have : LocallyOfFiniteType (T.map β) := hftβ
  have hsum := topologicalKrullDimAt_fiber_comp_le_add (T.map α) (T.map β) u₀
  rw [(hasFiberDimensionAt_ofSchemeHom_iff (T.map α) u₀ d).mp ((hbF d).mp hd),
    (hasFiberDimensionAt_ofSchemeHom_iff (T.map β) (T.map α u₀) e).mp ((hbG e).mp he),
    (hasFiberDimensionAt_ofSchemeHom_iff (T.map α ≫ T.map β) u₀ n).mp ((hbComp n).mp hn)]
    at hsum
  exact_mod_cast hsum

/-- **Stacks 04NR, part (1).** The composite of two morphisms of algebraic spaces over `S` which
are locally of finite type has a relative dimension at every point of its source, and that
dimension is at most the sum of the relative dimensions of the two factors. -/
@[stacks 04NR "part (1): the relative dimension of a composite is at most the sum"]
theorem exists_hasRelativeDimensionAt_comp_le_add {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hZ : IsAlgebraicSpace B S hS Z) (f : X ⟶ Y) (g : Y ⟶ Z) (x : points B S hS X)
    (hf : IsLocallyOfFiniteType B S hS f) (hg : IsLocallyOfFiniteType B S hS g) (d e : ℕ∞)
    (hd : HasRelativeDimensionAt d B S hS f x)
    (he : HasRelativeDimensionAt e B S hS g (pointsMap B S hS X f x)) :
    ∃ n : ℕ∞, HasRelativeDimensionAt n B S hS (f ≫ g) x ∧ n ≤ d + e := by
  obtain ⟨n, hn⟩ := exists_hasRelativeDimensionAt B S hS hX hZ (f ≫ g) x
  exact ⟨n, hn, hasRelativeDimensionAt_comp_le_add B S hS hX hY hZ f g x hf hg d e n hd he hn⟩

/-- **Stacks 04NR, part (2), special case.** The inequality of part (1) is an equality as soon as
the first morphism is flat at the point.

On compatible étale charts for the composite this is the corresponding part of Stacks 02JS,
flatness of `f` at `x` becoming flatness of the first chart morphism at the selected scheme
point. -/
@[stacks 04NR "part (2): equality when the first morphism is flat at the point"]
theorem hasRelativeDimensionAt_comp_of_isFlatAt {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hZ : IsAlgebraicSpace B S hS Z) (f : X ⟶ Y) (g : Y ⟶ Z) (x : points B S hS X)
    (hf : IsLocallyOfFiniteType B S hS f) (hg : IsLocallyOfFiniteType B S hS g) (d e : ℕ∞)
    (hd : HasRelativeDimensionAt d B S hS f x)
    (he : HasRelativeDimensionAt e B S hS g (pointsMap B S hS X f x))
    (hflat : IsFlatAt B S hS f x) :
    HasRelativeDimensionAt (d + e) B S hS (f ≫ g) x := by
  obtain ⟨U, V, W, α, β, u₀, hftα, hftβ, hbF, hbG, hbComp, hbFlat⟩ :=
    exists_chartMorphisms_reading_comp B S hS hX hY hZ f g x hf hg
  let T := BigFppfOver.toScheme B S hS
  have : LocallyOfFiniteType (T.map α) := hftα
  have : LocallyOfFiniteType (T.map β) := hftβ
  refine (hbComp (d + e)).mpr
    ((hasFiberDimensionAt_ofSchemeHom_iff (T.map α ≫ T.map β) u₀ (d + e)).mpr ?_)
  have hsum := topologicalKrullDimAt_fiber_comp_eq_add_of_isFlatAt (T.map α) (T.map β) u₀
    (flatAt_of_isFlat_germ (T.map α) u₀ (hbFlat hflat))
  rw [(hasFiberDimensionAt_ofSchemeHom_iff (T.map α) u₀ d).mp ((hbF d).mp hd),
    (hasFiberDimensionAt_ofSchemeHom_iff (T.map β) (T.map α u₀) e).mp ((hbG e).mp he)] at hsum
  rw [hsum]
  push_cast
  rfl

/-! ### Base change -/

/-- **Compatible pointed étale charts for a morphism and its base change.** In a cartesian
square of algebraic spaces over `S` whose right vertical arrow `f` is locally of finite type, a
point `x'` of the source of the base change `f'` has a pointed étale chart of `f` at the
image of `x'` and a pointed étale chart of `f'` at `x'` whose two chart morphisms sit in a
cartesian square of schemes, the scheme point selected by the second lying over the scheme
point selected by the first, and the two source charts commuting with the horizontal arrow of
the original square.

Compatible étale charts for the square (`AlgebraicGeometry.Space.exists_compatible_etale_charts`)
give a cartesian square of schemes `U ×_V V' ⟶ U` over `V' ⟶ V` whose top corner is a
surjective étale chart of the fibre product; a field-valued point of that chart lying over `x'`
turns the two squares into the two pointed charts, with corresponding selected scheme points.

The fourth corner `X'` need not be algebraic: the charts are produced from an atlas of the
other three corners and transported along the canonical isomorphism `X' ≅ X ×_Y Y'`. -/
theorem exists_etaleChartAtPoint_pair_of_isPullback
    {X' X Y' Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : IsPullback g' f' f g)
    (hX : IsAlgebraicSpace B S hS X) (hY' : IsAlgebraicSpace B S hS Y')
    (hY : IsAlgebraicSpace B S hS Y)
    (hf : IsLocallyOfFiniteType B S hS f) (x' : points B S hS X') :
    ∃ (c : EtaleChartAtPoint B S hS f (pointsMap B S hS X' g' x'))
        (c' : EtaleChartAtPoint B S hS f' x') (pU : c'.U ⟶ c.U) (q : c'.V ⟶ c.V),
      IsPullback ((BigFppfOver.toScheme B S hS).map pU)
          ((BigFppfOver.toScheme B S hS).map c'.h)
          ((BigFppfOver.toScheme B S hS).map c.h)
          ((BigFppfOver.toScheme B S hS).map q) ∧
        LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map c.h) ∧
        c.sourcePoint B S hS =
          (BigFppfOver.toScheme B S hS).map pU (c'.sourcePoint B S hS) ∧
        c'.a ≫ g' = yoneda.map pU ≫ c.a := by
  let T := BigFppfOver.toScheme B S hS
  let Q := MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u}) T
  have _ : Q.IsStableUnderBaseChange :=
    inverseImage_isStableUnderBaseChange B S hS Etale.etale_isStableUnderBaseChange
  have _ : Q.IsStableUnderComposition :=
    inverseImage_isStableUnderComposition B S hS etale_isStableUnderComposition.{u}
  have _ : Q.presheaf.IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange Q
  have _ : Q.presheaf.IsStableUnderComposition :=
    MorphismProperty.relative_isStableUnderComposition Q
  obtain ⟨U, V, U', V', p, q, pU, pV', v, a, b, c, hcharts, hap, _, hcX, hcY,
      _, hvEtale, _, haEtale, _, hbEtale, hcSurj, hcEtale⟩ :=
    exists_compatible_etale_charts B S hS
      (ObjectProperty.homMk f : (⟨X, hX⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Y, hY⟩)
      (ObjectProperty.homMk g : (⟨Y', hY'⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Y, hY⟩)
  simp only [ObjectProperty.homMk_hom] at hap hcX hcY
  let e : X' ≅ pullback f g := sq.isoPullback
  obtain ⟨z, hz⟩ :=
    (surjective_iff_surjective_pointsMap B S hS (pullback f g)
      (isAlgebraicSpace_pullback B S hS f g hX hY' hY) U' c).mp hcSurj
      (pointsMap B S hS X' e.hom x')
  obtain ⟨r, rfl⟩ := Quot.exists_rep z
  have hAEtale : Q.presheaf (a ≫ pullback.snd v f) :=
    MorphismProperty.IsStableUnderComposition.comp_mem a (pullback.snd v f) haEtale
      (MorphismProperty.IsStableUnderBaseChange.of_isPullback
        (IsPullback.of_hasPullback v f) hvEtale)
  have hBEtale : Q.presheaf (b ≫ pullback.snd v g) :=
    MorphismProperty.IsStableUnderComposition.comp_mem b (pullback.snd v g) hbEtale
      (MorphismProperty.IsStableUnderBaseChange.of_isPullback
        (IsPullback.of_hasPullback v g) hvEtale)
  have hcXEtale : Q.presheaf (c ≫ e.inv) :=
    have _ : Q.presheaf.RespectsIso := inferInstance
    MorphismProperty.RespectsIso.postcomp Q.presheaf e.inv c hcEtale
  have hcommF : yoneda.map p ≫ v = (a ≫ pullback.snd v f) ≫ f := by
    calc
      yoneda.map p ≫ v = (a ≫ pullback.fst v f) ≫ v := by rw [← hap]
      _ = (a ≫ pullback.snd v f) ≫ f := by
        simp only [Category.assoc, pullback.condition]
  have hcommF' : yoneda.map pV' ≫ (b ≫ pullback.snd v g) = (c ≫ e.inv) ≫ f' := by
    calc
      yoneda.map pV' ≫ (b ≫ pullback.snd v g) = c ≫ pullback.snd f g := by
        simpa only [Category.assoc] using hcY.symm
      _ = (c ≫ e.inv) ≫ f' := by
        rw [← IsPullback.isoPullback_inv_snd sq]
        simp only [e, Category.assoc]
  let chartF : EtaleChartAtPoint B S hS f (pointsMap B S hS X' g' x') :=
    { U := U
      V := V
      a := a ≫ pullback.snd v f
      b := v
      h := p
      a_etale := hAEtale
      b_etale := hvEtale
      comm := hcommF
      representative := FieldValuedPoint.map B S hS (yoneda.obj U') (yoneda.map pU) r
      point := IsLocalRing.closedPoint r.carrier
      maps_to := by
        change pointsMap B S hS (yoneda.obj U) (a ≫ pullback.snd v f)
          (pointsMap B S hS (yoneda.obj U') (yoneda.map pU)
            (r.class B S hS (yoneda.obj U'))) = pointsMap B S hS X' g' x'
        calc
          _ = pointsMap B S hS (yoneda.obj U') (c ≫ pullback.fst f g)
              (r.class B S hS (yoneda.obj U')) := by
            rw [hcX]
            exact congrFun (pointsMap_comp B S hS (yoneda.obj U') (yoneda.map pU)
              (a ≫ pullback.snd v f)).symm _
          _ = pointsMap B S hS X' (e.hom ≫ pullback.fst f g) x' := by
            rw [pointsMap_comp, pointsMap_comp]
            exact congrArg (pointsMap B S hS (pullback f g) (pullback.fst f g)) hz
          _ = pointsMap B S hS X' g' x' := by rw [IsPullback.isoPullback_hom_fst] }
  let chartF' : EtaleChartAtPoint B S hS f' x' :=
    { U := U'
      V := V'
      a := c ≫ e.inv
      b := b ≫ pullback.snd v g
      h := pV'
      a_etale := hcXEtale
      b_etale := hBEtale
      comm := hcommF'
      representative := r
      point := IsLocalRing.closedPoint r.carrier
      maps_to := by
        calc
          _ = pointsMap B S hS (pullback f g) e.inv
              (pointsMap B S hS (yoneda.obj U') c (r.class B S hS (yoneda.obj U'))) :=
            congrFun (pointsMap_comp B S hS (yoneda.obj U') c e.inv) _
          _ = pointsMap B S hS (pullback f g) e.inv
              (pointsMap B S hS X' e.hom x') := by rw [hz]
          _ = x' := by
            rw [← Function.comp_apply (f := pointsMap B S hS (pullback f g) e.inv),
              ← pointsMap_comp, e.hom_inv_id, pointsMap_id, id_eq] }
  refine ⟨chartF, chartF', pU, q, hcharts,
    hf U V (a ≫ pullback.snd v f) v p hAEtale hvEtale hcommF,
    schemePoint_map_yoneda B S hS pU r, ?_⟩
  change (c ≫ e.inv) ≫ g' = yoneda.map pU ≫ a ≫ pullback.snd v f
  rw [Category.assoc, show e.inv ≫ g' = pullback.fst f g from
    IsPullback.isoPullback_inv_fst sq]
  exact hcX

/-- **Invariance of relative dimension under base change**, part (1) of Stacks 04NS. In a
cartesian square of algebraic spaces over `S` whose right vertical arrow `f` is locally of
finite type, the relative dimension of the base change `f'` at a point `x'` of its source is
the relative dimension of `f` at the image of `x'`.

Read on the compatible pointed charts of
`AlgebraicGeometry.Space.exists_etaleChartAtPoint_pair_of_isPullback`, each side is the
dimension of the fibre of a morphism of schemes at corresponding points of a cartesian square,
which is part (1) of Stacks 02FY.

The source assumes all four corners of the square algebraic; the fourth corner `X'` need not
be, because the two chart conditions are compared on charts supplied as data rather than on
charts produced from an atlas. -/
@[stacks 04NS "part (1): invariance of the relative dimension under base change"]
theorem hasRelativeDimensionAt_iff_of_isPullback {X' X Y' Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : IsPullback g' f' f g)
    (hX : IsAlgebraicSpace B S hS X) (hY' : IsAlgebraicSpace B S hS Y')
    (hY : IsAlgebraicSpace B S hS Y)
    (hf : IsLocallyOfFiniteType B S hS f) (x' : points B S hS X') (d : ℕ∞) :
    HasRelativeDimensionAt d B S hS f (pointsMap B S hS X' g' x') ↔
      HasRelativeDimensionAt d B S hS f' x' := by
  obtain ⟨c, c', pU, q, hsq, hft, hpoint, -⟩ :=
    exists_etaleChartAtPoint_pair_of_isPullback B S hS sq hX hY' hY hf x'
  have _ : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map c.h) := hft
  have hfiber := topologicalKrullDimAt_fiber_eq_of_isPullback hsq (c'.sourcePoint B S hS)
  change HoldsOnEveryEtaleChartAtPoint B S hS (@HasFiberDimensionAt.{u} d) f
      (pointsMap B S hS X' g' x') ↔
    HoldsOnEveryEtaleChartAtPoint B S hS (@HasFiberDimensionAt.{u} d) f' x'
  rw [holdsOnEveryEtaleChartAtPoint_iff_of_chart B S hS (@HasFiberDimensionAt.{u} d)
      (fiberDimensionAt_isEtaleLocalOnSourceAndTarget d) f _ c,
    holdsOnEveryEtaleChartAtPoint_iff_of_chart B S hS (@HasFiberDimensionAt.{u} d)
      (fiberDimensionAt_isEtaleLocalOnSourceAndTarget d) f' x' c',
    hasFiberDimensionAt_ofSchemeHom_iff ((BigFppfOver.toScheme B S hS).map c.h)
      (c.sourcePoint B S hS) d,
    hasFiberDimensionAt_ofSchemeHom_iff ((BigFppfOver.toScheme B S hS).map c'.h)
      (c'.sourcePoint B S hS) d, hpoint, hfiber]

/-- A cartesian square of presheaves with algebraic corners is cartesian among algebraic spaces. -/
private theorem isPullback_homMk {X' X Y' Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : IsPullback g' f' f g)
    (hX' : IsAlgebraicSpace B S hS X') (hX : IsAlgebraicSpace B S hS X)
    (hY' : IsAlgebraicSpace B S hS Y') (hY : IsAlgebraicSpace B S hS Y) :
    IsPullback
      (ObjectProperty.homMk g' : (⟨X', hX'⟩ : AlgebraicSpaces B S hS) ⟶ ⟨X, hX⟩)
      (ObjectProperty.homMk f' : (⟨X', hX'⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Y', hY'⟩)
      (ObjectProperty.homMk f : (⟨X, hX⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Y, hY⟩)
      (ObjectProperty.homMk g : (⟨Y', hY'⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Y, hY⟩) :=
  IsPullback.of_map_of_faithful (F := ObjectProperty.ι _) sq

/-- The base change of a morphism locally of finite type, in a cartesian square of algebraic
spaces, is locally of finite type. -/
private theorem isLocallyOfFiniteType_of_isPullback' {X' X Y' Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : IsPullback g' f' f g)
    (hX' : IsAlgebraicSpace B S hS X') (hX : IsAlgebraicSpace B S hS X)
    (hY' : IsAlgebraicSpace B S hS Y') (hY : IsAlgebraicSpace B S hS Y)
    (hf : IsLocallyOfFiniteType B S hS f) : IsLocallyOfFiniteType B S hS f' :=
  (isLocallyOfFiniteType_isStableUnderBaseChange B S hS).of_isPullback
    (isPullback_homMk B S hS sq hX' hX hY' hY) hf

/-- The dimension of the local ring of the fibre plus the transcendence degree at a point takes
the same value for the base change `f'` at a point `x'` as for `f` at the image of `x'`: both
sums are the relative dimension by Stacks 04NQ, and the relative dimension is the same on the
two sides by part (1) of Stacks 04NS. -/
private theorem fiberLocalRingDimension_add_transcendenceDegreeAt_eq_of_isPullback
    {X' X Y' Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : IsPullback g' f' f g)
    (hX' : IsAlgebraicSpace B S hS X') (hX : IsAlgebraicSpace B S hS X)
    (hY' : IsAlgebraicSpace B S hS Y') (hY : IsAlgebraicSpace B S hS Y)
    (hf : IsLocallyOfFiniteType B S hS f) (x' : points B S hS X') (e r e' r' : ℕ∞)
    (he : HasFiberLocalRingDimension e B S hS hX hY f (pointsMap B S hS X' g' x'))
    (hr : HasTranscendenceDegreeAt B S hS f (pointsMap B S hS X' g' x') r)
    (he' : HasFiberLocalRingDimension e' B S hS hX' hY' f' x')
    (hr' : HasTranscendenceDegreeAt B S hS f' x' r') :
    e + r = e' + r' := by
  have hf' : IsLocallyOfFiniteType B S hS f' :=
    isLocallyOfFiniteType_of_isPullback' B S hS sq hX' hX hY' hY hf
  obtain ⟨d, hd⟩ := exists_hasRelativeDimensionAt B S hS hX hY f (pointsMap B S hS X' g' x')
  have hd' : HasRelativeDimensionAt d B S hS f' x' :=
    (hasRelativeDimensionAt_iff_of_isPullback B S hS sq hX hY' hY hf x' d).1 hd
  rw [← relativeDimensionAt_eq_fiberLocalRingDimension_add_transcendenceDegreeAt B S hS hX hY
      f (pointsMap B S hS X' g' x') hf d e r hd he hr,
    ← relativeDimensionAt_eq_fiberLocalRingDimension_add_transcendenceDegreeAt B S hS hX' hY'
      f' x' hf' d e' r' hd' he' hr']

/-- The transcendence degree at a point of the source of a morphism of algebraic spaces over
`S` which is locally of finite type is finite: on a pointed étale chart it is the transcendence
degree of a residue-field extension which is essentially of finite type. -/
private theorem transcendenceDegreeAt_ne_top (hF : IsAlgebraicSpace B S hS F)
    (hG : IsAlgebraicSpace B S hS G) (f : F ⟶ G) (hf : IsLocallyOfFiniteType B S hS f)
    (x : points B S hS F) (r : ℕ∞) (hr : HasTranscendenceDegreeAt B S hS f x r) : r ≠ ⊤ := by
  obtain ⟨c⟩ := exists_etaleChartAtPoint B S hS hF hG f x
  have _ : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map c.h) :=
    hf c.U c.V c.a c.b c.h c.a_etale c.b_etale c.comm
  obtain ⟨m, hm⟩ := MorphismOfGerms.exists_natCast_hasResidueFieldTranscendenceDegree
    ((BigFppfOver.toScheme B S hS).map c.h) (c.sourcePoint B S hS)
  rw [MorphismOfGerms.hasResidueFieldTranscendenceDegree_unique (hr c) hm]
  exact ENat.natCast_ne_top m

/-- **Part (2) of Stacks 04NS.** In a cartesian square of algebraic spaces over `S` whose right
vertical arrow `f` is locally of finite type, the dimension gained by the local ring of the
fibre at a point `x'` of the source of the base change, over its value for `f` at the image of
`x'`, is the transcendence degree lost there; in particular the common difference is
nonnegative, which is why it is recorded as a summand `n` rather than as a difference.

The transcendence degrees are compared on the compatible pointed charts of
`AlgebraicGeometry.Space.exists_etaleChartAtPoint_pair_of_isPullback`, where the drop is part
(2) of Stacks 02FY for the resulting cartesian square of schemes; the sum of the two invariants
is the relative dimension (Stacks 04NQ) and so agrees on the two sides by part (1) of Stacks
04NS, which turns that drop into the gain of the other invariant. The transcendence degree at
`x'` is finite, so it cancels. -/
@[stacks 04NS "part (2): the gain in the dimension of the local ring of the fibre is the loss \
in transcendence degree"]
theorem exists_fiberLocalRingDimension_add_eq_of_isPullback
    {X' X Y' Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : IsPullback g' f' f g)
    (hX' : IsAlgebraicSpace B S hS X') (hX : IsAlgebraicSpace B S hS X)
    (hY' : IsAlgebraicSpace B S hS Y') (hY : IsAlgebraicSpace B S hS Y)
    (hf : IsLocallyOfFiniteType B S hS f) (x' : points B S hS X') (e r e' r' : ℕ∞)
    (he : HasFiberLocalRingDimension e B S hS hX hY f (pointsMap B S hS X' g' x'))
    (hr : HasTranscendenceDegreeAt B S hS f (pointsMap B S hS X' g' x') r)
    (he' : HasFiberLocalRingDimension e' B S hS hX' hY' f' x')
    (hr' : HasTranscendenceDegreeAt B S hS f' x' r') :
    ∃ n : ℕ∞, e + n = e' ∧ r' + n = r := by
  have hf' : IsLocallyOfFiniteType B S hS f' :=
    isLocallyOfFiniteType_of_isPullback' B S hS sq hX' hX hY' hY hf
  have hle : r' ≤ r := by
    obtain ⟨c, c', pU, q, hsq, hft, hpoint, -⟩ :=
      exists_etaleChartAtPoint_pair_of_isPullback B S hS sq hX hY' hY hf x'
    let T := BigFppfOver.toScheme B S hS
    have _ : LocallyOfFiniteType (T.map c.h) := hft
    have hrc : MorphismOfGerms.HasResidueFieldTranscendenceDegree r
        (MorphismOfGerms.ofSchemeHom (T.map c.h)
          (T.map pU (c'.sourcePoint B S hS))) := by
      rw [← hpoint]
      exact hr c
    let _ : Algebra
        ((T.obj c.V).residueField ((T.map c.h) (T.map pU (c'.sourcePoint B S hS))))
        ((T.obj c.U).residueField (T.map pU (c'.sourcePoint B S hS))) :=
      ((T.map c.h).residueFieldMap (T.map pU (c'.sourcePoint B S hS))).hom.toAlgebra
    let _ : Algebra ((T.obj c'.V).residueField ((T.map c'.h) (c'.sourcePoint B S hS)))
        ((T.obj c'.U).residueField (c'.sourcePoint B S hS)) :=
      ((T.map c'.h).residueFieldMap (c'.sourcePoint B S hS)).hom.toAlgebra
    have htr := (MorphismOfGerms.hasResidueFieldTranscendenceDegree_ofSchemeHom_iff
      (T.map c.h) (T.map pU (c'.sourcePoint B S hS)) r).mp hrc
    have htr' := (MorphismOfGerms.hasResidueFieldTranscendenceDegree_ofSchemeHom_iff
      (T.map c'.h) (c'.sourcePoint B S hS) r').mp (hr' c')
    rw [← htr, ← htr']
    exact OrderHomClass.mono Cardinal.toENat
      (trdeg_residueField_le_of_baseChange hsq (c'.sourcePoint B S hS))
  obtain ⟨n, hn⟩ := exists_add_of_le hle
  have hsum := fiberLocalRingDimension_add_transcendenceDegreeAt_eq_of_isPullback B S hS sq
    hX' hX hY' hY hf x' e r e' r' he hr he' hr'
  have hcancel : e + n + r' = e' + r' := by
    rw [add_right_comm, add_assoc, ← hn, hsum]
  exact ⟨n, WithTop.add_right_cancel
    (transcendenceDegreeAt_ne_top B S hS hX' hY' f' hf' x' r' hr') hcancel, hn.symm⟩

/-- **Part (2) of Stacks 04NS.** Base change does not decrease the dimension of the local ring
of the fibre at a point. -/
@[stacks 04NS "part (2): the dimension of the local ring of the fibre does not decrease"]
theorem fiberLocalRingDimension_le_of_isPullback
    {X' X Y' Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : IsPullback g' f' f g)
    (hX' : IsAlgebraicSpace B S hS X') (hX : IsAlgebraicSpace B S hS X)
    (hY' : IsAlgebraicSpace B S hS Y') (hY : IsAlgebraicSpace B S hS Y)
    (hf : IsLocallyOfFiniteType B S hS f) (x' : points B S hS X') (e r e' r' : ℕ∞)
    (he : HasFiberLocalRingDimension e B S hS hX hY f (pointsMap B S hS X' g' x'))
    (hr : HasTranscendenceDegreeAt B S hS f (pointsMap B S hS X' g' x') r)
    (he' : HasFiberLocalRingDimension e' B S hS hX' hY' f' x')
    (hr' : HasTranscendenceDegreeAt B S hS f' x' r') : e ≤ e' := by
  obtain ⟨n, hn, -⟩ :=
    exists_fiberLocalRingDimension_add_eq_of_isPullback
      B S hS sq hX' hX hY' hY hf x' e r e' r' he hr he' hr'
  exact hn ▸ le_self_add

/-- **Part (2) of Stacks 04NS.** Base change does not increase the transcendence degree of a
point over its image. -/
@[stacks 04NS "part (2): the transcendence degree does not increase"]
theorem transcendenceDegreeAt_le_of_isPullback
    {X' X Y' Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : IsPullback g' f' f g)
    (hX' : IsAlgebraicSpace B S hS X') (hX : IsAlgebraicSpace B S hS X)
    (hY' : IsAlgebraicSpace B S hS Y') (hY : IsAlgebraicSpace B S hS Y)
    (hf : IsLocallyOfFiniteType B S hS f) (x' : points B S hS X') (e r e' r' : ℕ∞)
    (he : HasFiberLocalRingDimension e B S hS hX hY f (pointsMap B S hS X' g' x'))
    (hr : HasTranscendenceDegreeAt B S hS f (pointsMap B S hS X' g' x') r)
    (he' : HasFiberLocalRingDimension e' B S hS hX' hY' f' x')
    (hr' : HasTranscendenceDegreeAt B S hS f' x' r') : r' ≤ r := by
  obtain ⟨n, -, hn⟩ :=
    exists_fiberLocalRingDimension_add_eq_of_isPullback
      B S hS sq hX' hX hY' hY hf x' e r e' r' he hr he' hr'
  exact hn ▸ le_self_add

/-- The scheme point selected by a pointed étale chart is the scheme point underlying its
field-valued representative: the spectrum of a field is a one-point space, so the chosen point
of it is its closed point. -/
private theorem schemePoint_representative_eq_sourcePoint
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : X ⟶ Y} {x : points B S hS X}
    (c : EtaleChartAtPoint B S hS f x) :
    schemePoint B S hS c.U c.representative = c.sourcePoint B S hS :=
  have _ : Subsingleton (Spec (.of c.representative.carrier)) := inferInstance
  congrArg ((BigFppfOver.toScheme B S hS).map c.representative.value)
    (Subsingleton.elim _ c.point)

/-- **Part (3) of Stacks 04NS.** In a cartesian square of algebraic spaces over `S` whose right
vertical arrow `f` is locally of finite type, a point `x` of `X` and a point `y'` of `Y'` with
the same image in `Y` have a common lift `x'` to `X'` at which the dimension of the local ring
of the fibre and the transcendence degree both take the value they take at `x` — that is, at
which the common difference of part (2) vanishes.

Some common lift exists because the point set of a fibre product surjects onto the fibre product
of the point sets (Stacks 03H4). On the compatible pointed charts at such a lift
(`AlgebraicGeometry.Space.exists_etaleChartAtPoint_pair_of_isPullback`) part (3) of Stacks 02FY
replaces the scheme point selected by the chart of the base change by one lying over the same
two points at which both invariants are preserved; the same chart with that point as its
representative is a pointed chart at its image in `X'`, and that image is the required lift,
because the two source charts commute with the horizontal arrow of the square. -/
@[stacks 04NS "part (3): a common lift at which both invariants are preserved"]
theorem exists_point_preserving_fiberLocalRingDimension_and_trdeg
    {X' X Y' Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : IsPullback g' f' f g)
    (hX' : IsAlgebraicSpace B S hS X') (hX : IsAlgebraicSpace B S hS X)
    (hY' : IsAlgebraicSpace B S hS Y') (hY : IsAlgebraicSpace B S hS Y)
    (hf : IsLocallyOfFiniteType B S hS f) (x : points B S hS X) (y' : points B S hS Y')
    (hxy : pointsMap B S hS X f x = pointsMap B S hS Y' g y') :
    ∃ x' : points B S hS X', pointsMap B S hS X' g' x' = x ∧
      pointsMap B S hS X' f' x' = y' ∧
      (∀ d : ℕ∞, HasFiberLocalRingDimension d B S hS hX hY f x ↔
        HasFiberLocalRingDimension d B S hS hX' hY' f' x') ∧
      (∀ r : ℕ∞, HasTranscendenceDegreeAt B S hS f x r ↔
        HasTranscendenceDegreeAt B S hS f' x' r) := by
  have hcat := isPullback_homMk B S hS sq hX' hX hY' hY
  obtain ⟨x₀, hx₀, hy₀⟩ := exists_point_of_isPullback B S hS hcat x y' hxy
  simp only [ObjectProperty.homMk_hom] at hx₀ hy₀
  subst hx₀
  obtain ⟨c, c', pU, q, hsq, hft, hpoint, hcomm⟩ :=
    exists_etaleChartAtPoint_pair_of_isPullback B S hS sq hX hY' hY hf x₀
  set T := BigFppfOver.toScheme B S hS with hT
  have _ : LocallyOfFiniteType (T.map c.h) := hft
  set u' := c'.sourcePoint B S hS with hu'
  have hw : T.map c.h (T.map pU u') = T.map q (T.map c'.h u') := by
    have hh := congrArg (fun m : T.obj c'.U ⟶ T.obj c.V => m u') hsq.w
    simpa only [Scheme.Hom.comp_apply] using hh
  obtain ⟨w, hwU, hwV, hwdim, hwtr⟩ :=
    exists_pullback_point_preserving_fibre_dimension_and_trdeg hsq (T.map c'.h u')
      (T.map pU u') hw
  set ρ := schemePointRepresentative B S hS c'.U w with hρ
  have hρw : schemePoint B S hS c'.U ρ = w := schemePointRepresentative_point B S hS c'.U w
  let c'' : EtaleChartAtPoint B S hS f'
      (pointsMap B S hS (yoneda.obj c'.U) c'.a (ρ.class B S hS (yoneda.obj c'.U))) :=
    { U := c'.U
      V := c'.V
      a := c'.a
      b := c'.b
      h := c'.h
      a_etale := c'.a_etale
      b_etale := c'.b_etale
      comm := c'.comm
      representative := ρ
      point := IsLocalRing.closedPoint ρ.carrier
      maps_to := rfl }
  have hc'' : c''.sourcePoint B S hS = w := hρw
  -- moving the representative of the chart of the base change does not move either image
  have hmove {W : BigFppfOver B S hS} (k : c'.U ⟶ W) (hk : T.map k w = T.map k u') :
      pointsMap B S hS (yoneda.obj c'.U) (yoneda.map k) (ρ.class B S hS (yoneda.obj c'.U)) =
        pointsMap B S hS (yoneda.obj c'.U) (yoneda.map k)
          (c'.representative.class B S hS (yoneda.obj c'.U)) := by
    refine injective_pointsToScheme B S hS _ ?_
    rw [pointsToScheme_pointsMap, pointsToScheme_pointsMap]
    rw [show pointsToScheme B S hS c'.U (ρ.class B S hS (yoneda.obj c'.U)) = w from hρw,
      show pointsToScheme B S hS c'.U
          (c'.representative.class B S hS (yoneda.obj c'.U)) = u' from
        schemePoint_representative_eq_sourcePoint B S hS c']
    exact hk
  refine ⟨pointsMap B S hS (yoneda.obj c'.U) c'.a (ρ.class B S hS (yoneda.obj c'.U)),
    ?_, ?_, fun d => ?_, fun r => ?_⟩
  · calc pointsMap B S hS X' g'
          (pointsMap B S hS (yoneda.obj c'.U) c'.a (ρ.class B S hS (yoneda.obj c'.U)))
        = pointsMap B S hS (yoneda.obj c'.U) (c'.a ≫ g')
            (ρ.class B S hS (yoneda.obj c'.U)) :=
          (congrFun (pointsMap_comp B S hS (yoneda.obj c'.U) c'.a g') _).symm
      _ = pointsMap B S hS (yoneda.obj c.U) c.a
            (pointsMap B S hS (yoneda.obj c'.U) (yoneda.map pU)
              (ρ.class B S hS (yoneda.obj c'.U))) := by
          rw [hcomm]
          exact congrFun (pointsMap_comp B S hS (yoneda.obj c'.U) (yoneda.map pU) c.a) _
      _ = pointsMap B S hS (yoneda.obj c.U) c.a
            (c.representative.class B S hS (yoneda.obj c.U)) := by
          rw [hmove pU hwU]
          refine congrArg (pointsMap B S hS (yoneda.obj c.U) c.a) ?_
          refine injective_pointsToScheme B S hS _ ?_
          rw [pointsToScheme_pointsMap,
            show pointsToScheme B S hS c'.U
                (c'.representative.class B S hS (yoneda.obj c'.U)) = u' from
              schemePoint_representative_eq_sourcePoint B S hS c',
            show pointsToScheme B S hS c.U
                (c.representative.class B S hS (yoneda.obj c.U)) =
              c.sourcePoint B S hS from schemePoint_representative_eq_sourcePoint B S hS c]
          exact hpoint.symm
      _ = pointsMap B S hS X' g' x₀ := c.maps_to
  · have hstep (σ : FieldValuedPoint B S hS (yoneda.obj c'.U)) :
        pointsMap B S hS X' f'
            (pointsMap B S hS (yoneda.obj c'.U) c'.a (σ.class B S hS (yoneda.obj c'.U))) =
          pointsMap B S hS (yoneda.obj c'.V) c'.b
            (pointsMap B S hS (yoneda.obj c'.U) (yoneda.map c'.h)
              (σ.class B S hS (yoneda.obj c'.U))) :=
      calc pointsMap B S hS X' f'
            (pointsMap B S hS (yoneda.obj c'.U) c'.a (σ.class B S hS (yoneda.obj c'.U)))
          = pointsMap B S hS (yoneda.obj c'.U) (c'.a ≫ f')
              (σ.class B S hS (yoneda.obj c'.U)) :=
            (congrFun (pointsMap_comp B S hS (yoneda.obj c'.U) c'.a f') _).symm
        _ = pointsMap B S hS (yoneda.obj c'.U) (yoneda.map c'.h ≫ c'.b)
              (σ.class B S hS (yoneda.obj c'.U)) := by rw [c'.comm]
        _ = _ := congrFun (pointsMap_comp B S hS (yoneda.obj c'.U) (yoneda.map c'.h) c'.b) _
    rw [hstep ρ, hmove c'.h hwV, ← hstep c'.representative, c'.maps_to, hy₀]
  · have hdimeq :
        ringKrullDim (((T.map c.h).fiber ((T.map c.h) (c.sourcePoint B S hS))).presheaf.stalk
            ((T.map c.h).asFiber (c.sourcePoint B S hS))) =
          ringKrullDim (((T.map c'.h).fiber ((T.map c'.h) w)).presheaf.stalk
            ((T.map c'.h).asFiber w)) := by
      rw [hpoint, ← ringKrullDim_stalk_fiberHomeo_symm (T.map c.h) (T.map pU u')
          (T.map q (T.map c'.h u')) hw,
        ← ringKrullDim_stalk_fiberHomeo_symm (T.map c'.h) w (T.map c'.h u') hwV]
      exact hwdim.symm
    change HoldsOnEveryEtaleChartAtPoint B S hS
        (@_root_.AlgebraicGeometry.HasFiberLocalRingDimension.{u} d) f
        (pointsMap B S hS X' g' x₀) ↔
      HoldsOnEveryEtaleChartAtPoint B S hS
        (@_root_.AlgebraicGeometry.HasFiberLocalRingDimension.{u} d) f' _
    rw [holdsOnEveryEtaleChartAtPoint_iff_of_chart B S hS
        (@_root_.AlgebraicGeometry.HasFiberLocalRingDimension.{u} d)
        (fiberLocalRingDimension_isEtaleLocalOnSourceAndTarget d) f _ c,
      holdsOnEveryEtaleChartAtPoint_iff_of_chart B S hS
        (@_root_.AlgebraicGeometry.HasFiberLocalRingDimension.{u} d)
        (fiberLocalRingDimension_isEtaleLocalOnSourceAndTarget d) f' _ c'',
      hasFiberLocalRingDimension_ofSchemeHom_iff (T.map c.h) (c.sourcePoint B S hS) d,
      hasFiberLocalRingDimension_ofSchemeHom_iff (T.map c''.h) (c''.sourcePoint B S hS) d,
      hc'', hdimeq]
  · have htreq :
        let := ((T.map c.h).residueFieldMap (c.sourcePoint B S hS)).hom.toAlgebra
        let := ((T.map c''.h).residueFieldMap (c''.sourcePoint B S hS)).hom.toAlgebra
        Algebra.trdeg ((T.obj c.V).residueField ((T.map c.h) (c.sourcePoint B S hS)))
            ((T.obj c.U).residueField (c.sourcePoint B S hS)) =
          Algebra.trdeg ((T.obj c'.V).residueField ((T.map c''.h) (c''.sourcePoint B S hS)))
            ((T.obj c'.U).residueField (c''.sourcePoint B S hS)) := by
      refine (trdeg_residueField_congr_point (T.map c.h) hpoint).trans ?_
      refine ((trdeg_residueFieldMap_congr (T.map c.h) (T.map pU u')
        (T.map q (T.map c'.h u')) hw).symm.trans (hwtr.trans
          (trdeg_residueFieldMap_congr (T.map c'.h) w (T.map c'.h u') hwV))).trans ?_
      exact trdeg_residueField_congr_point (T.map c'.h) hc''.symm
    change HoldsOnEveryEtaleChartAtPoint B S hS
        (@MorphismOfGerms.HasResidueFieldTranscendenceDegree.{u} r) f
        (pointsMap B S hS X' g' x₀) ↔
      HoldsOnEveryEtaleChartAtPoint B S hS
        (@MorphismOfGerms.HasResidueFieldTranscendenceDegree.{u} r) f' _
    rw [holdsOnEveryEtaleChartAtPoint_iff_of_chart B S hS
        (@MorphismOfGerms.HasResidueFieldTranscendenceDegree.{u} r)
        (MorphismOfGerms.residueFieldTranscendenceDegree_isEtaleLocalOnSourceAndTarget r) f _ c,
      holdsOnEveryEtaleChartAtPoint_iff_of_chart B S hS
        (@MorphismOfGerms.HasResidueFieldTranscendenceDegree.{u} r)
        (MorphismOfGerms.residueFieldTranscendenceDegree_isEtaleLocalOnSourceAndTarget r) f' _
        c'',
      MorphismOfGerms.hasResidueFieldTranscendenceDegree_ofSchemeHom_iff (T.map c.h)
        (c.sourcePoint B S hS) r,
      MorphismOfGerms.hasResidueFieldTranscendenceDegree_ofSchemeHom_iff (T.map c''.h)
        (c''.sourcePoint B S hS) r, htreq]

/-! ### Equality of relative dimensions along a composite -/

/-- **Stacks 04NR, part (2).** The inequality of part (1) is an equality as soon as the morphism
of field-valued fibres over the image point is flat at a point above `x`: here `Xk` and `Yk` are
the fibres of `X` and `Y` over a field-valued representative `p` of the image of `x` in `Z`,
presented by the two cartesian squares, `x'` is a point of `Xk` above `x`, and `Xk ⟶ Yk` is flat
at `x'`.

Relative dimension is invariant under base change (part (1) of Stacks 04NS), so all three
relative dimensions may be read on the fibres over `p`, where the first morphism is flat at the
chosen point and `AlgebraicGeometry.Space.hasRelativeDimensionAt_comp_of_isFlatAt` applies. The
fibres are algebraic because they are fibre products of algebraic spaces (Stacks 02X2), and the
two morphisms between them are locally of finite type because being so is stable under base
change (Stacks 03XH).

No chosen fibre-product objects are imposed: the two squares are cartesian squares of arbitrary
presheaves, which is why neither fibre is assumed algebraic. -/
@[stacks 04NR "part (2): equality when the morphism of field-valued fibres is flat"]
theorem hasRelativeDimensionAt_comp_of_isFlatAt_fibre
    {X Y Z Xk Yk : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hZ : IsAlgebraicSpace B S hS Z) (f : X ⟶ Y) (g : Y ⟶ Z) (x : points B S hS X)
    (hf : IsLocallyOfFiniteType B S hS f) (hg : IsLocallyOfFiniteType B S hS g) (d e : ℕ∞)
    (hd : HasRelativeDimensionAt d B S hS f x)
    (he : HasRelativeDimensionAt e B S hS g (pointsMap B S hS X f x))
    (p : FieldValuedPoint B S hS Z) (px : Xk ⟶ X) (py : Yk ⟶ Y)
    (qy : Yk ⟶ yoneda.obj (p.siteObject B S hS Z)) (fk : Xk ⟶ Yk) (x' : points B S hS Xk)
    (hpx : IsPullback px fk f py)
    (hpy : IsPullback py qy g (yonedaEquiv.symm p.value))
    (hx : pointsMap B S hS Xk px x' = x) (hflat : IsFlatAt B S hS fk x') :
    HasRelativeDimensionAt (d + e) B S hS (f ≫ g) x := by
  have hZk : IsAlgebraicSpace B S hS (yoneda.obj (p.siteObject B S hS Z)) :=
    isAlgebraicSpace_yoneda B S hS (p.siteObject B S hS Z)
  have hYk : IsAlgebraicSpace B S hS Yk :=
    isAlgebraicSpace_of_iso B S hS hpy.isoPullback.symm
      (isAlgebraicSpace_pullback B S hS g (yonedaEquiv.symm p.value) hY hZk hZ)
  have hXk : IsAlgebraicSpace B S hS Xk :=
    isAlgebraicSpace_of_iso B S hS hpx.isoPullback.symm
      (isAlgebraicSpace_pullback B S hS f py hX hYk hY)
  have hfkLFT : IsLocallyOfFiniteType B S hS fk :=
    isLocallyOfFiniteType_of_isPullback' B S hS hpx hXk hX hYk hY hf
  have hqyLFT : IsLocallyOfFiniteType B S hS qy :=
    isLocallyOfFiniteType_of_isPullback' B S hS hpy hYk hY hZk hZ hg
  have hpointY : pointsMap B S hS Yk py (pointsMap B S hS Xk fk x') =
      pointsMap B S hS X f x := by
    have h₁ := congrFun (pointsMap_comp B S hS Xk fk py) x'
    have h₂ := congrFun (pointsMap_comp B S hS Xk px f) x'
    simp only [Function.comp_apply] at h₁ h₂
    rw [← hx, ← h₁, ← h₂, hpx.w]
  have hdk : HasRelativeDimensionAt d B S hS fk x' :=
    (hasRelativeDimensionAt_iff_of_isPullback B S hS hpx hX hYk hY hf x' d).mp (by rwa [hx])
  have hek : HasRelativeDimensionAt e B S hS qy (pointsMap B S hS Xk fk x') :=
    (hasRelativeDimensionAt_iff_of_isPullback B S hS hpy hY hZk hZ hg
      (pointsMap B S hS Xk fk x') e).mp (by rwa [hpointY])
  have hsum := hasRelativeDimensionAt_comp_of_isFlatAt B S hS hXk hYk hZk fk qy x'
    hfkLFT hqyLFT d e hdk hek hflat
  have hcomp : IsPullback px (fk ≫ qy) (f ≫ g) (yonedaEquiv.symm p.value) := by
    simpa only [Category.assoc] using hpx.paste_vert hpy
  rw [← hx]
  exact (hasRelativeDimensionAt_iff_of_isPullback B S hS hcomp hX hZk hZ
    (isLocallyOfFiniteType_comp B S hS hX hY hZ f g hf hg) x' (d + e)).mpr hsum

/-! ### The bounded relative-dimension locus -/

attribute [local instance] pointTopology

/-- The bounded-relative-dimension condition at a point of the source, read off a commuting
square of étale charts over a field-valued representative of that point: it is the bound on the
local dimension of the fibre of the morphism of charts at the selected scheme point. -/
private theorem exists_hasRelativeDimensionAt_le_iff_topologicalKrullDimAt_le (f : F ⟶ G)
    {U V : BigFppfOver B S hS} (a : yoneda.obj U ⟶ F) (b : yoneda.obj V ⟶ G) (α : U ⟶ V)
    (ha : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (hb : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf b)
    (hcomm : yoneda.map α ≫ b = a ≫ f)
    (p : FieldValuedPoint B S hS (yoneda.obj U)) (n : ℕ) :
    (∃ d : ℕ∞, d ≤ (n : ℕ∞) ∧ HasRelativeDimensionAt d B S hS f
        (pointsMap B S hS (yoneda.obj U) a (p.class B S hS (yoneda.obj U)))) ↔
      topologicalKrullDimAt
          (((BigFppfOver.toScheme B S hS).map α).fiber
            ((BigFppfOver.toScheme B S hS).map α (schemePoint B S hS U p)))
          (((BigFppfOver.toScheme B S hS).map α).asFiber (schemePoint B S hS U p)) ≤
        (n : WithBot ℕ∞) := by
  let c : EtaleChartAtPoint B S hS f
      (pointsMap B S hS (yoneda.obj U) a (p.class B S hS (yoneda.obj U))) :=
    { U := U
      V := V
      a := a
      b := b
      h := α
      a_etale := ha
      b_etale := hb
      comm := hcomm
      representative := p
      point := IsLocalRing.closedPoint p.carrier
      maps_to := rfl }
  have hc : c.sourcePoint B S hS = schemePoint B S hS U p := rfl
  constructor
  · rintro ⟨d, hd, hdim⟩
    rw [← hc, (hasFiberDimensionAt_ofSchemeHom_iff ((BigFppfOver.toScheme B S hS).map α)
      (c.sourcePoint B S hS) d).mp (hdim c)]
    exact WithBot.coe_le_coe.mpr hd
  · intro hle
    have hne := topologicalKrullDimAt_ne_bot
      (((BigFppfOver.toScheme B S hS).map α).asFiber (schemePoint B S hS U p))
    refine ⟨(topologicalKrullDimAt
        (((BigFppfOver.toScheme B S hS).map α).fiber
          ((BigFppfOver.toScheme B S hS).map α (schemePoint B S hS U p)))
        (((BigFppfOver.toScheme B S hS).map α).asFiber
          (schemePoint B S hS U p))).unbot hne, ?_, ?_⟩
    · exact WithBot.coe_le_coe.mp (by rwa [WithBot.coe_unbot])
    · refine (holdsOnEveryEtaleChartAtPoint_iff_of_chart B S hS
        (@HasFiberDimensionAt.{u} _) (fiberDimensionAt_isEtaleLocalOnSourceAndTarget _)
        f _ c).mpr ?_
      rw [hc, hasFiberDimensionAt_ofSchemeHom_iff, WithBot.coe_unbot]

/-- **Stacks 04NU.** For a morphism of algebraic spaces over `S` which is locally of finite
presentation and a natural number `n`, the open set of Stacks 04NT — the points of the source
at which the relative dimension is at most `n` — is retrocompact in the point space of Tag
03BU.

As for Stacks 04NT, a surjective étale chart `a` of the source lifted from an atlas of the
target reads the locus, point by point, as the bounded-fibre-dimension locus `Wₙ` of the
induced morphism of schemes, which is retrocompact by Stacks 02G0. Points of a represented
presheaf are homeomorphic to points of the representing scheme (Tag 03BX), so the preimage of
the locus under `|a|` is retrocompact; transporting that to the locus itself uses that `|a|` is
a continuous open surjection: a compact open `K` of the target is covered by the images of the
preimages of finitely many affine opens of the chart contained in the open `|a| ⁻¹' K`, and on
each of them the intersection with the locus is the image of a compact set. -/
@[stacks 04NU]
theorem isRetrocompact_setOf_exists_hasRelativeDimensionAt_le (hF : IsAlgebraicSpace B S hS F)
    (hG : IsAlgebraicSpace B S hS G) (f : F ⟶ G)
    (hf : IsLocallyOfFinitePresentation B S hS f) (n : ℕ) :
    IsRetrocompact {x : points B S hS F |
      ∃ d : ℕ∞, d ≤ (n : ℕ∞) ∧ HasRelativeDimensionAt d B S hS f x} := by
  classical
  obtain ⟨V, b, hbSurj, hbEtale⟩ := hG.exists_atlas
  obtain ⟨U, a, α, hcomm, haSurj, haEtale⟩ :=
    exists_surjective_etale_presentation_lift B S hS hF hG f V b hbSurj hbEtale
  let T := BigFppfOver.toScheme B S hS
  have _ : LocallyOfFinitePresentation (T.map α) :=
    hf U V a b α haEtale hbEtale hcomm.symm
  let h := schemePointsHomeomorph B S hS U
  let φ := pointsMap B S hS (yoneda.obj U) a
  let W := {x : points B S hS F |
    ∃ d : ℕ∞, d ≤ (n : ℕ∞) ∧ HasRelativeDimensionAt d B S hS f x}
  let Wₙ : Set (T.obj U) :=
    {z | topologicalKrullDimAt ((T.map α).fiber (T.map α z)) ((T.map α).asFiber z) ≤
      (n : WithBot ℕ∞)}
  have hWₙ : IsRetrocompact Wₙ := isRetrocompact_setOf_fiberDimensionAt_le (T.map α) n
  have hpre : φ ⁻¹' W = h ⁻¹' Wₙ := by
    ext y
    induction y using Quot.ind with
    | _ p =>
      have hhp : h (p.class B S hS (yoneda.obj U)) = schemePoint B S hS U p := rfl
      rw [Set.mem_preimage, Set.mem_preimage, hhp]
      exact exists_hasRelativeDimensionAt_le_iff_topologicalKrullDimAt_le B S hS f a b α
        haEtale hbEtale hcomm.symm p n
  have hφcont : Continuous φ := continuous_pointsMap B S hS a
  have hφopen : IsOpenMap φ := isOpenMap_pointsMap_of_etale B S hS hF U a haEtale
  intro K hKcompact hKopen
  have hKpre : IsOpen (φ ⁻¹' K) := hKopen.preimage hφcont
  have hDopen : IsOpen (h.symm ⁻¹' (φ ⁻¹' K)) := hKpre.preimage h.symm.continuous
  have hchoose (y : {y : points B S hS (yoneda.obj U) // φ y ∈ K}) :
      ∃ C : Set (T.obj U), IsOpen C ∧ IsCompact C ∧ h y.1 ∈ C ∧
        C ⊆ h.symm ⁻¹' (φ ⁻¹' K) := by
    obtain ⟨_, ⟨A, hA, rfl⟩, hyA, hAsub⟩ :=
      (T.obj U).isBasis_affineOpens.exists_subset_of_mem_open
        (show h y.1 ∈ h.symm ⁻¹' (φ ⁻¹' K) by
          simpa only [Set.mem_preimage, Homeomorph.symm_apply_apply] using y.2) hDopen
    exact ⟨A, A.2, hA.isCompact, hyA, hAsub⟩
  choose C hCopen hCcompact hmemC hCsub using hchoose
  have hsubK (y : {y : points B S hS (yoneda.obj U) // φ y ∈ K}) :
      h ⁻¹' C y ⊆ φ ⁻¹' K := fun z hz => by
    simpa only [Set.mem_preimage, Homeomorph.symm_apply_apply] using hCsub y hz
  have hcover : K ⊆ ⋃ y, φ '' (h ⁻¹' C y) := by
    intro x hx
    obtain ⟨y, rfl⟩ :=
      (surjective_iff_surjective_pointsMap B S hS F hF U a).mp haSurj x
    exact Set.mem_iUnion.mpr ⟨⟨y, hx⟩, ⟨y, hmemC ⟨y, hx⟩, rfl⟩⟩
  obtain ⟨t, ht⟩ := hKcompact.elim_finite_subcover (fun y => φ '' (h ⁻¹' C y))
    (fun y => hφopen _ ((hCopen y).preimage h.continuous)) hcover
  have hEq : W ∩ K = ⋃ y ∈ t, φ '' (h ⁻¹' (Wₙ ∩ C y)) := by
    ext x
    constructor
    · rintro ⟨hxW, hxK⟩
      obtain ⟨y, hyt, z, hzC, hzx⟩ := Set.mem_iUnion₂.mp (ht hxK)
      have hzW : z ∈ φ ⁻¹' W := by rwa [Set.mem_preimage, hzx]
      exact Set.mem_iUnion₂.mpr ⟨y, hyt, z, ⟨hpre.subset hzW, hzC⟩, hzx⟩
    · intro hx
      obtain ⟨y, _, z, hz, hzx⟩ := Set.mem_iUnion₂.mp hx
      have hzW : z ∈ φ ⁻¹' W := hpre.symm.subset hz.1
      have hzK : z ∈ φ ⁻¹' K := hsubK y hz.2
      rw [Set.mem_preimage, hzx] at hzW hzK
      exact ⟨hzW, hzK⟩
  rw [hEq]
  exact t.finite_toSet.isCompact_biUnion fun y _ =>
    ((h.isCompact_preimage.mpr (hWₙ (hCcompact y) (hCopen y))).image hφcont)

/-! ### The locally quasi-finite part -/

/-- Relative dimension at a point is unchanged by restricting the source to an open subspace
containing the point: a pointed chart for the restriction is a pointed chart for the morphism
and conversely, both squares having the same chart map. -/
private theorem hasRelativeDimensionAt_iff_of_isOpenSubspace
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (U : Subfunctor X) (hU : IsOpenSubspace B S hS U)
    (f : X ⟶ Y) (x' : points B S hS U.toFunctor) (d : ℕ∞) :
    HasRelativeDimensionAt d B S hS f (pointsMap B S hS U.toFunctor U.ι x') ↔
      HasRelativeDimensionAt d B S hS (U.ι ≫ f) x' := by
  refine ⟨fun hdim c => hdim (etaleChartAtPointOfOpenSubspace B S hS U hU f c), fun hdim => ?_⟩
  obtain ⟨c⟩ := exists_etaleChartAtPoint B S hS hU.1 hY (U.ι ≫ f) x'
  exact (holdsOnEveryEtaleChartAtPoint_iff_some B S hS (@HasFiberDimensionAt.{u} d)
    (fiberDimensionAt_isEtaleLocalOnSourceAndTarget d) hX hY f
    (pointsMap B S hS U.toFunctor U.ι x')).2
    ⟨etaleChartAtPointOfOpenSubspace B S hS U hU f c, hdim c⟩

/-- A point of the source of a morphism lies in the point set of the inverse image of a
subfunctor exactly when its image lies in the point set of that subfunctor. -/
private alias mem_range_pointsMap_preimage_iff :=
  AlgebraicGeometry.Space.mem_pointsRange_preimage_iff

/-- The point set of an open subspace, in the coerced form in which the order isomorphism of
Stacks 03BZ presents it. -/
private theorem coe_openSubspacesOrderIso (hF : IsAlgebraicSpace B S hS F)
    (U : {U : Subfunctor F // IsOpenSubspace B S hS U}) :
    ((openSubspacesOrderIso B S hS F hF U : TopologicalSpace.Opens (points B S hS F)) :
        Set (points B S hS F)) =
      Set.range (pointsMap B S hS U.1.toFunctor U.1.ι) :=
  openSubspacesOrderIso_apply B S hS F hF U

/-- **Stacks 04NW, the canonical open subspace.** The open subspace of the source of a morphism
of algebraic spaces over `S` which is locally of finite type cut out by the points of relative
dimension `0`; it is an open subspace by Stacks 04NT and Stacks 03BZ. -/
@[stacks 04NW "the canonical open subspace"]
noncomputable def locallyQuasiFinitePart (hF : IsAlgebraicSpace B S hS F)
    (hG : IsAlgebraicSpace B S hS G) (f : F ⟶ G) (hf : IsLocallyOfFiniteType B S hS f) :
    {U : Subfunctor F // IsOpenSubspace B S hS U} :=
  (openSubspacesOrderIso B S hS F hF).symm
    ⟨{x | ∃ d : ℕ∞, d ≤ (0 : ℕ∞) ∧ HasRelativeDimensionAt d B S hS f x},
      isOpen_setOf_hasRelativeDimensionAt_le B S hS hF hG f hf 0⟩

/-- **Stacks 04NW, the points of the canonical open subspace.** A point of the source lies in
the point set of `AlgebraicGeometry.Space.locallyQuasiFinitePart` exactly when the relative
dimension there is `0`. -/
@[stacks 04NW "the points of the canonical open subspace"]
theorem mem_range_pointsMap_locallyQuasiFinitePart_iff (hF : IsAlgebraicSpace B S hS F)
    (hG : IsAlgebraicSpace B S hS G) (f : F ⟶ G) (hf : IsLocallyOfFiniteType B S hS f)
    (x : points B S hS F) :
    x ∈ Set.range (pointsMap B S hS (locallyQuasiFinitePart B S hS hF hG f hf).1.toFunctor
        (locallyQuasiFinitePart B S hS hF hG f hf).1.ι) ↔
      HasRelativeDimensionAt 0 B S hS f x := by
  have hrange : Set.range (pointsMap B S hS
      (locallyQuasiFinitePart B S hS hF hG f hf).1.toFunctor
      (locallyQuasiFinitePart B S hS hF hG f hf).1.ι) =
      {x | ∃ d : ℕ∞, d ≤ (0 : ℕ∞) ∧ HasRelativeDimensionAt d B S hS f x} := by
    simpa only [locallyQuasiFinitePart, OrderIso.apply_symm_apply] using
      (openSubspacesOrderIso_apply B S hS F hF
        (locallyQuasiFinitePart B S hS hF hG f hf)).symm
  rw [hrange]
  refine ⟨fun ⟨d, hd, hdim⟩ => ?_, fun hdim => ⟨0, le_rfl, hdim⟩⟩
  simpa only [le_antisymm hd bot_le] using hdim

/-- **Stacks 04NW, local quasi-finiteness of the restriction.** The restriction of the morphism
to `AlgebraicGeometry.Space.locallyQuasiFinitePart` is locally quasi-finite.

Every point of the open subspace has relative dimension `0` for the restricted morphism,
because relative dimension is unchanged by restricting the source to an open subspace, so this
is Stacks 04NV for the restriction. -/
@[stacks 04NW "local quasi-finiteness of the restriction"]
theorem isLocallyQuasiFinite_locallyQuasiFinitePart (hF : IsAlgebraicSpace B S hS F)
    (hG : IsAlgebraicSpace B S hS G) (f : F ⟶ G) (hf : IsLocallyOfFiniteType B S hS f) :
    IsLocallyQuasiFinite B S hS ((locallyQuasiFinitePart B S hS hF hG f hf).1.ι ≫ f) := by
  set U := locallyQuasiFinitePart B S hS hF hG f hf with hU
  have hft : IsLocallyOfFiniteType B S hS (U.1.ι ≫ f) :=
    isLocallyOfFiniteType_comp B S hS U.2.1 hF hG U.1.ι f
      (isLocallyOfFiniteType_of_isEtale B S hS hF (isEtale_ι_of_isOpenSubspace U.2)) hf
  refine (isLocallyQuasiFinite_iff_forall_hasRelativeDimensionAt_zero B S hS
    (U.1.ι ≫ f) hft).2 fun x' => ?_
  exact (hasRelativeDimensionAt_iff_of_isOpenSubspace B S hS hF hG U.1 U.2 f x' 0).1
    ((mem_range_pointsMap_locallyQuasiFinitePart_iff B S hS hF hG f hf _).1 ⟨x', rfl⟩)

/-- **Stacks 04NW, positive relative dimension outside the canonical open subspace.** At a point
of the source which is not in the point set of
`AlgebraicGeometry.Space.locallyQuasiFinitePart` the relative dimension is at least `1`: a
relative dimension exists there, and were it `0` the point would lie in that point set. -/
@[stacks 04NW "positive relative dimension outside the canonical open subspace"]
theorem exists_one_le_hasRelativeDimensionAt_of_not_mem_locallyQuasiFinitePart
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G) (f : F ⟶ G)
    (hf : IsLocallyOfFiniteType B S hS f) (x : points B S hS F)
    (hx : x ∉ Set.range (pointsMap B S hS
      (locallyQuasiFinitePart B S hS hF hG f hf).1.toFunctor
      (locallyQuasiFinitePart B S hS hF hG f hf).1.ι)) :
    ∃ d : ℕ∞, 1 ≤ d ∧ HasRelativeDimensionAt d B S hS f x := by
  obtain ⟨d, hd⟩ := exists_hasRelativeDimensionAt B S hS hF hG f x
  refine ⟨d, Order.one_le_iff_ne_zero.mpr fun hzero => hx ?_, hd⟩
  exact (mem_range_pointsMap_locallyQuasiFinitePart_iff B S hS hF hG f hf x).2 (hzero ▸ hd)

/-- **Stacks 04NW, maximality.** Every open subspace of the source over which the morphism is
locally quasi-finite is contained in
`AlgebraicGeometry.Space.locallyQuasiFinitePart`; together with
`AlgebraicGeometry.Space.isLocallyQuasiFinite_locallyQuasiFinitePart` this is what makes it
canonical. -/
@[stacks 04NW "maximality of the canonical open subspace"]
theorem le_locallyQuasiFinitePart (hF : IsAlgebraicSpace B S hS F)
    (hG : IsAlgebraicSpace B S hS G) (f : F ⟶ G) (hf : IsLocallyOfFiniteType B S hS f)
    (U : {U : Subfunctor F // IsOpenSubspace B S hS U})
    (hU : IsLocallyQuasiFinite B S hS (U.1.ι ≫ f)) :
    U ≤ locallyQuasiFinitePart B S hS hF hG f hf := by
  have hft : IsLocallyOfFiniteType B S hS (U.1.ι ≫ f) :=
    isLocallyOfFiniteType_comp B S hS U.2.1 hF hG U.1.ι f
      (isLocallyOfFiniteType_of_isEtale B S hS hF (isEtale_ι_of_isOpenSubspace U.2)) hf
  have hdim := (isLocallyQuasiFinite_iff_forall_hasRelativeDimensionAt_zero B S hS
    (U.1.ι ≫ f) hft).1 hU
  have hle : ((openSubspacesOrderIso B S hS F hF) U : Set (points B S hS F)) ⊆
      ((openSubspacesOrderIso B S hS F hF)
        (locallyQuasiFinitePart B S hS hF hG f hf) : Set (points B S hS F)) := by
    rw [coe_openSubspacesOrderIso, coe_openSubspacesOrderIso]
    rintro x ⟨x', rfl⟩
    exact (mem_range_pointsMap_locallyQuasiFinitePart_iff B S hS hF hG f hf _).2
      ((hasRelativeDimensionAt_iff_of_isOpenSubspace B S hS hF hG U.1 U.2 f x' 0).2 (hdim x'))
  exact (openSubspacesOrderIso B S hS F hF).le_iff_le.mp hle

/-- **Stacks 04NW, compatibility with arbitrary base change.** In a cartesian square of
algebraic spaces over `S` whose right vertical arrow is locally of finite type, the base change
is locally of finite type and its locally quasi-finite part is the inverse image of the locally
quasi-finite part of the morphism.

On points both sides are the relative-dimension-zero locus, and relative dimension at a point
is invariant under base change by part (1) of Stacks 04NS. -/
@[stacks 04NW "compatibility with arbitrary base change", sga "3 V 7.4" "more general"]
theorem locallyQuasiFinitePart_preimage_of_isPullback
    {X' X Y' Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : IsPullback g' f' f g)
    (hX' : IsAlgebraicSpace B S hS X') (hX : IsAlgebraicSpace B S hS X)
    (hY' : IsAlgebraicSpace B S hS Y') (hY : IsAlgebraicSpace B S hS Y)
    (hf : IsLocallyOfFiniteType B S hS f) :
    ∃ hf' : IsLocallyOfFiniteType B S hS f',
      (locallyQuasiFinitePart B S hS hX' hY' f' hf').1 =
        (locallyQuasiFinitePart B S hS hX hY f hf).1.preimage g' := by
  have hf' : IsLocallyOfFiniteType B S hS f' :=
    isLocallyOfFiniteType_of_isPullback' B S hS sq hX' hX hY' hY hf
  have hiso : locallyQuasiFinitePart B S hS hX' hY' f' hf' =
      ⟨(locallyQuasiFinitePart B S hS hX hY f hf).1.preimage g',
        isOpenSubspace_preimage B S hS g' (locallyQuasiFinitePart B S hS hX hY f hf).1 hX hX'
          (locallyQuasiFinitePart B S hS hX hY f hf).2⟩ := by
    refine (openSubspacesOrderIso B S hS X' hX').injective (TopologicalSpace.Opens.ext ?_)
    rw [coe_openSubspacesOrderIso, coe_openSubspacesOrderIso]
    ext x'
    rw [mem_range_pointsMap_locallyQuasiFinitePart_iff,
      mem_range_pointsMap_preimage_iff,
      mem_range_pointsMap_locallyQuasiFinitePart_iff,
      hasRelativeDimensionAt_iff_of_isPullback B S hS sq hX hY' hY hf x' 0]
  exact ⟨hf', congrArg Subtype.val hiso⟩

/-- A morphism of algebraic spaces over `S` whose target is represented by an object of the
site with subsingleton underlying scheme has relative dimension `0` at each point at which the
source has dimension `0` in the sense of Stacks 04N5: on an étale scheme chart at the point the
fibre of the chart map is the whole chart. -/
theorem hasRelativeDimensionAt_zero_of_dimensionAtPoint_eq_zero
    (hF : IsAlgebraicSpace B S hS F) (T : BigFppfOver B S hS)
    [Subsingleton ((BigFppfOver.toScheme B S hS).obj T)] (g : F ⟶ yoneda.obj T)
    (x : points B S hS F) (hdim : dimensionAtPoint B S hS F hF x = 0) :
    HasRelativeDimensionAt 0 B S hS g x := by
  obtain ⟨U, a, ha, q, hq⟩ := exists_etale_chart_at_point B S hS F hF x
  have hdimU : topologicalKrullDimAt ((BigFppfOver.toScheme B S hS).obj U)
      (schemePoint B S hS U q) = 0 := by
    rw [← dimensionAtPoint_eq_of_etale_chart B S hS F hF x U a ha q hq]
    exact hdim
  let c : EtaleChartAtPoint B S hS g x :=
    { U := U
      V := T
      a := a
      b := 𝟙 (yoneda.obj T)
      h := yoneda.preimage (a ≫ g)
      a_etale := ha
      b_etale := presheaf_etale_of_iso B S hS (Iso.refl (yoneda.obj T))
      comm := by simp
      representative := q
      point := IsLocalRing.closedPoint q.carrier
      maps_to := hq }
  refine (holdsOnEveryEtaleChartAtPoint_iff_of_chart B S hS (@HasFiberDimensionAt.{u} 0)
    (fiberDimensionAt_isEtaleLocalOnSourceAndTarget 0) g x c).2 ?_
  exact hasFiberDimensionAt_zero_of_subsingleton
    ((BigFppfOver.toScheme B S hS).map c.h) (c.sourcePoint B S hS) hdimU

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for the pullbacks of presheaves on the big fppf site in the statement is slow
/-- A morphism of algebraic spaces over `S` which is locally of finite type is quasi-finite at
the image of a point of a base change along a morphism from a represented object with
subsingleton underlying scheme at which that base change has dimension `0`.

The base change has relative dimension `0` at the point, so the point lies in the locally
quasi-finite part of the base change; that part is the inverse image of the locally
quasi-finite part of the morphism (Stacks 04NW), over which the morphism is locally
quasi-finite. -/
@[sga "3 V 7.4" "more general"]
theorem isQuasiFiniteAt_of_dimensionAtPoint_eq_zero_of_subsingleton
    (hX : IsAlgebraicSpace B S hS F) (hY : IsAlgebraicSpace B S hS G) (f : F ⟶ G)
    (hf : IsLocallyOfFiniteType B S hS f) (T : BigFppfOver B S hS)
    [Subsingleton ((BigFppfOver.toScheme B S hS).obj T)] (g : yoneda.obj T ⟶ G)
    (z : points B S hS (pullback f g))
    (hz : dimensionAtPoint B S hS (pullback f g)
      (isAlgebraicSpace_pullback B S hS f g hX (isAlgebraicSpace_yoneda B S hS T) hY) z = 0) :
    IsQuasiFiniteAt B S hS f (pointsMap B S hS (pullback f g) (pullback.fst f g) z) := by
  have hTalg := isAlgebraicSpace_yoneda B S hS T
  have hFib := isAlgebraicSpace_pullback B S hS f g hX hTalg hY
  have hrel : HasRelativeDimensionAt 0 B S hS (pullback.snd f g) z :=
    hasRelativeDimensionAt_zero_of_dimensionAtPoint_eq_zero B S hS hFib T
      (pullback.snd f g) z hz
  obtain ⟨hf', hUeq⟩ := locallyQuasiFinitePart_preimage_of_isPullback B S hS
    (IsPullback.of_hasPullback f g) hFib hX hTalg hY hf
  have hpart : z ∈ Set.range (pointsMap B S hS
      (locallyQuasiFinitePart B S hS hFib hTalg (pullback.snd f g) hf').1.toFunctor
      (locallyQuasiFinitePart B S hS hFib hTalg (pullback.snd f g) hf').1.ι) :=
    (mem_range_pointsMap_locallyQuasiFinitePart_iff B S hS hFib hTalg
      (pullback.snd f g) hf' z).2 hrel
  rw [hUeq, mem_range_pointsMap_preimage_iff] at hpart
  obtain ⟨w, hw⟩ := hpart
  exact ⟨(locallyQuasiFinitePart B S hS hX hY f hf).1,
    (locallyQuasiFinitePart B S hS hX hY f hf).2, w, hw,
    isLocallyQuasiFinite_locallyQuasiFinitePart B S hS hX hY f hf⟩

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for the pullbacks of presheaves on the big fppf site in the statement is slow
/-- **Stacks 06LS.** Let `f : X ⟶ Y` be a morphism of algebraic spaces over `S` which is
locally of finite type, let `p` be a field-valued point of `Y` — a morphism `Spec k ⟶ Y` from
the spectrum of a field over `S` — and let `z` be a point of the fibre `X ×_Y Spec k` at which
that fibre has dimension `0` in the sense of Stacks 04N5. Then `f` is quasi-finite at the image
of `z`: after replacing `X` by an open subspace containing that image, `f` is locally
quasi-finite. -/
@[stacks 06LS]
theorem isQuasiFiniteAt_of_dimensionAtPoint_fiber_eq_zero (hX : IsAlgebraicSpace B S hS F)
    (hY : IsAlgebraicSpace B S hS G) (f : F ⟶ G) (hf : IsLocallyOfFiniteType B S hS f)
    (p : FieldValuedPoint B S hS G)
    (z : points B S hS (pullback f (yonedaEquiv.symm p.value)))
    (hz : dimensionAtPoint B S hS (pullback f (yonedaEquiv.symm p.value))
      (isAlgebraicSpace_pullback B S hS f (yonedaEquiv.symm p.value) hX
        (isAlgebraicSpace_yoneda B S hS (p.siteObject B S hS G)) hY) z = 0) :
    IsQuasiFiniteAt B S hS f
      (pointsMap B S hS (pullback f (yonedaEquiv.symm p.value))
        (pullback.fst f (yonedaEquiv.symm p.value)) z) :=
  have _ : Subsingleton ((BigFppfOver.toScheme B S hS).obj (p.siteObject B S hS G)) :=
    inferInstanceAs (Subsingleton (Spec (.of p.carrier)))
  isQuasiFiniteAt_of_dimensionAtPoint_eq_zero_of_subsingleton B S hS hX hY f hf
    (p.siteObject B S hS G) (yonedaEquiv.symm p.value) z hz




end Space

end AlgebraicGeometry

end
