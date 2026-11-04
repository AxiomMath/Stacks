module

public import StacksFrontier.AlgebraicGeometry.Descent.Germ.TranscendenceDegree
public import StacksFrontier.AlgebraicGeometry.Descent.Germs.FiberDimension
public import StacksFrontier.AlgebraicGeometry.Descent.Germs.FiberLocalRingDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartAtPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts

/-!
# Relative dimension and transcendence degree at a point of a morphism of algebraic spaces

Stacks 04NM introduces three numerical invariants at a point `x` of a morphism of algebraic
spaces `f : X ⟶ Y`: the dimension of the local ring of the fibre at `x`, the dimension of
the fibre at `x`, and the transcendence degree of `x` over its image. Each is defined by
testing the corresponding property of germs of schemes (Tags 04NJ, 04NL, 04NK) on étale
scheme charts at the point.

## Main definitions

* `AlgebraicGeometry.Space.HasFiberLocalRingDimension` is the dimension condition on the
  local ring of the fibre at a point.
* `AlgebraicGeometry.Space.HasRelativeDimensionAt` is relative dimension `d` at a point.
* `AlgebraicGeometry.Space.HasTranscendenceDegreeAt` says the transcendence degree at a
  point is a specified value in `ℕ∞`.

## Main results

* `AlgebraicGeometry.Space.exists_compatible_etale_charts_comp`: two composable morphisms of
  algebraic spaces over `S` admit surjective étale scheme charts of all three spaces,
  compatible with both morphisms and with a chosen point of the source, on which relative
  dimension and transcendence degree of each morphism and of the composite can be read.

The rest of the chart-locality API comes from Tag 04NC.

## Implementation notes

All three use the every-chart condition
`AlgebraicGeometry.Space.HoldsOnEveryEtaleChartAtPoint` of Tag 04NC. Each of the three germ
properties is étale local on source and target (Tags 04NJ, 04NL, 04NK), so by
`AlgebraicGeometry.Space.chart_property_iff_of_pointedCharts` the condition does not depend
on the chosen chart, and by
`AlgebraicGeometry.Space.holdsOnEveryEtaleChartAtPoint_iff_some` it agrees with the
some-chart condition for algebraic spaces. Keeping them as abbreviations lets clients apply
that API without an extra unfolding lemma.

The germ-level properties live in the namespace `AlgebraicGeometry`, and the first of them
shares its name with the space-level predicate defined here; inside
`AlgebraicGeometry.Space` the short name is the space-level one, so the germ-level property
is written out in full.

The algebraic-space hypotheses on source and target are recorded in the first definition, as
in the source, but unused: the predicate itself is meaningful for an arbitrary morphism of
presheaves, and clients supply the hypotheses when they apply the chart equivalence.

The compatible charts of `exists_compatible_etale_charts_comp` are obtained by lifting a
surjective étale atlas of the final target back through the second morphism and then through
the first (Tag 02X1); the chart of the source is surjective, so some point of it lies over the
chosen point (Tag 03H5), and the points of the other two charts are its images. Each of the
six comparisons is an instance of
`AlgebraicGeometry.Space.holdsOnEveryEtaleChartAtPoint_iff_chartMap` for the germ property
defining the invariant, which is étale local on source and target by Tags 04NL and 04NK. No
finite-type hypothesis on either morphism is needed: both invariants are defined, and read on
charts, for an arbitrary morphism.

## References

* [Stacks Project, Tag 04NM](https://stacks.math.columbia.edu/tag/04NM)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

/-- **Stacks 04NM, dimension of the local ring of a fibre.** The local ring of the fibre of
`f` has dimension `d` at `x`, tested on every étale chart at `x`. -/
@[stacks 04NM "local_ring_fibre_dimension"]
abbrev HasFiberLocalRingDimension (d : ℕ∞) (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (_hF : IsAlgebraicSpace B S hS F) (_hG : IsAlgebraicSpace B S hS G)
    (f : F ⟶ G) (x : points B S hS F) : Prop :=
  HoldsOnEveryEtaleChartAtPoint B S hS
    (@_root_.AlgebraicGeometry.HasFiberLocalRingDimension.{u} d) f x

/-- **Stacks 04NM, relative dimension at a point.** A morphism of algebraic spaces has
relative dimension `d` at `x` if its fibre has dimension `d` at the corresponding point in
every étale chart. -/
@[stacks 04NM "relative_dimension_at_point"]
abbrev HasRelativeDimensionAt (d : ℕ∞) (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : F ⟶ G) (x : points B S hS F) : Prop :=
  HoldsOnEveryEtaleChartAtPoint B S hS (@HasFiberDimensionAt.{u} d) f x

/-- **Stacks 04NM, transcendence degree at a point.** The transcendence degree of `x` over
its image under `f` is `r`. For algebraic spaces this is equivalently tested on one or every
étale scheme chart at `x`. -/
@[stacks 04NM "transcendence_degree"]
abbrev HasTranscendenceDegreeAt (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : F ⟶ G) (x : points B S hS F) (r : ℕ∞) :
    Prop :=
  HoldsOnEveryEtaleChartAtPoint B S hS
    (@MorphismOfGerms.HasResidueFieldTranscendenceDegree.{u} r) f x

/-! ### Compatible charts for a composite -/

/-- **Compatible étale charts for a composite.** Two composable morphisms `f : X ⟶ Y` and
`g : Y ⟶ Z` of algebraic spaces over `S` admit surjective étale scheme charts `a`, `b`, `c` of
the three spaces, morphisms `α`, `β` of the site between them making both squares commute, and
points `u`, `v`, `w` of the three charts over the chosen point `x` of `X`, its image under `f`
and its image under `f ≫ g`. On these charts the relative dimension and the transcendence
degree at the corresponding point agree for `f`, for `g` and for the composite. -/
theorem exists_compatible_etale_charts_comp
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hZ : IsAlgebraicSpace B S hS Z)
    (f : X ⟶ Y) (g : Y ⟶ Z) (x : points B S hS X) :
    ∃ (U V W : BigFppfOver B S hS)
      (a : yoneda.obj U ⟶ X) (b : yoneda.obj V ⟶ Y) (c : yoneda.obj W ⟶ Z)
      (α : U ⟶ V) (β : V ⟶ W)
      (u : points B S hS (yoneda.obj U)) (v : points B S hS (yoneda.obj V))
      (w : points B S hS (yoneda.obj W)),
      (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf a ∧
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf a ∧
      (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf b ∧
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf b ∧
      (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf c ∧
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf c ∧
      yoneda.map α ≫ b = a ≫ f ∧
      yoneda.map β ≫ c = b ≫ g ∧
      pointsMap B S hS (yoneda.obj U) a u = x ∧
      pointsMap B S hS (yoneda.obj U) (yoneda.map α) u = v ∧
      pointsMap B S hS (yoneda.obj V) (yoneda.map β) v = w ∧
      pointsMap B S hS (yoneda.obj V) b v = pointsMap B S hS X f x ∧
      pointsMap B S hS (yoneda.obj W) c w = pointsMap B S hS X (f ≫ g) x ∧
      (∀ d : ℕ∞, HasRelativeDimensionAt d B S hS f x ↔
        HasRelativeDimensionAt d B S hS (yoneda.map α) u) ∧
      (∀ d : ℕ∞, HasRelativeDimensionAt d B S hS g (pointsMap B S hS X f x) ↔
        HasRelativeDimensionAt d B S hS (yoneda.map β) v) ∧
      (∀ d : ℕ∞, HasRelativeDimensionAt d B S hS (f ≫ g) x ↔
        HasRelativeDimensionAt d B S hS (yoneda.map (α ≫ β)) u) ∧
      (∀ r : ℕ∞, HasTranscendenceDegreeAt B S hS f x r ↔
        HasTranscendenceDegreeAt B S hS (yoneda.map α) u r) ∧
      (∀ r : ℕ∞, HasTranscendenceDegreeAt B S hS g (pointsMap B S hS X f x) r ↔
        HasTranscendenceDegreeAt B S hS (yoneda.map β) v r) ∧
      (∀ r : ℕ∞, HasTranscendenceDegreeAt B S hS (f ≫ g) x r ↔
        HasTranscendenceDegreeAt B S hS (yoneda.map (α ≫ β)) u r) := by
  obtain ⟨W, c, hcSurj, hcEtale⟩ := hZ.exists_atlas
  obtain ⟨V, b, β, hcommG, hbSurj, hbEtale⟩ :=
    exists_surjective_etale_presentation_lift B S hS hY hZ g W c hcSurj hcEtale
  obtain ⟨U, a, α, hcommF, haSurj, haEtale⟩ :=
    exists_surjective_etale_presentation_lift B S hS hX hY f V b hbSurj hbEtale
  obtain ⟨u, hu⟩ := (surjective_iff_surjective_pointsMap B S hS X hX U a).mp haSurj x
  let v : points B S hS (yoneda.obj V) :=
    pointsMap B S hS (yoneda.obj U) (yoneda.map α) u
  let w : points B S hS (yoneda.obj W) :=
    pointsMap B S hS (yoneda.obj V) (yoneda.map β) v
  have hvb : pointsMap B S hS (yoneda.obj V) b v = pointsMap B S hS X f x :=
    (congrFun (pointsMap_comp B S hS (yoneda.obj U) (yoneda.map α) b) u).symm.trans (by
      rw [← hcommF, pointsMap_comp B S hS (yoneda.obj U) a f, Function.comp_apply, hu])
  have hwc : pointsMap B S hS (yoneda.obj W) c w = pointsMap B S hS X (f ≫ g) x :=
    (congrFun (pointsMap_comp B S hS (yoneda.obj V) (yoneda.map β) c) v).symm.trans (by
      rw [← hcommG, pointsMap_comp B S hS (yoneda.obj V) b g, Function.comp_apply, hvb,
        pointsMap_comp B S hS X f g, Function.comp_apply])
  have hcomp : a ≫ (f ≫ g) = yoneda.map (α ≫ β) ≫ c := by
    rw [← Category.assoc, hcommF, Category.assoc, hcommG, Functor.map_comp, Category.assoc]
  obtain ⟨p, hp⟩ := Quot.exists_rep u
  have hpV : (FieldValuedPoint.map B S hS (yoneda.obj U) (yoneda.map α) p).class
      B S hS (yoneda.obj V) = v :=
    congrArg (pointsMap B S hS (yoneda.obj U) (yoneda.map α)) hp
  exact ⟨U, V, W, a, b, c, α, β, u, v, w, haSurj, haEtale, hbSurj, hbEtale,
    hcSurj, hcEtale, hcommF.symm, hcommG.symm, hu, rfl, rfl, hvb, hwc,
    fun d => holdsOnEveryEtaleChartAtPoint_iff_chartMap B S hS
      (@HasFiberDimensionAt.{u} d)
      (fiberDimensionAt_isEtaleLocalOnSourceAndTarget d) hX hY f x a b α
      haEtale hbEtale hcommF u p hp hu,
    fun d => holdsOnEveryEtaleChartAtPoint_iff_chartMap B S hS
      (@HasFiberDimensionAt.{u} d)
      (fiberDimensionAt_isEtaleLocalOnSourceAndTarget d) hY hZ g
      (pointsMap B S hS X f x) b c β hbEtale hcEtale hcommG v _ hpV hvb,
    fun d => holdsOnEveryEtaleChartAtPoint_iff_chartMap B S hS
      (@HasFiberDimensionAt.{u} d)
      (fiberDimensionAt_isEtaleLocalOnSourceAndTarget d) hX hZ (f ≫ g) x a c (α ≫ β)
      haEtale hcEtale hcomp u p hp hu,
    fun r => holdsOnEveryEtaleChartAtPoint_iff_chartMap B S hS
      (@MorphismOfGerms.HasResidueFieldTranscendenceDegree.{u} r)
      (MorphismOfGerms.residueFieldTranscendenceDegree_isEtaleLocalOnSourceAndTarget r)
      hX hY f x a b α haEtale hbEtale hcommF u p hp hu,
    fun r => holdsOnEveryEtaleChartAtPoint_iff_chartMap B S hS
      (@MorphismOfGerms.HasResidueFieldTranscendenceDegree.{u} r)
      (MorphismOfGerms.residueFieldTranscendenceDegree_isEtaleLocalOnSourceAndTarget r)
      hY hZ g (pointsMap B S hS X f x) b c β hbEtale hcEtale hcommG v _ hpV hvb,
    fun r => holdsOnEveryEtaleChartAtPoint_iff_chartMap B S hS
      (@MorphismOfGerms.HasResidueFieldTranscendenceDegree.{u} r)
      (MorphismOfGerms.residueFieldTranscendenceDegree_isEtaleLocalOnSourceAndTarget r)
      hX hZ (f ≫ g) x a c (α ≫ β) haEtale hcEtale hcomp u p hp hu⟩

end AlgebraicGeometry.Space

end
