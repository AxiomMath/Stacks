module

public import StacksFrontier.AlgebraicGeometry.Properties.ReducedSubschemeSmoothPullback
public import StacksFrontier.AlgebraicGeometry.Stacks.ComponentMultiplicity
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactPointRepresentative

/-!
# The reduced induced closed subscheme of a chart of an algebraic stack, and its invariance

Let `𝒳` be an algebraic stack over `S`, let `a : U ⟶ 𝒳` be a 1-morphism from the algebraic
stack of a scheme `U` of the big fppf site, and let `T` be a closed set of points of `𝒳`. The
part of `U` lying over `T` is a closed subset of the scheme `U`, and it carries the reduced
induced closed subscheme structure of **Stacks 01J3**. If `s, t : R ⟶ U` are two morphisms of
the site whose underlying morphisms of schemes are smooth and whose composites with `a` are
joined by a 2-morphism — as the two legs of the relation `R = U ×_𝒳 U` of a chart are — then the
two pullbacks of that subscheme along `s` and along `t` agree.

## Main definitions

* `AlgebraicGeometry.Stack.chartPointSet`: the part of a chart lying over a set of points
  of `𝒳`.
* `AlgebraicGeometry.Stack.chartVanishingIdeal` and
  `AlgebraicGeometry.Stack.chartReducedSubscheme`: the vanishing ideal of that part and the
  reduced induced closed subscheme it cuts out.

## Main results

* `AlgebraicGeometry.Stack.isClosed_chartPointSet`: the part of a chart lying over a closed set
  of points is closed.
* `AlgebraicGeometry.Stack.image_chartPointSet`: for a chart surjective on points, the part
  lying over `T` has image `T`.
* `AlgebraicGeometry.Stack.pullback_subobject_chartReducedSubscheme_eq`: the invariance.

## Implementation notes

The part of the chart lying over `T` is the preimage of `T` along
`AlgebraicGeometry.Stack.AlgebraicStacks.chartPointMap`, the map on points of the chart read on
the scheme `U` through the identification of the points of the algebraic stack of a scheme of
the site with the scheme. Closedness is continuity of that map, which is **Stacks 04XL**.

Invariance is the statement of
`AlgebraicGeometry.Space.isInvariantSubscheme_atlasReducedSubscheme` with the étale legs of the
relation of a chart of an algebraic *space* replaced by smooth legs, which is the generality an
algebraic stack needs: the two pullbacks of the ideal along the legs are both reduced because
the legs are smooth — this is
`AlgebraicGeometry.Scheme.IdealSheafData.isReduced_subscheme_comap_of_smooth` — and they have
the same support because the two legs induce the same map on points after composition with the
chart; a reduced closed subscheme is determined by its support.

The relation is taken to be an object of the site rather than the algebraic space `U ×_𝒳 U`
itself, and the comparison of the two composites is carried as an arbitrary 2-morphism, since
only the resulting equality of the two induced maps on points is used. Both weakenings of the
hypotheses are what makes the statement applicable on a chart of that algebraic space.

The point topology of **Stacks 04Y8** is not a global instance and is written out in the
hypotheses that mention it, as in `StacksFrontier/AlgebraicGeometry/Stacks/Reduction.lean`.

## References

* [Stacks Project, Tag 01J3](https://stacks.math.columbia.edu/tag/01J3)
* [Stacks Project, Tag 04XL](https://stacks.math.columbia.edu/tag/04XL)
* [Stacks Project, Tag 04Y8](https://stacks.math.columbia.edu/tag/04Y8)
* [Stacks Project, Tag 07TW](https://stacks.math.columbia.edu/tag/07TW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The subset of a chart `U` of an algebraic stack `𝒳` lying over a set `T` of points of `𝒳`:
the preimage of `T` under the chart map on points
`AlgebraicGeometry.Stack.AlgebraicStacks.chartPointMap`. -/
def chartPointSet (𝒳 : AlgebraicStacks.{u, w} B S hS) (U : BigFppfOver B S hS)
    (a : schemeStack.{u, w} B S hS U ⟶ 𝒳) (T : Set (AlgebraicStacks.points B S hS 𝒳)) :
    Set ((BigFppfOver.toScheme B S hS).obj U) :=
  AlgebraicStacks.chartPointMap B S hS U 𝒳 a ⁻¹' T

/-- Membership in the part of a chart lying over `T` is membership in `T` of the corresponding
point of `𝒳`. -/
theorem mem_chartPointSet_iff (𝒳 : AlgebraicStacks.{u, w} B S hS) (U : BigFppfOver B S hS)
    (a : schemeStack.{u, w} B S hS U ⟶ 𝒳) (T : Set (AlgebraicStacks.points B S hS 𝒳))
    (z : (BigFppfOver.toScheme B S hS).obj U) :
    z ∈ chartPointSet B S hS 𝒳 U a T ↔
      AlgebraicStacks.chartPointMap B S hS U 𝒳 a z ∈ T :=
  Iff.rfl

/-- The chart map on points of a chart precomposed with a morphism of the site is the chart map
on points of the chart, precomposed with the underlying morphism of schemes. -/
theorem chartPointMap_schemeStackMap_comp (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (U V : BigFppfOver B S hS) (a : schemeStack.{u, w} B S hS U ⟶ 𝒳) (g : V ⟶ U) :
    AlgebraicStacks.chartPointMap B S hS V 𝒳 (schemeStackMap.{u, w} B S hS g ≫ a) =
      AlgebraicStacks.chartPointMap B S hS U 𝒳 a ∘
        ((BigFppfOver.toScheme B S hS).map g).base := by
  let _ := pointTopology B S hS (schemeFibredCategory B S hS U)
  let _ := pointTopology B S hS (schemeFibredCategory B S hS V)
  refine funext fun z => ?_
  have hnat : pointsHomeomorphScheme B S hS U
        (AlgebraicStacks.pointsMap B S hS (schemeStackMap.{u, w} B S hS g)
          ((pointsHomeomorphScheme B S hS V).symm z)) =
      ((BigFppfOver.toScheme B S hS).map g).base
        (pointsHomeomorphScheme B S hS V ((pointsHomeomorphScheme B S hS V).symm z)) :=
    pointsHomeomorphScheme_naturality B S hS g _
  rw [Homeomorph.apply_symm_apply] at hnat
  have hz : (pointsHomeomorphScheme B S hS U).symm
        (((BigFppfOver.toScheme B S hS).map g).base z) =
      AlgebraicStacks.pointsMap B S hS (schemeStackMap.{u, w} B S hS g)
        ((pointsHomeomorphScheme B S hS V).symm z) := by
    refine (pointsHomeomorphScheme B S hS U).injective ?_
    rw [Homeomorph.apply_symm_apply, hnat]
  show AlgebraicStacks.pointsMap B S hS (schemeStackMap.{u, w} B S hS g ≫ a)
      ((pointsHomeomorphScheme B S hS V).symm z) =
    AlgebraicStacks.pointsMap B S hS a
      ((pointsHomeomorphScheme B S hS U).symm
        (((BigFppfOver.toScheme B S hS).map g).base z))
  rw [hz, AlgebraicStacks.pointsMap_comp]
  rfl

/-- Charts with the same map on points cut out the same part lying over `T`. -/
private theorem chartPointSet_eq_of_pointsMap_eq (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (U : BigFppfOver B S hS) {a b : schemeStack.{u, w} B S hS U ⟶ 𝒳}
    (h : AlgebraicStacks.pointsMap B S hS a = AlgebraicStacks.pointsMap B S hS b)
    (T : Set (AlgebraicStacks.points B S hS 𝒳)) :
    chartPointSet B S hS 𝒳 U a T = chartPointSet B S hS 𝒳 U b T := by
  let _ := pointTopology B S hS (schemeFibredCategory B S hS U)
  unfold chartPointSet
  show (AlgebraicStacks.pointsMap B S hS a ∘ _) ⁻¹' T =
    (AlgebraicStacks.pointsMap B S hS b ∘ _) ⁻¹' T
  rw [h]

/-- The part of a chart lying over `T` depends on the chart only through its map on points, so
2-isomorphic charts cut out the same subset. -/
theorem chartPointSet_eq_of_hom₂ (𝒳 : AlgebraicStacks.{u, w} B S hS) (U : BigFppfOver B S hS)
    {a b : schemeStack.{u, w} B S hS U ⟶ 𝒳} (η : a ⟶ b)
    (T : Set (AlgebraicStacks.points B S hS 𝒳)) :
    chartPointSet B S hS 𝒳 U a T = chartPointSet B S hS 𝒳 U b T :=
  chartPointSet_eq_of_pointsMap_eq B S hS 𝒳 U (AlgebraicStacks.pointsMap_eq_of_hom₂ B S hS η) T

/-- Precomposing a chart with a morphism of the site pulls the part lying over `T` back along
the underlying morphism of schemes. -/
theorem preimage_chartPointSet (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (U V : BigFppfOver B S hS) (a : schemeStack.{u, w} B S hS U ⟶ 𝒳) (g : V ⟶ U)
    (T : Set (AlgebraicStacks.points B S hS 𝒳)) :
    ((BigFppfOver.toScheme B S hS).map g).base ⁻¹' chartPointSet B S hS 𝒳 U a T =
      chartPointSet B S hS 𝒳 V (schemeStackMap.{u, w} B S hS g ≫ a) T := by
  unfold chartPointSet
  rw [chartPointMap_schemeStackMap_comp, Set.preimage_comp]

/-- The part of a chart lying over a closed set of points is closed: it is the preimage of that
set under a continuous map, the chart map on points being continuous by **Stacks 04XL**. -/
theorem isClosed_chartPointSet (𝒳 : AlgebraicStacks.{u, w} B S hS) (U : BigFppfOver B S hS)
    (a : schemeStack.{u, w} B S hS U ⟶ 𝒳) (T : Set (AlgebraicStacks.points B S hS 𝒳))
    (hT : @IsClosed _ (pointTopology B S hS 𝒳.val) T) :
    IsClosed (chartPointSet B S hS 𝒳 U a T) := by
  let _ := pointTopology B S hS 𝒳.val
  exact hT.preimage (AlgebraicStacks.continuous_chartPointMap B S hS U 𝒳 a)

/-- A chart surjective on points cuts out a part lying over `T` whose image is `T`. -/
theorem image_chartPointSet (𝒳 : AlgebraicStacks.{u, w} B S hS) (U : BigFppfOver B S hS)
    (a : schemeStack.{u, w} B S hS U ⟶ 𝒳) (ha : IsSurjective B S hS a)
    (T : Set (AlgebraicStacks.points B S hS 𝒳)) :
    AlgebraicStacks.chartPointMap B S hS U 𝒳 a '' chartPointSet B S hS 𝒳 U a T = T :=
  Set.image_preimage_eq T (AlgebraicStacks.surjective_chartPointMap B S hS U 𝒳 a ha)

/-- The quasi-coherent ideal of a chart `U` cutting out the reduced induced closed subscheme on
the part of `U` lying over a closed set `T` of points of `𝒳`. -/
def chartVanishingIdeal (𝒳 : AlgebraicStacks.{u, w} B S hS) (U : BigFppfOver B S hS)
    (a : schemeStack.{u, w} B S hS U ⟶ 𝒳) (T : Set (AlgebraicStacks.points B S hS 𝒳))
    (hT : @IsClosed _ (pointTopology B S hS 𝒳.val) T) :
    ((BigFppfOver.toScheme B S hS).obj U).IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal
    ⟨chartPointSet B S hS 𝒳 U a T, isClosed_chartPointSet B S hS 𝒳 U a T hT⟩

/-- The support of `AlgebraicGeometry.Stack.chartVanishingIdeal` is the part of the chart lying
over `T`. -/
theorem coe_support_chartVanishingIdeal (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (U : BigFppfOver B S hS) (a : schemeStack.{u, w} B S hS U ⟶ 𝒳)
    (T : Set (AlgebraicStacks.points B S hS 𝒳))
    (hT : @IsClosed _ (pointTopology B S hS 𝒳.val) T) :
    ((chartVanishingIdeal B S hS 𝒳 U a T hT).support :
      Set ((BigFppfOver.toScheme B S hS).obj U)) = chartPointSet B S hS 𝒳 U a T :=
  Scheme.IdealSheafData.coe_support_vanishingIdeal _

/-- The reduced induced closed subscheme of a chart `U` on the part of `U` lying over a closed
set `T` of points of `𝒳`, as a subobject of `U`. -/
def chartReducedSubscheme (𝒳 : AlgebraicStacks.{u, w} B S hS) (U : BigFppfOver B S hS)
    (a : schemeStack.{u, w} B S hS U ⟶ 𝒳) (T : Set (AlgebraicStacks.points B S hS 𝒳))
    (hT : @IsClosed _ (pointTopology B S hS 𝒳.val) T) :
    Subobject ((BigFppfOver.toScheme B S hS).obj U) :=
  Subobject.mk (chartVanishingIdeal B S hS 𝒳 U a T hT).subschemeι

/-- The reduced induced closed subscheme of a chart is a closed subscheme. -/
theorem isClosedImmersion_arrow_chartReducedSubscheme (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (U : BigFppfOver B S hS) (a : schemeStack.{u, w} B S hS U ⟶ 𝒳)
    (T : Set (AlgebraicStacks.points B S hS 𝒳))
    (hT : @IsClosed _ (pointTopology B S hS 𝒳.val) T) :
    _root_.AlgebraicGeometry.IsClosedImmersion
      (chartReducedSubscheme B S hS 𝒳 U a T hT).arrow := by
  show _root_.AlgebraicGeometry.IsClosedImmersion
    (Subobject.mk (chartVanishingIdeal B S hS 𝒳 U a T hT).subschemeι).arrow
  rw [← Subobject.underlyingIso_hom_comp_eq_mk
    (chartVanishingIdeal B S hS 𝒳 U a T hT).subschemeι]
  infer_instance

/-- The reduced induced closed subscheme of a chart is reduced. -/
theorem isReduced_chartReducedSubscheme (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (U : BigFppfOver B S hS) (a : schemeStack.{u, w} B S hS U ⟶ 𝒳)
    (T : Set (AlgebraicStacks.points B S hS 𝒳))
    (hT : @IsClosed _ (pointTopology B S hS 𝒳.val) T) :
    IsReduced (Subobject.underlying.obj (chartReducedSubscheme B S hS 𝒳 U a T hT)) :=
  ObjectProperty.prop_of_iso (P := fun Z : Scheme.{u} => IsReduced Z)
    (Subobject.underlyingIso (chartVanishingIdeal B S hS 𝒳 U a T hT).subschemeι).symm
    (Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal _)

/-- **The reduced induced closed subscheme of a chart of an algebraic stack is invariant, given
equal maps on points.** Let `a : U ⟶ 𝒳` be a 1-morphism from the algebraic stack of a scheme of
the site, let `T` be a closed set of points of `𝒳`, and let `s, t : R ⟶ U` be morphisms of the
site with smooth underlying morphisms of schemes whose composites with `a` induce the same map on
points. Then the two pullbacks of the reduced induced closed subscheme of `U` on the part lying
over `T` agree.

The two pullbacks of the ideal are both reduced because the legs are smooth, and they have the
same support because the two legs induce the same map on points after composing with `a`; a
reduced closed subscheme is determined by its support. -/
theorem pullback_subobject_chartReducedSubscheme_eq_of_pointsMap_eq
    (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (U R : BigFppfOver B S hS) (a : schemeStack.{u, w} B S hS U ⟶ 𝒳)
    (T : Set (AlgebraicStacks.points B S hS 𝒳))
    (hT : @IsClosed _ (pointTopology B S hS 𝒳.val) T) (s t : R ⟶ U)
    (hs : Smooth ((BigFppfOver.toScheme B S hS).map s))
    (ht : Smooth ((BigFppfOver.toScheme B S hS).map t))
    (hpts : AlgebraicStacks.pointsMap B S hS (schemeStackMap.{u, w} B S hS s ≫ a) =
      AlgebraicStacks.pointsMap B S hS (schemeStackMap.{u, w} B S hS t ≫ a)) :
    (Subobject.pullback ((BigFppfOver.toScheme B S hS).map s)).obj
        (chartReducedSubscheme B S hS 𝒳 U a T hT) =
      (Subobject.pullback ((BigFppfOver.toScheme B S hS).map t)).obj
        (chartReducedSubscheme B S hS 𝒳 U a T hT) := by
  have _hs := hs
  have _ht := ht
  have hset := chartPointSet_eq_of_pointsMap_eq B S hS 𝒳 R hpts T
  have hsupp : ((chartVanishingIdeal B S hS 𝒳 U a T hT).comap
        ((BigFppfOver.toScheme B S hS).map s)).support =
      ((chartVanishingIdeal B S hS 𝒳 U a T hT).comap
        ((BigFppfOver.toScheme B S hS).map t)).support := by
    refine Closeds.ext ?_
    rw [Scheme.IdealSheafData.support_comap, Scheme.IdealSheafData.support_comap]
    show ((BigFppfOver.toScheme B S hS).map s).base ⁻¹'
        ((chartVanishingIdeal B S hS 𝒳 U a T hT).support : Set _) =
      ((BigFppfOver.toScheme B S hS).map t).base ⁻¹'
        ((chartVanishingIdeal B S hS 𝒳 U a T hT).support : Set _)
    rw [coe_support_chartVanishingIdeal, preimage_chartPointSet, preimage_chartPointSet, hset]
  exact Scheme.IdealSheafData.pullback_subobject_eq_of_support_comap_eq_of_smooth
    (chartVanishingIdeal B S hS 𝒳 U a T hT) _ _
    (Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal _) hsupp

/-- **The reduced induced closed subscheme of a chart of an algebraic stack is invariant.** Let
`a : U ⟶ 𝒳` be a 1-morphism from the algebraic stack of a scheme of the site, let `T` be a
closed set of points of `𝒳`, and let `s, t : R ⟶ U` be morphisms of the site with smooth
underlying morphisms of schemes whose composites with `a` are joined by a 2-morphism — as the two
legs of the relation `R = U ×_𝒳 U` of a chart are. Then the two pullbacks of the reduced induced
closed subscheme of `U` on the part lying over `T` agree.

This is the step at which the closed subschemes constructed chart-locally glue; it is
`AlgebraicGeometry.Stack.pullback_subobject_chartReducedSubscheme_eq_of_pointsMap_eq`, the
2-morphism making the two maps on points equal. -/
theorem pullback_subobject_chartReducedSubscheme_eq (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (U R : BigFppfOver B S hS) (a : schemeStack.{u, w} B S hS U ⟶ 𝒳)
    (T : Set (AlgebraicStacks.points B S hS 𝒳))
    (hT : @IsClosed _ (pointTopology B S hS 𝒳.val) T) (s t : R ⟶ U)
    (hs : Smooth ((BigFppfOver.toScheme B S hS).map s))
    (ht : Smooth ((BigFppfOver.toScheme B S hS).map t))
    (η : schemeStackMap.{u, w} B S hS s ≫ a ⟶ schemeStackMap.{u, w} B S hS t ≫ a) :
    (Subobject.pullback ((BigFppfOver.toScheme B S hS).map s)).obj
        (chartReducedSubscheme B S hS 𝒳 U a T hT) =
      (Subobject.pullback ((BigFppfOver.toScheme B S hS).map t)).obj
        (chartReducedSubscheme B S hS 𝒳 U a T hT) :=
  pullback_subobject_chartReducedSubscheme_eq_of_pointsMap_eq B S hS 𝒳 U R a T hT s t hs ht
    (AlgebraicStacks.pointsMap_eq_of_hom₂ B S hS η)

end AlgebraicGeometry.Stack

end
