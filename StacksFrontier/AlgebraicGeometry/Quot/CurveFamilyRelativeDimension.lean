module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresentable
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilies
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartAtPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartFppfDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.Topology.Dimension.LocalKrullDim

/-!
# A relative-dimension bound from a bound on the dimension of the source

The relative-dimension condition in the definition of a family of curves (Stacks 0D4Z) is the
every-étale-chart bound on the fibre dimension of Stacks 06LR, part (1), written out through
`AlgebraicGeometry.Space.HoldsOnEveryEtaleChartAtPoint` of Stacks 04NC and
`AlgebraicGeometry.HasFiberDimensionAt` of Stacks 04NL. This file discharges that condition for
the morphism of algebraic spaces induced by a morphism of the big fppf site, from the single
hypothesis that the source scheme has topological Krull dimension at most the given bound.

## Main results

* `AlgebraicGeometry.Space.relativeDimensionLE_schemeSpaceMap`: the relative-dimension field of
  `AlgebraicGeometry.CurveFamily`, at the bound `n`, for a morphism of the site whose source
  scheme has dimension at most `n`.
* `AlgebraicGeometry.Space.holdsOnEveryEtaleChartAtPoint_yoneda_map_iff`: for a morphism of the
  site, the every-étale-chart condition at a point of the represented presheaf is the germ
  property at the corresponding point of the representing scheme. This is the pointwise
  companion of `AlgebraicGeometry.Space.holdsOnEveryEtaleChart_yoneda_map_iff`.
* `AlgebraicGeometry.exists_hasFiberDimensionAt_ofSchemeHom`: the germ of a morphism of schemes
  has fibre dimension some natural number at most `n` at each point of its source, as soon as
  the source has dimension at most `n`.
* `AlgebraicGeometry.topologicalKrullDimAt_fiber_le` and `topologicalKrullDimAt_nonneg`: with
  the imported `topologicalKrullDimAt_le_topologicalKrullDim`, the three bounds that pin a
  fibre dimension to a natural number at most `n`.

## Implementation notes

Both directions of the chart comparison come from a single chart whose two chart edges are the
identity, exactly as in `AlgebraicGeometry.Space.holdsOnEveryEtaleChart_yoneda_map_iff`: the
forward direction is that chart's instance of the universally quantified condition, and the
converse is Stacks 04NC, the equivalence of the every- and some-chart conditions. The point of
the chart is the canonical field-valued representative above the scheme point, so no choice of
residue-field spectrum has to be made. That chart is built here rather than taken from
`AlgebraicGeometry.Space.etaleChartAtPointOfId`, which is indexed by a field-valued point and a
point of its spectrum; the one below is indexed by a point of the presheaf and chooses the
representative itself, which is why it carries the separate name
`etaleChartAtClassPointOfId`.

No hypothesis on the target of the morphism is needed. The scheme-theoretic fibre is a
preimmersion into the source, hence topologically embedded, so its dimension at a point is
bounded by the dimension of the source; and that point witnesses that the fibre is nonempty, so
the dimension there is not `-∞`. Between those two bounds a value at most `n` in `WithBot ℕ∞` is
the image of a natural number at most `n`, which is the shape the `relativeDimensionLE` field
asks for. The germ of a morphism of schemes is represented on the top open of the source, which
`AlgebraicGeometry.Scheme.topIso` compares with the whole scheme.

`AlgebraicGeometry.RelativeDimensionLE` is a different notion and is not what is proved here: it
is the scheme-level Stacks 02NJ relative dimension of a morphism of schemes locally of finite
type, defined through the local Krull dimension of the scheme-theoretic fibre, whereas the
condition below is the Stacks 06LR condition on a morphism of algebraic spaces, tested in every
étale chart.

## References

* [Stacks Project, Tag 06LR](https://stacks.math.columbia.edu/tag/06LR)
* [Stacks Project, Tag 04NC](https://stacks.math.columbia.edu/tag/04NC)
* [Stacks Project, Tag 04NL](https://stacks.math.columbia.edu/tag/04NL)
* [Stacks Project, Tag 0D4Z](https://stacks.math.columbia.edu/tag/0D4Z)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace TopologicalSpace

end TopologicalSpace

namespace AlgebraicGeometry

/-- A value of `WithBot ℕ∞` which is at least zero and at most a natural number `n` is the image
of a natural number at most `n`. -/
private theorem exists_nat_le_eq (d : WithBot ℕ∞) (n : ℕ) (h0 : (0 : WithBot ℕ∞) ≤ d)
    (hn : d ≤ ((n : ℕ∞) : WithBot ℕ∞)) : ∃ e : ℕ, e ≤ n ∧ d = ((e : ℕ∞) : WithBot ℕ∞) := by
  obtain ⟨c, rfl⟩ := WithBot.ne_bot_iff_exists.1 (ne_bot_of_le_ne_bot (by simp) h0)
  have hcn : c ≤ (n : ℕ∞) := WithBot.coe_le_coe.1 hn
  obtain ⟨m, rfl⟩ := WithTop.ne_top_iff_exists.1 (ne_top_of_le_ne_top (by simp) hcn)
  exact ⟨m, ENat.natCast_le_natCast.mp hcn, rfl⟩

/-- The dimension of the scheme-theoretic fibre of a morphism at a point of the source is at
most the dimension of the source: the fibre is a preimmersion, hence topologically embedded. No
hypothesis on the target is needed. -/
theorem topologicalKrullDimAt_fiber_le {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) :
    topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) ≤ topologicalKrullDim X :=
  (topologicalKrullDimAt_le_topologicalKrullDim _).trans
    (Topology.IsInducing.topologicalKrullDim_le (f.fiberι (f x)).isEmbedding.isInducing)

/-- The germ of a morphism of schemes whose source has dimension at most `n` has, at the given
point, fibre dimension some natural number at most `n`. The value is not `-∞` because the point
itself lies in the fibre, and is at most `n` because the fibre is embedded in the source. -/
theorem exists_hasFiberDimensionAt_ofSchemeHom {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) (n : ℕ)
    (hdim : topologicalKrullDim X ≤ ((n : ℕ∞) : WithBot ℕ∞)) :
    ∃ e : ℕ, e ≤ n ∧ HasFiberDimensionAt (e : ℕ∞) (MorphismOfGerms.ofSchemeHom f x) := by
  set h : ((⊤ : X.Opens) : Scheme.{u}) ⟶ Y := X.topIso.hom ≫ f
  set z : ((⊤ : X.Opens) : Scheme.{u}) := ⟨x, by simp⟩
  have hle : topologicalKrullDimAt (h.fiber (h z)) (h.asFiber z) ≤ topologicalKrullDim X :=
    (topologicalKrullDimAt_fiber_le h z).trans
      (IsHomeomorph.topologicalKrullDim_eq _ (Scheme.homeoOfIso X.topIso).isHomeomorph).le
  obtain ⟨e, hen, hee⟩ := exists_nat_le_eq _ n
    (topologicalKrullDimAt_nonneg (h.asFiber z)) (hle.trans hdim)
  exact ⟨e, hen, { source := ⊤
                   mem_source := by simp
                   hom := X.topIso.hom ≫ f
                   map_point := rfl }, rfl, hee⟩

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The étale chart of a morphism of represented presheaves whose two chart edges are the
identity, pointed at the canonical field-valued representative above the scheme point. -/
private def etaleChartAtClassPointOfId {U V : BigFppfOver B S hS} (g : U ⟶ V)
    (x : points B S hS (yoneda.obj U)) :
    EtaleChartAtPoint B S hS (yoneda.map g) x where
  U := U
  V := V
  a := yoneda.map (𝟙 U)
  b := yoneda.map (𝟙 V)
  h := g
  a_etale := presheaf_yoneda_map_id_etale B S hS U
  b_etale := presheaf_yoneda_map_id_etale B S hS V
  comm := by simp
  representative := schemePointRepresentative B S hS U (pointsToScheme B S hS U x)
  point := IsLocalRing.closedPoint _
  maps_to := by
    rw [CategoryTheory.Functor.map_id, pointsMap_id]
    refine Quot.inductionOn x ?_
    intro p
    exact schemePointRepresentative_class B S hS U p

/-- The scheme point of the identity chart is the scheme point of the given point. -/
private theorem etaleChartAtClassPointOfId_sourcePoint {U V : BigFppfOver B S hS} (g : U ⟶ V)
    (x : points B S hS (yoneda.obj U)) :
    (etaleChartAtClassPointOfId B S hS g x).sourcePoint B S hS = pointsToScheme B S hS U x :=
  schemePointRepresentative_point B S hS U (pointsToScheme B S hS U x)

/-- For a morphism `g` of the big fppf site of `S` and a property `Q` of morphisms of germs
which is étale local on the source and target, the every-étale-chart condition of Stacks 04NC at
a point of the presheaf represented by the source is `Q` for the germ of the underlying morphism
of schemes at the corresponding scheme point.

This is the pointwise companion of
`AlgebraicGeometry.Space.holdsOnEveryEtaleChart_yoneda_map_iff`: the forward direction is the
condition at the chart whose two edges are identities, and the converse is Stacks 04NC. -/
theorem holdsOnEveryEtaleChartAtPoint_yoneda_map_iff
    (Q : ∀ {X Y : GermOfScheme.{u}}, MorphismOfGerms X Y → Prop)
    (hQ : MorphismOfGerms.IsEtaleLocalOnSourceAndTarget Q)
    {U V : BigFppfOver B S hS} (g : U ⟶ V) (x : points B S hS (yoneda.obj U)) :
    HoldsOnEveryEtaleChartAtPoint B S hS Q (yoneda.map g) x ↔
      Q (MorphismOfGerms.ofSchemeHom ((BigFppfOver.toScheme B S hS).map g)
        (pointsToScheme B S hS U x)) := by
  constructor
  · intro h
    have hc := h (etaleChartAtClassPointOfId B S hS g x)
    rwa [etaleChartAtClassPointOfId_sourcePoint] at hc
  · intro h
    exact (holdsOnEveryEtaleChartAtPoint_iff_some B S hS Q hQ
      (isAlgebraicSpace_yoneda B S hS U) (isAlgebraicSpace_yoneda B S hS V)
      (yoneda.map g) x).2
      ⟨etaleChartAtClassPointOfId B S hS g x, by rwa [etaleChartAtClassPointOfId_sourcePoint]⟩

/-- **The relative-dimension condition of Stacks 0D4Z, at the bound `n`.** A morphism of the big
fppf site of `S` whose source has topological Krull dimension at most `n` induces a morphism of
algebraic spaces of relative dimension at most `n` in the sense of the `relativeDimensionLE`
field of `AlgebraicGeometry.CurveFamily`: at every point of the total space the fibre dimension
is bounded by `n` in every étale chart. No hypothesis on the base is needed. -/
theorem relativeDimensionLE_schemeSpaceMap {T U : BigFppfOver B S hS} (g : T ⟶ U) (n : ℕ)
    (hdim : topologicalKrullDim ((BigFppfOver.toScheme B S hS).obj T)
      ≤ ((n : ℕ∞) : WithBot ℕ∞))
    (x : points B S hS (schemeSpace T).obj) :
    ∃ e : ℕ, e ≤ n ∧
      HoldsOnEveryEtaleChartAtPoint B S hS (@HasFiberDimensionAt.{u} (e : ℕ∞))
        (schemeSpaceMap g).hom x := by
  obtain ⟨e, hen, hee⟩ := exists_hasFiberDimensionAt_ofSchemeHom
    ((BigFppfOver.toScheme B S hS).map g) (pointsToScheme B S hS T x) n hdim
  exact ⟨e, hen, (holdsOnEveryEtaleChartAtPoint_yoneda_map_iff B S hS
    (@HasFiberDimensionAt.{u} (e : ℕ∞))
    (fiberDimensionAt_isEtaleLocalOnSourceAndTarget (e : ℕ∞)) g x).2 hee⟩

end Space

end AlgebraicGeometry

end
