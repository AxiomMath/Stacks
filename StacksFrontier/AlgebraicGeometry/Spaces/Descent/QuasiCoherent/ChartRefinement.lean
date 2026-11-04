module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsOfPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleChartEquivalenceClosure
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtalePostcomp
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.EtaleTopos
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.Zariski
public import StacksFrontier.AlgebraicGeometry.Stacks.EtaleOpenImmersion

/-!
# Refining an étale chart of an algebraic space by an étale covering

Let `X` be an algebraic space over a scheme `S` and let `(f i : Y i ⟶ X)` be a family of algebraic
spaces over `X` whose members are étale and which is jointly surjective on points, for instance an
étale covering or a Zariski covering. A chart `W` of the small étale site of `X` is then covered by
charts of the members: for every `i` the fibre product `Y i ×_X W` is an algebraic space, an étale
scheme chart `T i` of it maps étale to `Y i` and over `W`, and the resulting family of charts of
`X` generates a covering sieve of `W`.

## Main definitions

* `AlgebraicGeometry.Space.chartFibreProduct` is the fibre product `Y ×_X W` of an algebraic space
  over `X` with a chart of `X`, with `chartFibreProductFst` and `chartFibreProductSnd` its two
  projections.
* `AlgebraicGeometry.Space.refinedChart` is the chart of `Y` attached to an étale chart of
  `Y ×_X W`, and `AlgebraicGeometry.Space.refinedChartMap` is the morphism of charts of `X` that it
  induces into `W` after postcomposition with `f`.

## Main results

* `AlgebraicGeometry.Space.isEtale_chartFibreProductFst`: the first projection of `Y ×_X W` is
  étale.
* `AlgebraicGeometry.Space.exists_refinement_of_jointlySurjective`: a family of étale morphisms
  which is jointly surjective on points refines every chart of `X`, in the sense that charts of the
  members generate a covering sieve of it.
* `AlgebraicGeometry.Space.exists_refinement_of_isEtaleCovering` and
  `AlgebraicGeometry.Space.exists_refinement_of_isZariskiCovering`: the same for an étale covering
  and for a Zariski covering.

## References

* [Stacks Project, Tag 041E](https://stacks.math.columbia.edu/tag/041E)
* [Stacks Project, Tag 041G](https://stacks.math.columbia.edu/tag/041G)
* [Stacks Project, Tag 03ED](https://stacks.math.columbia.edu/tag/03ED)
* [Stacks Project, Tag 03BX](https://stacks.math.columbia.edu/tag/03BX)
* [Stacks Project, Tag 03H4](https://stacks.math.columbia.edu/tag/03H4)
* [Stacks Project, Tag 02X2](https://stacks.math.columbia.edu/tag/02X2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {X : AlgebraicSpaces B S hS}

/-- The fibre product `Y ×_X W` of an algebraic space `Y` over `X` with the algebraic space
represented by an étale chart `W` of `X`. -/
def chartFibreProduct (W : SmallEtale B S hS X.1) {Y : AlgebraicSpaces B S hS} (g : Y ⟶ X) :
    AlgebraicSpaces B S hS :=
  AlgebraicSpaces.fiberProduct B S hS g (chartToSpace B S hS X W)

/-- The projection `Y ×_X W ⟶ Y`. -/
def chartFibreProductFst (W : SmallEtale B S hS X.1) {Y : AlgebraicSpaces B S hS} (g : Y ⟶ X) :
    (chartFibreProduct B S hS W g).1 ⟶ Y.1 :=
  pullback.fst g.hom (chartToSpace B S hS X W).hom

/-- The projection `Y ×_X W ⟶ W`, landing in the presheaf represented by the chart. -/
def chartFibreProductSnd (W : SmallEtale B S hS X.1) {Y : AlgebraicSpaces B S hS} (g : Y ⟶ X) :
    (chartFibreProduct B S hS W g).1 ⟶ yoneda.obj ((SmallEtale.toOver B S hS X.1).obj W) :=
  pullback.snd g.hom (chartToSpace B S hS X W).hom

/-- The two projections of `Y ×_X W` form a cartesian square of presheaves over `X`. -/
theorem isPullback_chartFibreProduct (W : SmallEtale B S hS X.1)
    {Y : AlgebraicSpaces B S hS} (g : Y ⟶ X) :
    IsPullback (chartFibreProductFst B S hS W g) (chartFibreProductSnd B S hS W g) g.hom
      (chartToSpace B S hS X W).hom :=
  IsPullback.of_hasPullback g.hom (chartToSpace B S hS X W).hom

/-- The two projections of `Y ×_X W` have equal composites to `X`. -/
theorem chartFibreProduct_condition (W : SmallEtale B S hS X.1)
    {Y : AlgebraicSpaces B S hS} (g : Y ⟶ X) :
    chartFibreProductFst B S hS W g ≫ g.hom =
      chartFibreProductSnd B S hS W g ≫ (chartToSpace B S hS X W).hom :=
  (isPullback_chartFibreProduct B S hS W g).w

/-- The first projection of `Y ×_X W` is étale. -/
theorem isEtale_chartFibreProductFst (W : SmallEtale B S hS X.1)
    {Y : AlgebraicSpaces B S hS} (g : Y ⟶ X) :
    IsEtale B S hS (chartFibreProductFst B S hS W g) :=
  isEtale_of_isPullback B S hS (ObjectProperty.homMk (chartFibreProductSnd B S hS W g))
    (ObjectProperty.homMk (chartFibreProductFst B S hS W g)) (chartToSpace B S hS X W) g
    (AlgebraicSpaces.isPullback_fiberProduct B S hS g (chartToSpace B S hS X W)).flip
    (isEtale_chartToSpace B S hS X W)

variable {Y : AlgebraicSpaces B S hS}

/-- The chart of `Y` attached to an étale chart `a` of the fibre product `Y ×_X W`: the composite
of `a` with the first projection. -/
def refinedChart (W : SmallEtale B S hS X.1) (g : Y ⟶ X) {T : BigFppfOver B S hS}
    (a : yoneda.obj T ⟶ (chartFibreProduct B S hS W g).1) (ha : IsEtale B S hS a) :
    SmallEtale B S hS Y.1 :=
  ⟨CostructuredArrow.mk (a ≫ chartFibreProductFst B S hS W g),
    (isEtale_iff_presheaf_of_yoneda B S hS _).1
      (isEtale_comp B S hS ha (isEtale_chartFibreProductFst B S hS W g))⟩

/-- The triangle over `X` of the morphism of charts attached to an étale chart `a` of `Y ×_X W`:
the Yoneda preimage of the second projection, composed with the structure morphism of `W`, is the
chart of `Y` defined by `a` composed with `g`. -/
theorem refinedChart_triangle (W : SmallEtale B S hS X.1) (g : Y ⟶ X)
    {T : BigFppfOver B S hS} (a : yoneda.obj T ⟶ (chartFibreProduct B S hS W g).1) :
    yoneda.map (Yoneda.fullyFaithful.preimage (a ≫ chartFibreProductSnd B S hS W g)) ≫
        (chartToSpace B S hS X W).hom =
      (a ≫ chartFibreProductFst B S hS W g) ≫ g.hom :=
  (congrArg (fun m ↦ m ≫ (chartToSpace B S hS X W).hom)
      (Yoneda.fullyFaithful.map_preimage (a ≫ chartFibreProductSnd B S hS W g))).trans
    (((Category.assoc a (chartFibreProductSnd B S hS W g)
          (chartToSpace B S hS X W).hom).trans
        (congrArg (fun m ↦ a ≫ m) (chartFibreProduct_condition B S hS W g).symm)).trans
      (Category.assoc a (chartFibreProductFst B S hS W g) g.hom).symm)

/-- The morphism of charts of `X` induced by an étale chart `a` of `Y ×_X W`: the chart of `Y` it
defines, postcomposed with `g`, maps to `W` through the second projection. -/
def refinedChartMap (W : SmallEtale B S hS X.1) (g : Y ⟶ X) (hg : IsEtale B S hS g.hom)
    {T : BigFppfOver B S hS} (a : yoneda.obj T ⟶ (chartFibreProduct B S hS W g).1)
    (ha : IsEtale B S hS a) :
    (smallEtalePostcomp B S hS g hg).obj (refinedChart B S hS W g a ha) ⟶ W :=
  ObjectProperty.homMk
    (CostructuredArrow.homMk
      (Yoneda.fullyFaithful.preimage (a ≫ chartFibreProductSnd B S hS W g))
      (refinedChart_triangle B S hS W g a))

/-- The morphism of the big fppf site underlying `AlgebraicGeometry.Space.refinedChartMap` is the
Yoneda preimage of the second projection, read on the étale chart `a`. -/
theorem yoneda_map_refinedChartMap (W : SmallEtale B S hS X.1) (g : Y ⟶ X)
    (hg : IsEtale B S hS g.hom) {T : BigFppfOver B S hS}
    (a : yoneda.obj T ⟶ (chartFibreProduct B S hS W g).1) (ha : IsEtale B S hS a) :
    yoneda.map ((SmallEtale.toOver B S hS X.1).map (refinedChartMap B S hS W g hg a ha)) =
      a ≫ chartFibreProductSnd B S hS W g :=
  Yoneda.fullyFaithful.map_preimage _

variable {I : Type v} (Yi : I → AlgebraicSpaces B S hS) (f : ∀ i, Yi i ⟶ X)

/-- A family of étale morphisms which is jointly surjective on points refines every chart: for a
chart `W` of the small étale site of `X` there are charts `V i` of the members `Y i` whose
postcomposites with the `f i` generate a covering sieve of `W`. -/
theorem exists_refinement_of_jointlySurjective (hf : ∀ i, IsEtale B S hS (f i).hom)
    (hsurj : ∀ x : points B S hS X.1, ∃ i, ∃ y : points B S hS (Yi i).1,
      pointsMap B S hS (Yi i).1 (f i).hom y = x)
    (W : SmallEtale B S hS X.1) :
    ∃ (V : ∀ i, SmallEtale B S hS (Yi i).1)
      (q : ∀ i, (smallEtalePostcomp B S hS (f i) (hf i)).obj (V i) ⟶ W),
      Sieve.ofArrows (fun i => (smallEtalePostcomp B S hS (f i) (hf i)).obj (V i)) q ∈
        SmallEtale.topology B S hS X.1 W := by
  classical
  choose T a hasurj haetale using fun i ↦
    (chartFibreProduct B S hS W (f i)).property.exists_atlas
  have hae : ∀ i, IsEtale B S hS (a i) := fun i ↦
    (isEtale_iff_presheaf_of_yoneda B S hS (a i)).2 (haetale i)
  refine ⟨fun i ↦ refinedChart B S hS W (f i) (a i) (hae i),
    fun i ↦ refinedChartMap B S hS W (f i) (hf i) (a i) (hae i), ?_⟩
  refine (SmallEtale.mem_topology_iff_exists_mem_range ..).2 fun x ↦ ?_
  obtain ⟨w, hw⟩ :=
    surjective_pointsToScheme B S hS ((SmallEtale.toOver B S hS X.1).obj W) x
  obtain ⟨i, y, hy⟩ :=
    hsurj (pointsMap B S hS _ (chartToSpace B S hS X W).hom w)
  obtain ⟨z, hz, -⟩ := exists_point_of_isPullback_presheaf B S hS
    (isPullback_chartFibreProduct B S hS W (f i)).flip w y hy.symm
  obtain ⟨t, ht⟩ := (presheafSurjective_iff_isSurjective_yoneda B S hS
    (chartFibreProduct B S hS W (f i)).1 (chartFibreProduct B S hS W (f i)).property
    (T i) (a i)).1 (hasurj i) z
  have key : pointsMap B S hS (yoneda.obj (T i))
      (yoneda.map ((SmallEtale.toOver B S hS X.1).map
        (refinedChartMap B S hS W (f i) (hf i) (a i) (hae i)))) t = w :=
    (congrArg (fun m ↦ pointsMap B S hS (yoneda.obj (T i)) m t)
        (yoneda_map_refinedChartMap B S hS W (f i) (hf i) (a i) (hae i))).trans
      ((congrFun (pointsMap_comp B S hS (yoneda.obj (T i)) (a i)
            (chartFibreProductSnd B S hS W (f i))) t).trans
        ((congrArg (pointsMap B S hS (chartFibreProduct B S hS W (f i)).1
            (chartFibreProductSnd B S hS W (f i))) ht).trans hz))
  refine ⟨_, _, Sieve.ofArrows_mk _ _ i, pointsToScheme B S hS (T i) t, ?_⟩
  exact (pointsToScheme_pointsMap B S hS ((SmallEtale.toOver B S hS X.1).map
      (refinedChartMap B S hS W (f i) (hf i) (a i) (hae i))) t).symm.trans
    ((congrArg (pointsToScheme B S hS ((SmallEtale.toOver B S hS X.1).obj W)) key).trans hw)

/-- An étale covering of `X` refines every chart of the small étale site of `X`. -/
theorem exists_refinement_of_isEtaleCovering
    (hcov : IsEtaleCovering B S hS (fun i => (Yi i).1) (fun i => (f i).hom))
    (W : SmallEtale B S hS X.1) :
    ∃ (V : ∀ i, SmallEtale B S hS (Yi i).1)
      (q : ∀ i, (smallEtalePostcomp B S hS (f i) (hcov.etale i)).obj (V i) ⟶ W),
      Sieve.ofArrows (fun i => (smallEtalePostcomp B S hS (f i) (hcov.etale i)).obj (V i)) q ∈
        SmallEtale.topology B S hS X.1 W :=
  exists_refinement_of_jointlySurjective B S hS Yi f hcov.etale
    (fun x ↦ Set.mem_iUnion.1 (hcov.jointly_surjective.symm ▸ Set.mem_univ x)) W

/-- A Zariski covering of `X` refines every chart of the small étale site of `X`. -/
theorem exists_refinement_of_isZariskiCovering
    (hcov : IsZariskiCovering B S hS I (fun i => (Yi i).1) (fun i => (f i).hom))
    (W : SmallEtale B S hS X.1) :
    ∃ (V : ∀ i, SmallEtale B S hS (Yi i).1)
      (q : ∀ i, (smallEtalePostcomp B S hS (f i)
        (isEtale_of_isOpenImmersion B S hS (hcov.1 i))).obj (V i) ⟶ W),
      Sieve.ofArrows (fun i => (smallEtalePostcomp B S hS (f i)
        (isEtale_of_isOpenImmersion B S hS (hcov.1 i))).obj (V i)) q ∈
        SmallEtale.topology B S hS X.1 W :=
  exists_refinement_of_jointlySurjective B S hS Yi f
    (fun i ↦ isEtale_of_isOpenImmersion B S hS (hcov.1 i)) hcov.2 W

end AlgebraicGeometry.Space

end
