module

public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FromLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Spaces.CofinalChartGluing
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringSieveSurjective
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleAffineRefinement
public import StacksFrontier.CategoryTheory.Sites.DenseSubsite.NatIsoTransport

/-!
# A cofinal class of affine étale charts is a dense subsite of the small étale site

`AlgebraicGeometry.Space.IsCofinalChartFamily` is the condition on a class `P` of scheme charts
of a presheaf `F` on the big fppf site of `S` that every affine étale chart of `F` is covered by
affine étale charts in `P`.  This file reads that condition as a statement about the small étale
site of `F`: the full subcategory on the affine `P`-charts is **cover-dense**
(`CategoryTheory.Functor.IsCoverDense`), hence a dense subsite for the induced topology, hence
restriction of sheaves along it is fully faithful.

The consequence this is for is right cancellation, which the dense-subsite property unlocks in
`StacksFrontier.CategoryTheory.Sites.DenseSubsite.NatIsoTransport`: a natural isomorphism of
functors whose values are sheaves on the small étale site of `F` may be produced from its
restriction to the affine `P`-charts, by
`CategoryTheory.Functor.IsDenseSubsite.natIsoOfRestriction`, and a natural transformation of such
functors is determined by that restriction.  That is what glues a chartwise comparison of two
inverse-image functors on the small étale site into a global one without any gluing argument
being written out.  Those transport statements are stated there for an arbitrary dense subsite;
this file only supplies the hypothesis.

## Main definitions

* `AlgebraicGeometry.Space.IsCofinalChart` — the property of an object of the small étale site of
  `F` that it is affine and selected by `P`.
* `AlgebraicGeometry.Space.CofinalChart` — the full subcategory of the small étale site of `F` on
  those objects, with `AlgebraicGeometry.Space.cofinalChartInclusion` its inclusion and
  `AlgebraicGeometry.Space.cofinalChartMk` the affine étale `P`-chart as an object of it.
* `AlgebraicGeometry.Space.cofinalChartTopology` — the topology induced on it.

## Main results

* `AlgebraicGeometry.Space.isCoverDense_cofinalChartInclusion` — **the inclusion is cover-dense**,
  which is `AlgebraicGeometry.Space.IsCofinalChartFamily.exists_cover` read as a statement about
  covering sieves of the small étale site.
* `AlgebraicGeometry.Space.isDenseSubsite_cofinalChartInclusion` — consequently the inclusion
  exhibits the affine `P`-charts as a dense subsite.

## Implementation notes

Cover-density asks for the sieve of arrows into an object of the small étale site which factor
through an object in the image of the inclusion.  The covering family that
`AlgebraicGeometry.Space.IsCofinalChartFamily.exists_cover` produces consists of such arrows, so
it suffices to see that *it* generates a covering sieve, and that is
`AlgebraicGeometry.Space.SmallEtale.ofArrows_mem_topology`: a family of charts whose underlying
family of morphisms of schemes is an étale covering family is covering.  Its two inputs are
étaleness, which is `AlgebraicGeometry.Space.etale_toScheme_toOver_map` for a morphism of étale
charts, and joint surjectivity, which comes from the fppf covering sieve by
`AlgebraicGeometry.BigFppfOver.exists_mem_range_of_mem_topology`.

The index type of the family produced by `exists_cover` is in `Type u` while cover-density
quantifies over no index type at all, so no size condition arises;
`AlgebraicGeometry.Space.SmallEtale.ofArrows_mem_topology` is stated for an arbitrary index type
for that reason.

## References

* [Stacks Project, Tag 03ED](https://stacks.math.columbia.edu/tag/03ED)
* [Stacks Project, Tag 03FR](https://stacks.math.columbia.edu/tag/03FR)
* [Stacks Project, Tag 04KL](https://stacks.math.columbia.edu/tag/04KL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (P : ∀ T : BigFppfOver B S hS, (yoneda.obj T ⟶ F) → Prop)

/-- The property of an étale chart of `F` that its source is affine and that it is selected by
the class `P`. -/
def IsCofinalChart : ObjectProperty (SmallEtale B S hS F) :=
  fun V ↦ IsAffineOver B S hS V.obj.left ∧ P V.obj.left V.obj.hom

/-- The full subcategory of the small étale site of `F` on the affine `P`-charts. -/
abbrev CofinalChart := (IsCofinalChart B S hS P).FullSubcategory

/-- The inclusion of the affine `P`-charts into the small étale site of `F`. -/
abbrev cofinalChartInclusion : CofinalChart B S hS P ⥤ SmallEtale B S hS F :=
  (IsCofinalChart B S hS P).ι

/-- An affine étale `P`-chart, read as an object of
`AlgebraicGeometry.Space.CofinalChart`. -/
def cofinalChartMk {T : BigFppfOver B S hS} (hT : IsAffineOver B S hS T)
    (b : yoneda.obj T ⟶ F) (hb : IsEtale B S hS b) (hPb : P T b) :
    CofinalChart B S hS P :=
  ⟨⟨CostructuredArrow.mk b, (isEtale_iff_presheaf_of_yoneda B S hS b).1 hb⟩, hT, hPb⟩

/-- The étale chart underlying `AlgebraicGeometry.Space.cofinalChartMk` is the given one. -/
theorem cofinalChartMk_obj_hom {T : BigFppfOver B S hS} (hT : IsAffineOver B S hS T)
    (b : yoneda.obj T ⟶ F) (hb : IsEtale B S hS b) (hPb : P T b) :
    (cofinalChartMk B S hS P hT b hb hPb).obj.obj.hom = b :=
  rfl

/-- **A cofinal class of affine étale charts is cover-dense in the small étale site.**  Every
étale chart of `F` is covered by arrows factoring through affine `P`-charts, which is
`AlgebraicGeometry.Space.IsCofinalChartFamily.exists_cover` read as a covering sieve of the small
étale site. -/
theorem isCoverDense_cofinalChartInclusion (hP : IsCofinalChartFamily B S hS P) :
    (cofinalChartInclusion B S hS P).IsCoverDense (SmallEtale.topology B S hS F) := by
  refine ⟨fun U => ?_⟩
  have hU := (isEtale_iff_presheaf_of_yoneda B S hS U.obj.hom).2 U.property
  obtain ⟨I, V, π, hV, hπ, hcover, hPV⟩ := hP.exists_cover B S hS U.obj.left U.obj.hom hU
  have hetale (i : I) : IsEtale B S hS (yoneda.map (π i) ≫ U.obj.hom) :=
    isEtale_comp B S hS (hπ i) hU
  set W : I → CofinalChart B S hS P := fun i =>
    cofinalChartMk B S hS P (hV i) (yoneda.map (π i) ≫ U.obj.hom) (hetale i) (hPV i)
  set a : ∀ i, (W i).obj ⟶ U := fun i =>
    ObjectProperty.homMk (CostructuredArrow.homMk (π i) rfl)
  have hsub : Sieve.ofArrows (fun i => (W i).obj) a ≤
      Sieve.coverByImage (cofinalChartInclusion B S hS P) U := by
    rintro Z g ⟨Z', k, l, ⟨i⟩, rfl⟩
    exact ⟨⟨W i, k, a i, rfl⟩⟩
  refine GrothendieckTopology.superset_covering _ hsub ?_
  refine SmallEtale.ofArrows_mem_topology B S hS F (fun i => (W i).obj) a ?_
  rw [AlgebraicGeometry.ofArrows_mem_etalePrecoverage_iff]
  refine ⟨fun x => ?_, fun i => etale_toScheme_toOver_map B S hS F (a i)⟩
  obtain ⟨V', f, ⟨Z', k, l, ⟨i⟩, rfl⟩, y, hy⟩ :=
    BigFppfOver.exists_mem_range_of_mem_topology B S hS hcover x
  refine ⟨i, (BigFppfOver.toScheme B S hS).map k y, ?_⟩
  rw [← hy]
  exact ((BigFppfOver.toScheme B S hS).map_comp k (π i)) ▸ rfl

/-- The topology induced on the affine `P`-charts by the small étale topology. -/
abbrev cofinalChartTopology : GrothendieckTopology (CofinalChart B S hS P) :=
  (cofinalChartInclusion B S hS P).inducedTopology (SmallEtale.topology B S hS F)

/-- **A cofinal class of affine étale charts is a dense subsite of the small étale site.** -/
theorem isDenseSubsite_cofinalChartInclusion (hP : IsCofinalChartFamily B S hS P) :
    (cofinalChartInclusion B S hS P).IsDenseSubsite
      (cofinalChartTopology B S hS P) (SmallEtale.topology B S hS F) :=
  have := isCoverDense_cofinalChartInclusion B S hS P hP
  inferInstance

end AlgebraicGeometry.Space

end
