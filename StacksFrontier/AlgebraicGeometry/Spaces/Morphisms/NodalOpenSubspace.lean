module

public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SchemeTheoreticImageSiteOpen
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Curves.NodalLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.Coproduct
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.FactorThroughOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat
public import StacksFrontier.AlgebraicGeometry.Spaces.FpqcOpenSubspaceDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.Nodal
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceImage
public import StacksFrontier.AlgebraicGeometry.Spaces.PointTopologyEtaleOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsMono
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentableProperty
public import StacksFrontier.AlgebraicGeometry.Spaces.StrictTransform
public import StacksFrontier.AlgebraicGeometry.Spaces.Support.CompatibleEtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints

/-!
# The maximal at-worst-nodal open subspace of a flat family of algebraic spaces

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` which is flat and locally
of finite presentation. Among the open subspaces `W ⊆ X` on which `f` restricts to a morphism
which is at-worst-nodal of relative dimension one there is a largest one, and forming it
commutes with arbitrary base change.

The locus is cut out, through the correspondence of **Stacks 03BZ** between the open subspaces
of an algebraic space and the open subsets of its space of points, by the union of the point
sets of all the open subspaces with the property; so it is manifestly the largest one, and
nothing has to be chosen. The work is in showing that `f` really is at-worst-nodal of relative
dimension one over it, and in the base change.

Both rest on one chart computation. Given a commuting square of étale charts, with
`c : h_U ⟶ X` a chart of the source and `v : h_V ⟶ Y` a chart of the target lying over a
morphism `α : U ⟶ V` of the site, the part of the chart lying over the locus is exactly the
*scheme-level* nodal locus of **Stacks 0DSC** of the morphism of schemes underlying `α`. One
inclusion restricts the chart to the part lying over a member of the family and reads the
chart condition of **Stacks 03MJ** there; the other turns the scheme-level nodal locus into an
open subspace of `X` which is a member of the family, recognized by criterion (7) of
**Stacks 0DSG** on the single surjective étale chart that the scheme-level locus provides.

With that, the chart condition over the locus holds because the chart of an open subspace
lands in the locus, so the scheme-level nodal locus of the chart morphism is everything; and
the base change follows from the base-change half of **Stacks 0DSC** read on the compatible
étale charts of **Stacks 02X1**, whose square of charts is cartesian.

## Main definitions

* `AlgebraicGeometry.Space.IsNodalOpen` is the property of an open subspace of the source that
  the restriction of the morphism to it is at-worst-nodal of relative dimension one.
* `AlgebraicGeometry.Space.nodalPointSet` is the union of the point sets of the open subspaces
  with that property.
* `AlgebraicGeometry.Space.nodalOpenSubspace` is the open subspace of **Stacks 03BZ** which
  that set of points cuts out. This is the candidate largest open subspace.

## Main results

* `AlgebraicGeometry.Space.isOpenSubspace_nodalOpenSubspace`: it is an open subspace.
* `AlgebraicGeometry.Space.le_nodalOpenSubspace`: every open subspace with the property is
  contained in it.
* `AlgebraicGeometry.Space.isAtWorstNodalOfRelativeDimensionOne_nodalOpenSubspace`: the
  restriction of the morphism to it is at-worst-nodal of relative dimension one.
* `AlgebraicGeometry.Space.nodalOpenSubspace_isGreatest`: the two statements above together,
  as the assertion that the locus is the greatest open subspace with the property.
* `AlgebraicGeometry.Space.nodalOpenSubspace_baseChange`: forming it commutes with arbitrary
  base change.
* `AlgebraicGeometry.Space.exists_isGreatest_isNodalOpen_baseChange`: **Stacks 0DSH**, the
  three assertions together.

## Implementation notes

Everything is stated for morphisms of presheaves on the big fppf site of `S` together with
algebraicity hypotheses, rather than for morphisms of the category of algebraic spaces, so
that the base change may be taken to be the fibre product of presheaves and no transport along
a comparison isomorphism of fibre products occurs. The compatible charts of Stacks 02X1 are
produced for morphisms of the category, and the two are joined by `ObjectProperty.homMk`.

Flatness and local finite presentation of a morphism of algebraic spaces are themselves chart
conditions of Stacks 03MJ, so the two instances which the scheme-level base change of
Stacks 0DSC asks of the chart morphism are read off the hypotheses on `f` directly.

The open subscheme of a chart which a set of points cuts out is produced inside the site by
`AlgebraicGeometry.exists_restrict_bigFppfOver`, and the bijection between the points of a
representable presheaf and the points of the representing scheme is a homeomorphism by
`AlgebraicGeometry.Space.isOpen_pointTopology_yoneda_iff_isOpen_image`. Both directions of the
chart computation use that open subscheme, in the first case to restrict the chart to the part
lying over a member of the family, in the second to turn the scheme-level nodal locus into a
chart of an open subspace of the source.

## References

* [Stacks Project, Tag 0DSH](https://stacks.math.columbia.edu/tag/0DSH)
* [Stacks Project, Tag 0DSC](https://stacks.math.columbia.edu/tag/0DSC)
* [Stacks Project, Tag 0DSG](https://stacks.math.columbia.edu/tag/0DSG)
* [Stacks Project, Tag 03BZ](https://stacks.math.columbia.edu/tag/03BZ)
* [Stacks Project, Tag 03IE](https://stacks.math.columbia.edu/tag/03IE)
* [Stacks Project, Tag 02X1](https://stacks.math.columbia.edu/tag/02X1)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for pullbacks of presheaves on the big fppf site is slow
/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance hasPullbacks_presheaf_nodalOpenSubspace :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

local instance (priority := high) hasPullback_presheaf_nodalOpenSubspace
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-! ### The locus and its two formal properties -/

/-- An open subspace of the source of a morphism of algebraic spaces over `S` on which the
morphism restricts to one which is at-worst-nodal of relative dimension one. -/
def IsNodalOpen {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y) (W : Subfunctor X) : Prop :=
  IsOpenSubspace B S hS W ∧ IsAtWorstNodalOfRelativeDimensionOne B S hS (W.ι ≫ f)

/-- The set of points of the source covered by the open subspaces on which the morphism is
at-worst-nodal of relative dimension one. -/
def nodalPointSet {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y) :
    Set (points B S hS X) :=
  ⋃ W : {W : Subfunctor X // IsNodalOpen B S hS f W},
    Set.range (pointsMap B S hS W.1.toFunctor W.1.ι)

/-- The union of the point sets of the open subspaces on which the morphism is at-worst-nodal
of relative dimension one is open, each of them being open. -/
theorem isOpen_nodalPointSet {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y) :
    IsOpen (nodalPointSet B S hS f) :=
  isOpen_iUnion fun W =>
    isOpen_range_pointsMap_of_isOpenImmersion B S hS W.1.ι W.2.1.2

/-- **The candidate largest at-worst-nodal open subspace**: the open subspace of Stacks 03BZ
cut out by the union of the point sets of the open subspaces on which the morphism is
at-worst-nodal of relative dimension one. -/
def nodalOpenSubspace {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y) : Subfunctor X :=
  openSubspaceOfPoints B S hS X (nodalPointSet B S hS f)

/-- The point set of the locus is the union it is cut out by. -/
theorem range_pointsMap_nodalOpenSubspace {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y) :
    Set.range (pointsMap B S hS (nodalOpenSubspace B S hS f).toFunctor
      (nodalOpenSubspace B S hS f).ι) = nodalPointSet B S hS f :=
  range_pointsMap_ι_openSubspaceOfPoints B S hS _

/-- The locus is an open subspace, by part (1) of Stacks 03BZ. -/
theorem isOpenSubspace_nodalOpenSubspace {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (f : X ⟶ Y) :
    IsOpenSubspace B S hS (nodalOpenSubspace B S hS f) :=
  isOpenSubspace_openSubspaceOfPoints B S hS hX _ (isOpen_nodalPointSet B S hS f)

/-- **Maximality.** Every open subspace on which the morphism restricts to one which is
at-worst-nodal of relative dimension one is contained in the locus: its point set is one of
the sets the union is taken over. -/
theorem le_nodalOpenSubspace {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (f : X ⟶ Y) {W : Subfunctor X}
    (hW : IsNodalOpen B S hS f W) : W ≤ nodalOpenSubspace B S hS f :=
  le_of_range_pointsMap_ι_subset B S hS (isOpenSubspace_nodalOpenSubspace B S hS hX f) <| by
    rw [range_pointsMap_nodalOpenSubspace]
    exact Set.subset_iUnion
      (fun W : {W : Subfunctor X // IsNodalOpen B S hS f W} =>
        Set.range (pointsMap B S hS W.1.toFunctor W.1.ι)) ⟨W, hW⟩

/-- Precomposing an at-worst-nodal morphism of relative dimension one with an étale morphism
of schemes leaves it at-worst-nodal of relative dimension one: this is the left-respecting
clause of the étale locality of Stacks 0C5B, 0C5D and 0C5E. -/
private theorem nodal_precomp_etale {W X S : Scheme.{u}} (e : W ⟶ X)
    (he : AlgebraicGeometry.Etale e) (g : X ⟶ S)
    (hg : AlgebraicGeometry.IsAtWorstNodalOfRelativeDimensionOne g) :
    AlgebraicGeometry.IsAtWorstNodalOfRelativeDimensionOne (e ≫ g) :=
  have hloc := AlgebraicGeometry.isAtWorstNodalOfRelativeDimensionOne_isEtaleLocalOnSourceAndTarget
  hloc.precomp.precomp e he g hg

private theorem nodal_comp_of_range_eq {X Y Z T : Scheme.{u}} (j : Y ⟶ X) (k : Z ⟶ X)
    [AlgebraicGeometry.IsOpenImmersion j] [AlgebraicGeometry.IsOpenImmersion k]
    (h : Set.range k = Set.range j) (g : X ⟶ T)
    (hg : AlgebraicGeometry.IsAtWorstNodalOfRelativeDimensionOne (j ≫ g)) :
    AlgebraicGeometry.IsAtWorstNodalOfRelativeDimensionOne (k ≫ g) := by
  have := nodal_precomp_etale (AlgebraicGeometry.IsOpenImmersion.isoOfRangeEq k j h).hom
    inferInstance _ hg
  rwa [← Category.assoc, AlgebraicGeometry.IsOpenImmersion.isoOfRangeEq_hom_fac] at this

private theorem mem_range_pointsMap_yoneda_of_mem_range {U V : BigFppfOver B S hS} (i : U ⟶ V)
    (z : points B S hS (yoneda.obj V))
    (hz : pointsToScheme B S hS V z ∈ Set.range ((BigFppfOver.toScheme B S hS).map i)) :
    z ∈ Set.range (pointsMap B S hS (yoneda.obj U) (yoneda.map i)) := by
  obtain ⟨y, hy⟩ := hz
  obtain ⟨w, hw⟩ := surjective_pointsToScheme B S hS U y
  exact ⟨w, injective_pointsToScheme B S hS V (by rw [pointsToScheme_pointsMap_yoneda, hw, hy])⟩

/-! ### The chart computation -/

/-- Restricting an étale chart to an open immersion and factoring through an open subspace gives
an étale chart of the subspace, lying over the same chart of the target. -/
private theorem etale_and_square_of_factors_open {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (f : X ⟶ Y) {U₀ V₀ UW : BigFppfOver B S hS}
    (a : yoneda.obj U₀ ⟶ X) (b : yoneda.obj V₀ ⟶ Y) (α : U₀ ⟶ V₀)
    (ha : HasSchemeProperty B S hS (@AlgebraicGeometry.Etale.{u}) a)
    (hsq : yoneda.map α ≫ b = a ≫ f) (W : Subfunctor X) (hW : IsOpenSubspace B S hS W)
    (i : UW ⟶ U₀) [AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map i)]
    (k : yoneda.obj UW ⟶ W.toFunctor) (hk : k ≫ W.ι = yoneda.map i ≫ a) :
    HasSchemeProperty B S hS (@AlgebraicGeometry.Etale.{u}) k ∧
      yoneda.map (i ≫ α) ≫ b = k ≫ W.ι ≫ f := by
  have hiaE : HasSchemeProperty B S hS (@AlgebraicGeometry.Etale.{u}) (yoneda.map i ≫ a) :=
    presheafEtale_comp B S hS ((presheaf_yoneda_map_etale_iff B S hS i).mpr inferInstance) ha
  refine ⟨(isEtale_iff_presheaf_of_yoneda B S hS k).mp
      (isEtale_of_isEtale_over B S hS (isAlgebraicSpace_yoneda B S hS UW) hW.1 hX
        k (yoneda.map i ≫ a) W.ι ((isEtale_iff_presheaf_of_yoneda B S hS _).mpr hiaE)
        (isEtale_ι_of_isOpenSubspace hW) hk), ?_⟩
  rw [Functor.map_comp, Category.assoc, hsq, ← Category.assoc, ← hk, Category.assoc]

section Chart

variable {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
  {U₀ V₀ : BigFppfOver B S hS}
  (a : yoneda.obj U₀ ⟶ X) (b : yoneda.obj V₀ ⟶ Y) (α : U₀ ⟶ V₀)

include hX in
/-- A point of an étale chart of the source whose image lies in the locus lies in the
scheme-level nodal locus of the chart morphism.

The point lies over a member `W` of the family; restricting the chart to the part lying over
`W` gives an étale chart of `W`, which together with the chart of the target is a commuting
square of étale charts over the restriction of the morphism to `W`, so the chart condition of
Stacks 03MJ applies to it and the restricted chart morphism is at-worst-nodal of relative
dimension one. Maximality of the scheme-level nodal locus of Stacks 0DSC finishes. -/
private theorem mem_chart_nodalLocus_of_mem_nodalPointSet
    (ha : HasSchemeProperty B S hS (@AlgebraicGeometry.Etale.{u}) a)
    (hb : HasSchemeProperty B S hS (@AlgebraicGeometry.Etale.{u}) b)
    (hsq : yoneda.map α ≫ b = a ≫ f) (z : points B S hS (yoneda.obj U₀))
    (hz : pointsMap B S hS (yoneda.obj U₀) a z ∈ nodalPointSet B S hS f) :
    pointsToScheme B S hS U₀ z ∈
      AlgebraicGeometry.nodalLocus ((BigFppfOver.toScheme B S hS).map α) := by
  obtain ⟨W, hzW⟩ := Set.mem_iUnion.mp hz
  have hRopen : IsOpen (pointsMap B S hS (yoneda.obj U₀) a ⁻¹'
      Set.range (pointsMap B S hS W.1.toFunctor W.1.ι)) :=
    (isOpen_range_pointsMap_of_isOpenImmersion B S hS W.1.ι W.2.1.2).preimage
      (continuous_pointsMap B S hS a)
  set T : ((BigFppfOver.toScheme B S hS).obj U₀).Opens :=
    ⟨pointsToScheme B S hS U₀ '' (pointsMap B S hS (yoneda.obj U₀) a ⁻¹'
        Set.range (pointsMap B S hS W.1.toFunctor W.1.ι)),
      (isOpen_pointTopology_yoneda_iff_isOpen_image B S hS U₀ _).mp hRopen⟩
  obtain ⟨UW, i, hi, hirange, -⟩ := AlgebraicGeometry.exists_restrict_bigFppfOver U₀ T
  have hi' : AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map i) := hi
  have hsub : Set.range (pointsMap B S hS (yoneda.obj UW) (yoneda.map i ≫ a)) ⊆
      Set.range (pointsMap B S hS W.1.toFunctor W.1.ι) := by
    rintro - ⟨w, rfl⟩
    rw [pointsMap_comp_apply]
    have hmem : pointsToScheme B S hS U₀
        (pointsMap B S hS (yoneda.obj UW) (yoneda.map i) w) ∈ (T : Set _) := by
      rw [pointsToScheme_pointsMap_yoneda, ← hirange]
      exact ⟨_, rfl⟩
    obtain ⟨r, hrR, hr⟩ := hmem
    exact (injective_pointsToScheme B S hS U₀ hr) ▸ hrR
  obtain ⟨k, hk⟩ := (factorsThrough_openSubspace_iff_points B S hS hX
    (isAlgebraicSpace_yoneda B S hS UW) W.1 W.2.1 (yoneda.map i ≫ a)).mpr hsub
  obtain ⟨hkE, hsq'⟩ := etale_and_square_of_factors_open B S hS hX f a b α ha hsq W.1 W.2.1 i k hk
  have hP : AlgebraicGeometry.IsAtWorstNodalOfRelativeDimensionOne
      ((BigFppfOver.toScheme B S hS).map i ≫ (BigFppfOver.toScheme B S hS).map α) := by
    rw [← Functor.map_comp]
    exact W.2.2 UW V₀ k b (i ≫ α) hkE hb hsq'
  have hrange : Set.range T.ι = Set.range ((BigFppfOver.toScheme B S hS).map i) := by
    rw [hirange, Scheme.Opens.range_ι]
  have hTle : T ≤ AlgebraicGeometry.nodalLocus ((BigFppfOver.toScheme B S hS).map α) :=
    AlgebraicGeometry.le_nodalLocus _ (nodal_comp_of_range_eq _ T.ι hrange _ hP)
  exact hTle ⟨z, hzW, rfl⟩

include hX hY in
/-- A point of an étale chart of the source lying in the scheme-level nodal locus of the chart
morphism has its image in the locus.

The scheme-level nodal locus of Stacks 0DSC is an open subscheme of the chart on which the
chart morphism is at-worst-nodal of relative dimension one; its image in the source is the
point set of an open subspace `Z`, the chart being an open map on points, and the locus is a
surjective étale chart of `Z`. Criterion (7) of Stacks 0DSG on that single chart square shows
that the restriction of the morphism to `Z` is at-worst-nodal of relative dimension one, so
`Z` is a member of the family. -/
private theorem mem_nodalPointSet_of_mem_chart_nodalLocus
    (ha : HasSchemeProperty B S hS (@AlgebraicGeometry.Etale.{u}) a)
    (hb : HasSchemeProperty B S hS (@AlgebraicGeometry.Etale.{u}) b)
    (hsq : yoneda.map α ≫ b = a ≫ f) (z : points B S hS (yoneda.obj U₀))
    (hz : pointsToScheme B S hS U₀ z ∈
      AlgebraicGeometry.nodalLocus ((BigFppfOver.toScheme B S hS).map α)) :
    pointsMap B S hS (yoneda.obj U₀) a z ∈ nodalPointSet B S hS f := by
  obtain ⟨UN, i, hi, hirange, -⟩ := AlgebraicGeometry.exists_restrict_bigFppfOver U₀
    (AlgebraicGeometry.nodalLocus ((BigFppfOver.toScheme B S hS).map α))
  have hi' : AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map i) := hi
  have hiaE : HasSchemeProperty B S hS (@AlgebraicGeometry.Etale.{u}) (yoneda.map i ≫ a) :=
    presheafEtale_comp B S hS ((presheaf_yoneda_map_etale_iff B S hS i).mpr inferInstance) ha
  have hRopen : IsOpen (Set.range (pointsMap B S hS (yoneda.obj UN) (yoneda.map i ≫ a))) :=
    (isOpenMap_pointsMap_of_presheafEtale B S hS _ hiaE).isOpen_range
  set Z : Subfunctor X := openSubspaceOfPoints B S hS X
    (Set.range (pointsMap B S hS (yoneda.obj UN) (yoneda.map i ≫ a)))
  have hZopen : IsOpenSubspace B S hS Z :=
    isOpenSubspace_openSubspaceOfPoints B S hS hX _ hRopen
  have hZpts : Set.range (pointsMap B S hS Z.toFunctor Z.ι) =
      Set.range (pointsMap B S hS (yoneda.obj UN) (yoneda.map i ≫ a)) :=
    range_pointsMap_ι_openSubspaceOfPoints B S hS _
  obtain ⟨k, hk⟩ := (factorsThrough_openSubspace_iff_points B S hS hX
    (isAlgebraicSpace_yoneda B S hS UN) Z hZopen (yoneda.map i ≫ a)).mpr (by rw [hZpts])
  obtain ⟨hkE, hsq'⟩ := etale_and_square_of_factors_open B S hS hX f a b α ha hsq Z hZopen i k hk
  have hkS : IsSurjective B S hS k := by
    intro t
    obtain ⟨w, hw⟩ := hZpts.subset ⟨t, rfl⟩
    refine ⟨w, pointsMap_injective_of_mono B S hS Z.ι ?_⟩
    rw [← pointsMap_comp_apply, hk]
    exact hw
  have hNrange : Set.range ((BigFppfOver.toScheme B S hS).map i) =
      Set.range (AlgebraicGeometry.nodalLocus ((BigFppfOver.toScheme B S hS).map α)).ι := by
    rw [hirange, Scheme.Opens.range_ι]
  have hP : AlgebraicGeometry.IsAtWorstNodalOfRelativeDimensionOne
      ((BigFppfOver.toScheme B S hS).map (i ≫ α)) := by
    rw [Functor.map_comp]
    exact nodal_comp_of_range_eq _ _ hNrange _
      (AlgebraicGeometry.nodalLocus_isAtWorstNodalOfRelativeDimensionOne _)
  have htfae :=
    (isAtWorstNodalOfRelativeDimensionOne_tfae B S hS hZopen.1 hY (Z.ι ≫ f)).out 7 1
  have hZgood : IsAtWorstNodalOfRelativeDimensionOne B S hS (Z.ι ≫ f) :=
    htfae.mp ⟨UN, V₀, k, b, i ≫ α, (isEtale_iff_presheaf_of_yoneda B S hS k).mpr hkE,
      (isEtale_iff_presheaf_of_yoneda B S hS b).mpr hb, hkS, hsq'.symm, hP⟩
  refine Set.mem_iUnion.mpr ⟨⟨Z, hZopen, hZgood⟩, ?_⟩
  rw [hZpts]
  obtain ⟨w, rfl⟩ := mem_range_pointsMap_yoneda_of_mem_range B S hS i z (by
    rw [hirange]
    exact hz)
  exact ⟨w, by rw [pointsMap_comp_apply]⟩

include hX hY in
/-- **The chart computation.** The part of an étale chart of the source lying over the locus is
exactly the scheme-level nodal locus of Stacks 0DSC of the chart morphism. -/
private theorem preimage_pointsMap_nodalPointSet_eq_chart_nodalLocus
    (ha : HasSchemeProperty B S hS (@AlgebraicGeometry.Etale.{u}) a)
    (hb : HasSchemeProperty B S hS (@AlgebraicGeometry.Etale.{u}) b)
    (hsq : yoneda.map α ≫ b = a ≫ f) :
    pointsMap B S hS (yoneda.obj U₀) a ⁻¹' nodalPointSet B S hS f =
      pointsToScheme B S hS U₀ ⁻¹'
        (AlgebraicGeometry.nodalLocus ((BigFppfOver.toScheme B S hS).map α) : Set _) :=
  Set.ext fun z =>
    ⟨mem_chart_nodalLocus_of_mem_nodalPointSet B S hS hX f a b α ha hb hsq z,
      mem_nodalPointSet_of_mem_chart_nodalLocus B S hS hX hY f a b α ha hb hsq z⟩

end Chart

/-! ### The locus is at-worst-nodal of relative dimension one -/

section Locus

variable {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)

include hX in
/-- **The restriction of the morphism to the locus is at-worst-nodal of relative dimension
one.**

A commuting square of étale charts over the restriction has its chart of the source landing in
the locus, so by the chart computation the scheme-level nodal locus of Stacks 0DSC of the chart
morphism is the whole chart; the chart morphism is therefore at-worst-nodal of relative
dimension one, which is the chart condition of Stacks 03MJ. -/
theorem isAtWorstNodalOfRelativeDimensionOne_nodalOpenSubspace :
    IsAtWorstNodalOfRelativeDimensionOne B S hS ((nodalOpenSubspace B S hS f).ι ≫ f) := by
  intro U₀ V₀ a b α ha hb hsq
  have hopen := isOpenSubspace_nodalOpenSubspace B S hS hX f
  have haE : HasSchemeProperty B S hS (@AlgebraicGeometry.Etale.{u})
      (a ≫ (nodalOpenSubspace B S hS f).ι) :=
    presheafEtale_comp B S hS ha (presheaf_etale_of_isOpenImmersion B S hS hopen.2)
  have hsq2 : yoneda.map α ≫ b = (a ≫ (nodalOpenSubspace B S hS f).ι) ≫ f := by
    rw [Category.assoc]; exact hsq
  have htop : AlgebraicGeometry.nodalLocus ((BigFppfOver.toScheme B S hS).map α) = ⊤ := by
    refine eq_top_iff.mpr fun x _ => ?_
    obtain ⟨z, hz⟩ := surjective_pointsToScheme B S hS U₀ x
    rw [← hz]
    refine mem_chart_nodalLocus_of_mem_nodalPointSet B S hS hX f
      (a ≫ (nodalOpenSubspace B S hS f).ι) b α haE hb hsq2 z ?_
    rw [pointsMap_comp_apply, ← range_pointsMap_nodalOpenSubspace B S hS f]
    exact ⟨_, rfl⟩
  have h0 := AlgebraicGeometry.nodalLocus_isAtWorstNodalOfRelativeDimensionOne
    ((BigFppfOver.toScheme B S hS).map α)
  rw [htop] at h0
  have heq : ((BigFppfOver.toScheme B S hS).obj U₀).topIso.inv ≫
      (⊤ : ((BigFppfOver.toScheme B S hS).obj U₀).Opens).ι ≫
      (BigFppfOver.toScheme B S hS).map α = (BigFppfOver.toScheme B S hS).map α := by
    rw [← Category.assoc, Scheme.toIso_inv_ι, Category.id_comp]
  exact heq ▸ nodal_precomp_etale _ inferInstance _ h0

include hX in
/-- **Existence and maximality.** The locus is the greatest open subspace of the source on
which the morphism restricts to one which is at-worst-nodal of relative dimension one. -/
theorem nodalOpenSubspace_isGreatest :
    IsGreatest {W : Subfunctor X | IsNodalOpen B S hS f W} (nodalOpenSubspace B S hS f) :=
  ⟨⟨isOpenSubspace_nodalOpenSubspace B S hS hX f,
      isAtWorstNodalOfRelativeDimensionOne_nodalOpenSubspace B S hS hX f⟩,
    fun _ hW => le_nodalOpenSubspace B S hS hX f hW⟩

end Locus

/-! ### Compatibility with arbitrary base change -/

/-- The compatible surjective étale charts of Stacks 02X1 for a fibre product of algebraic
spaces, restated for morphisms of presheaves on the big fppf site of `S` together with
algebraicity hypotheses. -/
private theorem exists_compatible_etale_charts_presheaf
    {X Y Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hY' : IsAlgebraicSpace B S hS Y') (f : X ⟶ Y) (g : Y' ⟶ Y) :
    ∃ (U V U' V' : BigFppfOver B S hS) (p : U ⟶ V) (q : V' ⟶ V)
      (pU : U' ⟶ U) (pV' : U' ⟶ V') (v : yoneda.obj V ⟶ Y)
      (aa : yoneda.obj U ⟶ pullback v f) (bb : yoneda.obj V' ⟶ pullback v g)
      (cc : yoneda.obj U' ⟶ pullback f g),
      IsPullback ((BigFppfOver.toScheme B S hS).map pU)
          ((BigFppfOver.toScheme B S hS).map pV')
          ((BigFppfOver.toScheme B S hS).map p)
          ((BigFppfOver.toScheme B S hS).map q) ∧
        aa ≫ pullback.fst v f = yoneda.map p ∧
        cc ≫ pullback.fst f g = yoneda.map pU ≫ aa ≫ pullback.snd v f ∧
        cc ≫ pullback.snd f g = yoneda.map pV' ≫ bb ≫ pullback.snd v g ∧
        HasSchemeProperty B S hS (@AlgebraicGeometry.Etale.{u}) v ∧
        HasSchemeProperty B S hS (@AlgebraicGeometry.Etale.{u}) aa ∧
        HasSchemeProperty B S hS (@AlgebraicGeometry.Etale.{u}) bb ∧
        HasSchemeProperty B S hS (@AlgebraicGeometry.Etale.{u}) cc ∧
        (MorphismProperty.inverseImage
          (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS)).presheaf cc := by
  obtain ⟨U, V, U', V', p, q, pU, pV', v, aa, bb, cc, h1, h2, -, h4, h5,
    -, hvE, -, haE, -, hbE, hcS, hcE⟩ :=
    exists_compatible_etale_charts B S hS (X := ⟨X, hX⟩) (Y := ⟨Y, hY⟩) (Y' := ⟨Y', hY'⟩)
      (ObjectProperty.homMk f) (ObjectProperty.homMk g)
  exact ⟨U, V, U', V', p, q, pU, pV', v, aa, bb, cc, h1, h2, h4, h5,
    hvE, haE, hbE, hcE, hcS⟩

/-- A base change of an étale chart is an étale chart. -/
private theorem presheafEtale_pullback_snd {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (w : F ⟶ H) (t : G ⟶ H) (hw : HasSchemeProperty B S hS (@AlgebraicGeometry.Etale.{u}) w) :
    HasSchemeProperty B S hS (@AlgebraicGeometry.Etale.{u}) (pullback.snd w t) :=
  let PE := MorphismProperty.inverseImage
    (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)
  have : PE.IsStableUnderBaseChange :=
    inverseImage_isStableUnderBaseChange B S hS inferInstance
  (MorphismProperty.relative_isStableUnderBaseChange PE).of_isPullback
    (IsPullback.of_hasPullback w t) hw

/-- **Formation of the locus commutes with arbitrary base change.** In the fibre product of the
source with an arbitrary morphism `g` into the target, the locus of the base change of the
morphism is the inverse image of the locus.

Both sides are open subspaces, so by part (1) of Stacks 03BZ it is enough to compare their
point sets, and those may be compared after pulling back along a chart of the fibre product
which is surjective on points. The compatible charts of Stacks 02X1 provide such a chart
together with a cartesian square of charts, so the chart computation turns the comparison into
the base-change half of the scheme-level Stacks 0DSC. -/
theorem nodalOpenSubspace_baseChange {X Y Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hY' : IsAlgebraicSpace B S hS Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    (hflat : IsFlat B S hS f) (hfp : IsLocallyOfFinitePresentation B S hS f) :
    nodalOpenSubspace B S hS (pullback.snd f g) =
      (nodalOpenSubspace B S hS f).preimage (pullback.fst f g) := by
  have hXY' : IsAlgebraicSpace B S hS (pullback f g) :=
    isAlgebraicSpace_pullback B S hS f g hX hY' hY
  obtain ⟨U, V, U', V', p, q, pU, pV', v, aa, bb, cc, hsqSch, hap, hcX, hcY',
    hvE, haE, hbE, hcE, hcS⟩ := exists_compatible_etale_charts_presheaf B S hS hX hY hY' f g
  have htXE : HasSchemeProperty B S hS (@AlgebraicGeometry.Etale.{u}) (aa ≫ pullback.snd v f) :=
    presheafEtale_comp B S hS haE (presheafEtale_pullback_snd B S hS v f hvE)
  have htY'E : HasSchemeProperty B S hS (@AlgebraicGeometry.Etale.{u}) (bb ≫ pullback.snd v g) :=
    presheafEtale_comp B S hS hbE (presheafEtale_pullback_snd B S hS v g hvE)
  have hsqX : yoneda.map p ≫ v = (aa ≫ pullback.snd v f) ≫ f := by
    rw [← hap, Category.assoc, Category.assoc, pullback.condition]
  have hflatp : AlgebraicGeometry.Flat ((BigFppfOver.toScheme B S hS).map p) :=
    hflat U V (aa ≫ pullback.snd v f) v p htXE hvE hsqX
  have hfpp : AlgebraicGeometry.LocallyOfFinitePresentation
      ((BigFppfOver.toScheme B S hS).map p) :=
    hfp U V (aa ≫ pullback.snd v f) v p htXE hvE hsqX
  have hbc : AlgebraicGeometry.nodalLocus ((BigFppfOver.toScheme B S hS).map pV') =
      (BigFppfOver.toScheme B S hS).map pU ⁻¹ᵁ
        AlgebraicGeometry.nodalLocus ((BigFppfOver.toScheme B S hS).map p) :=
    AlgebraicGeometry.nodalLocus_baseChange ((BigFppfOver.toScheme B S hS).map pU)
      ((BigFppfOver.toScheme B S hS).map pV') ((BigFppfOver.toScheme B S hS).map p)
      ((BigFppfOver.toScheme B S hS).map q) hsqSch
  have hchart := preimage_pointsMap_nodalPointSet_eq_chart_nodalLocus B S hS hX hY
    f (aa ≫ pullback.snd v f) v p htXE hvE hsqX
  have hchart' := preimage_pointsMap_nodalPointSet_eq_chart_nodalLocus B S hS hXY' hY'
    (pullback.snd f g) cc (bb ≫ pullback.snd v g) pV' hcE htY'E hcY'.symm
  have hccS : Function.Surjective (pointsMap B S hS (yoneda.obj U') cc) :=
    isSurjective_of_presheafSurjective B S hS cc hcS
  have hpts : nodalPointSet B S hS (pullback.snd f g) =
      pointsMap B S hS (pullback f g) (pullback.fst f g) ⁻¹' nodalPointSet B S hS f := by
    refine hccS.preimage_injective ?_
    calc pointsMap B S hS (yoneda.obj U') cc ⁻¹' nodalPointSet B S hS (pullback.snd f g)
        = pointsToScheme B S hS U' ⁻¹'
            (AlgebraicGeometry.nodalLocus ((BigFppfOver.toScheme B S hS).map pV') : Set _) :=
          hchart'
      _ = pointsToScheme B S hS U' ⁻¹' ((BigFppfOver.toScheme B S hS).map pU ⁻¹'
            (AlgebraicGeometry.nodalLocus ((BigFppfOver.toScheme B S hS).map p) : Set _)) := by
          rw [hbc]; rfl
      _ = pointsMap B S hS (yoneda.obj U') (yoneda.map pU) ⁻¹' (pointsToScheme B S hS U ⁻¹'
            (AlgebraicGeometry.nodalLocus ((BigFppfOver.toScheme B S hS).map p) : Set _)) := by
          ext w
          simp only [Set.mem_preimage]
          rw [pointsToScheme_pointsMap_yoneda]
      _ = pointsMap B S hS (yoneda.obj U') (yoneda.map pU) ⁻¹'
            (pointsMap B S hS (yoneda.obj U) (aa ≫ pullback.snd v f) ⁻¹'
              nodalPointSet B S hS f) := by rw [hchart]
      _ = pointsMap B S hS (yoneda.obj U') (yoneda.map pU ≫ aa ≫ pullback.snd v f) ⁻¹'
            nodalPointSet B S hS f := by
          rw [pointsMap_comp B S hS (yoneda.obj U') (yoneda.map pU) (aa ≫ pullback.snd v f),
            Set.preimage_comp]
      _ = pointsMap B S hS (yoneda.obj U') (cc ≫ pullback.fst f g) ⁻¹'
            nodalPointSet B S hS f := by rw [hcX]
      _ = pointsMap B S hS (yoneda.obj U') cc ⁻¹'
            (pointsMap B S hS (pullback f g) (pullback.fst f g) ⁻¹'
              nodalPointSet B S hS f) := by
          rw [pointsMap_comp B S hS (yoneda.obj U') cc (pullback.fst f g), Set.preimage_comp]
  have hopen1 : IsOpenSubspace B S hS (nodalOpenSubspace B S hS (pullback.snd f g)) :=
    isOpenSubspace_nodalOpenSubspace B S hS hXY' (pullback.snd f g)
  have hopen2 : IsOpenSubspace B S hS
      ((nodalOpenSubspace B S hS f).preimage (pullback.fst f g)) :=
    isOpenSubspace_preimage B S hS (pullback.fst f g) (nodalOpenSubspace B S hS f) hX hXY'
      (isOpenSubspace_nodalOpenSubspace B S hS hX f)
  have hpts2 : Set.range (pointsMap B S hS
      ((nodalOpenSubspace B S hS f).preimage (pullback.fst f g)).toFunctor
      ((nodalOpenSubspace B S hS f).preimage (pullback.fst f g)).ι) =
      pointsMap B S hS (pullback f g) (pullback.fst f g) ⁻¹' nodalPointSet B S hS f := by
    rw [range_pointsMap_preimage_ι, range_pointsMap_nodalOpenSubspace]
  refine le_antisymm (le_of_range_pointsMap_ι_subset B S hS hopen2 ?_)
    (le_of_range_pointsMap_ι_subset B S hS hopen1 ?_) <;>
    rw [range_pointsMap_nodalOpenSubspace, hpts2, hpts]

/-! ### Families of nodal curves -/

/-- **Stacks 0DSH.** Let `S` be a scheme and let `f : X ⟶ Y` be a morphism of algebraic spaces
over `S` which is flat and locally of finite presentation. Then there is a maximal open
subspace `X' ⊆ X` such that the restriction of `f` to `X'` is at-worst-nodal of relative
dimension one, and formation of `X'` commutes with arbitrary base change.

The maximal open subspace is `AlgebraicGeometry.Space.nodalOpenSubspace`; it is an open
subspace on which the restriction of `f` is at-worst-nodal of relative dimension one, and it
contains every open subspace with that property, which is the content of the `IsGreatest`
assertion. The second assertion is that for an arbitrary morphism `g : Y' ⟶ Y` of algebraic
spaces over `S`, the locus of the base change `X ×_Y Y' ⟶ Y'` of `f` along `g` is the inverse
image of the locus of `f` under the projection to `X`. -/
@[stacks 0DSH]
theorem exists_isGreatest_isNodalOpen_baseChange {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hflat : IsFlat B S hS f) (hfp : IsLocallyOfFinitePresentation B S hS f) :
    IsGreatest {W : Subfunctor X | IsNodalOpen B S hS f W} (nodalOpenSubspace B S hS f) ∧
      ∀ Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u, IsAlgebraicSpace B S hS Y' →
        ∀ g : Y' ⟶ Y, nodalOpenSubspace B S hS (pullback.snd f g) =
          (nodalOpenSubspace B S hS f).preimage (pullback.fst f g) :=
  ⟨nodalOpenSubspace_isGreatest B S hS hX f,
    fun _ hY' g => nodalOpenSubspace_baseChange B S hS hX hY hY' f g hflat hfp⟩

end AlgebraicGeometry.Space

end
