module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartBasicOpenLocalization
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionPointEmbedding
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FlatEtaleLocalRing
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenComplement
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SubspacePreimage

/-!
# Lifting a neighbourhood of the image of a geometric point

Let `f : F ⟶ G` be a morphism of algebraic spaces and `x` a geometric point of `F`.  Every small
étale neighbourhood `V` of `f ∘ x` is the target of a commuting diagram of pointed étale charts
over `f` whose source is a small étale neighbourhood of `x` (the base change of the chart of `V`),
and along such a diagram the homomorphism of étale local rings of Stacks 04NG sends the germ of a
regular function to the germ of its pullback.

This is the statement the stalkwise proof of Stacks 0AF0 needs to compare, at a point `ȳ` of
`f⁻¹Z`, the images in `𝒪_{Y, ȳ}` of the generators of the stalk of the ideal of `Z` with germs
of functions on charts of `Y`.  The construction is the one inside the proof of Stacks 04NG
(`AlgebraicGeometry.Space.existsUnique_etaleLocalRingMap`), where it is private.

## Main results

* `AlgebraicGeometry.Space.exists_smallEtaleNeighborhood_lift`: the lift.
* `AlgebraicGeometry.Space.etaleLocalRingMap_germ`: the homomorphism of étale local rings on germs
  along such a diagram.
* `AlgebraicGeometry.Space.range_pointsMap_subfunctor_preimage`: the point set of an inverse image
  of a subfunctor is the inverse image of its point set.
* `AlgebraicGeometry.Space.preimage_chartPointsMap_preimage_eq_zeroLocus`: if `Z` is cut out on a
  chart `V` of `G` by functions `gᵢ` (as a point set), then `p⁻¹Z` is cut out on a chart over `V`
  by their pullbacks.
* `AlgebraicGeometry.Space.range_pointsMap_openChart_basicOpen_subset`: the basic-open charts
  `D(gᵢ)` lie in the open complement of `Z`.

## References

* [Stacks Project, Tag 04NG](https://stacks.math.columbia.edu/tag/04NG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **A small étale neighbourhood of the image of a geometric point lifts.**  Given a small étale
neighbourhood `V` of `f ∘ x` and one, `N`, of `x`, the base change of the chart of `V` along the
chart of `N` is a small étale neighbourhood `U` of `x` lying over both, compatibly with `f`. -/
theorem exists_smallEtaleNeighborhood_lift (f : F ⟶ G) {x : GeometricPoint B S hS F}
    (N : SmallEtaleNeighborhood x) (V : SmallEtaleNeighborhood (geometricPointMap f x)) :
    ∃ (U : SmallEtaleNeighborhood x) (_ : U ⟶ N) (g : U.chart.obj.left ⟶ V.chart.obj.left),
      U.chart.obj.hom ≫ f = yoneda.map g ≫ V.chart.obj.hom ∧ U.point ≫ g = V.point := by
  set q : yoneda.obj N.chart.obj.left ⟶ G := N.chart.obj.hom ≫ f with hq
  set s : V.chart.property.rep.pullback q ⟶ N.chart.obj.left := V.chart.property.rep.snd q
  have sq : IsPullback (V.chart.property.rep.fst q) (yoneda.map s) V.chart.obj.hom q :=
    V.chart.property.rep.isPullback q
  set g : V.chart.property.rep.pullback q ⟶ V.chart.obj.left :=
    yoneda.preimage (V.chart.property.rep.fst q)
  have hg : yoneda.map g = V.chart.property.rep.fst q := yoneda.map_preimage _
  have hchart : IsEtaleChart B S hS F
      (CostructuredArrow.mk (yoneda.map s ≫ N.chart.obj.hom)) :=
    etale_comp_of_scheme B S hS s N.chart.obj.hom
      (V.chart.property.property_snd q) N.chart.property
  set pointV : x.val.siteObject ⟶ V.chart.obj.left := V.point
  have hbase : yoneda.map pointV ≫ V.chart.obj.hom = yoneda.map N.point ≫ q := by
    apply yonedaEquiv.injective
    rw [yonedaEquiv_comp, yonedaEquiv_comp, yonedaEquiv_yoneda_map, yonedaEquiv_yoneda_map]
    change V.chart.obj.hom.app (Opposite.op x.val.siteObject) V.point =
      f.app (Opposite.op x.val.siteObject)
        (N.chart.obj.hom.app (Opposite.op x.val.siteObject) N.point)
    rw [N.point_comp]
    exact V.point_comp
  set pointR : x.val.siteObject ⟶ V.chart.property.rep.pullback q :=
    yoneda.preimage (sq.lift (yoneda.map pointV) (yoneda.map N.point) hbase)
  have hmapR : yoneda.map pointR = sq.lift (yoneda.map pointV) (yoneda.map N.point) hbase :=
    yoneda.map_preimage _
  have hrs : pointR ≫ s = N.point := by
    apply yoneda.map_injective
    rw [Functor.map_comp, hmapR]
    exact sq.lift_snd (yoneda.map pointV) (yoneda.map N.point) hbase
  have hrg : pointR ≫ g = V.point := by
    apply yoneda.map_injective
    rw [Functor.map_comp, hmapR, hg]
    exact sq.lift_fst (yoneda.map pointV) (yoneda.map N.point) hbase
  have hpc : (yoneda.map s ≫ N.chart.obj.hom).app (Opposite.op x.val.siteObject) pointR =
      x.val.value := by
    rw [show (yoneda.map s ≫ N.chart.obj.hom).app (Opposite.op x.val.siteObject) pointR =
        N.chart.obj.hom.app (Opposite.op x.val.siteObject) (pointR ≫ s) by simp, hrs]
    exact N.point_comp
  let U : SmallEtaleNeighborhood x :=
    { chart := ⟨CostructuredArrow.mk (yoneda.map s ≫ N.chart.obj.hom), hchart⟩
      point := pointR
      point_comp := hpc }
  refine ⟨U, ⟨ObjectProperty.homMk (CostructuredArrow.homMk s rfl), hrs⟩, g, ?_, hrg⟩
  change (yoneda.map s ≫ N.chart.obj.hom) ≫ f = yoneda.map g ≫ V.chart.obj.hom
  rw [Category.assoc, ← hq, ← sq.w, hg]

/-- **Stacks 04NG on germs.**  Along a commuting diagram of pointed charts over `f`, the
homomorphism of étale local rings sends the germ of a regular function to the germ of its
pullback. -/
theorem etaleLocalRingMap_germ (hF : IsAlgebraicSpace B S hS F) (f : F ⟶ G)
    {x : GeometricPoint B S hS F} (U : SmallEtaleNeighborhood x)
    (V : SmallEtaleNeighborhood (geometricPointMap f x))
    (g : U.chart.obj.left ⟶ V.chart.obj.left)
    (hcomm : U.chart.obj.hom ≫ f = yoneda.map g ≫ V.chart.obj.hom) (hpt : U.point ≫ g = V.point)
    (a : (structurePresheaf B S hS G).obj (Opposite.op V.chart)) :
    etaleLocalRingMap hF f x
        (etaleLocalRingGerm B S hS G (geometricPointMap f x) (Opposite.op V) a) =
      etaleLocalRingGerm B S hS F x (Opposite.op U)
        ((Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map g).op).hom a) :=
  (RingHom.congr_fun (etaleLocalRingMap_isEtaleLocalRingMap hF f x U V g hcomm hpt) a).symm

/-- The point set of the inverse image of a subfunctor is the inverse image of its point set. -/
theorem range_pointsMap_subfunctor_preimage (p : F ⟶ G) (Z : Subfunctor G) :
    Set.range (pointsMap B S hS (Z.preimage p).toFunctor (Z.preimage p).ι) =
      pointsMap B S hS F p ⁻¹' Set.range (pointsMap B S hS Z.toFunctor Z.ι) := by
  refine Set.eq_of_subset_of_subset ?_ ?_
  · rintro x ⟨z, rfl⟩
    refine ⟨pointsMap B S hS (Z.preimage p).toFunctor (Z.fromPreimage p) z, ?_⟩
    rw [← pointsMap_comp_apply, ← pointsMap_comp_apply, Subfunctor.fromPreimage_ι]
  · rintro x ⟨w, hw⟩
    obtain ⟨z, -, hz⟩ :=
      exists_points_of_isPullback B S hS (Subfunctor.isPullback_preimage p Z) w x hw
    exact ⟨z, hz⟩

/-- **The zero locus of pulled-back generators.**  If on the chart `V` of `G` the point set of
`Z` is the zero locus of `g`, then on a chart `U` of `F` lying over `V` along `p` the point set of
`p⁻¹Z` is the zero locus of the pullbacks of `g`. -/
theorem preimage_chartPointsMap_preimage_eq_zeroLocus (p : F ⟶ G) (Z : Subfunctor G)
    (U : SmallEtale B S hS F) (V : SmallEtale B S hS G) (m : U.obj.left ⟶ V.obj.left)
    (hcomm : U.obj.hom ≫ p = yoneda.map m ≫ V.obj.hom) {ι : Type*}
    (g : ι → Γ(chartScheme V, ⊤))
    (hg : chartPointsMap V ⁻¹' Set.range (pointsMap B S hS Z.toFunctor Z.ι) =
      (chartScheme V).zeroLocus (U := ⊤) (Set.range g)) :
    chartPointsMap U ⁻¹' Set.range (pointsMap B S hS (Z.preimage p).toFunctor (Z.preimage p).ι) =
      (chartScheme U).zeroLocus (U := ⊤)
        (Set.range fun i => ((BigFppfOver.toScheme B S hS).map m).appTop (g i)) := by
  have hpt : ∀ x : chartScheme U, pointsMap B S hS F p (chartPointsMap U x) =
      chartPointsMap V (((BigFppfOver.toScheme B S hS).map m) x) := by
    intro x
    simp only [chartPointsMap, Function.comp_apply]
    rw [← pointsMap_comp_apply, hcomm, pointsMap_comp_apply, pointsMap_yoneda_eq_conj]
    simp only [Function.comp_apply, Homeomorph.apply_symm_apply]
    rfl
  ext x
  rw [Set.mem_preimage, range_pointsMap_subfunctor_preimage, Set.mem_preimage, hpt,
    ← Set.mem_preimage, hg, ← Set.mem_preimage]
  have h := preimage_zeroLocus_ideal_map ((BigFppfOver.toScheme B S hS).map m)
    (Ideal.span (Set.range g))
  rw [Scheme.zeroLocus_span, Ideal.map_span, Scheme.zeroLocus_span, ← Set.range_comp] at h
  exact Iff.of_eq (congrArg (x ∈ ·) h)

attribute [local instance] pointTopology in
/-- **The basic opens of the generators lie off `Z`.**  If on the chart `V` the point set of
`Z` is the zero locus of the `gᵢ`, then every point of the basic-open chart `D(gᵢ)` lies in the
open complement of `Z`. -/
theorem range_pointsMap_openChart_basicOpen_subset (Z : Subfunctor F)
    (V : SmallEtale B S hS F) {ι : Type*} (g : ι → Γ(chartScheme V, ⊤))
    (hg : chartPointsMap V ⁻¹' Set.range (pointsMap B S hS Z.toFunctor Z.ι) =
      (chartScheme V).zeroLocus (U := ⊤) (Set.range g)) (i : ι) :
    Set.range (pointsMap B S hS _
        (openChart B S hS F V ((chartScheme V).basicOpen (g i))).1.hom) ⊆
      Set.range
        (pointsMap B S hS (openComplement B S hS Z).toFunctor (openComplement B S hS Z).ι) := by
  rw [range_pointsMap_ι_openComplement B S hS Z]
  rintro _ ⟨w, rfl⟩ hw
  have hval : pointsMap B S hS _ (openChart B S hS F V ((chartScheme V).basicOpen (g i))).1.hom w =
      chartPointsMap V (((BigFppfOver.toScheme B S hS).map
        ((SmallEtale.toOver B S hS F).map (openChartInclusion B S hS F V
          ((chartScheme V).basicOpen (g i))))) (schemePointsHomeomorph B S hS _ w)) := by
    rw [← chartPointsMap_comp]
    exact congrArg _ ((schemePointsHomeomorph B S hS _).symm_apply_apply w).symm
  rw [hval, toScheme_map_toOver_map_openChartInclusion] at hw
  have hz : ((chartScheme V).basicOpen (g i)).ι (schemePointsHomeomorph B S hS _ w) ∈
      (chartScheme V).zeroLocus (U := ⊤) (Set.range g) := by
    rwa [← hg]
  exact (Scheme.mem_zeroLocus_iff _ _ _).1 hz (g i) ⟨i, rfl⟩
    (((chartScheme V).basicOpen (g i)).range_ι.le ⟨_, rfl⟩)

/-- **Generators restrict along a morphism of charts.**  If on the chart `V` the point set of `Z`
is the zero locus of the `gᵢ`, then on a chart `U` over `V` it is the zero locus of the restricted
`gᵢ`. -/
theorem preimage_chartPointsMap_eq_zeroLocus_restrict (Z : Subfunctor F) {U V : SmallEtale B S hS F}
    (m : U ⟶ V) {ι : Type*} (g : ι → Γ(chartScheme V, ⊤))
    (hg : chartPointsMap V ⁻¹' Set.range (pointsMap B S hS Z.toFunctor Z.ι) =
      (chartScheme V).zeroLocus (U := ⊤) (Set.range g)) :
    chartPointsMap U ⁻¹' Set.range (pointsMap B S hS Z.toFunctor Z.ι) =
      (chartScheme U).zeroLocus (U := ⊤)
        (Set.range fun i => ((BigFppfOver.toScheme B S hS).map
          ((SmallEtale.toOver B S hS F).map m)).appTop (g i)) := by
  ext x
  rw [Set.mem_preimage, chartPointsMap_comp B S hS m x, ← Set.mem_preimage, hg, ← Set.mem_preimage]
  have h := preimage_zeroLocus_ideal_map ((BigFppfOver.toScheme B S hS).map
    ((SmallEtale.toOver B S hS F).map m)) (Ideal.span (Set.range g))
  rw [Scheme.zeroLocus_span, Ideal.map_span, Scheme.zeroLocus_span, ← Set.range_comp] at h
  exact Iff.of_eq (congrArg (x ∈ ·) h)

/-- **The basic opens of the generators cover the open complement.**  If on the chart `V` the
point set of `Z` is the zero locus of the `gᵢ`, every point of the chart lying over the open
complement of `Z` lies in some `D(gᵢ)`. -/
theorem exists_mem_basicOpen_of_mem_openComplement (Z : Subfunctor F) (V : SmallEtale B S hS F)
    {ι : Type*} (g : ι → Γ(chartScheme V, ⊤))
    (hg : chartPointsMap V ⁻¹' Set.range (pointsMap B S hS Z.toFunctor Z.ι) =
      (chartScheme V).zeroLocus (U := ⊤) (Set.range g)) (x : chartScheme V)
    (hx : chartPointsMap V x ∈
      Set.range
        (pointsMap B S hS (openComplement B S hS Z).toFunctor (openComplement B S hS Z).ι)) :
    ∃ i, x ∈ (chartScheme V).basicOpen (g i) := by
  rw [range_pointsMap_ι_openComplement B S hS Z] at hx
  have hx' : x ∉ (chartScheme V).zeroLocus (U := ⊤) (Set.range g) := by
    rwa [← hg]
  rw [Scheme.mem_zeroLocus_iff] at hx'
  push Not at hx'
  obtain ⟨_, ⟨i, rfl⟩, hi⟩ := hx'
  exact ⟨i, hi⟩

end AlgebraicGeometry.Space

end
