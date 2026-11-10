module

public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricRepresentative
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafSupport

/-!
# The support of a sheaf through its sections and under surjections

Let `F` be an abelian sheaf on the small étale site of an algebraic space `X`. Its support is
the set of points at which some geometric stalk is nonzero, while the support of a section
over an étale chart is the complement of the largest open on which that section vanishes.
This file relates the two: the support of the sheaf is the union, over all charts and all
sections, of the images of the supports of the sections, and a surjection of abelian sheaves
cannot enlarge the support.

The bridge is a criterion for a germ to vanish. A germ at a geometric point `p` is
represented by a section `σ` over a small étale neighbourhood `N` of `p`, and it vanishes
exactly when the point of `N` carried by `p` lies in the largest open zero locus of `σ`. The
substantial direction is that the open zero locus can be refined to a neighbourhood: the zero
locus is an open set of points of the chart, hence an open subscheme of it, the lift of `p`
lands in that open subscheme, and an affine open of the open subscheme through that lift is
again an étale chart of `X` small enough to lie in the site.

## Main definitions

* `AlgebraicGeometry.Space.neighborhoodPoint` is the geometric point of a small étale
  neighbourhood of a geometric point given by the chosen lift.

## Main results

* `AlgebraicGeometry.Space.exists_geometricRepresentative` — every point of a presheaf over
  the big fppf site is the image of a geometric point: replace the field of a representative
  by its algebraic closure, which is still small enough for the site.
* `AlgebraicGeometry.Space.germ_eq_zero_iff` and
  `AlgebraicGeometry.Space.subsingleton_stalkSet_iff` — the vanishing criteria for a germ and
  for a whole geometric stalk, resting on
  `AlgebraicGeometry.Space.exists_neighborhood_imageInOpen`.
* `AlgebraicGeometry.Space.supportOfSheaf_eq_iUnion_image_supportOfSection` — **Stacks 04KB**,
  part (4): the support of the sheaf is the union of the images of the supports of its local
  sections.
* `AlgebraicGeometry.Space.supportOfSheaf_subset_of_isLocallySurjective` — **Stacks 04KB**,
  part (5): a surjection of abelian sheaves does not enlarge the support.

## Implementation notes

Surjectivity of a map of abelian sheaves is `CategoryTheory.Sheaf.IsLocallySurjective`, which
is the Stacks Project's notion of a surjection of sheaves: locally on a covering every section
of the target lifts. It is *not* replaced by `CategoryTheory.Epi` here. The two agree whenever
the category of abelian sheaves on the site has sheafification, and locally surjective
always implies epi, but sheafification of `AddCommGrpCat`-valued sheaves on the small étale
site of an algebraic space is not available at the universe at which `supportOfSheaf` is
stated — the colimits it needs are indexed one universe above the site — so `Epi` is strictly
weaker information there and cannot be used.

The topology on the point sets is `AlgebraicGeometry.Space.pointTopology`, a local instance,
exactly as in `StacksFrontier.AlgebraicGeometry.Spaces.SheafSupport`; no algebraicity hypothesis
is needed to speak of it, and the two clauses carry one only because the geometric stalks
compute the support only for an algebraic space.

## References

* [Stacks Project, Lemma 66.21.2 (Tag 04KB)](https://stacks.math.columbia.edu/tag/04KB)
* [Stacks Project, Tag 04KA](https://stacks.math.columbia.edu/tag/04KA)
* [Stacks Project, Tag 04JY](https://stacks.math.columbia.edu/tag/04JY)
* [Stacks Project, Tag 04K0](https://stacks.math.columbia.edu/tag/04K0)
* [Stacks Project, Tag 04K5](https://stacks.math.columbia.edu/tag/04K5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

attribute [local instance] pointTopology

/-! ### Geometric representatives of points -/

/-! ### The geometric point carried by a small étale neighbourhood -/

/-- The geometric point of an étale chart given by the chosen lift of a geometric point of the
algebraic space to a small étale neighbourhood. -/
noncomputable def neighborhoodPoint {p : GeometricPoint B S hS X}
    (N : SmallEtaleNeighborhood p) :
    GeometricPoint B S hS (yoneda.obj ((SmallEtale.toOver B S hS X).obj N.chart)) :=
  ⟨{ carrier := p.val.carrier
     contained := p.val.contained
     toBase := p.val.toBase
     value := N.point }, p.property⟩

/-- The image of `AlgebraicGeometry.Space.neighborhoodPoint` in the points of the algebraic
space is the image of the geometric point it came from. -/
theorem neighborhoodPoint_image {p : GeometricPoint B S hS X}
    (N : SmallEtaleNeighborhood p) :
    pointsMap B S hS (yoneda.obj ((SmallEtale.toOver B S hS X).obj N.chart))
        N.chart.obj.hom (neighborhoodPoint B S hS X N).image = p.image := by
  rw [pointsMap_class]
  congr 1
  change (⟨p.val.carrier, p.val.contained, p.val.toBase,
    N.chart.obj.hom.app (op p.val.siteObject) N.point⟩ : FieldValuedPoint B S hS X) = p.val
  rw [N.point_comp]

/-- A refinement of small étale neighbourhoods carries the geometric point of the source to
the geometric point of the target. -/
theorem neighborhoodPoint_image_map {p : GeometricPoint B S hS X}
    {M N : SmallEtaleNeighborhood p} (f : M ⟶ N) :
    pointsMap B S hS (yoneda.obj ((SmallEtale.toOver B S hS X).obj M.chart))
        (yoneda.map ((SmallEtale.toOver B S hS X).map f.hom))
        (neighborhoodPoint B S hS X M).image =
      (neighborhoodPoint B S hS X N).image := by
  rw [pointsMap_class]
  congr 1
  change (⟨p.val.carrier, p.val.contained, p.val.toBase,
      M.point ≫ (SmallEtale.toOver B S hS X).map f.hom⟩ :
    FieldValuedPoint B S hS (yoneda.obj ((SmallEtale.toOver B S hS X).obj N.chart))) = _
  rw [f.point_comp]
  rfl

/-! ### Refining a neighbourhood into an open set of points -/

/-- An open set of points of a small étale neighbourhood containing the point carried by the
geometric point is accounted for by a refinement of that neighbourhood: there is a smaller
small étale neighbourhood whose image lies inside the open set.

The open set is the point set of an open subscheme of the chart, the chosen lift of the
geometric point lands in that open subscheme, and an affine open of it through the lift is an
étale chart of `X` in the site, by `AlgebraicGeometry.Space.etale_comp_of_scheme`. -/
theorem exists_neighborhood_imageInOpen {p : GeometricPoint B S hS X}
    (N : SmallEtaleNeighborhood p)
    (W : Set (points B S hS
      (yoneda.obj ((SmallEtale.toOver B S hS X).obj N.chart))))
    (hW : IsOpen W) (hp : (neighborhoodPoint B S hS X N).image ∈ W) :
    ∃ (M : SmallEtaleNeighborhood p) (f : M ⟶ N), ImageInOpen B S hS X W f.hom := by
  let T := BigFppfOver.toScheme B S hS
  let A := (SmallEtale.toOver B S hS X).obj N.chart
  let O : (T.obj A).Opens :=
    ⟨pointsToScheme B S hS A '' W,
      (isOpen_pointTopology_yoneda_iff_isOpen_image B S hS A W).1 hW⟩
  have hmem : ∀ z : points B S hS (yoneda.obj A),
      z ∈ W ↔ pointsToScheme B S hS A z ∈ O := fun z ↦
    (injective_pointsToScheme B S hS A).mem_set_image.symm
  let w : Spec (.of p.val.carrier) ⟶ T.obj A := T.map N.point
  have hwO : w (IsLocalRing.closedPoint p.val.carrier) ∈ O :=
    (hmem (neighborhoodPoint B S hS X N).image).1 hp
  obtain ⟨R, j, hj, hrange, hsubset⟩ :=
    Scheme.exists_affine_mem_range_and_range_subset
      (x := w (IsLocalRing.closedPoint p.val.carrier)) (U := O) hwO
  have : _root_.AlgebraicGeometry.IsOpenImmersion j := hj
  have hw : Set.range w ⊆ Set.range j := by
    rintro _ ⟨a, rfl⟩
    simpa only [Subsingleton.elim a (IsLocalRing.closedPoint p.val.carrier)] using hrange
  let q := _root_.AlgebraicGeometry.IsOpenImmersion.lift j w hw
  have hq : q ≫ j = w := _root_.AlgebraicGeometry.IsOpenImmersion.lift_fac j w hw
  let V : BigFppfOver B S hS :=
    Over.mk (ObjectProperty.homMk (j ≫ B.inclusion.map A.hom) :
      (⟨Spec R, Scheme.size_lt_of_isOpenImmersion j A.left.property⟩ : B.Schemes) ⟶ B.obj hS)
  let jOver : V ⟶ A := Over.homMk (ObjectProperty.homMk j) (ObjectProperty.hom_ext _ rfl)
  let C : SmallEtale B S hS X :=
    ⟨CostructuredArrow.mk (yoneda.map jOver ≫ N.chart.obj.hom),
      etale_comp_of_scheme B S hS jOver _ (by rw [show T.map jOver = j from rfl]; infer_instance)
        N.chart.property⟩
  let g : C ⟶ N.chart := ObjectProperty.homMk (CostructuredArrow.homMk jOver rfl)
  let qOver : p.val.siteObject ⟶ V := Over.homMk (ObjectProperty.homMk q) (by
    apply ObjectProperty.hom_ext
    change q ≫ B.inclusion.map V.hom = B.inclusion.map p.val.siteObject.hom
    rw [show B.inclusion.map V.hom = j ≫ B.inclusion.map A.hom from rfl, ← Category.assoc, hq]
    exact congrArg B.inclusion.map N.point.w)
  have hqOver : qOver ≫ jOver = N.point := Over.OverMorphism.ext (ObjectProperty.hom_ext _ hq)
  let M : SmallEtaleNeighborhood p :=
    ⟨C, qOver, by
      change N.chart.obj.hom.app (op p.val.siteObject) (qOver ≫ jOver) = _
      rw [hqOver]
      exact N.point_comp⟩
  refine ⟨M, ⟨g, hqOver⟩, fun z ↦ (hmem _).2 ?_⟩
  rw [pointsToScheme_pointsMap_yoneda B S hS ((SmallEtale.toOver B S hS X).map g) z]
  change T.map jOver (pointsToScheme B S hS V z) ∈ O
  exact hsubset ⟨pointsToScheme B S hS V z, rfl⟩

/-! ### Vanishing of a germ -/

variable (hX : IsAlgebraicSpace B S hS X)

include hX

/-- A germ of an abelian sheaf at a geometric point vanishes exactly when the point of the
chart carried by the geometric point lies in the largest open zero locus of the representing
section. -/
theorem germ_eq_zero_iff
    (F : Sheaf (SmallEtale.topology B S hS X) AddCommGrpCat.{v})
    {p : GeometricPoint B S hS X} (N : SmallEtaleNeighborhood p)
    (σ : F.obj.obj (op N.chart)) :
    (SmallEtaleNeighborhood.sections (x := p)
        (F.obj ⋙ CategoryTheory.forget AddCommGrpCat.{v})).ιColimitType (op N) σ =
      (SmallEtaleNeighborhood.sections (x := p)
        (F.obj ⋙ CategoryTheory.forget AddCommGrpCat.{v})).ιColimitType (op N)
          (0 : F.obj.obj (op N.chart)) ↔
      (neighborhoodPoint B S hS X N).image ∈
        (largestOpenZeroLocus B S hS X F N.chart σ).1 := by
  have := isCofiltered_smallEtaleNeighborhood B S hS X hX p
  set D := SmallEtaleNeighborhood.sections (x := p)
    (F.obj ⋙ CategoryTheory.forget AddCommGrpCat.{v})
  have key (M : SmallEtale B S hS X) (f : M ⟶ N.chart) :
      F.obj.map f.op σ = F.obj.map f.op 0 ↔
        ImageInOpen B S hS X (largestOpenZeroLocus B S hS X F N.chart σ).1 f := by
    rw [map_zero]
    exact largestOpenZeroLocus_restrict_iff B S hS X F N.chart σ M f
  refine (Functor.ιColimitType_eq_iff_of_isFiltered' (F := D) σ
    (0 : F.obj.obj (op N.chart))).trans
    ⟨fun ⟨M, f, hf⟩ ↦ ?_, fun hp ↦ ?_⟩
  · have hm := (key M.unop.chart f.unop.hom).mp hf (neighborhoodPoint B S hS X M.unop).image
    rwa [neighborhoodPoint_image_map] at hm
  · obtain ⟨M, f, hf⟩ := exists_neighborhood_imageInOpen B S hS X N _
      (largestOpenZeroLocus B S hS X F N.chart σ).2 hp
    exact ⟨op M, f.op, (key M.chart f.hom).mpr hf⟩

/-- A geometric stalk of an abelian sheaf vanishes exactly when every section on every small
étale neighbourhood of the point vanishes near it. -/
theorem subsingleton_stalkSet_iff
    (F : Sheaf (SmallEtale.topology B S hS X) AddCommGrpCat.{v})
    (p : GeometricPoint B S hS X) :
    Subsingleton (stalkSet p (F.obj ⋙ CategoryTheory.forget AddCommGrpCat.{v})) ↔
      ∀ (N : SmallEtaleNeighborhood p) (σ : F.obj.obj (op N.chart)),
        (neighborhoodPoint B S hS X N).image ∈
          (largestOpenZeroLocus B S hS X F N.chart σ).1 := by
  have := isCofiltered_smallEtaleNeighborhood B S hS X hX p
  set D := SmallEtaleNeighborhood.sections (x := p)
    (F.obj ⋙ CategoryTheory.forget AddCommGrpCat.{v})
  refine ⟨fun h N σ ↦ (germ_eq_zero_iff B S hS X hX F N σ).mp (h.elim _ _),
    fun h ↦ ⟨fun a b ↦ ?_⟩⟩
  have h0 (N : (SmallEtaleNeighborhood p)ᵒᵖ) (σ : F.obj.obj (op N.unop.chart)) :=
    (germ_eq_zero_iff B S hS X hX F N.unop σ).mpr (h N.unop σ)
  obtain ⟨N, σ, rfl⟩ := D.ιColimitType_jointly_surjective a
  obtain ⟨M, τ, rfl⟩ := D.ιColimitType_jointly_surjective b
  rw [h0 N σ, h0 M τ]
  obtain ⟨L, f, g, -⟩ := IsFilteredOrEmpty.cocone_objs N M
  refine (D.ιColimitType_eq_iff_of_isFiltered _ _).mpr ⟨L, f, g, ?_⟩
  change F.obj.map f.unop.hom.op 0 = F.obj.map g.unop.hom.op 0
  simp

/-! ### The support of a sheaf through its sections -/

/-- **Stacks 04KB, part (4).** The support of an abelian sheaf on the small étale site of an
algebraic space is the union, over all étale charts and all sections on them, of the images of
the supports of those sections.

A point of the support carries a geometric point with a nonzero stalk, hence a neighbourhood
and a section whose germ there is nonzero, and that section has the point of the chart in its
support. Conversely a point in the support of a section is the image of a geometric point of
the chart, whose germ there is then nonzero. -/
@[stacks 04KB "sheaf_support_sections",
  stacks 04KB "part (4): the support of a sheaf is the union of the section supports"]
theorem supportOfSheaf_eq_iUnion_image_supportOfSection
    (F : Sheaf (SmallEtale.topology B S hS X) AddCommGrpCat.{v}) :
    supportOfSheaf B S hS X F =
      ⋃ U : SmallEtale B S hS X, ⋃ σ : F.obj.obj (op U),
        pointsMap B S hS (yoneda.obj ((SmallEtale.toOver B S hS X).obj U)) U.obj.hom ''
          supportOfSection B S hS X F U σ := by
  ext x
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨p, hp, hn⟩
    obtain ⟨N, σ, hσ⟩ : ∃ (N : SmallEtaleNeighborhood p) (σ : F.obj.obj (op N.chart)),
        (neighborhoodPoint B S hS X N).image ∉
          (largestOpenZeroLocus B S hS X F N.chart σ).1 := by
      by_contra! h
      exact hn ((subsingleton_stalkSet_iff B S hS X hX F p).mpr h)
    exact ⟨N.chart, σ, (neighborhoodPoint B S hS X N).image, hσ,
      (neighborhoodPoint_image B S hS X N).trans hp⟩
  · rintro ⟨U, σ, y, hy, rfl⟩
    obtain ⟨r, hr⟩ := exists_geometricRepresentative B S hS
      (yoneda.obj ((SmallEtale.toOver B S hS X).obj U)) y
    let p : GeometricPoint B S hS X :=
      ⟨FieldValuedPoint.map B S hS _ U.obj.hom r.val, r.property⟩
    let N : SmallEtaleNeighborhood p := ⟨U, r.val.value, rfl⟩
    refine ⟨p, ?_, ?_⟩
    · change (FieldValuedPoint.map B S hS _ U.obj.hom r.val).class B S hS X =
        pointsMap B S hS _ U.obj.hom y
      rw [← hr]
      exact (pointsMap_class B S hS _ U.obj.hom r.val).symm
    · intro hn
      have hz := (subsingleton_stalkSet_iff B S hS X hX F p).mp hn N σ
      change r.image ∈ (largestOpenZeroLocus B S hS X F U σ).1 at hz
      exact hy (hr ▸ hz)

/-! ### The support of a sheaf under a surjection -/

/-- **Stacks 04KB.** A surjection of abelian sheaves on the small étale site of an algebraic
space does not enlarge the support: the support of the target is contained in the support of
the source.

A surjection of sheaves is surjective on every geometric stalk by Stacks 04K5, so a point at
which the stalk of the source is a subsingleton is one at which the stalk of the target is one
too. -/
@[stacks 04KB "part (5): support along a surjection"]
theorem supportOfSheaf_subset_of_isLocallySurjective
    {F G : Sheaf (SmallEtale.topology B S hS X) AddCommGrpCat.{v}} (a : F ⟶ G)
    [Sheaf.IsLocallySurjective a] :
    supportOfSheaf B S hS X G ⊆ supportOfSheaf B S hS X F := by
  intro x hx
  rw [mem_supportOfSheaf_iff_exists] at hx ⊢
  obtain ⟨p, hp, hG⟩ := hx
  have hsurj : Sheaf.IsLocallySurjective ((sheafCompose (SmallEtale.topology B S hS X)
      (CategoryTheory.forget AddCommGrpCat.{v})).map a) := inferInstance
  refine ⟨p, hp, fun hF ↦ hG ⟨fun b c ↦ ?_⟩⟩
  have hs := (surjective_iff_stalkSetMap_surjective B S hS X hX _).1 hsurj p
  obtain ⟨b', rfl⟩ := hs b
  obtain ⟨c', rfl⟩ := hs c
  exact congrArg _ (hF.elim b' c')

end AlgebraicGeometry.Space

end
