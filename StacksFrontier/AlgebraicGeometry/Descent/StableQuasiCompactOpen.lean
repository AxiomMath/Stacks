module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence

/-!
# Enlarging an open of an étale chart to one stable under the descent datum

This is the second step of the proof of Stacks 02W8. Let `G` be a presheaf on the big fppf site
of `S` and let `g : yoneda.obj V ⟶ G` be a chart of it — in the application `G` is the descended
sheaf `X ×[Y] yoneda.obj a` of
`AlgebraicGeometry.Space.IsEffectiveDescentAlongSurjectiveEtale` and `V` is the scheme carrying
the descent datum, so that `g` is a base change of the surjective étale covering morphism. The
source attaches to an affine open `W¹ ⊆ V` the open `W = pr(φ(W¹ ×_S X))`, shows it is a
quasi-compact open containing `W¹` and stable under the descent datum `φ`, and descends it.

Here that open is the *saturation* of `W¹` for the chart: the preimage under `g` of the image of
`W¹` in the point space of `G`. Being a preimage it is stable for the datum by construction, and
`AlgebraicGeometry.Space.preimage_image_pointsMap_of_isPullback` identifies it with
`π₂ '' (π₁ ⁻¹' W¹)` for the two projections `π₁ π₂ : D ⟶ V` of the fibre product of the chart
with itself — which is exactly the source's `pr(φ(W¹ ×_S X))`. Openness of the image in the
point space of `G` is where the universal openness of Stacks 01UA enters, through
`AlgebraicGeometry.Space.isOpenMap_pointsMap_of_presheafIsOpenMap`, and quasi-compactness of the
saturation is the quasi-compactness of `π₁` — which in the source comes from the reduction to an
affine covering of an affine base.

The open subfunctor of `G` cutting the saturation out is
`AlgebraicGeometry.Space.openSubspaceOfPoints`, whose inclusion is an open immersion by
`AlgebraicGeometry.Space.presheaf_isOpenImmersion_ι_openSubspaceOfPoints`; that theorem asks
only that the set of points be open, so it applies to `X ×[Y] yoneda.obj a` before anything is
known about it.

## Main results

* `AlgebraicGeometry.Space.presheafIsOpenMap_yoneda_map_of_universallyOpen` is the entry point
  of Stacks 01UA: a morphism of the site whose underlying morphism of schemes is universally
  open is an open map of schemes after every represented base change.
* `AlgebraicGeometry.Space.isOpen_image_pointsMap_of_isOpen`: the image in the point space of
  `G` of an open subset of the chart is open.
* `AlgebraicGeometry.Space.presheaf_isOpenImmersion_ι_openSubspaceOfPoints_image`: the
  subfunctor of `G` cut out by that image is an open subfunctor.
* `AlgebraicGeometry.Space.image_pointsToScheme_preimage_image_pointsMap` identifies the part of
  the chart lying over that image — the saturation — with `π₂ '' (π₁ ⁻¹' T)`, the construction of
  the source.
* `AlgebraicGeometry.Space.isOpen_preimage_image_pointsMap` and
  `AlgebraicGeometry.Space.isCompact_preimage_image_pointsMap`: the saturation is an open,
  quasi-compact subset of the chart, the second for a quasi-compact chart.
* `AlgebraicGeometry.Space.subset_preimage_image_pointsMap`: it contains the open it was built
  from.
* `AlgebraicGeometry.Space.exists_isPullback_ι_openSubspaceOfPoints_image` is the descent datum
  the open subfunctor carries: the part of the chart lying over it is, Cartesianly, the open
  subscheme of the chart cutting out the saturation. This is what the third and fourth steps of
  Stacks 02W8 are applied to.
* `AlgebraicGeometry.Space.isQuotientMap_pointsMap_of_presheafIsOpenMap`: a chart which is
  surjective and universally open after every represented base change is a quotient map on
  point spaces, so a set of points of `G` is open exactly when its part in the chart is.
* `AlgebraicGeometry.Space.iUnion_image_pointsMap_eq_univ`: the images of a covering of the
  chart cover the point space of `G`.

## Implementation notes

Nothing here is specific to the descent situation: `G` is an arbitrary presheaf and `g` an
arbitrary morphism from a representable one. The two hypotheses actually used are that `g` is an
open map of schemes after every represented base change, and — for the quasi-compactness — that
the first projection of the fibre product of `g` with itself is a quasi-compact morphism of
schemes. In the application to Stacks 02W8 both come from the covering morphism `q : c ⟶ a`
of the site: it is surjective and étale, hence flat and locally of finite presentation, hence
universally open by Stacks 01UA; and after the reduction of Descent, Lemma 35.36.2 to affine
`a` and `c` it is a morphism of affine schemes, hence quasi-compact, and so are all its base
changes.

The two projections are taken as data, in the form of a cartesian square of representables,
rather than as the chosen fibre product `pullback g g` of presheaves: in the application they
are produced as the two projections of a fibre product *in the site*, and identifying that with
the chosen presheaf-level fibre product would only have to be undone again.

## References

* [Stacks Project, Tag 02W8](https://stacks.math.columbia.edu/tag/02W8)
* [Stacks Project, Tag 01UA](https://stacks.math.columbia.edu/tag/01UA)
* [Stacks Project, Tag 03BZ](https://stacks.math.columbia.edu/tag/03BZ)
* [Stacks Project, Tag 03BX](https://stacks.math.columbia.edu/tag/03BX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Where the universal openness of Stacks 01UA enters -/

/-- **The entry point of Stacks 01UA.** A morphism of the big fppf category over `S` whose
underlying morphism of schemes is universally open is an open map of schemes after every
represented base change.

Being universally open is stable under base change, so the represented form of the property
reduces to the property of the underlying morphism by
`AlgebraicGeometry.BigFppfOver.presheaf_inverseImage_yoneda_map_iff`, and a universally open
morphism is in particular an open map.

In the application the hypothesis is supplied by `AlgebraicGeometry.UniversallyOpen.of_flat`,
which is Stacks 01UA: the covering morphism of the descent datum is surjective and étale, hence
flat and locally of finite presentation. -/
theorem presheafIsOpenMap_yoneda_map_of_universallyOpen {V U : BigFppfOver B S hS} (w : V ⟶ U)
    (hw : UniversallyOpen ((BigFppfOver.toScheme B S hS).map w)) :
    (MorphismProperty.inverseImage (topologically @IsOpenMap : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (yoneda.map w) := by
  have hle : (@_root_.AlgebraicGeometry.UniversallyOpen.{u} : MorphismProperty Scheme.{u}) ≤
      (topologically @IsOpenMap : MorphismProperty Scheme.{u}) := fun _ _ f hf =>
    have := hf
    f.isOpenMap
  exact MorphismProperty.relative_monotone
    (MorphismProperty.monotone_inverseImage (BigFppfOver.toScheme B S hS) hle) _
    ((BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS
      (@_root_.AlgebraicGeometry.UniversallyOpen.{u}) w).2 hw)

variable {G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {V : BigFppfOver B S hS}

/-! ### The open subfunctor cut out by an open of the chart -/

/-- The image in the point space of `G` of an open subset of a chart `g : yoneda.obj V ⟶ G` is
open, as soon as `g` is an open map of schemes after every represented base change.

This is the openness of the set of points which
`AlgebraicGeometry.Space.presheaf_isOpenImmersion_ι_openSubspaceOfPoints` asks for, and the
hypothesis on `g` is where Stacks 01UA is consumed. -/
theorem isOpen_image_pointsMap_of_isOpen (g : yoneda.obj V ⟶ G)
    (hg : (MorphismProperty.inverseImage (topologically @IsOpenMap : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf g)
    {T : Set ((BigFppfOver.toScheme B S hS).obj V)} (hT : IsOpen T) :
    IsOpen (pointsMap B S hS (yoneda.obj V) g '' (pointsToScheme B S hS V ⁻¹' T)) :=
  isOpenMap_pointsMap_of_presheafIsOpenMap B S hS g hg _
    ((isOpen_pointTopology_yoneda_iff_isOpen_image B S hS V _).2
      (by rwa [Set.image_preimage_eq _ (surjective_pointsToScheme B S hS V)]))

/-- **The open subfunctor of the second step of Stacks 02W8.** The subfunctor of `G` cut out by
the image of an open subset of a chart is an open subfunctor.

No hypothesis is placed on `G`: in the application `G` is the fibre product
`X ×[Y] yoneda.obj a` whose representability is the point of the whole argument, and
`AlgebraicGeometry.Space.presheaf_isOpenImmersion_ι_openSubspaceOfPoints` asks only for
openness of the set of points. -/
theorem presheaf_isOpenImmersion_ι_openSubspaceOfPoints_image (g : yoneda.obj V ⟶ G)
    (hg : (MorphismProperty.inverseImage (topologically @IsOpenMap : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf g)
    {T : Set ((BigFppfOver.toScheme B S hS).obj V)} (hT : IsOpen T) :
    IsOpenImmersion B S hS (openSubspaceOfPoints B S hS G
      (pointsMap B S hS (yoneda.obj V) g '' (pointsToScheme B S hS V ⁻¹' T))).ι :=
  presheaf_isOpenImmersion_ι_openSubspaceOfPoints B S hS _
    (isOpen_image_pointsMap_of_isOpen B S hS g hg hT)

/-! ### The saturation in the chart -/

/-- **The construction of the second step of Stacks 02W8.** The part of the chart lying over the
image of a subset `T` — the saturation of `T` for the chart — is `π₂ '' (π₁ ⁻¹' T)`, for the two
projections of the fibre product of the chart with itself.

This is the set the source writes `pr(φ(W¹ ×_S X))`: the descent isomorphism `φ` is the
identification of the fibre product of the chart with itself used here, and the two projections
are the two legs of the given cartesian square. The only non-formal inclusion is surjectivity of
the comparison map from the points of a fibre product onto the fibre product of the point sets,
which is `AlgebraicGeometry.Space.exists_points_of_isPullback`. -/
theorem image_pointsToScheme_preimage_image_pointsMap {D : BigFppfOver B S hS}
    (g : yoneda.obj V ⟶ G) {π₁ π₂ : D ⟶ V}
    (sq : IsPullback (yoneda.map π₁) (yoneda.map π₂) g g)
    (T : Set ((BigFppfOver.toScheme B S hS).obj V)) :
    pointsToScheme B S hS V ''
        (pointsMap B S hS (yoneda.obj V) g ⁻¹'
          (pointsMap B S hS (yoneda.obj V) g '' (pointsToScheme B S hS V ⁻¹' T))) =
      (BigFppfOver.toScheme B S hS).map π₂ ''
        ((BigFppfOver.toScheme B S hS).map π₁ ⁻¹' T) := by
  rw [preimage_image_pointsMap_of_isPullback B S hS sq, image_pointsToScheme_image_pointsMap]
  congr 1
  have hpre : pointsMap B S hS (yoneda.obj D) (yoneda.map π₁) ⁻¹'
      (pointsToScheme B S hS V ⁻¹' T) =
      pointsToScheme B S hS D ⁻¹' ((BigFppfOver.toScheme B S hS).map π₁ ⁻¹' T) := by
    ext w
    simp only [Set.mem_preimage, pointsToScheme_pointsMap_yoneda]
  rw [hpre, Set.image_preimage_eq _ (surjective_pointsToScheme B S hS D)]

/-- The saturation of an open subset of the chart is open: it is the part of the chart lying
over an open set of points. -/
theorem isOpen_preimage_image_pointsMap (g : yoneda.obj V ⟶ G)
    (hg : (MorphismProperty.inverseImage (topologically @IsOpenMap : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf g)
    {T : Set ((BigFppfOver.toScheme B S hS).obj V)} (hT : IsOpen T) :
    IsOpen (pointsToScheme B S hS V ''
      (pointsMap B S hS (yoneda.obj V) g ⁻¹'
        (pointsMap B S hS (yoneda.obj V) g '' (pointsToScheme B S hS V ⁻¹' T)))) :=
  (isOpen_pointTopology_yoneda_iff_isOpen_image B S hS V _).1
    ((isOpen_image_pointsMap_of_isOpen B S hS g hg hT).preimage
      (continuous_pointsMap B S hS g))

/-- **The quasi-compactness of the second step of Stacks 02W8.** The saturation of a
quasi-compact open subset of the chart is quasi-compact, provided the first projection of the
fibre product of the chart with itself is a quasi-compact morphism of schemes.

In the source that quasi-compactness is the reduction of Descent, Lemma 35.36.2 to a covering of
affines: `W¹ ×_S X` is then affine, hence quasi-compact, and `W` is a continuous image of it. -/
theorem isCompact_preimage_image_pointsMap {D : BigFppfOver B S hS}
    (g : yoneda.obj V ⟶ G) {π₁ π₂ : D ⟶ V}
    (sq : IsPullback (yoneda.map π₁) (yoneda.map π₂) g g)
    (hπ₁ : QuasiCompact ((BigFppfOver.toScheme B S hS).map π₁))
    {T : Set ((BigFppfOver.toScheme B S hS).obj V)} (hTopen : IsOpen T) (hTcomp : IsCompact T) :
    IsCompact (pointsToScheme B S hS V ''
      (pointsMap B S hS (yoneda.obj V) g ⁻¹'
        (pointsMap B S hS (yoneda.obj V) g '' (pointsToScheme B S hS V ⁻¹' T)))) := by
  rw [image_pointsToScheme_preimage_image_pointsMap B S hS g sq]
  exact (hπ₁.isCompact_preimage T hTopen hTcomp).image
    ((BigFppfOver.toScheme B S hS).map π₂).continuous

/-- The saturation of a subset of the chart contains it. -/
theorem subset_preimage_image_pointsMap (g : yoneda.obj V ⟶ G)
    (T : Set ((BigFppfOver.toScheme B S hS).obj V)) :
    T ⊆ pointsToScheme B S hS V ''
      (pointsMap B S hS (yoneda.obj V) g ⁻¹'
        (pointsMap B S hS (yoneda.obj V) g '' (pointsToScheme B S hS V ⁻¹' T))) := by
  intro x hx
  obtain ⟨w, hw⟩ := surjective_pointsToScheme B S hS V x
  exact ⟨w, ⟨w, Set.mem_preimage.2 (hw ▸ hx), rfl⟩, hw⟩

/-- **The descent datum carried by the open subfunctor of the second step of Stacks 02W8.** The
part of the chart lying over the open subfunctor cut out by the image of an open `T` is the open
subscheme of the chart cutting out the saturation of `T`, Cartesianly: there is an object `b` of
the site and an open immersion `i : b ⟶ V` with image the saturation, fitting into a Cartesian
square over the chart.

This is what turns the open subfunctor into a descent datum: by
`AlgebraicGeometry.Space.isOpen_preimage_image_pointsMap` and
`AlgebraicGeometry.Space.isCompact_preimage_image_pointsMap` the scheme `b` is a quasi-compact
open of the chart, so the third and fourth steps of Stacks 02W8 — that such an open is
quasi-affine over the base (Stacks 02LR) and that quasi-affine morphisms descend effectively
(Stacks 0247) — apply to it, and what they produce is a representable open subfunctor of the
descended sheaf.

The square is the canonical one of `CategoryTheory.Subfunctor.isPullback_fromPreimage`, carried
across the identification of
`AlgebraicGeometry.Space.range_yoneda_map_eq_preimage_openSubspaceOfPoints`; the open subscheme
itself is produced inside the site by `AlgebraicGeometry.exists_restrict_bigFppfOver`. -/
theorem exists_isPullback_ι_openSubspaceOfPoints_image (g : yoneda.obj V ⟶ G)
    (hg : (MorphismProperty.inverseImage (topologically @IsOpenMap : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf g)
    {T : Set ((BigFppfOver.toScheme B S hS).obj V)} (hT : IsOpen T) :
    ∃ (b : BigFppfOver B S hS) (i : b ⟶ V)
      (k : yoneda.obj b ⟶ (openSubspaceOfPoints B S hS G
        (pointsMap B S hS (yoneda.obj V) g '' (pointsToScheme B S hS V ⁻¹' T))).toFunctor),
      _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map i) ∧
        Set.range ((BigFppfOver.toScheme B S hS).map i) =
          pointsToScheme B S hS V ''
            (pointsMap B S hS (yoneda.obj V) g ⁻¹'
              (pointsMap B S hS (yoneda.obj V) g '' (pointsToScheme B S hS V ⁻¹' T))) ∧
          IsPullback k (yoneda.map i)
            (openSubspaceOfPoints B S hS G
              (pointsMap B S hS (yoneda.obj V) g ''
                (pointsToScheme B S hS V ⁻¹' T))).ι g := by
  set W := pointsMap B S hS (yoneda.obj V) g '' (pointsToScheme B S hS V ⁻¹' T)
  set Vsat := pointsToScheme B S hS V '' (pointsMap B S hS (yoneda.obj V) g ⁻¹' W) with hVsat
  obtain ⟨b, i, hi, hirange, hiuniv⟩ := exists_restrict_bigFppfOver V
    ⟨Vsat, isOpen_preimage_image_pointsMap B S hS g hg hT⟩
  have hpoints : ∀ p : FieldValuedPoint B S hS (yoneda.obj V),
      pointsMap B S hS (yoneda.obj V) g (p.class B S hS (yoneda.obj V)) ∈ W ↔
        schemePoint B S hS V p ∈ Vsat := by
    -- The two sides match by injectivity of the comparison of points with scheme points.
    intro p
    rw [hVsat, ← pointsToScheme_class B S hS V p,
      (injective_pointsToScheme B S hS V).mem_set_image]
    exact Iff.rfl
  have hkey : Subfunctor.range (yoneda.map i) =
      (openSubspaceOfPoints B S hS G W).preimage g :=
    range_yoneda_map_eq_preimage_openSubspaceOfPoints B S hS W g i Vsat hirange hiuniv hpoints
  have hsq := Subfunctor.isPullback_fromPreimage (openSubspaceOfPoints B S hS G W) g
  have hmono : Mono i := inverseImage_isOpenImmersion_le_monomorphisms i hi
  have hiso := Subfunctor.isIso_lift hkey.le hkey.ge
  refine ⟨b, i, Subfunctor.lift (yoneda.map i) hkey.le ≫
    (openSubspaceOfPoints B S hS G W).fromPreimage g, hi, hirange, ?_⟩
  refine IsPullback.of_iso_pullback
    ⟨by rw [Category.assoc, (openSubspaceOfPoints B S hS G W).fromPreimage_ι g,
      ← Category.assoc, Subfunctor.lift_ι]⟩
    (asIso (Subfunctor.lift (yoneda.map i) hkey.le) ≪≫ hsq.isoPullback) ?_ ?_
  · simp [hsq.isoPullback_hom_fst]
  · simp [hsq.isoPullback_hom_snd]

/-! ### The chart detects the open sets of points, and its images cover -/

/-- A chart which is surjective on points and an open map of schemes after every represented
base change is a quotient map on point spaces: a subset of the point space of `G` is open
exactly when the part of the chart lying over it is open.

Continuity is `AlgebraicGeometry.Space.continuous_pointsMap` and openness of the direct image is
`AlgebraicGeometry.Space.isOpenMap_pointsMap_of_presheafIsOpenMap`, and surjectivity turns the
two into the quotient property. It is the precise sense in which the second step of Stacks 02W8
can be carried out on the chart: a set of points of the descended sheaf is open as soon as its
part in the chart is. -/
theorem isQuotientMap_pointsMap_of_presheafIsOpenMap (g : yoneda.obj V ⟶ G)
    (hsurj : Function.Surjective (pointsMap B S hS (yoneda.obj V) g))
    (hg : (MorphismProperty.inverseImage (topologically @IsOpenMap : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf g) :
    Topology.IsQuotientMap (pointsMap B S hS (yoneda.obj V) g) :=
  (isOpenMap_pointsMap_of_presheafIsOpenMap B S hS g hg).isQuotientMap
    (continuous_pointsMap B S hS g) hsurj

/-- **The covering claim of the second step of Stacks 02W8, on points.** The images in the point
space of `G` of the members of a covering of the chart cover it, as soon as the chart is
surjective on points. -/
theorem iUnion_image_pointsMap_eq_univ (g : yoneda.obj V ⟶ G)
    (hsurj : Function.Surjective (pointsMap B S hS (yoneda.obj V) g))
    {ι : Type*} (T : ι → Set ((BigFppfOver.toScheme B S hS).obj V))
    (hT : ⋃ i, T i = Set.univ) :
    ⋃ i, pointsMap B S hS (yoneda.obj V) g '' (pointsToScheme B S hS V ⁻¹' T i) =
      Set.univ := by
  rwa [← Set.image_iUnion, ← Set.preimage_iUnion, hT, Set.preimage_univ, Set.image_univ,
    Set.range_eq_univ]

end AlgebraicGeometry.Space

end
