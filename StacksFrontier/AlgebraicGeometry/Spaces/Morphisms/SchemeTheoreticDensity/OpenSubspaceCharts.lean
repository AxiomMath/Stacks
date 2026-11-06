module

public import StacksFrontier.AlgebraicGeometry.SchemeTheoreticImage.DenseOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceRange
public import StacksFrontier.AlgebraicGeometry.Spaces.FpqcOpenSubspaceDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SchemeTheoreticImageSiteOpen
public import
  StacksFrontier.AlgebraicGeometry.Etale.ElementaryNeighborhood.StructureSheafProjectiveSections
public import StacksFrontier.AlgebraicGeometry.Morphisms.Closure.DenseOpenImmersion
public import StacksFrontier.AlgebraicGeometry.Morphisms.Closure.DensePreimageQuasiFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.SchemeImageDominant
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionStructureMap
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceRange
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.RationalMapDomainOfDefinition
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SchemeTheoreticImage
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRingedToposHom
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallZariskiSite

/-!
# Open subspaces of an algebraic space and their étale scheme charts

Preliminaries for scheme-theoretic density of an open subspace of an algebraic space
(`StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SchemeTheoreticDensity`): injectivity of the
structure-sheaf map of an open immersion of schemes, open subfunctors of a representable presheaf
and their images in the site, the chart of the inverse image of an open subspace, descent of
subfunctors along a surjective étale chart, the scheme-theoretic image of a morphism of the
site, and injectivity of the structure-sheaf map over every chart.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Sheaves.ToposPullback

universe u

namespace AlgebraicGeometry

/-! ### Injectivity of the structure-sheaf map of an open immersion of schemes

The lemmas of this section restate, for an open immersion of schemes, the relation between
injectivity of the maps on sections, scheme-theoretic dominance and scheme-theoretic density of
the image. The general statements are not restated but used directly:
`AlgebraicGeometry.app_injective_iff_appTop_inter`,
`AlgebraicGeometry.mono_c_iff_app_injective`,
`AlgebraicGeometry.ker_eq_bot_of_app_injective_affine` and
`AlgebraicGeometry.isSchemeTheoreticallyDense_opensRange_iff_mono`. -/

section Schemes

/-- Injectivity of the map on sections only depends on the open subscheme. -/
private lemma app_injective_congr_opens {A A' : Scheme.{u}} (f : A ⟶ A') (V W : A'.Opens)
    (h : V = W) :
    Function.Injective (f.app V).hom ↔ Function.Injective (f.app W).hom := by
  subst h
  rfl

/-- Injectivity of the map on sections only depends on the morphism. -/
private lemma app_injective_congr_hom {A A' : Scheme.{u}} {f g : A ⟶ A'} (h : f = g)
    (V : A'.Opens) :
    Function.Injective (f.app V).hom ↔ Function.Injective (g.app V).hom := by
  subst h
  rfl

/-- Precomposing with an isomorphism of schemes does not change injectivity of the maps on
sections. -/
private lemma app_injective_iso_precomp_iff {A A' A'' : Scheme.{u}} (e : A ≅ A') (f : A' ⟶ A'')
    (V : A''.Opens) :
    Function.Injective ((e.hom ≫ f).app V).hom ↔ Function.Injective (f.app V).hom := by
  rw [Scheme.Hom.comp_app]
  exact (ConcreteCategory.mono_iff_injective_of_preservesPullback
      (f.app V ≫ e.hom.app (f ⁻¹ᵁ V))).symm.trans
    ((mono_comp_iff_of_mono (f.app V) (e.hom.app (f ⁻¹ᵁ V))).trans
      (ConcreteCategory.mono_iff_injective_of_preservesPullback (f.app V)))

/-- For an open immersion of schemes, injectivity on sections over an open subscheme `P` of the
target is injectivity on global sections of the inclusion of the part of the image lying over
`P`. -/
private lemma app_injective_iff_appTop_preimage_opensRange {A Y : Scheme.{u}} (j : A ⟶ Y)
    [IsOpenImmersion j] (P : Y.Opens) :
    Function.Injective (j.app P).hom ↔
      Function.Injective ((P.ι ⁻¹ᵁ j.opensRange).ι.appTop).hom := by
  have hfactor : j.isoOpensRange.hom ≫ j.opensRange.ι = j := by simp
  exact ((app_injective_congr_hom hfactor P).symm.trans
    (app_injective_iso_precomp_iff j.isoOpensRange j.opensRange.ι P)).trans
    (app_injective_iff_appTop_inter j.opensRange P)

/-- Two open immersions with the same image are injective on global sections together. -/
private lemma appTop_injective_iff_of_opensRange_eq {A A' Y : Scheme.{u}} (j : A ⟶ Y)
    (k : A' ⟶ Y) [IsOpenImmersion j] [IsOpenImmersion k] (h : j.opensRange = k.opensRange) :
    Function.Injective (j.appTop).hom ↔ Function.Injective (k.appTop).hom := by
  have hrange : Set.range ⇑j = Set.range ⇑k := congrArg SetLike.coe h
  exact (app_injective_congr_hom
      (IsOpenImmersion.isoOfRangeEq_hom_fac j k hrange) ⊤).symm.trans
    (app_injective_iso_precomp_iff (IsOpenImmersion.isoOfRangeEq j k hrange) k ⊤)

/-- Scheme-theoretic dominance of an open immersion only depends on its image. -/
lemma isSchemeTheoreticallyDominant_of_opensRange_eq {A A' Y : Scheme.{u}} (j : A ⟶ Y)
    (k : A' ⟶ Y) [IsOpenImmersion j] [IsOpenImmersion k] (h : j.opensRange = k.opensRange)
    (hj : IsSchemeTheoreticallyDominant j) : IsSchemeTheoreticallyDominant k := by
  have hrange : Set.range ⇑j = Set.range ⇑k := congrArg SetLike.coe h
  let e := IsOpenImmersion.isoOfRangeEq j k hrange
  have he : e.hom ≫ k = j := IsOpenImmersion.isoOfRangeEq_hom_fac j k hrange
  have h' : IsSchemeTheoreticallyDominant (e.inv ≫ e.hom ≫ k) := by
    rw [he]
    infer_instance
  simpa using h'

/-- An open subscheme is contained in a second one as soon as the inverse image of the second
along the inclusion of the first is everything. -/
private lemma le_of_ι_preimage_eq_top {X : Scheme.{u}} (W W' : X.Opens)
    (h : W.ι ⁻¹ᵁ W' = ⊤) : W ≤ W' := by
  intro x hx
  obtain ⟨z, rfl⟩ : x ∈ Set.range W.ι := by simpa using hx
  change z ∈ W.ι ⁻¹ᵁ W'
  rw [h]
  exact Set.mem_univ z

end Schemes

/-! ### Open subfunctors of a representable presheaf, and their images in the site -/

section Site

/-- Membership in a subfunctor of a representable presheaf which is itself represented by a
morphism of the site is factorization through that morphism. -/
private lemma mem_iff_factors {C : Type*} [Category C] {V R T : C}
    (A : Subfunctor (yoneda.obj V)) (e : yoneda.obj R ≅ A.toFunctor) (j : R ⟶ V)
    (he : e.hom ≫ A.ι = yoneda.map j) (g : T ⟶ V) :
    g ∈ A.obj (op T) ↔ ∃ k : T ⟶ R, k ≫ j = g := by
  have hA : Subfunctor.range (yoneda.map j) = A := by
    rw [← he, Subfunctor.range_comp, Subfunctor.range_eq_top, Subfunctor.image_top,
      Subfunctor.range_ι]
  rw [← hA]
  rfl

/-- A morphism of schemes factors through an open immersion exactly when its set-theoretic
image lies in the image of that open immersion. -/
private lemma schemeMap_factors_openImmersion_iff {T R V : Scheme.{u}} (j : R ⟶ V)
    [IsOpenImmersion j] (g : T ⟶ V) :
    (∃ k : T ⟶ R, k ≫ j = g) ↔ g ⁻¹ᵁ j.opensRange = ⊤ := by
  constructor
  · rintro ⟨k, rfl⟩
    rw [Scheme.Hom.comp_preimage]
    simp
  · intro h
    let k₀ : T ⟶ j.opensRange.toScheme :=
      T.topIso.inv ≫ g.resLE j.opensRange ⊤ (by rw [h])
    refine ⟨k₀ ≫ j.isoOpensRange.inv, ?_⟩
    dsimp [k₀]
    rw [Category.assoc, j.isoOpensRange_inv_comp]
    simp [Scheme.Hom.resLE_comp_ι]

end Site

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Site

/-- A morphism of the site whose underlying morphism of schemes has a base-change stable
property has that property relatively, as a morphism of representable presheaves. -/
lemma presheaf_yoneda_map_of_property (P : MorphismProperty Scheme.{u})
    [P.IsStableUnderBaseChange] {R V : BigFppfOver B S hS} (j : R ⟶ V)
    (hj : P ((BigFppfOver.toScheme B S hS).map j)) :
    (MorphismProperty.inverseImage P (BigFppfOver.toScheme B S hS)).presheaf
      (yoneda.map j) := by
  classical
  have : P.RespectsIso := MorphismProperty.IsStableUnderBaseChange.respectsIso
  have : (MorphismProperty.inverseImage P (BigFppfOver.toScheme B S hS)).RespectsIso :=
    inferInstance
  refine MorphismProperty.relative.of_exists (F := yoneda)
    (P := MorphismProperty.inverseImage P (BigFppfOver.toScheme B S hS)) ?_
  intro A g
  obtain ⟨g₀, rfl⟩ := yoneda.map_surjective g
  have hbase : P ((BigFppfOver.toScheme B S hS).map (pullback.snd j g₀)) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      ((BigFppfOver.toScheme B S hS).map_isPullback (IsPullback.of_hasPullback j g₀)) hj
  exact ⟨pullback j g₀, yoneda.map (pullback.fst j g₀), pullback.snd j g₀,
    yoneda.map_isPullback (IsPullback.of_hasPullback j g₀), hbase⟩

/-- A morphism of the site factors through an open immersion of the site exactly when the
underlying morphism of schemes has image in the open subscheme. -/
lemma siteMap_factors_openImmersion_iff (T R V : BigFppfOver B S hS) (j : R ⟶ V)
    [AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map j)] (g : T ⟶ V) :
    (∃ k : T ⟶ R, k ≫ j = g) ↔
      ((BigFppfOver.toScheme B S hS).map g) ⁻¹ᵁ
        ((BigFppfOver.toScheme B S hS).map j).opensRange = ⊤ := by
  have hs := schemeMap_factors_openImmersion_iff ((BigFppfOver.toScheme B S hS).map j)
    ((BigFppfOver.toScheme B S hS).map g)
  constructor
  · rintro ⟨k, hk⟩
    exact hs.mp ⟨(BigFppfOver.toScheme B S hS).map k, by
      simpa only [(BigFppfOver.toScheme B S hS).map_comp] using
        congrArg (BigFppfOver.toScheme B S hS).map hk⟩
  · intro h
    obtain ⟨k, hk⟩ := hs.mpr h
    let k₀ : T.left ⟶ R.left := B.inclusion.preimage (X := T.left) (Y := R.left) k
    have hk₀ : B.inclusion.map k₀ = k := B.inclusion.map_preimage k
    have hjw : B.inclusion.map j.left ≫ B.inclusion.map V.hom = B.inclusion.map R.hom := by
      simpa only [B.inclusion.map_comp] using congrArg B.inclusion.map j.w
    have hgw : B.inclusion.map g.left ≫ B.inclusion.map V.hom = B.inclusion.map T.hom := by
      simpa only [B.inclusion.map_comp] using congrArg B.inclusion.map g.w
    have hkg : k ≫ B.inclusion.map j.left = B.inclusion.map g.left := hk
    have hbase : k₀ ≫ R.hom = T.hom := by
      refine B.inclusion.map_injective ?_
      change B.inclusion.map k₀ ≫ B.inclusion.map R.hom = B.inclusion.map T.hom
      rw [hk₀, ← hjw, ← Category.assoc, hkg, hgw]
    refine ⟨Over.homMk k₀ hbase, Functor.map_injective (BigFppfOver.toScheme B S hS) ?_⟩
    rw [(BigFppfOver.toScheme B S hS).map_comp]
    change B.inclusion.map k₀ ≫ (BigFppfOver.toScheme B S hS).map j =
      (BigFppfOver.toScheme B S hS).map g
    rw [hk₀, hk]

/-- The inclusion of `AlgebraicGeometry.Space.siteOpenObject` into the ambient object. -/
noncomputable def siteOpenObject_ι (V : BigFppfOver B S hS)
    (W : ((BigFppfOver.toScheme B S hS).obj V).Opens) : siteOpenObject B S hS V W ⟶ V :=
  Over.homMk (B.inclusion.preimage
    (X := B.obj ((Scheme.size_coe_opens_le _ W).trans_lt V.left.property))
    (Y := V.left) W.ι) (by rfl)

/-- The inclusion of `AlgebraicGeometry.Space.siteOpenObject` is the inclusion of the open
subscheme. -/
lemma siteOpenObject_ι_map (V : BigFppfOver B S hS)
    (W : ((BigFppfOver.toScheme B S hS).obj V).Opens) :
    (BigFppfOver.toScheme B S hS).map (siteOpenObject_ι B S hS V W) = W.ι := by
  change B.inclusion.map (B.inclusion.preimage
    (X := B.obj ((Scheme.size_coe_opens_le _ W).trans_lt V.left.property))
    (Y := V.left) W.ι) = W.ι
  rw [B.inclusion.map_preimage]

/-- The inclusion of `AlgebraicGeometry.Space.siteOpenObject` is an open immersion. -/
lemma isOpenImmersion_siteOpenObject_ι (V : BigFppfOver B S hS)
    (W : ((BigFppfOver.toScheme B S hS).obj V).Opens) :
    AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map
      (siteOpenObject_ι B S hS V W)) := by
  rw [siteOpenObject_ι_map]
  infer_instance

/-- The image of `AlgebraicGeometry.Space.siteOpenObject_ι` is the given open subscheme. -/
private lemma siteOpenObject_ι_opensRange (V : BigFppfOver B S hS)
    (W : ((BigFppfOver.toScheme B S hS).obj V).Opens)
    [AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map
      (siteOpenObject_ι B S hS V W))] :
    ((BigFppfOver.toScheme B S hS).map (siteOpenObject_ι B S hS V W)).opensRange = W := by
  ext x
  change (∃ y, ((BigFppfOver.toScheme B S hS).map (siteOpenObject_ι B S hS V W)) y = x) ↔ x ∈ W
  rw [siteOpenObject_ι_map]
  change (∃ y : W, (y : (BigFppfOver.toScheme B S hS).obj V) = x) ↔ x ∈ W
  constructor
  · rintro ⟨y, rfl⟩
    exact y.property
  · intro hx
    exact ⟨⟨x, hx⟩, rfl⟩

/-- The image of an open immersion of the site is pinned down by which morphisms of the site
factor through it: it is the unique open subscheme `W'` for which factorization through the
immersion is the condition that the underlying morphism of schemes land in `W'`.

Both inclusions come from testing the hypothesis on the inclusion of an open subscheme, for
which the condition holds tautologically on its own image. -/
lemma opensRange_eq_of_factors_iff {V R : BigFppfOver B S hS} (j : R ⟶ V)
    [AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map j)]
    (W' : ((BigFppfOver.toScheme B S hS).obj V).Opens)
    (h : ∀ (Q : BigFppfOver B S hS) (k : Q ⟶ V),
      (∃ l : Q ⟶ R, l ≫ j = k) ↔ ((BigFppfOver.toScheme B S hS).map k) ⁻¹ᵁ W' = ⊤) :
    ((BigFppfOver.toScheme B S hS).map j).opensRange = W' := by
  have key : ∀ (W : ((BigFppfOver.toScheme B S hS).obj V).Opens),
      ((BigFppfOver.toScheme B S hS).map (siteOpenObject_ι B S hS V W)) ⁻¹ᵁ W = ⊤ := by
    intro W
    rw [siteOpenObject_ι_map]
    exact W.ι_preimage_self
  refine le_antisymm (le_of_ι_preimage_eq_top _ _ ?_) (le_of_ι_preimage_eq_top _ _ ?_)
  · have hfac := (siteMap_factors_openImmersion_iff B S hS
      (siteOpenObject B S hS V ((BigFppfOver.toScheme B S hS).map j).opensRange) R V j
      (siteOpenObject_ι B S hS V _)).mpr (key _)
    have := (h _ (siteOpenObject_ι B S hS V _)).1 hfac
    rwa [siteOpenObject_ι_map] at this
  · have hfac := (h (siteOpenObject B S hS V W') (siteOpenObject_ι B S hS V W')).2 (key W')
    have := (siteMap_factors_openImmersion_iff B S hS (siteOpenObject B S hS V W') R V j
      (siteOpenObject_ι B S hS V W')).mp hfac
    rwa [siteOpenObject_ι_map] at this

/-! ### The chart of the inverse image of an open subspace -/

/-- For a representable inclusion of an open subspace `U ⊆ X` and a scheme chart
`φ : V ⟶ X`, the inverse image `U ×_X V` is represented by the object
`hU.rep.pullback φ` of the site. -/
noncomputable def preimageIso {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (U : Subfunctor X)
    (hrep : yoneda.relativelyRepresentable U.ι) {V : BigFppfOver B S hS}
    (φ : yoneda.obj V ⟶ X) :
    yoneda.obj (hrep.pullback φ) ≅ (U.preimage φ).toFunctor :=
  (hrep.isPullback φ).flip.isoIsPullback _ _ (Subfunctor.isPullback_preimage φ U).flip

/-- The representation `AlgebraicGeometry.Space.preimageIso` of the inverse image of an open
subspace is compatible with the inclusions into the chart. -/
lemma preimageIso_hom_ι {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (U : Subfunctor X)
    (hrep : yoneda.relativelyRepresentable U.ι) {V : BigFppfOver B S hS}
    (φ : yoneda.obj V ⟶ X) :
    (preimageIso B S hS U hrep φ).hom ≫ (U.preimage φ).ι = yoneda.map (hrep.snd φ) :=
  (hrep.isPullback φ).flip.isoIsPullback_hom_fst _ _ (Subfunctor.isPullback_preimage φ U).flip

/-- A morphism of the site lies in the inverse image of an open subspace along a scheme chart
exactly when it factors through the representing morphism of that inverse image. -/
lemma mem_preimage_iff_factors {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (U : Subfunctor X)
    (hrep : yoneda.relativelyRepresentable U.ι) {V : BigFppfOver B S hS}
    (φ : yoneda.obj V ⟶ X) (Q : BigFppfOver B S hS) (k : Q ⟶ V) :
    k ∈ (U.preimage φ).obj (op Q) ↔ ∃ l : Q ⟶ hrep.pullback φ, l ≫ hrep.snd φ = k :=
  mem_iff_factors (U.preimage φ) (preimageIso B S hS U hrep φ) (hrep.snd φ)
    (preimageIso_hom_ι B S hS U hrep φ) k

/-- The morphism of schemes representing the inverse image of an open subspace along a scheme
chart is an open immersion. -/
lemma isOpenImmersion_snd {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {U : Subfunctor X}
    (hU : IsOpenImmersion B S hS U.ι) {V : BigFppfOver B S hS} (φ : yoneda.obj V ⟶ X) :
    AlgebraicGeometry.IsOpenImmersion
      ((BigFppfOver.toScheme B S hS).map (hU.rep.snd φ)) :=
  hU.property_snd φ

/-- An open subscheme of an étale scheme chart of `X`, as an étale scheme chart of `X`: the
inclusion of an open subscheme is étale, and étale morphisms compose. -/
private noncomputable abbrev chartOpenRestriction {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (V : SmallEtale B S hS X)
    (W : ((BigFppfOver.toScheme B S hS).obj V.1.left).Opens) : SmallEtale B S hS X := by
  refine ⟨CostructuredArrow.mk
    (yoneda.map (siteOpenObject_ι B S hS V.1.left W) ≫ V.1.hom), ?_⟩
  have hopen : Etale ((BigFppfOver.toScheme B S hS).map
      (siteOpenObject_ι B S hS V.1.left W)) := by
    rw [siteOpenObject_ι_map]
    exact HasRingHomProperty.of_isOpenImmersion RingHom.Etale.containsIdentities
  have := etale_isStableUnderComposition.{u}
  have : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).IsStableUnderComposition :=
    MorphismProperty.IsStableUnderComposition.inverseImage (BigFppfOver.toScheme B S hS)
  have : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf.IsStableUnderComposition :=
    MorphismProperty.relative_isStableUnderComposition _
  exact MorphismProperty.comp_mem _ (yoneda.map (siteOpenObject_ι B S hS V.1.left W))
    V.1.hom (presheaf_yoneda_map_of_property B S hS (@Etale.{u}) _ hopen) V.2

/-- The chart of `AlgebraicGeometry.Space.chartOpenRestriction` is the given open subscheme of
the chart, over `X` through the original chart. -/
private lemma chartOpenRestriction_hom {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (V : SmallEtale B S hS X)
    (W : ((BigFppfOver.toScheme B S hS).obj V.1.left).Opens) :
    (chartOpenRestriction B S hS V W).1.hom =
      yoneda.map (siteOpenObject_ι B S hS V.1.left W) ≫ V.1.hom := rfl

/-- **The inverse image of an open subspace is compatible with restriction of the chart.** For
an open subspace `U ⊆ X`, an étale scheme chart `V` of `X` and an open subscheme `W` of `V`,
the image of the morphism of schemes representing `U ×_X W` is the part of the image of the one
representing `U ×_X V` lying over `W`.

Both are open subschemes of `W` through which the same morphisms of the site factor, namely
those landing in `U` after composition with the chart `V`, so
`AlgebraicGeometry.Space.opensRange_eq_of_factors_iff` identifies them. -/
private lemma opensRange_snd_chartOpenRestriction {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {U : Subfunctor X} (hU : IsOpenImmersion B S hS U.ι) (V : SmallEtale B S hS X)
    (W : ((BigFppfOver.toScheme B S hS).obj V.1.left).Opens)
    [AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map
      (hU.rep.snd (chartOpenRestriction B S hS V W).1.hom))]
    [AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map
      (hU.rep.snd V.1.hom))] :
    ((BigFppfOver.toScheme B S hS).map
        (hU.rep.snd (chartOpenRestriction B S hS V W).1.hom)).opensRange =
      (W.ι ⁻¹ᵁ ((BigFppfOver.toScheme B S hS).map (hU.rep.snd V.1.hom)).opensRange).ι.opensRange
        := by
  rw [Scheme.Opens.opensRange_ι]
  refine opensRange_eq_of_factors_iff B S hS
    (hU.rep.snd (chartOpenRestriction B S hS V W).1.hom) _ fun Q k => ?_
  have h1 : k ∈ (U.preimage (chartOpenRestriction B S hS V W).1.hom).obj (op Q) ↔
      (k ≫ siteOpenObject_ι B S hS V.1.left W) ∈ (U.preimage V.1.hom).obj (op Q) := Iff.rfl
  have h4 : ((BigFppfOver.toScheme B S hS).map
        (k ≫ siteOpenObject_ι B S hS V.1.left W)) ⁻¹ᵁ
        ((BigFppfOver.toScheme B S hS).map (hU.rep.snd V.1.hom)).opensRange =
      ((BigFppfOver.toScheme B S hS).map k) ⁻¹ᵁ (W.ι ⁻¹ᵁ
        ((BigFppfOver.toScheme B S hS).map (hU.rep.snd V.1.hom)).opensRange) := by
    rw [(BigFppfOver.toScheme B S hS).map_comp, Scheme.Hom.comp_preimage, siteOpenObject_ι_map]
  exact (mem_preimage_iff_factors B S hS U hU.rep
      (chartOpenRestriction B S hS V W).1.hom Q k).symm.trans
    (h1.trans ((mem_preimage_iff_factors B S hS U hU.rep V.1.hom Q
      (k ≫ siteOpenObject_ι B S hS V.1.left W)).trans
      ((siteMap_factors_openImmersion_iff B S hS Q (hU.rep.pullback V.1.hom) V.1.left
        (hU.rep.snd V.1.hom) (k ≫ siteOpenObject_ι B S hS V.1.left W)).trans
          (by rw [h4]))))

end Site

/-! ### Descent of subfunctors along a surjective étale chart -/

/-- A subsheaf of an algebraic space is everything as soon as its inverse image along one
surjective étale scheme chart is everything.

The chart presents the algebraic space as the coequalizer of its kernel pair in sheaves of
sets, by `AlgebraicGeometry.Space.isCoequalizer_of_surjectiveEtale`. The chart factors through
the subsheaf, and the two projections of the kernel pair agree after that factorization because
the inclusion of a subfunctor is a monomorphism, so the factorization descends to a section of
the inclusion. -/
lemma subfunctor_eq_top_of_isSurjective_isEtale_preimage
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y)
    (Z : Subfunctor Y)
    (hZ : Presheaf.IsSheaf (BigFppfOver.topology B S hS) Z.toFunctor)
    (V : BigFppfOver B S hS) (f : yoneda.obj V ⟶ Y)
    (hsurj : MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)) f)
    (hetale : MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)) f)
    (hpre : Z.preimage f = ⊤) : Z = ⊤ := by
  classical
  have : HasBinaryProducts (BigFppfOver B S hS) :=
    hasBinaryProducts_of_hasTerminal_and_pullbacks _
  have hrep : yoneda.relativelyRepresentable f :=
    (Functor.relativelyRepresentable.diag_iff (F := yoneda) (X := Y)).1
      hY.diagonal_representable f
  have hpb : IsPullback (yoneda.map (hrep.fst' f)) (yoneda.map (hrep.snd f)) f f :=
    hrep.isPullback' f
  obtain ⟨hRsh, hVsh, hcol⟩ := isCoequalizer_of_surjectiveEtale B S hS f (hrep.fst' f)
    (hrep.snd f) hpb hY hsurj hetale
  have hmem : Subfunctor.range f ≤ Z := by
    rintro T _ ⟨x, rfl⟩
    have hx : x ∈ (Z.preimage f).obj T := by
      rw [hpre]
      simp
    exact hx
  have hfz : Subfunctor.lift f hmem ≫ Z.ι = f := Subfunctor.lift_ι f hmem
  set J := BigFppfOver.topology B S hS
  set RF : Sheaf J (Type u) := ⟨yoneda.obj (hrep.pullback f), hRsh⟩
  set VF : Sheaf J (Type u) := ⟨yoneda.obj V, hVsh⟩
  set YF : Sheaf J (Type u) := ⟨Y, hY.isSheaf⟩
  set ZF : Sheaf J (Type u) := ⟨Z.toFunctor, hZ⟩
  set sf : RF ⟶ VF := ⟨yoneda.map (hrep.fst' f)⟩
  set tf : RF ⟶ VF := ⟨yoneda.map (hrep.snd f)⟩
  set ff : VF ⟶ YF := ⟨f⟩
  have hw : sf ≫ ff = tf ≫ ff := Sheaf.hom_ext hpb.w
  have hcolim : IsColimit (Cofork.ofπ ff hw) := Classical.choice hcol
  have heq : sf ≫ (⟨Subfunctor.lift f hmem⟩ : VF ⟶ ZF) =
      tf ≫ (⟨Subfunctor.lift f hmem⟩ : VF ⟶ ZF) := by
    refine Sheaf.hom_ext ?_
    change yoneda.map (hrep.fst' f) ≫ Subfunctor.lift f hmem =
      yoneda.map (hrep.snd f) ≫ Subfunctor.lift f hmem
    refine (cancel_mono Z.ι).1 ?_
    simpa only [Category.assoc, hfz] using hpb.w
  have hdesc : ff ≫ Cofork.IsColimit.desc hcolim (⟨Subfunctor.lift f hmem⟩ : VF ⟶ ZF) heq =
      (⟨Subfunctor.lift f hmem⟩ : VF ⟶ ZF) :=
    Cofork.IsColimit.π_desc' hcolim _ heq
  have hcomp : Cofork.IsColimit.desc hcolim (⟨Subfunctor.lift f hmem⟩ : VF ⟶ ZF) heq ≫
      (⟨Z.ι⟩ : ZF ⟶ YF) = 𝟙 YF := by
    refine Cofork.IsColimit.hom_ext hcolim ?_
    change ff ≫ _ ≫ _ = ff ≫ 𝟙 YF
    rw [← Category.assoc, hdesc, Category.comp_id]
    exact Sheaf.hom_ext hfz
  ext T x
  refine ⟨fun _ => Set.mem_univ x, fun _ => ?_⟩
  have hz : (Z.ι.app T (Cofork.IsColimit.desc hcolim
      (⟨Subfunctor.lift f hmem⟩ : VF ⟶ ZF) heq |>.hom.app T x) : Y.obj T) = x := by
    simpa using congrArg (fun g : YF ⟶ YF => g.hom.app T x) hcomp
  rw [← hz]
  exact (Cofork.IsColimit.desc hcolim (⟨Subfunctor.lift f hmem⟩ : VF ⟶ ZF) heq
    |>.hom.app T x).property

/-! ### The scheme-theoretic image of a morphism of the site -/

section Image

/-- The scheme-theoretic image of a morphism of schemes underlying a morphism of the site is
again an object of the site: it is a closed subscheme of the target, hence no larger. -/
private lemma exists_schemeImage_site {A V : BigFppfOver B S hS} (f : A ⟶ V) :
    ∃ (R : BigFppfOver B S hS) (q : R ⟶ V) (l : A ⟶ R),
      ∃ e : (BigFppfOver.toScheme B S hS).obj R ≅
          ((BigFppfOver.toScheme B S hS).map f).image,
        (BigFppfOver.toScheme B S hS).map q =
            e.hom ≫ ((BigFppfOver.toScheme B S hS).map f).imageι ∧
          l ≫ q = f := by
  classical
  have hI : B.Contains ((BigFppfOver.toScheme B S hS).map f).image :=
    lt_of_le_of_lt (Scheme.size_le_of_mono_quasiCompact
      ((BigFppfOver.toScheme B S hS).map f).imageι) V.left.property
  let qI : B.obj hI ⟶ V.left := B.inclusion.preimage (X := B.obj hI) (Y := V.left)
    ((BigFppfOver.toScheme B S hS).map f).imageι
  let lI : A.left ⟶ B.obj hI := B.inclusion.preimage (X := A.left) (Y := B.obj hI)
    ((BigFppfOver.toScheme B S hS).map f).toImage
  have hlI : lI ≫ qI = f.left := by
    refine B.inclusion.map_injective ?_
    rw [B.inclusion.map_comp, B.inclusion.map_preimage (X := A.left) (Y := B.obj hI)
      ((BigFppfOver.toScheme B S hS).map f).toImage,
      B.inclusion.map_preimage (X := B.obj hI) (Y := V.left)
        ((BigFppfOver.toScheme B S hS).map f).imageι]
    change ((BigFppfOver.toScheme B S hS).map f).toImage ≫
      ((BigFppfOver.toScheme B S hS).map f).imageι = (BigFppfOver.toScheme B S hS).map f
    rw [Scheme.Hom.toImage_imageι]
  refine ⟨Over.mk (qI ≫ V.hom), Over.homMk qI, Over.homMk lI (by
    change lI ≫ (qI ≫ V.hom) = A.hom
    rw [← Category.assoc, hlI, f.w]), eqToIso (by rfl), ?_, ?_⟩
  · change B.inclusion.map qI = _
    rw [B.inclusion.map_preimage (X := B.obj hI) (Y := V.left)
      ((BigFppfOver.toScheme B S hS).map f).imageι]
    simp
  · ext
    exact congrArg (fun k => k.hom) hlI

/-- A morphism of the site whose scheme-theoretic image is everything has scheme-theoretically
dominant underlying morphism of schemes. -/
private lemma isSchemeTheoreticallyDominant_of_schemeTheoreticImageSubfunctor_yoneda_eq_top
    {A V : BigFppfOver B S hS} (f : A ⟶ V)
    (htop : schemeTheoreticImageSubfunctor B S hS (yoneda.map f) = ⊤) :
    IsSchemeTheoreticallyDominant ((BigFppfOver.toScheme B S hS).map f) := by
  classical
  obtain ⟨R, q, l, e, hq, hlq⟩ := exists_schemeImage_site B S hS f
  have hqClosed : AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map q) := by
    rw [hq]
    infer_instance
  have hIle : schemeTheoreticImageSubfunctor B S hS (yoneda.map f) ≤
      Subfunctor.range (yoneda.map q) := by
    refine schemeTheoreticImageSubfunctor_le B S hS (yoneda.map f)
      (isClosedSubspace_range_yoneda_map B S hS q hqClosed) ?_
    rw [← hlq, yoneda.map_comp]
    exact Subfunctor.range_comp_le _ _
  rw [htop] at hIle
  obtain ⟨a, ha⟩ : ∃ a : V ⟶ R, a ≫ q = 𝟙 V := by
    have hm : (𝟙 V) ∈ (Subfunctor.range (yoneda.map q)).obj (op V) := by
      rw [top_le_iff.mp hIle]
      simp
    obtain ⟨a, ha⟩ := hm
    exact ⟨a, ha⟩
  have hqa : (BigFppfOver.toScheme B S hS).map a ≫ (BigFppfOver.toScheme B S hS).map q =
      𝟙 ((BigFppfOver.toScheme B S hS).obj V) := by
    simpa using congrArg (BigFppfOver.toScheme B S hS).map ha
  have : IsSplitEpi ((BigFppfOver.toScheme B S hS).map q) :=
    IsSplitEpi.mk' ⟨(BigFppfOver.toScheme B S hS).map a, hqa⟩
  have hkerq : ((BigFppfOver.toScheme B S hS).map q).ker = ⊥ :=
    IsClosedImmersion.isIso_iff_ker_eq_bot.mp
      (isIso_of_mono_of_isSplitEpi ((BigFppfOver.toScheme B S hS).map q))
  refine ⟨?_⟩
  rw [← hkerq, hq, Scheme.Hom.ker_comp_of_isIso, Scheme.Hom.imageι,
    Scheme.IdealSheafData.ker_subschemeι]

/-- A morphism of the site whose underlying morphism of schemes is scheme-theoretically dominant
has scheme-theoretic image everything. -/
private lemma schemeTheoreticImageSubfunctor_yoneda_eq_top_of_isSchemeTheoreticallyDominant
    {A V : BigFppfOver B S hS} (f : A ⟶ V)
    (hdom : IsSchemeTheoreticallyDominant ((BigFppfOver.toScheme B S hS).map f)) :
    schemeTheoreticImageSubfunctor B S hS (yoneda.map f) = ⊤ := by
  classical
  obtain ⟨R, j, hj, heq⟩ := exists_closedImmersion_range B S hS
    (schemeTheoreticImageSubfunctor B S hS (yoneda.map f))
    (isClosedSubspace_schemeTheoreticImageSubfunctor B S hS (yoneda.map f)
      (isAlgebraicSpace_yoneda B S hS V))
  obtain ⟨l, hcompSite⟩ : ∃ l : A ⟶ R, l ≫ j = f := by
    have hmem : Subfunctor.range (yoneda.map f) ≤ Subfunctor.range (yoneda.map j) := by
      rw [← heq]
      exact range_le_schemeTheoreticImageSubfunctor B S hS (yoneda.map f)
    have hf : f ∈ (Subfunctor.range (yoneda.map f)).obj (op A) := ⟨𝟙 A, by simp⟩
    obtain ⟨l, hl⟩ := hmem (op A) hf
    exact ⟨l, hl⟩
  have hle : ((BigFppfOver.toScheme B S hS).map j).ker ≤
      ((BigFppfOver.toScheme B S hS).map f).ker := by
    rw [← hcompSite, (BigFppfOver.toScheme B S hS).map_comp]
    exact Scheme.Hom.le_ker_comp _ _
  rw [hdom.ker_eq_bot, le_bot_iff] at hle
  have : IsIso j := (isIso_iff_of_reflects_iso j (BigFppfOver.toScheme B S hS)).mp
    (IsClosedImmersion.isIso_iff_ker_eq_bot.mpr hle)
  rw [heq]
  have : IsIso (yoneda.map j) := Functor.map_isIso _ _
  exact @Subfunctor.range_eq_top _ _ _ _ (yoneda.map j) (IsIso.epi_of_iso _)

/-- **The scheme-theoretic image of a morphism of the site is everything exactly when the
morphism is scheme-theoretically dominant.** The scheme-theoretic image of the morphism of
representable presheaves is `⊤` if and only if the kernel ideal sheaf of the underlying
morphism of schemes vanishes.

If the image is `⊤` then the closed subspace cut out by the scheme-theoretic image of schemes,
which is an object of the site by
`AlgebraicGeometry.Space.exists_schemeImage_site`, is `⊤` as well, so its inclusion has a
section and is therefore an isomorphism, forcing the kernel to vanish. Conversely a closed
subspace containing the range is the range of a closed immersion of schemes through which the
morphism factors, so its kernel is contained in the kernel of the morphism; if the latter
vanishes, that closed immersion is an isomorphism. -/
lemma schemeTheoreticImageSubfunctor_yoneda_eq_top_iff {A V : BigFppfOver B S hS}
    (f : A ⟶ V) :
    schemeTheoreticImageSubfunctor B S hS (yoneda.map f) = ⊤ ↔
      IsSchemeTheoreticallyDominant ((BigFppfOver.toScheme B S hS).map f) :=
  ⟨isSchemeTheoreticallyDominant_of_schemeTheoreticImageSubfunctor_yoneda_eq_top B S hS f,
    schemeTheoreticImageSubfunctor_yoneda_eq_top_of_isSchemeTheoreticallyDominant B S hS f⟩

/-- **The scheme-theoretic closure of the inverse image of an open subspace in a chart.** For
an open subspace `U ⊆ X` and a scheme chart `φ : V ⟶ X`, the scheme-theoretic closure of
`U ×_X V` in `V` is everything exactly when the morphism of schemes representing `U ×_X V` is
scheme-theoretically dominant. -/
lemma schemeTheoreticImageSubfunctor_preimage_eq_top_iff
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {U : Subfunctor X}
    (hU : IsOpenImmersion B S hS U.ι) {V : BigFppfOver B S hS} (φ : yoneda.obj V ⟶ X) :
    schemeTheoreticImageSubfunctor B S hS (U.preimage φ).ι = ⊤ ↔
      IsSchemeTheoreticallyDominant ((BigFppfOver.toScheme B S hS).map (hU.rep.snd φ)) := by
  have hepi : Subfunctor.range (preimageIso B S hS U hU.rep φ).hom = ⊤ :=
    @Subfunctor.range_eq_top _ _ _ _ _ (IsIso.epi_of_iso _)
  have hrange : Subfunctor.range ((U.preimage φ).ι) =
      Subfunctor.range (yoneda.map (hU.rep.snd φ)) := by
    rw [← preimageIso_hom_ι B S hS U hU.rep φ, Subfunctor.range_comp, hepi,
      Subfunctor.image_top]
  rw [schemeTheoreticImageSubfunctor_congr_range B S hS _ _
    (isAlgebraicSpace_yoneda B S hS V) hrange]
  exact schemeTheoreticImageSubfunctor_yoneda_eq_top_iff B S hS (hU.rep.snd φ)

end Image

/-! ### Injectivity over every chart -/

section Charts

variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {U : Subfunctor X}

/-- **Injectivity on global sections over every chart is injectivity on all sections.** For an
open subspace `U ⊆ X`, pullback of regular functions along the morphism of schemes representing
`U ×_X V` is injective for every étale scheme chart `V` of `X` exactly when, for every such
chart, the whole structure-sheaf map of that morphism is a monomorphism.

The charts of `X` include every open subscheme of every chart, by
`AlgebraicGeometry.Space.chartOpenRestriction`, and over an open subscheme `P` of `V` the
inverse image of `U` is the part of `U ×_X V` lying over `P` by
`AlgebraicGeometry.Space.opensRange_snd_chartOpenRestriction`. So injectivity on global
sections over all charts is injectivity on sections over every open subscheme of every
chart. -/
lemma forall_injective_appTop_iff_forall_mono_c (hU : IsOpenImmersion B S hS U.ι) :
    (∀ V : SmallEtale B S hS X, Function.Injective
        ((BigFppfOver.toScheme B S hS).map (hU.rep.snd V.1.hom)).appTop.hom) ↔
      ∀ V : SmallEtale B S hS X,
        Mono ((BigFppfOver.toScheme B S hS).map (hU.rep.snd V.1.hom)).c := by
  constructor
  · intro h V
    have := isOpenImmersion_snd B S hS hU V.1.hom
    refine (mono_c_iff_app_injective _).mpr fun P => ?_
    rw [app_injective_iff_appTop_preimage_opensRange]
    have := isOpenImmersion_snd B S hS hU (chartOpenRestriction B S hS V P).1.hom
    have hr := opensRange_snd_chartOpenRestriction B S hS hU V P
    exact (appTop_injective_iff_of_opensRange_eq _ _ hr).mp
      (h (chartOpenRestriction B S hS V P))
  · intro h V
    exact (mono_c_iff_app_injective _).mp (h V) ⊤

/-- **Scheme-theoretic dominance over every chart.** For an open subspace `U ⊆ X` the
structure-sheaf map of the morphism of schemes representing `U ×_X V` is a monomorphism for
every étale scheme chart `V` of `X` exactly when that morphism is scheme-theoretically dominant
for every such chart.

A monomorphic structure-sheaf map is injective on the sections over the affine opens, so the
kernel ideal sheaf vanishes. Conversely dominance over all the charts restricting `V` says
exactly that the image of `U ×_X V` is a scheme-theoretically dense open subscheme of `V`,
which is `AlgebraicGeometry.isSchemeTheoreticallyDense_opensRange_iff_mono`. -/
lemma forall_mono_c_iff_forall_isSchemeTheoreticallyDominant
    (hU : IsOpenImmersion B S hS U.ι) :
    (∀ V : SmallEtale B S hS X,
        Mono ((BigFppfOver.toScheme B S hS).map (hU.rep.snd V.1.hom)).c) ↔
      ∀ V : SmallEtale B S hS X, IsSchemeTheoreticallyDominant
        ((BigFppfOver.toScheme B S hS).map (hU.rep.snd V.1.hom)) := by
  constructor
  · intro h V
    exact ⟨ker_eq_bot_of_app_injective_affine _ fun W =>
      (mono_c_iff_app_injective _).mp (h V) W.1⟩
  · intro h V
    have := isOpenImmersion_snd B S hS hU V.1.hom
    refine (isSchemeTheoreticallyDense_opensRange_iff_mono
      ((BigFppfOver.toScheme B S hS).map (hU.rep.snd V.1.hom))).1 fun P => ?_
    have := isOpenImmersion_snd B S hS hU (chartOpenRestriction B S hS V P).1.hom
    have hr := opensRange_snd_chartOpenRestriction B S hS hU V P
    exact isSchemeTheoreticallyDominant_of_opensRange_eq _ _ hr
      (h (chartOpenRestriction B S hS V P))

end Charts

/-! ### The structure map of a morphism of algebraic spaces, chartwise -/

section StructureMap

variable {X Y : AlgebraicSpaces B S hS}

end StructureMap

end Space

end AlgebraicGeometry

end
