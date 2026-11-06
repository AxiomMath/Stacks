module

public import StacksFrontier.AlgebraicGeometry.Descent.OpenImmersionEtaleDescent
public import StacksFrontier.AlgebraicGeometry.Scheme.PreimageComp
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompact
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteLocusOnCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedCriteria

/-!
# Zariski's main theorem for a representable morphism of algebraic spaces

Let `f : X ⟶ Y` be a morphism of algebraic spaces over `S` which is representable, of finite type
and separated, and let

`X --f'--> Y' --ν--> Y`

be the normalization of `Y` in `X` with its canonical factorization of `f`. Tag 0ABR says that
there is an open subspace `U' ⊆ Y'` such that `(f')⁻¹(U') ⟶ U'` is an isomorphism and
`(f')⁻¹(U') ⊆ X` is the set of points at which `f` is quasi-finite. This file proves it, with
`U'` the image of the quasi-finite locus.

## Main definitions

* `AlgebraicGeometry.Space.NormalizationInData` is the normalization of `Y` in `X` as data: the
  space `Y'`, the two morphisms, the factorization, and the étale-chart description of Tag 0ABP.
* `AlgebraicGeometry.Space.NormalizationInData.quasiFiniteImage` is the image in `Y'` of the
  quasi-finite locus of `f`. It is the open subspace `U'` of the tag.

## Main results

* `AlgebraicGeometry.preimage_range_quasiFiniteLocus_comp_toNormalization`,
  `AlgebraicGeometry.isOpenImmersion_comp_of_range_eq_quasiFiniteLocus` and
  `AlgebraicGeometry.preimage_range_comp_eq_quasiFiniteLocus` are Zariski's main theorem for
  schemes, Tag 03GW, in the two forms the chart argument uses: the quasi-finite locus maps into
  the relative normalization by an open immersion, and its image has the quasi-finite locus as
  inverse image.
* `AlgebraicGeometry.Space.NormalizationInData.isOpenSubspace_quasiFiniteImage`,
  `AlgebraicGeometry.Space.NormalizationInData.isIso_fromPreimage_quasiFiniteImage`,
  `AlgebraicGeometry.Space.NormalizationInData.preimage_quasiFiniteImage_eq` and
  `AlgebraicGeometry.Space.NormalizationInData.range_pointsMap_preimage_quasiFiniteImage` are the
  three assertions of **Tag 0ABR**: the image of the quasi-finite locus is an open subspace, the
  canonical morphism is an isomorphism over it, and its inverse image is the quasi-finite locus —
  both as a subspace and, as the source states it, as a set of points.
* `Space.exists_isOpenSubspace_isIso_fromPreimage_and_range_pointsMap_preimage_eq` is the
  existence statement of the tag, assembled from those.

## Implementation notes

**Why the normalization is data.** Tag 0ABR takes `Y'` as given: it is the normalization of
`Y` in `X`, Definition 0822. In this library that construction
(`AlgebraicGeometry.Space.normalizationIn`) is the relative spectrum of the integral closure of
`𝒪_Y` in `f_* 𝒪_X`, and it is available only under the hypotheses of Tag 081V — an
anti-equivalence between algebraic spaces affine over `Y` and quasi-coherent `𝒪_Y`-algebras,
which has no inhabitant in this library — together with quasi-coherence of `f_* 𝒪_X` and of the
integral closure. The *content* of the tag does not use any of that: it uses only what Tag 0ABP
says about the normalization, namely that over an étale scheme chart `W ⟶ Y` the fibre product
`W ×_Y Y'` is the relative normalization of the scheme `W` in the scheme `W ×_Y X`. So the
normalization enters here as `AlgebraicGeometry.Space.NormalizationInData`, which records exactly
that description. Producing such a datum from `AlgebraicGeometry.Space.normalizationIn` is Tag
0ABP — `AlgebraicGeometry.Space.normalizationInBaseChangeIso` for part (1) and
`AlgebraicGeometry.Space.normalizationInRepresentableIso` for part (2) — and is not done here;
nothing in this file carries the tag of 0822 or of 0ABP.

**Where the scheme case comes from.** Zariski's main theorem for schemes is Tag 03GW, and Mathlib
proves it as `AlgebraicGeometry.Scheme.Hom.exists_isIso_morphismRestrict_toNormalization`. That
statement produces *some* open of the normalization; the two forms used here name it, as the
image of the quasi-finite locus, which is possible because the restriction of the canonical
morphism over it is an isomorphism and hence surjective. Both forms are stated in terms of a
morphism `ρ` into an arbitrary scheme together with an identification of that scheme with the
normalization, which is the shape in which the chart description of
`AlgebraicGeometry.Space.NormalizationInData` supplies them.

**The descent step.** The restriction of `f'` to the quasi-finite locus is shown to be an open
immersion by Tag 03M4 for open immersions
(`AlgebraicGeometry.Space.isOpenImmersion_tfae_of_isAlgebraicSpace`), tested on the single
surjective étale chart `W ×_Y Y' ⟶ Y'` which the chart description provides; and the identity
`(f')⁻¹(U') = ` quasi-finite locus is proved after inverse image along the surjective chart
`W ×_Y X ⟶ X` and then descended, two open subspaces with the same inverse image along a
morphism surjective on points being equal
(`AlgebraicGeometry.Space.eq_of_preimage_eq_of_isSurjective`). The source omits this
verification.

**On the hypotheses.** Finite type is carried as its two halves, `IsLocallyOfFiniteType` and
`IsQuasiCompact`, which is how Tag 03XF part (3) defines it. Separatedness and quasi-compactness
of `f` are used only through their chart forms, Tag 03KY
(`AlgebraicGeometry.Space.isSeparated_iff_presheaf`) and Tag 03HD
(`AlgebraicGeometry.Space.presheaf_quasiCompact_iff_isQuasiCompact`), which is where
representability of `f` is needed a second time.

## References

* [Stacks Project, Tag 0ABM](https://stacks.math.columbia.edu/tag/0ABM)
* [Stacks Project, Tag 0ABP](https://stacks.math.columbia.edu/tag/0ABP)
* [Stacks Project, Tag 0ABR](https://stacks.math.columbia.edu/tag/0ABR)
* [Stacks Project, Tag 0822](https://stacks.math.columbia.edu/tag/0822)
* [Stacks Project, Tag 03GW](https://stacks.math.columbia.edu/tag/03GW)
* [Stacks Project, Tag 03HD](https://stacks.math.columbia.edu/tag/03HD)
* [Stacks Project, Tag 03KY](https://stacks.math.columbia.edu/tag/03KY)
* [Stacks Project, Tag 03M4](https://stacks.math.columbia.edu/tag/03M4)
* [Stacks Project, Tag 03XF](https://stacks.math.columbia.edu/tag/03XF)
* [Stacks Project, Tag 03XJ](https://stacks.math.columbia.edu/tag/03XJ)
* [Stacks Project, Tag 081V](https://stacks.math.columbia.edu/tag/081V)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-! ### Zariski's main theorem for schemes, in the form used on a chart -/

section SchemeLevel

/-- The range of a composite, on the underlying spaces. -/
private theorem range_comp_base {A C D : Scheme.{u}} (g : A ⟶ C) (h : C ⟶ D) :
    Set.range (g ≫ h).base = h.base '' Set.range g.base := by
  ext t
  simp only [Set.mem_range, Set.mem_image]
  constructor
  · rintro ⟨s, rfl⟩
    exact ⟨g s, ⟨s, rfl⟩, Scheme.Hom.comp_apply g h s⟩
  · rintro ⟨y, ⟨s, rfl⟩, rfl⟩
    exact ⟨s, (Scheme.Hom.comp_apply g h s).symm⟩

/-- Precomposing with a surjection does not change the range. -/
private theorem range_comp_base_of_surjective {A C D : Scheme.{u}} (g : A ⟶ C) (h : C ⟶ D)
    (hg : Function.Surjective g.base) : Set.range (g ≫ h).base = Set.range h.base := by
  rw [range_comp_base, hg.range_eq, Set.image_univ]

/-- **Zariski's main theorem for schemes, the second clause, with the open subscheme named.** For
a separated morphism of finite type the inverse image under the canonical morphism to the
relative normalization of the image of the quasi-finite locus is the quasi-finite locus itself.

Tag 03GW, which Mathlib proves as
`AlgebraicGeometry.Scheme.Hom.exists_isIso_morphismRestrict_toNormalization`, produces *some*
open `U` of the normalization whose inverse image is the quasi-finite locus and over which the
canonical morphism restricts to an isomorphism; being an isomorphism that restriction is
surjective, so `U` is the image of the quasi-finite locus and the open of the tag is pinned
down. -/
theorem preimage_range_quasiFiniteLocus_comp_toNormalization {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] [IsSeparated f] [QuasiCompact f] :
    f.toNormalization.base ⁻¹' Set.range (f.quasiFiniteLocus.ι ≫ f.toNormalization).base =
      (f.quasiFiniteLocus : Set X) := by
  obtain ⟨U, hiso, he⟩ := Scheme.Hom.exists_isIso_morphismRestrict_toNormalization f
  have hsurj : Function.Surjective (f.toNormalization ∣_ U).base := Surjective.surj
  have hpre : f.toNormalization.base ⁻¹' (U : Set _) = (f.quasiFiniteLocus : Set X) := he
  have hrange : Set.range (f.quasiFiniteLocus.ι ≫ f.toNormalization).base = (U : Set _) := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      rw [Scheme.Hom.comp_apply]
      exact (Set.ext_iff.1 hpre (f.quasiFiniteLocus.ι x)).2 x.2
    · intro hy
      obtain ⟨z, hz⟩ := hsurj ⟨y, hy⟩
      have hzmem : ((f.toNormalization ⁻¹ᵁ U).ι z : X) ∈ (f.quasiFiniteLocus : Set X) := by
        rw [← hpre]
        exact z.2
      have h2 : U.ι ((f.toNormalization ∣_ U) z) =
          f.toNormalization ((f.toNormalization ⁻¹ᵁ U).ι z) := by
        rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, morphismRestrict_ι]
      rw [hz] at h2
      exact ⟨(⟨((f.toNormalization ⁻¹ᵁ U).ι z : X), hzmem⟩ :
        ((f.quasiFiniteLocus : Set X) : Type u)), h2.symm⟩
  rw [hrange, hpre]

section ChartComparison

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] [IsSeparated f] [QuasiCompact f]
    {Q : Scheme.{u}} (j : Q ⟶ X) [IsOpenImmersion j]
    (hj : Set.range j.base = (f.quasiFiniteLocus : Set X))
    (ρ : X ⟶ Z) (e : Z ≅ f.normalization) (hρ : ρ ≫ e.hom = f.toNormalization)

include hj hρ

/-- An open immersion whose image is the quasi-finite locus is, after the identification of its
target with the relative normalization, the inclusion of the quasi-finite locus followed by the
canonical morphism to the normalization. -/
private theorem comp_eq_isoOfRangeEq_comp :
    j ≫ ρ = (IsOpenImmersion.isoOfRangeEq j f.quasiFiniteLocus.ι
        (hj.trans (Scheme.Opens.range_ι _).symm)).hom ≫
      (f.quasiFiniteLocus.ι ≫ f.toNormalization) ≫ e.inv := by
  have hcalc : j ≫ ρ = ((IsOpenImmersion.isoOfRangeEq j f.quasiFiniteLocus.ι
      (hj.trans (Scheme.Opens.range_ι _).symm)).hom ≫ f.quasiFiniteLocus.ι) ≫
      (f.toNormalization ≫ e.inv) := by
    rw [IsOpenImmersion.isoOfRangeEq_hom_fac, (Iso.eq_comp_inv e).2 hρ]
  rw [hcalc]
  simp

/-- **Zariski's main theorem for schemes, the open immersion, in the form used on a chart.** -/
theorem isOpenImmersion_comp_of_range_eq_quasiFiniteLocus : IsOpenImmersion (j ≫ ρ) := by
  rw [comp_eq_isoOfRangeEq_comp f j hj ρ e hρ]
  infer_instance

/-- **Zariski's main theorem for schemes, the second clause, in the form used on a chart.** -/
theorem preimage_range_comp_eq_quasiFiniteLocus :
    ρ.base ⁻¹' Set.range (j ≫ ρ).base = (f.quasiFiniteLocus : Set X) := by
  rw [comp_eq_isoOfRangeEq_comp f j hj ρ e hρ,
    range_comp_base_of_surjective _ _ Surjective.surj, range_comp_base, (Iso.eq_comp_inv e).2 hρ,
    preimage_comp_base, Set.preimage_image_eq _ (Scheme.Hom.injective e.inv),
    preimage_range_quasiFiniteLocus_comp_toNormalization f]

end ChartComparison

end SchemeLevel

namespace Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

set_option synthInstance.maxHeartbeats 400000 in
/-- Pullbacks of presheaves on the big fppf site over `S` (instance search times out
without this shortcut). -/
private instance hasPullbacks_presheaf_normalizationQuasiFiniteLocus :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

private instance (priority := high) hasPullback_presheaf_normalizationQuasiFiniteLocus
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-- Over a cartesian square from a scheme chart, the quasi-finite locus of `f` pulls back to the
quasi-finite locus of the chart morphism of schemes. -/
theorem preimage_quasiFiniteLocusSubspace_eq_of_isPullback
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : X ⟶ Y}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hft : IsLocallyOfFiniteType B S hS f) {W XW : BigFppfOver B S hS}
    {w : yoneda.obj W ⟶ Y} {p : XW ⟶ W} {a : yoneda.obj XW ⟶ X}
    (hsq : IsPullback a (yoneda.map p) f w) :
    (quasiFiniteLocusSubspace B S hS f).preimage a =
      quasiFiniteLocusSubspace B S hS (yoneda.map p) := by
  have hcat : IsPullback
      (ObjectProperty.homMk a :
        (⟨yoneda.obj XW, isAlgebraicSpace_yoneda B S hS XW⟩ : AlgebraicSpaces B S hS) ⟶
          ⟨X, hX⟩)
      (ObjectProperty.homMk (yoneda.map p) :
        (⟨yoneda.obj XW, isAlgebraicSpace_yoneda B S hS XW⟩ : AlgebraicSpaces B S hS) ⟶
          ⟨yoneda.obj W, isAlgebraicSpace_yoneda B S hS W⟩)
      (ObjectProperty.homMk f : (⟨X, hX⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Y, hY⟩)
      (ObjectProperty.homMk w :
        (⟨yoneda.obj W, isAlgebraicSpace_yoneda B S hS W⟩ : AlgebraicSpaces B S hS) ⟶
          ⟨Y, hY⟩) :=
    IsPullback.of_map_of_faithful (F := ObjectProperty.ι _) hsq
  refine eq_of_range_pointsMap_ι_eq B S hS
    (isOpenSubspace_preimage B S hS a (quasiFiniteLocusSubspace B S hS f) hX
      (isAlgebraicSpace_yoneda B S hS XW) (isOpenSubspace_quasiFiniteLocusSubspace B S hS hX f))
    (isOpenSubspace_quasiFiniteLocusSubspace B S hS (isAlgebraicSpace_yoneda B S hS XW) _) ?_
  rw [pointsRange_preimage, range_pointsMap_quasiFiniteLocusSubspace,
    range_pointsMap_quasiFiniteLocusSubspace]
  exact (setOf_isQuasiFiniteAt_eq_preimage_of_isPullback B S hS hcat hft).symm

/-- A morphism of algebraic spaces is an open immersion as soon as its base change along one
surjective étale scheme chart of the target is. -/
theorem isOpenImmersion_of_isPullback_of_surjective_of_etale
    {F G P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    (hG : IsAlgebraicSpace B S hS G) {φ : F ⟶ G} {V : BigFppfOver B S hS}
    {b : yoneda.obj V ⟶ G}
    (hbs : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) b)
    (hbe : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) b)
    {g : P ⟶ F} {k : P ⟶ yoneda.obj V} (hpb : IsPullback g k φ b)
    (hk : IsOpenImmersion B S hS k) : IsOpenImmersion B S hS φ := by
  have hiso : Arrow.mk k ≅ Arrow.mk (pullback.snd φ b) :=
    Arrow.isoMk hpb.isoPullback (Iso.refl _) (by simp)
  refine ((isOpenImmersion_tfae_of_isAlgebraicSpace hF hG φ).out 4 1).1 ?_
  exact ⟨V, b, hbs, hbe, (MorphismProperty.arrow_mk_iso_iff _ hiso).1 hk⟩

/-- **Zariski's main theorem for schemes, on a chart.** Over a cartesian square from a scheme
chart, the pulled-back quasi-finite locus maps by an open immersion into the relative
normalization of the chart, and is the inverse image of its image. -/
theorem isOpenImmersion_and_preimage_range_eq_of_isPullback
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : X ⟶ Y}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hft : IsLocallyOfFiniteType B S hS f) {W XW W' : BigFppfOver B S hS}
    {w : yoneda.obj W ⟶ Y} {p : XW ⟶ W} {a : yoneda.obj XW ⟶ X}
    (hsq : IsPullback a (yoneda.map p) f w)
    [LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map p)]
    [_root_.AlgebraicGeometry.IsSeparated ((BigFppfOver.toScheme B S hS).map p)]
    [QuasiCompact ((BigFppfOver.toScheme B S hS).map p)]
    (r : XW ⟶ W') (e : (BigFppfOver.toScheme B S hS).obj W' ≅
      ((BigFppfOver.toScheme B S hS).map p).normalization)
    (hre : (BigFppfOver.toScheme B S hS).map r ≫ e.hom =
      ((BigFppfOver.toScheme B S hS).map p).toNormalization) :
    IsOpenImmersion B S hS (((quasiFiniteLocusSubspace B S hS f).preimage a).ι ≫ yoneda.map r) ∧
      (Subfunctor.range (((quasiFiniteLocusSubspace B S hS f).preimage a).ι ≫
        yoneda.map r)).preimage (yoneda.map r) =
        (quasiFiniteLocusSubspace B S hS f).preimage a := by
  obtain ⟨Vq, i, hiOI, hirange, -⟩ :=
    exists_restrict_bigFppfOver XW ((BigFppfOver.toScheme B S hS).map p).quasiFiniteLocus
  have hrangei : Subfunctor.range (yoneda.map i) =
      subspaceOfOpens B S hS XW ((BigFppfOver.toScheme B S hS).map p).quasiFiniteLocus :=
    range_yoneda_map_eq_subspaceOfOpens B S hS i hiOI _ hirange
  have hPeq : (quasiFiniteLocusSubspace B S hS f).preimage a =
      Subfunctor.range (yoneda.map i) := by
    rw [preimage_quasiFiniteLocusSubspace_eq_of_isPullback B S hS hX hY hft hsq,
      quasiFiniteLocusSubspace_yoneda_map, hrangei]
  have hoiS : _root_.AlgebraicGeometry.IsOpenImmersion
      ((BigFppfOver.toScheme B S hS).map (i ≫ r)) := by
    rw [Functor.map_comp]
    exact isOpenImmersion_comp_of_range_eq_quasiFiniteLocus _ _ hirange _ e hre
  have hmonoi : Mono (yoneda.map i) := mono_of_presheaf_isOpenImmersion
    ((presheaf_yoneda_map_iff B S hS inferInstance i).2 hiOI)
  have hcomp : (Subfunctor.range (yoneda.map i)).ι ≫ yoneda.map r =
      (rangeIsoOfMono B S hS (yoneda.map i)).inv ≫ yoneda.map (i ≫ r) := by
    rw [Functor.map_comp, ← Category.assoc, rangeIsoOfMono_inv_comp]
  have hOpens : (BigFppfOver.toScheme B S hS).map r ⁻¹ᵁ
      ((BigFppfOver.toScheme B S hS).map (i ≫ r)).opensRange =
      ((BigFppfOver.toScheme B S hS).map p).quasiFiniteLocus := by
    refine Opens.ext ?_
    rw [Scheme.Hom.coe_preimage, Scheme.Hom.coe_opensRange, Functor.map_comp]
    exact preimage_range_comp_eq_quasiFiniteLocus _ _ hirange _ e hre
  rw [hPeq, hcomp]
  refine ⟨MorphismProperty.RespectsIso.precomp _ _ _
    ((presheaf_yoneda_map_iff B S hS inferInstance (i ≫ r)).2 hoiS), ?_⟩
  have hepi : Epi (rangeIsoOfMono B S hS (yoneda.map i)).inv := IsIso.epi_of_iso _
  rw [Subfunctor.range_comp,
    Subfunctor.range_eq_top (p := (rangeIsoOfMono B S hS (yoneda.map i)).inv), Subfunctor.image_top,
    range_yoneda_map_eq_subspaceOfOpens B S hS (i ≫ r) hoiS _ (Scheme.Hom.coe_opensRange _).symm,
    subspaceOfOpens_preimage_yoneda_map, hOpens, hrangei]

/-- The restriction of a morphism of algebraic spaces to an open subspace is an open immersion
whose image has that subspace as inverse image, as soon as this holds after base change along one
surjective étale scheme chart of the target whose pullback to the source is surjective. -/
theorem isOpenImmersion_and_preimage_range_eq_of_isPullback_of_surjective_of_etale
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    (hG : IsAlgebraicSpace B S hS G) {g : F ⟶ G} {U : Subfunctor F}
    (hU : IsOpenSubspace B S hS U) {V XV : BigFppfOver B S hS}
    {a : yoneda.obj XV ⟶ F} {r : XV ⟶ V} {b : yoneda.obj V ⟶ G}
    (hsq : IsPullback a (yoneda.map r) g b)
    (has : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) a)
    (hbs : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) b)
    (hbe : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) b)
    (hoi : IsOpenImmersion B S hS ((U.preimage a).ι ≫ yoneda.map r))
    (hrange : (Subfunctor.range ((U.preimage a).ι ≫ yoneda.map r)).preimage (yoneda.map r) =
      U.preimage a) :
    IsOpenImmersion B S hS (U.ι ≫ g) ∧ (Subfunctor.range (U.ι ≫ g)).preimage g = U := by
  have hpaste : IsPullback (U.fromPreimage a) ((U.preimage a).ι ≫ yoneda.map r) (U.ι ≫ g) b :=
    (Subfunctor.isPullback_preimage a U).paste_vert hsq
  have hoi' : IsOpenImmersion B S hS (U.ι ≫ g) :=
    isOpenImmersion_of_isPullback_of_surjective_of_etale B S hS hU.1 hG hbs hbe hpaste hoi
  have hmono : Mono (U.ι ≫ g) := mono_of_presheaf_isOpenImmersion hoi'
  refine ⟨hoi', eq_of_preimage_eq_of_isSurjective B S hS a
    (isSurjective_of_presheafSurjective B S hS a has)
    (isOpenSubspace_preimage B S hS g (Subfunctor.range (U.ι ≫ g)) hG hF
      (isOpenSubspace_range_of_isAlgebraicSpace B S hS hU.1 _ hoi')) hU ?_⟩
  rw [← Subfunctor.preimage_comp, hsq.w, Subfunctor.preimage_comp,
    ← Subfunctor.range_eq_preimage_of_isPullback hpaste.flip, hrange]

/-! ### The normalization of one algebraic space in another, as data -/

/-- Data exhibiting an algebraic space over `S` as **the normalization of `Y` in `X`** for a
morphism `f : X ⟶ Y` of algebraic spaces over `S`, together with the canonical factorization
`X ⟶ Y' ⟶ Y` of `f`.

The defining property is the étale-chart description of Tag 0ABP: over an étale scheme chart
`w : W ⟶ Y` the fibre product `W ×_Y Y'` is representable and is the normalization of the scheme
`W` in the scheme `W ×_Y X`, compatibly with both legs of the triangle. -/
structure NormalizationInData {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y) where
  /-- The normalization `Y'`, as a presheaf on the big fppf site of `S`. -/
  space : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u
  /-- The normalization is an algebraic space over `S`. -/
  isAlgebraicSpace : IsAlgebraicSpace B S hS space
  /-- The canonical morphism `f' : X ⟶ Y'`. -/
  toNorm : X ⟶ space
  /-- The normalization morphism `ν : Y' ⟶ Y`. -/
  fromNorm : space ⟶ Y
  /-- The factorization `f = ν ∘ f'` of the source. -/
  fac : toNorm ≫ fromNorm = f
  /-- Over every étale scheme chart `w : W ⟶ Y` and every representation of `W ×_Y X` by a
  scheme `XW` of the site, the fibre product `W ×_Y Y'` is represented by a scheme `W'` of the
  site which is the relative normalization of `XW ⟶ W`, compatibly with both legs. -/
  chart : ∀ (W XW : BigFppfOver B S hS) (w : yoneda.obj W ⟶ Y) (p : XW ⟶ W)
      (a : yoneda.obj XW ⟶ X),
      (MorphismProperty.inverseImage
        (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf w →
      IsPullback a (yoneda.map p) f w →
      ∀ [QuasiCompact ((BigFppfOver.toScheme B S hS).map p)]
        [QuasiSeparated ((BigFppfOver.toScheme B S hS).map p)],
      ∃ (W' : BigFppfOver B S hS) (q : W' ⟶ W) (b : yoneda.obj W' ⟶ space) (r : XW ⟶ W')
        (e : (BigFppfOver.toScheme B S hS).obj W' ≅
          ((BigFppfOver.toScheme B S hS).map p).normalization),
        IsPullback b (yoneda.map q) fromNorm w ∧
        yoneda.map r ≫ b = a ≫ toNorm ∧
        (BigFppfOver.toScheme B S hS).map r ≫ e.hom =
          ((BigFppfOver.toScheme B S hS).map p).toNormalization ∧
        e.hom ≫ ((BigFppfOver.toScheme B S hS).map p).fromNormalization =
          (BigFppfOver.toScheme B S hS).map q

namespace NormalizationInData

variable {B S hS} {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : X ⟶ Y}

/-- The image in the normalization of `Y` in `X` of the quasi-finite locus of `f`. This is the
open subspace `U' ⊆ Y'` of Tag 0ABR. -/
def quasiFiniteImage (N : NormalizationInData B S hS f) : Subfunctor N.space :=
  Subfunctor.range ((quasiFiniteLocusSubspace B S hS f).ι ≫ N.toNorm)

/-- **The three assertions of Tag 0ABR**, proved at once so that the chart and the open subspace
are chosen once. -/
theorem quasiFiniteImage_spec (N : NormalizationInData B S hS f)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hrep : yoneda.relativelyRepresentable f)
    (hft : IsLocallyOfFiniteType B S hS f) (hqc : IsQuasiCompact B S hS f)
    (hsep : IsSeparated B S hS f) :
    IsOpenSubspace B S hS N.quasiFiniteImage ∧
      IsIso (N.quasiFiniteImage.fromPreimage N.toNorm) ∧
      N.quasiFiniteImage.preimage N.toNorm = quasiFiniteLocusSubspace B S hS f := by
  have hUopen : IsOpenSubspace B S hS (quasiFiniteLocusSubspace B S hS f) :=
    isOpenSubspace_quasiFiniteLocusSubspace B S hS hX f
  obtain ⟨W, w, hwsurj, hwet⟩ := hY.exists_atlas
  have hsq : IsPullback (hrep.fst w) (yoneda.map (hrep.snd w)) f w := hrep.isPullback w
  have hbcE := MorphismProperty.relative_isStableUnderBaseChange
    (MorphismProperty.inverseImage (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)) (F := yoneda)
  have hbcS := MorphismProperty.relative_isStableUnderBaseChange
    (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)) (F := yoneda)
  have haet := hbcE.of_isPullback hsq.flip hwet
  have hasurj := hbcS.of_isPullback hsq.flip hwsurj
  have hgft : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map (hrep.snd w)) :=
    hft _ _ (hrep.fst w) w (hrep.snd w) haet hwet hsq.w.symm
  have hgsep : _root_.AlgebraicGeometry.IsSeparated
      ((BigFppfOver.toScheme B S hS).map (hrep.snd w)) :=
    ((isSeparated_iff_presheaf B S hS f hX hY hrep).1 hsep).property w (hrep.fst w)
      (hrep.snd w) hsq
  have hgqc : QuasiCompact ((BigFppfOver.toScheme B S hS).map (hrep.snd w)) :=
    ((presheaf_quasiCompact_iff_isQuasiCompact B S hS hrep).2 hqc).property w (hrep.fst w)
      (hrep.snd w) hsq
  obtain ⟨W', q, b, r, e, hbq, hrb, hre, heq⟩ :=
    N.chart W (hrep.pullback w) w (hrep.snd w) (hrep.fst w) hwet hsq
  have hrq : r ≫ q = hrep.snd w := by
    apply (BigFppfOver.toScheme B S hS).map_injective
    rw [Functor.map_comp, ← heq, ← Category.assoc, hre,
      Scheme.Hom.toNormalization_fromNormalization]
  have hsq2 : IsPullback (hrep.fst w) (yoneda.map r) N.toNorm b := by
    refine IsPullback.of_bot ?_ hrb.symm hbq
    rw [← Functor.map_comp, hrq, N.fac]
    exact hsq
  obtain ⟨hoiPre, hrangePre⟩ :=
    isOpenImmersion_and_preimage_range_eq_of_isPullback B S hS hX hY hft hsq r e hre
  obtain ⟨hjoi, hpre⟩ := isOpenImmersion_and_preimage_range_eq_of_isPullback_of_surjective_of_etale
    B S hS hX N.isAlgebraicSpace hUopen hsq2 hasurj (hbcS.of_isPullback hbq.flip hwsurj)
    (hbcE.of_isPullback hbq.flip hwet) hoiPre hrangePre
  have hmonoj : Mono ((quasiFiniteLocusSubspace B S hS f).ι ≫ N.toNorm) :=
    mono_of_presheaf_isOpenImmersion hjoi
  have hU'open : IsOpenSubspace B S hS N.quasiFiniteImage :=
    isOpenSubspace_range_of_isAlgebraicSpace B S hS hUopen.1 _ hjoi
  exact ⟨hU'open, isIso_fromPreimage_range_of_preimage_eq B S hS N.toNorm
    (quasiFiniteLocusSubspace B S hS f) hpre, hpre⟩

/-- **Stacks 0ABR, the open subspace.** For a representable morphism of algebraic spaces over `S`
which is of finite type and separated, the image in the normalization of `Y` in `X` of the
quasi-finite locus of `f` is an open subspace of that normalization.

Over a surjective étale scheme chart `W ⟶ Y` the quasi-finite locus base changes to the
quasi-finite locus of the induced morphism of schemes (part (2) of Tag 0ABM), and Zariski's main
theorem for schemes — Tag 03GW, Mathlib's
`AlgebraicGeometry.Scheme.Hom.exists_isIso_morphismRestrict_toNormalization` — says that locus
maps by an open immersion into the relative normalization of the chart, which by the chart
description of the normalization datum is the base change of `ν`. So the restriction of `f'` to
the quasi-finite locus is an open immersion after base change along one surjective étale chart
of `Y'`, hence an open immersion, by Tag 03M4 for open immersions; its image is therefore an
open subspace. -/
@[stacks 0ABR "the open subspace"]
theorem isOpenSubspace_quasiFiniteImage (N : NormalizationInData B S hS f)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hrep : yoneda.relativelyRepresentable f)
    (hft : IsLocallyOfFiniteType B S hS f) (hqc : IsQuasiCompact B S hS f)
    (hsep : IsSeparated B S hS f) :
    IsOpenSubspace B S hS N.quasiFiniteImage :=
  (N.quasiFiniteImage_spec hX hY hrep hft hqc hsep).1

/-- **Stacks 0ABR, part (1).** The inverse image of the open subspace under `f'` maps
isomorphically onto it. -/
@[stacks 0ABR "part (1): the inverse image of the open subspace maps isomorphically onto it"]
theorem isIso_fromPreimage_quasiFiniteImage (N : NormalizationInData B S hS f)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hrep : yoneda.relativelyRepresentable f)
    (hft : IsLocallyOfFiniteType B S hS f) (hqc : IsQuasiCompact B S hS f)
    (hsep : IsSeparated B S hS f) :
    IsIso (N.quasiFiniteImage.fromPreimage N.toNorm) :=
  (N.quasiFiniteImage_spec hX hY hrep hft hqc hsep).2.1

/-- **Stacks 0ABR, part (2).** The inverse image of the open subspace under `f'` is the
quasi-finite locus of `f`, as a subspace of `X`. -/
@[stacks 0ABR "part (2): the inverse image is the quasi-finite locus, as a subspace"]
theorem preimage_quasiFiniteImage_eq (N : NormalizationInData B S hS f)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hrep : yoneda.relativelyRepresentable f)
    (hft : IsLocallyOfFiniteType B S hS f) (hqc : IsQuasiCompact B S hS f)
    (hsep : IsSeparated B S hS f) :
    N.quasiFiniteImage.preimage N.toNorm = quasiFiniteLocusSubspace B S hS f :=
  (N.quasiFiniteImage_spec hX hY hrep hft hqc hsep).2.2

/-- **Stacks 0ABR, part (2), on points.** The point set of the inverse image of the open subspace
under `f'` is the set of points of `X` at which `f` is quasi-finite. This is the form in which
the source states part (2). -/
@[stacks 0ABR "part (2): the inverse image is the set of points of quasi-finiteness"]
theorem range_pointsMap_preimage_quasiFiniteImage (N : NormalizationInData B S hS f)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hrep : yoneda.relativelyRepresentable f)
    (hft : IsLocallyOfFiniteType B S hS f) (hqc : IsQuasiCompact B S hS f)
    (hsep : IsSeparated B S hS f) :
    Set.range (pointsMap B S hS (N.quasiFiniteImage.preimage N.toNorm).toFunctor
        (N.quasiFiniteImage.preimage N.toNorm).ι) =
      {x : points B S hS X | IsQuasiFiniteAt B S hS f x} := by
  rw [N.preimage_quasiFiniteImage_eq hX hY hrep hft hqc hsep,
    range_pointsMap_quasiFiniteLocusSubspace]

end NormalizationInData

/-- **Stacks 0ABR.** Let `f : X ⟶ Y` be a morphism of algebraic spaces over `S` which is
representable, of finite type and separated, and let `X ⟶ Y' ⟶ Y` be the normalization of `Y`
in `X`. Then there is an open subspace `U' ⊆ Y'` such that `(f')⁻¹(U') ⟶ U'` is an isomorphism
and `(f')⁻¹(U') ⊆ X` is the set of points at which `f` is quasi-finite.

The open subspace is `AlgebraicGeometry.Space.NormalizationInData.quasiFiniteImage`, the image of
the quasi-finite locus. -/
@[stacks 0ABR "the existence statement"]
theorem exists_isOpenSubspace_isIso_fromPreimage_and_range_pointsMap_preimage_eq
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : X ⟶ Y} (N : NormalizationInData B S hS f)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hrep : yoneda.relativelyRepresentable f)
    (hft : IsLocallyOfFiniteType B S hS f) (hqc : IsQuasiCompact B S hS f)
    (hsep : IsSeparated B S hS f) :
    ∃ U' : Subfunctor N.space, IsOpenSubspace B S hS U' ∧
      IsIso (U'.fromPreimage N.toNorm) ∧
      Set.range (pointsMap B S hS (U'.preimage N.toNorm).toFunctor
          (U'.preimage N.toNorm).ι) =
        {x : points B S hS X | IsQuasiFiniteAt B S hS f x} :=
  ⟨N.quasiFiniteImage, N.isOpenSubspace_quasiFiniteImage hX hY hrep hft hqc hsep,
    N.isIso_fromPreimage_quasiFiniteImage hX hY hrep hft hqc hsep,
    N.range_pointsMap_preimage_quasiFiniteImage hX hY hrep hft hqc hsep⟩

end Space

end AlgebraicGeometry

end
