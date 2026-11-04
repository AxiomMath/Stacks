module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleOpenOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.EtalePermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Monomorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiAffineTfae

/-!
# The quasi-compact open image of a quasi-affine open subspace

Tag 03XW considers an étale morphism `T' ⟶ T` of affine schemes, a separated and locally
quasi-finite morphism `X ⟶ T` of algebraic spaces, and an open subspace `V' ⊆ T' ×_T X`
which is quasi-affine over `T'`; it asserts that the image `U` of `V'` in `X` is a
quasi-compact open subspace of `X` which is *representable*.

This file proves everything in that conclusion except representability, which is to say the
whole of the first paragraph of the source proof. There are two halves.

The first is about `V'` alone: it is a quasi-affine *scheme* over `T'`, and it is therefore a
quasi-compact algebraic space. Both come out of the definition of quasi-affineness for a
morphism of algebraic spaces, `AlgebraicGeometry.Space.IsQuasiAffineHom` (Tag 03WL), which
asks for representability of every base change along a morphism from an affine object of the
site: over an affine target the identity is such a morphism, so no descent is involved.

The second is about the image. It is carried out for an arbitrary étale morphism `g : Y ⟶ X`
of algebraic spaces and an arbitrary open subspace `V ⊆ Y`, since that is all the argument
uses: the point set of the image is open because `g` is open on points (Tag 03IR) and `V` has
open point set (Tag 03BZ), so it is the point set of an open subspace `U ⊆ X`, again by Tag
03BZ; and `U` is quasi-compact as soon as `V` is, because a quasi-compact atlas of `V`
composes with the factorisation `V ⟶ U` to a quasi-compact atlas of `U`. The source instead
gets quasi-compactness of `U` from quasi-compactness of `|U|` through Tag 03E4; that tag is
available, as `AlgebraicGeometry.Space.isQuasiCompactSpace_iff_compactSpace_points`
(`StacksFrontier/AlgebraicGeometry/Spaces/QuasiCompactTopology.lean:86`), but going through the
atlas needs neither it nor the identification of `|U|`.

## Main results

* `AlgebraicGeometry.Space.exists_isQuasiAffine_iso_of_isQuasiAffineHom`: a quasi-affine
  morphism of algebraic spaces over `S` whose target is represented by an affine object of
  the big fppf site has representable source, and the representing object has quasi-affine
  underlying scheme. In the situation of Tag 03XW this is the first sentence of the proof:
  `V'` is a scheme, by Tag 03WM.
* `AlgebraicGeometry.Space.isQuasiCompactSpace_of_isQuasiAffineHom`: such a source is a
  quasi-compact algebraic space over `S`. In the situation of Tag 03XW this is the second
  sentence of the proof: `V'` is quasi-compact, by Tag 01SL.
* `AlgebraicGeometry.Space.isRepresentable_of_isQuasiAffineHom_openSubspace` packages the
  two for an open subspace of a base change along a morphism of the site, which is the shape
  in which the proof of Tag 03XW uses them.
* `AlgebraicGeometry.Space.isOpen_range_pointsMap_ι_comp_of_isEtale`,
  `AlgebraicGeometry.Space.isOpenSubspace_openSubspaceOfPoints_range_comp_of_isEtale` and
  `AlgebraicGeometry.Space.isQuasiCompactSpace_openSubspaceOfPoints_range_comp_of_isEtale`:
  the image of an open subspace along an étale morphism of algebraic spaces is an open
  subspace of the target, and it is quasi-compact when the subspace is.
* `AlgebraicGeometry.Space.isOpenSubspace_isQuasiCompactSpace_image_of_isQuasiAffineHom` is
  those three in the situation of Tag 03XW: the image of `V'` in `X` is a quasi-compact open
  subspace of `X`.

## Implementation notes

Nothing here carries the tag 03XW, because the tag asserts in addition that the image is
representable, and that is what the remaining inputs are needed for.

* **The degree induction**, which is the whole obstruction. The argument is an induction on an
  integer bounding the degrees of the fibres of `T' ⟶ T`, using the decomposition
  `T' ×_T T' = Δ(T') ⨿ T^*` of an étale separated morphism of affines and the fact that
  `T^* ⟶ T'` has fibre degrees bounded by one less. Of its inputs the definition of a
  universally bounded morphism and the characterisation driving the bookkeeping are available
  — `AlgebraicGeometry.HasUniversallyBoundedFibers` (Tag 03J4) and Tag 03J5 — and so is the
  openness of the diagonal of an étale morphism of schemes (Tag 02GE,
  `StacksFrontier/AlgebraicGeometry/Morphisms/Unramified/Diagonal.lean`). Tags 03J7 and 025G are
  available too, and so is Tag 03GU, the factorisation of a quasi-finite morphism of affines
  through a finite morphism by an open immersion, proved as
  `AlgebraicGeometry.exists_isOpenImmersion_isFinite_factorization` in
  `StacksFrontier/AlgebraicGeometry/Morphisms/QuasiFinite/FiniteFactorization.lean` out of the
  commutative algebra of Tag 00QB
  (`StacksFrontier/RingTheory/ZariskisMainTheorem.lean`, three parts, the third producing the
  finite subalgebra). Tags 03JA and 03WU are available as well, as
  `AlgebraicGeometry.hasUniversallyBoundedFibers_of_locallyQuasiFinite_of_compactSpace` and
  `AlgebraicGeometry.etale_boundsFiberDegrees_tfae`, so the bookkeeping of the induction is
  done: `StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.EtaleDiagonalComplement`
  carries the two statements it runs on, namely that an étale morphism with quasi-compact
  source has a *natural number* bounding its fibre degrees
  (`AlgebraicGeometry.exists_nat_boundsFiberDegrees_of_etale_of_compactSpace`) and that
  restricting the second projection of `T' ×_T T'` to the complement of the diagonal drops
  that bound by one (`AlgebraicGeometry.boundsFiberDegrees_diagonalComplement`). What the
  induction still needs assembled is its geometric step: that
  `p₁(p₀⁻¹(V')) = V' ∪ p₁(p₀⁻¹(V') ∩ X^*)` is the base change `T' ×_T U` and is a scheme,
  the union of two schematic opens being schematic by Tag 03JH.
* **Effective descent of representability.** The proof concludes by descending the scheme
  `T' ×_T U` along the étale covering `{T' ⟶ W}`, where `W ⊆ T` is the open image of `T'`
  (Tags 02W5 and 0247). This input does exist in conditional form, as
  `AlgebraicGeometry.Space.IsEffectiveDescentAlongSurjectiveEtale`; the Zariski glueing
  (Tag 01JJ) used midway is not even conditional any more, being proved as
  `AlgebraicGeometry.hasZariskiGluing` in
  `StacksFrontier.AlgebraicGeometry.Spaces.ZariskiGluingCover`
  (`ZariskiGluingCover.lean:440`), and Tag 02LR — that a quasi-compact separated locally
  quasi-finite morphism to an affine scheme is quasi-affine, which is what makes the descent
  datum effective — is proved in
  `StacksFrontier/AlgebraicGeometry/Morphisms/Affine/QuasiAffineQuasiFinite.lean` as
  `AlgebraicGeometry.isSeparated_inf_quasiFinite_le_isQuasiAffineHom`.

  The *minimal* obligation here is Tag 02W8 rather than Tag 0247: the morphism to be descended,
  `T' ×_T U ⟶ T'`, is separated, locally quasi-finite and locally of finite type, so effective
  descent at that property suffices, and that is exactly the theorem
  `isEffectiveDescentAlongSurjectiveEtale_isSeparated_locallyQuasiFinite_locallyOfFiniteType`
  of `StacksFrontier.AlgebraicGeometry.Descent.StableOpenQuasiFiniteDescent`, in the namespace
  `AlgebraicGeometry.Space`.
  As the tree stands this is no weakening, because that theorem derives Tag 02W8 from Tag 0247
  and nothing else; so Tag 0247 is the one genuinely open input, and it is not reached by the
  unconditional effective descent already available — `IsAffineHom`
  (`AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_isAffineHom`) and
  `IsOpenImmersion`
  (`AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_isOpenImmersion`), neither of
  which contains the quasi-affine morphisms. Zariski-local reduction cannot replace it either:
  `AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_of_zariskiCover` asks for a
  Zariski covering of `U` by representable open subfunctors, which is what representability of
  `U` would provide.

## References

* [Stacks Project, Tag 03XW](https://stacks.math.columbia.edu/tag/03XW)
* [Stacks Project, Tag 03WL](https://stacks.math.columbia.edu/tag/03WL)
* [Stacks Project, Tag 03WM](https://stacks.math.columbia.edu/tag/03WM)
* [Stacks Project, Tag 01SL](https://stacks.math.columbia.edu/tag/01SL)
* [Stacks Project, Tag 03IR](https://stacks.math.columbia.edu/tag/03IR)
* [Stacks Project, Tag 03BZ](https://stacks.math.columbia.edu/tag/03BZ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### The subspace quasi-affine over the affine base -/

/-- A property of scheme morphisms containing identities and respecting isomorphisms, pulled
back along the underlying-scheme functor of the big fppf category over `S`, still does.

Typeclass inference does not unify a goal about such an inverse image with the conclusions of
`CategoryTheory.MorphismProperty.ContainsIdentities.inverseImage` and
`CategoryTheory.MorphismProperty.RespectsIso.inverseImage`, so the two terms are named
here. -/
private theorem inverseImage_containsIdentities_and_respectsIso
    (P : MorphismProperty Scheme.{u}) (_ : P.ContainsIdentities) (_ : P.RespectsIso) :
    MorphismProperty.ContainsIdentities
        (P.inverseImage (BigFppfOver.toScheme B S hS)) ∧
      MorphismProperty.RespectsIso (P.inverseImage (BigFppfOver.toScheme B S hS)) :=
  ⟨MorphismProperty.ContainsIdentities.inverseImage (BigFppfOver.toScheme B S hS),
    MorphismProperty.RespectsIso.inverseImage _ (BigFppfOver.toScheme B S hS)⟩

/-- A quasi-affine morphism of algebraic spaces over `S` whose target is represented by an
affine object of the big fppf site has representable source, represented by an object of the
site whose underlying scheme is quasi-affine.

Only the base change along the identity of the target is used, so this needs no descent. In
the situation of Stacks 03XW it says that the open subspace `V' ⊆ T' ×_T X`, being
quasi-affine over the affine scheme `T'`, is a quasi-affine scheme. -/
theorem exists_isQuasiAffine_iso_of_isQuasiAffineHom
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {Z : BigFppfOver B S hS}
    (hZ : IsAffine ((BigFppfOver.toScheme B S hS).obj Z)) {f : F ⟶ yoneda.obj Z}
    (hf : IsQuasiAffineHom B S hS f) :
    ∃ W : BigFppfOver B S hS,
      Scheme.IsQuasiAffine ((BigFppfOver.toScheme B S hS).obj W) ∧
        Nonempty (yoneda.obj W ≅ F) := by
  obtain ⟨W, hW, ⟨e⟩⟩ := hf ⟨Z, hZ⟩ (𝟙 (yoneda.obj Z))
  exact ⟨W, hW, ⟨e.trans (IsPullback.of_id_snd (f := f)).isoPullback.symm⟩⟩

/-- A quasi-affine morphism of algebraic spaces over `S` whose target is represented by an
affine object of the big fppf site has quasi-compact source.

This is Stacks 01SL — a scheme quasi-affine over an affine scheme is quasi-compact — read
through `AlgebraicGeometry.Space.IsQuasiCompactSpace`: the isomorphism of
`AlgebraicGeometry.Space.exists_isQuasiAffine_iso_of_isQuasiAffineHom` is itself the
required surjective étale chart, and the representing object is compact because it is
quasi-affine. -/
theorem isQuasiCompactSpace_of_isQuasiAffineHom
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {Z : BigFppfOver B S hS}
    (hZ : IsAffine ((BigFppfOver.toScheme B S hS).obj Z)) {f : F ⟶ yoneda.obj Z}
    (hf : IsQuasiAffineHom B S hS f) :
    IsQuasiCompactSpace B S hS F := by
  obtain ⟨W, hW, ⟨e⟩⟩ := exists_isQuasiAffine_iso_of_isQuasiAffineHom hZ hf
  obtain ⟨hs₁, hs₂⟩ := inverseImage_containsIdentities_and_respectsIso (B := B) (S := S)
    (hS := hS) (@AlgebraicGeometry.Surjective.{u})
    MorphismProperty.IsMultiplicative.toContainsIdentities inferInstance
  obtain ⟨he₁, he₂⟩ := inverseImage_containsIdentities_and_respectsIso (B := B) (S := S)
    (hS := hS) (@AlgebraicGeometry.Etale.{u})
    MorphismProperty.IsMultiplicative.toContainsIdentities inferInstance
  exact ⟨W, e.hom, hW.toCompactSpace, MorphismProperty.presheaf_of_isIso _ e.hom,
    isEtale_of_presheaf_etale B S hS (MorphismProperty.presheaf_of_isIso _ e.hom)⟩

/-- In the situation of Stacks 03XW: an open subspace of a base change `T' ×_T X` which is
quasi-affine over an affine object `T'` of the big fppf site is a quasi-compact scheme.

This is the content of the first paragraph of the proof of Stacks 03XW which concerns the
subspace itself; the image of the subspace in `X` is not addressed here. -/
theorem isRepresentable_of_isQuasiAffineHom_openSubspace
    {T' T : BigFppfOver B S hS} (hT' : IsAffine ((BigFppfOver.toScheme B S hS).obj T'))
    (t : T' ⟶ T) {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ yoneda.obj T)
    (V : Subfunctor (pullback (yoneda.map t) f))
    (hVqa : IsQuasiAffineHom B S hS (V.ι ≫ pullback.fst (yoneda.map t) f)) :
    V.toFunctor.IsRepresentable ∧ IsQuasiCompactSpace B S hS V.toFunctor := by
  obtain ⟨W, -, ⟨e⟩⟩ := exists_isQuasiAffine_iso_of_isQuasiAffineHom hT' hVqa
  exact ⟨Functor.IsRepresentable.mk' e,
    isQuasiCompactSpace_of_isQuasiAffineHom hT' hVqa⟩

/-! ### Étaleness of an inclusion and of a represented base change -/

/-- A morphism of presheaves on the big fppf category over `S` which is étale after every
represented base change is étale in the sense of `AlgebraicGeometry.Space.IsEtale`: compose
with the given étale chart of its source.

This is `AlgebraicGeometry.Space.isEtale_of_presheaf_etale` with the hypothesis that the
source be representable removed. That hypothesis is never used — the proof is the same
single application of multiplicativity — but the morphisms whose étaleness is needed below
are the inclusion of an open subspace and a base change, neither of which has representable
source. -/
private theorem isEtale_of_presheaf_etale_source
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : F ⟶ G}
    (hf : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf f) :
    IsEtale B S hS f := by
  have := isMultiplicative_presheaf_etale B S hS
  exact fun _ φ hφ ↦ MorphismProperty.comp_mem _ φ f hφ hf

/-- The inclusion of an open subspace of an algebraic space over `S` is étale, an open
immersion of schemes being étale. -/
theorem isEtale_ι_of_isOpenSubspace {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {V : Subfunctor F}
    (hV : IsOpenSubspace B S hS V) : IsEtale B S hS V.ι :=
  isEtale_of_presheaf_etale_source (presheaf_etale_of_isOpenImmersion B S hS hV.2)

/-- The projection to `X` of a base change `T' ×_T X` along a morphism `t : T' ⟶ T` of the
big fppf category over `S` whose underlying morphism of schemes is étale is étale.

In the situation of Stacks 03XW this is the morphism `T' ×_T X ⟶ X` of the diagram, and the
statement is Tag 03FU for the special case of a represented base, where no atlas of the base
is needed: the represented morphism `yoneda.map t` is étale after every represented base
change by `AlgebraicGeometry.BigFppfOver.presheaf_inverseImage_yoneda_map_iff`, and that
condition is stable under base change. -/
theorem isEtale_pullback_snd_yoneda_map
    {T' T : BigFppfOver B S hS} {t : T' ⟶ T}
    (ht : AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map t))
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ yoneda.obj T) :
    IsEtale B S hS (pullback.snd (yoneda.map t) f) :=
  isEtale_of_presheaf_etale_source (presheaf_of_isPullback B S hS
    (IsPullback.of_hasPullback (yoneda.map t) f)
    ((BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ t).2 ht))

/-! ### The image of an open subspace along an étale morphism -/

variable {Y X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- A morphism of presheaves on the big fppf category over `S` factors through the subspace
cut out by the image of its points.

The sections of `AlgebraicGeometry.Space.openSubspaceOfPoints` over an object of the site are
the sections all of whose points lie in the given set, and a section in the range of `h` has
all its points in the range of the points of `h`. -/
theorem range_le_openSubspaceOfPoints_range_pointsMap
    {A F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (h : A ⟶ F) :
    Subfunctor.range h ≤ openSubspaceOfPoints B S hS F
      (Set.range (pointsMap B S hS A h)) := by
  intro T x hx
  obtain ⟨a, rfl⟩ := hx
  rw [mem_openSubspaceOfPoints_iff]
  have he : yonedaEquiv.symm (h.app T a) = yonedaEquiv.symm a ≫ h := by
    apply yonedaEquiv.injective
    rw [Equiv.apply_symm_apply, yonedaEquiv_comp, Equiv.apply_symm_apply]
  rw [he, pointsMap_comp]
  exact Set.range_comp_subset_range _ _

/-- The image in `|X|` of the point set of an open subspace `V ⊆ Y` under an étale morphism
`g : Y ⟶ X` of algebraic spaces over `S` is open.

This is the first assertion of the first paragraph of the proof of Stacks 03XW: the point set
of `V` is open by Tag 03BZ, and `|g|` is an open map by Tag 03IR. -/
theorem isOpen_range_pointsMap_ι_comp_of_isEtale
    (hY : IsAlgebraicSpace B S hS Y) (hX : IsAlgebraicSpace B S hS X) {g : Y ⟶ X}
    (hg : IsEtale B S hS g) {V : Subfunctor Y} (hV : IsOpenSubspace B S hS V) :
    IsOpen (Set.range (pointsMap B S hS V.toFunctor (V.ι ≫ g))) := by
  rw [pointsMap_comp, Set.range_comp]
  exact isOpenMap_pointsMap_of_isEtale B S hS g hY hX hg _
    (isOpen_range_pointsMap_of_isOpenImmersion B S hS V.ι hV.2)

/-- The image of an open subspace `V ⊆ Y` under an étale morphism `g : Y ⟶ X` of algebraic
spaces over `S` is an open subspace of `X`.

The image is taken as the subspace cut out by the image of the point set of `V`, which has
that image as its own point set by Tag 03BZ
(`AlgebraicGeometry.Space.range_pointsMap_ι_openSubspaceOfPoints`). -/
theorem isOpenSubspace_openSubspaceOfPoints_range_comp_of_isEtale
    (hY : IsAlgebraicSpace B S hS Y) (hX : IsAlgebraicSpace B S hS X) {g : Y ⟶ X}
    (hg : IsEtale B S hS g) {V : Subfunctor Y} (hV : IsOpenSubspace B S hS V) :
    IsOpenSubspace B S hS (openSubspaceOfPoints B S hS X
      (Set.range (pointsMap B S hS V.toFunctor (V.ι ≫ g)))) :=
  isOpenSubspace_openSubspaceOfPoints B S hS hX _
    (isOpen_range_pointsMap_ι_comp_of_isEtale hY hX hg hV)

/-- The image of a quasi-compact open subspace `V ⊆ Y` under an étale morphism `g : Y ⟶ X` of
algebraic spaces over `S` is a quasi-compact algebraic space.

`V` factors through its image `U` by `AlgebraicGeometry.Space.Subfunctor.lift`, and that
factorisation is étale by Tag 03FV, both `V ⟶ X` and `U ⟶ X` being étale. So a quasi-compact
surjective étale atlas of `V` composes with it to an étale chart of `U` from a quasi-compact
scheme, and that chart is surjective on points because the point set of `U` is by construction
the image of the point set of `V` and the inclusion of `U` is injective on points. Tag 03H5
turns surjectivity on points back into the relatively representable surjectivity which
`AlgebraicGeometry.Space.IsQuasiCompactSpace` asks for.

The source argument instead observes that `|U|` is a continuous image of the quasi-compact
`|V'|` and invokes Tag 03E4 to descend quasi-compactness of the point space to the algebraic
space. That tag *is* available, as
`AlgebraicGeometry.Space.isQuasiCompactSpace_iff_compactSpace_points`, but going through the
atlas needs neither it nor the identification of `|U|`, so the atlas is produced here
directly. -/
theorem isQuasiCompactSpace_openSubspaceOfPoints_range_comp_of_isEtale
    (hY : IsAlgebraicSpace B S hS Y) (hX : IsAlgebraicSpace B S hS X) {g : Y ⟶ X}
    (hg : IsEtale B S hS g) {V : Subfunctor Y} (hV : IsOpenSubspace B S hS V)
    (hVqc : IsQuasiCompactSpace B S hS V.toFunctor) :
    IsQuasiCompactSpace B S hS (openSubspaceOfPoints B S hS X
      (Set.range (pointsMap B S hS V.toFunctor (V.ι ≫ g)))).toFunctor := by
  have := isMultiplicative_presheaf_etale B S hS
  set U := openSubspaceOfPoints B S hS X
    (Set.range (pointsMap B S hS V.toFunctor (V.ι ≫ g)))
  have hU : IsOpenSubspace B S hS U :=
    isOpenSubspace_openSubspaceOfPoints_range_comp_of_isEtale hY hX hg hV
  set j := Subfunctor.lift (V.ι ≫ g) (range_le_openSubspaceOfPoints_range_pointsMap (V.ι ≫ g))
  have hj : j ≫ U.ι = V.ι ≫ g := Subfunctor.lift_ι _ _
  have hjEt : IsEtale B S hS j :=
    isEtale_of_isEtale_over B S hS hV.1 hU.1 hX j (V.ι ≫ g) U.ι
      (isEtale_comp B S hS (isEtale_ι_of_isOpenSubspace hV) hg)
      (isEtale_ι_of_isOpenSubspace hU) hj
  obtain ⟨W, a, hWc, hasurj, haet⟩ := hVqc
  refine ⟨W, a ≫ j, hWc, ?_, isEtale_comp B S hS haet hjEt⟩
  refine (presheafSurjective_iff_isSurjective_yoneda B S hS U.toFunctor hU.1 W (a ≫ j)).2 ?_
  have hιinj : Function.Injective (pointsMap B S hS U.toFunctor U.ι) :=
    pointsMap_injective_of_mono B S hS U.ι
  intro y
  have hmem : pointsMap B S hS U.toFunctor U.ι y ∈
      Set.range (pointsMap B S hS V.toFunctor (V.ι ≫ g)) := by
    rw [← range_pointsMap_ι_openSubspaceOfPoints B S hS
      (Set.range (pointsMap B S hS V.toFunctor (V.ι ≫ g)))]
    exact ⟨y, rfl⟩
  obtain ⟨v, hv⟩ := hmem
  obtain ⟨w, hw⟩ := isSurjective_of_presheafSurjective B S hS a hasurj v
  refine ⟨w, hιinj ?_⟩
  rwa [← pointsMap_comp_apply, Category.assoc, hj, pointsMap_comp_apply, hw]

/-- **The conclusion of Stacks 03XW except representability.** In the situation of that tag —
`t : T' ⟶ T` with étale underlying morphism of schemes, `f : X ⟶ T` a morphism of algebraic
spaces over `S`, `V'` an open subspace of `T' ×_T X` which is quasi-affine over the affine
`T'` — the image of `V'` in `X` is a quasi-compact open subspace of `X`.

The image is the subspace cut out by the image of the point set of `V'`, whose own point set
is that image by Tag 03BZ. The tag asserts in addition that this subspace is representable,
which is not proved: that is the part of the source proof which runs the induction on the
degrees of the fibres of `T' ⟶ T`.

Separatedness and local quasi-finiteness of `f`, and affineness of `T`, are hypotheses of the
tag which this part of its conclusion does not need; they are omitted. -/
theorem isOpenSubspace_isQuasiCompactSpace_image_of_isQuasiAffineHom
    {T' T : BigFppfOver B S hS} (hT' : IsAffine ((BigFppfOver.toScheme B S hS).obj T'))
    {t : T' ⟶ T} (ht : AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map t))
    (hX : IsAlgebraicSpace B S hS X) (f : X ⟶ yoneda.obj T)
    (V : Subfunctor (pullback (yoneda.map t) f))
    (hV : IsOpenSubspace B S hS V)
    (hVqa : IsQuasiAffineHom B S hS (V.ι ≫ pullback.fst (yoneda.map t) f)) :
    IsOpenSubspace B S hS (openSubspaceOfPoints B S hS X
        (Set.range (pointsMap B S hS V.toFunctor
          (V.ι ≫ pullback.snd (yoneda.map t) f)))) ∧
      IsQuasiCompactSpace B S hS (openSubspaceOfPoints B S hS X
        (Set.range (pointsMap B S hS V.toFunctor
          (V.ι ≫ pullback.snd (yoneda.map t) f)))).toFunctor :=
  have hP : IsAlgebraicSpace B S hS (pullback (yoneda.map t) f) :=
    isAlgebraicSpace_pullback B S hS (yoneda.map t) f (isAlgebraicSpace_yoneda B S hS T')
      hX (isAlgebraicSpace_yoneda B S hS T)
  have hg : IsEtale B S hS (pullback.snd (yoneda.map t) f) :=
    isEtale_pullback_snd_yoneda_map ht f
  ⟨isOpenSubspace_openSubspaceOfPoints_range_comp_of_isEtale hP hX hg hV,
    isQuasiCompactSpace_openSubspaceOfPoints_range_comp_of_isEtale hP hX hg hV
      (isQuasiCompactSpace_of_isQuasiAffineHom hT' hVqa)⟩

end AlgebraicGeometry.Space

end
