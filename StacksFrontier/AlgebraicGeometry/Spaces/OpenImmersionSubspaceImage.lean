module

public import StacksFrontier.AlgebraicGeometry.Spaces.OpenImmersionCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceImage

/-!
# The image of an open subspace along an open immersion

The image of an open subspace `V ⊆ Y` along an *étale* morphism `g : Y ⟶ X` of algebraic spaces
over `S` is an open subspace of `X`, by
`AlgebraicGeometry.Space.isOpenSubspace_openSubspaceOfPoints_range_comp_of_isEtale`, but the
factorisation `V ⟶ g(V)` is in general far from an isomorphism. When `g` is an *open immersion* it
is one: the factorisation is then an open immersion whose map on points is surjective by
construction, and an open immersion surjective on points is an isomorphism.

In particular the image is representable as soon as `V` is, with no descent involved. That is the
base case of the induction in the proof of Stacks 03XW. There the induction runs on a bound `n` for
the degrees of the fibres of an étale morphism `t : T' ⟶ T` of affine schemes, and for `n = 1` the
source invokes Stacks 025G to see that `t` is an open immersion — whereupon `T' ×_T X ⟶ X` is an
open immersion as well, by base change, and "the result is clear".

## Main definitions

There are no new definitions.

## Main results

* `AlgebraicGeometry.Space.isMultiplicative_presheaf_isOpenImmersion`: open immersions of schemes,
  tested after every represented base change, contain the identities and are stable under
  composition.
* `AlgebraicGeometry.Space.isOpenImmersion_pullback_snd_yoneda_map`: the projection to `X` of a
  base change `T' ×_T X` along a morphism of the site whose underlying morphism of schemes is an
  open immersion is an open immersion. This is the open-immersion analogue of
  `AlgebraicGeometry.Space.isEtale_pullback_snd_yoneda_map`.
* `AlgebraicGeometry.Space.isIso_lift_range_pointsMap_of_isOpenImmersion`: for an open immersion
  `g : Y ⟶ X` and an open subspace `V ⊆ Y`, the factorisation of `V.ι ≫ g` through the subspace of
  `X` cut out by the image of the points of `V` is an isomorphism.
* `AlgebraicGeometry.Space.isRepresentable_openSubspaceOfPoints_range_comp_of_isOpenImmersion`:
  that image is therefore representable as soon as `V` is.
* `isOpenSubspace_isQuasiCompactSpace_isRepresentable_image_of_isOpenImmersion`, in the namespace
  `AlgebraicGeometry.Space`: **the base case of Stacks 03XW.** For `t : T' ⟶ T` an open immersion
  of objects of the site with `T'` affine, and `V'` an open subspace of `T' ×_T X` quasi-affine
  over `T'`, the image of `V'` in `X` is a quasi-compact open subspace of `X` which is
  representable — all three assertions of the tag.

## Implementation notes

Openness of the factorisation is `CategoryTheory.MorphismProperty.presheaf_of_comp_mono`: its
composite with the inclusion of the image is `V.ι ≫ g`, a composite of open immersions, and the
inclusion of a subfunctor is a monomorphism. Surjectivity on points is immediate from
`AlgebraicGeometry.Space.range_pointsMap_ι_openSubspaceOfPoints`, the points of the image being by
definition the image of the points of `V`, together with injectivity of the points of a
monomorphism; it is turned into the relatively representable form by Stacks 03MD. The two are then
fed to `AlgebraicGeometry.Space.isIso_of_presheaf_isOpenImmersion_of_presheafSurjective`.

No étaleness hypothesis is needed anywhere: an open immersion is étale, but the openness of the
point set used by the étale route is here subsumed by the isomorphism.

The base case carries no Stacks tag. It is the conclusion of Stacks 03XW under a hypothesis on `t`
which the tag does not make — `t` is only assumed étale there, the open-immersion case being the
start of an induction — so tagging it would weaken the statement.

## References

* [Stacks Project, Tag 03XW](https://stacks.math.columbia.edu/tag/03XW)
* [Stacks Project, Tag 025G](https://stacks.math.columbia.edu/tag/025G)
* [Stacks Project, Tag 03MD](https://stacks.math.columbia.edu/tag/03MD)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Open immersions of schemes, tested after every represented base change, contain the
identities and are stable under composition. -/
theorem isMultiplicative_presheaf_isOpenImmersion :
    MorphismProperty.IsMultiplicative
      ((MorphismProperty.inverseImage
        (@_root_.AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf) := by
  exact MorphismProperty.relative_isMultiplicative _

/-- The projection to `X` of a base change `T' ×_T X` along a morphism `t : T' ⟶ T` of the big
fppf category over `S` whose underlying morphism of schemes is an open immersion is an open
immersion.

This is the open-immersion analogue of
`AlgebraicGeometry.Space.isEtale_pullback_snd_yoneda_map`, and the same proof: the represented
morphism `yoneda.map t` is an open immersion after every represented base change by
`AlgebraicGeometry.BigFppfOver.presheaf_inverseImage_yoneda_map_iff`, and that condition is stable
under base change. -/
theorem isOpenImmersion_pullback_snd_yoneda_map
    {T' T : BigFppfOver B S hS} {t : T' ⟶ T}
    (ht : _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map t))
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ yoneda.obj T) :
    IsOpenImmersion B S hS (pullback.snd (yoneda.map t) f) :=
  presheaf_of_isPullback B S hS (IsPullback.of_hasPullback (yoneda.map t) f)
    ((BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ t).2 ht)

variable {Y X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **The image of an open subspace along an open immersion is a copy of the subspace.** For an
open immersion `g : Y ⟶ X` of algebraic spaces over `S` and an open subspace `V ⊆ Y`, the
factorisation of `V.ι ≫ g` through the subspace of `X` cut out by the image of the point set of
`V` is an isomorphism.

The factorisation is an open immersion because its composite with the inclusion of the image is
the composite of the two open immersions `V.ι` and `g`, and that inclusion is a monomorphism
(`CategoryTheory.MorphismProperty.presheaf_of_comp_mono`). It is surjective on points because the
points of the image are by definition the image of the points of `V`, and an open immersion
surjective on points is an isomorphism. -/
theorem isIso_lift_range_pointsMap_of_isOpenImmersion
    {g : Y ⟶ X} (hg : IsOpenImmersion B S hS g)
    {V : Subfunctor Y} (hV : IsOpenSubspace B S hS V) :
    IsIso (Subfunctor.lift (V.ι ≫ g)
      (range_le_openSubspaceOfPoints_range_pointsMap (V.ι ≫ g))) := by
  have hmul := isMultiplicative_presheaf_isOpenImmersion B S hS
  set U := openSubspaceOfPoints B S hS X
    (Set.range (pointsMap B S hS V.toFunctor (V.ι ≫ g))) with hUdef
  set j := Subfunctor.lift (V.ι ≫ g)
    (range_le_openSubspaceOfPoints_range_pointsMap (V.ι ≫ g)) with hjdef
  have hj : j ≫ U.ι = V.ι ≫ g := Subfunctor.lift_ι _ _
  have hVg : IsOpenImmersion B S hS (V.ι ≫ g) :=
    MorphismProperty.comp_mem _ V.ι g hV.2 hg
  have hjoi : IsOpenImmersion B S hS j :=
    MorphismProperty.presheaf_of_comp_mono _ (f := j) (m := U.ι) (hj ▸ hVg)
  have hιinj : Function.Injective (pointsMap B S hS U.toFunctor U.ι) :=
    pointsMap_injective_of_mono B S hS U.ι
  have hsurj : IsSurjective B S hS j := by
    intro y
    have hmem : pointsMap B S hS U.toFunctor U.ι y ∈
        Set.range (pointsMap B S hS V.toFunctor (V.ι ≫ g)) := by
      rw [← range_pointsMap_ι_openSubspaceOfPoints B S hS
        (Set.range (pointsMap B S hS V.toFunctor (V.ι ≫ g)))]
      exact ⟨y, rfl⟩
    obtain ⟨v, hv⟩ := hmem
    refine ⟨v, hιinj ?_⟩
    rw [← pointsMap_comp_apply, hj]
    exact hv
  exact isIso_of_presheaf_isOpenImmersion_of_presheafSurjective B S hS j hjoi
    (presheafSurjective_of_isSurjective B S hS j hjoi.rep hsurj)

/-- The image of a representable open subspace along an open immersion of algebraic spaces over
`S` is representable, being isomorphic to the subspace by
`AlgebraicGeometry.Space.isIso_lift_range_pointsMap_of_isOpenImmersion`. -/
theorem isRepresentable_openSubspaceOfPoints_range_comp_of_isOpenImmersion
    {g : Y ⟶ X} (hg : IsOpenImmersion B S hS g)
    {V : Subfunctor Y} (hV : IsOpenSubspace B S hS V)
    (hVrep : V.toFunctor.IsRepresentable) :
    (openSubspaceOfPoints B S hS X
      (Set.range (pointsMap B S hS V.toFunctor (V.ι ≫ g)))).toFunctor.IsRepresentable :=
  have _ := hVrep
  have _ := isIso_lift_range_pointsMap_of_isOpenImmersion B S hS hg hV
  isRepresentable_of_natIso V.toFunctor
    (asIso (Subfunctor.lift (V.ι ≫ g)
      (range_le_openSubspaceOfPoints_range_pointsMap (V.ι ≫ g))))

/-- **The base case of Stacks 03XW.** In the situation of that tag, with the étale morphism
`t : T' ⟶ T` assumed moreover to be an *open immersion* — which is what Stacks 025G gives when the
degrees of its fibres are bounded by `1` — the image `U` of `V'` in `X` is a quasi-compact open
subspace of `X` which is representable. All three assertions of the tag are delivered.

Openness and quasi-compactness are
`AlgebraicGeometry.Space.isOpenSubspace_isQuasiCompactSpace_image_of_isQuasiAffineHom`, which needs
only étaleness of `t`. Representability is
`AlgebraicGeometry.Space.isRepresentable_openSubspaceOfPoints_range_comp_of_isOpenImmersion`
applied to the open immersion `T' ×_T X ⟶ X`, the subspace `V'` being representable because it is
quasi-affine over the affine `T'`
(`AlgebraicGeometry.Space.isRepresentable_of_isQuasiAffineHom_openSubspace`). -/
theorem isOpenSubspace_isQuasiCompactSpace_isRepresentable_image_of_isOpenImmersion
    {T' T : BigFppfOver B S hS} (hT' : IsAffine ((BigFppfOver.toScheme B S hS).obj T'))
    {t : T' ⟶ T}
    (ht : _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map t))
    (hX : IsAlgebraicSpace B S hS X) (f : X ⟶ yoneda.obj T)
    (V : Subfunctor (pullback (yoneda.map t) f))
    (hV : IsOpenSubspace B S hS V)
    (hVqa : IsQuasiAffineHom B S hS (V.ι ≫ pullback.fst (yoneda.map t) f)) :
    IsOpenSubspace B S hS (openSubspaceOfPoints B S hS X
        (Set.range (pointsMap B S hS V.toFunctor
          (V.ι ≫ pullback.snd (yoneda.map t) f)))) ∧
      IsQuasiCompactSpace B S hS (openSubspaceOfPoints B S hS X
        (Set.range (pointsMap B S hS V.toFunctor
          (V.ι ≫ pullback.snd (yoneda.map t) f)))).toFunctor ∧
      (openSubspaceOfPoints B S hS X
        (Set.range (pointsMap B S hS V.toFunctor
          (V.ι ≫ pullback.snd (yoneda.map t) f)))).toFunctor.IsRepresentable :=
  have hetale : AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map t) :=
    have _ := ht
    inferInstance
  have hqc := isOpenSubspace_isQuasiCompactSpace_image_of_isQuasiAffineHom hT' hetale hX f
    V hV hVqa
  ⟨hqc.1, hqc.2,
    isRepresentable_openSubspaceOfPoints_range_comp_of_isOpenImmersion B S hS
      (isOpenImmersion_pullback_snd_yoneda_map B S hS ht f) hV
      (isRepresentable_of_isQuasiAffineHom_openSubspace hT' t f V hVqa).1⟩

end AlgebraicGeometry.Space

end
