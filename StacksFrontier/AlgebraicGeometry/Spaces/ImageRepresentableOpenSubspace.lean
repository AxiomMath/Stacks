module

public import StacksFrontier.AlgebraicGeometry.Spaces.DenseSchematicLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.ImageRepresentableInduction

/-!
# Stacks 03XW for an arbitrary open subspace cut out by the image

Stacks 03XW considers an étale morphism `t : T' ⟶ T` of affine schemes, a separated and locally
quasi-finite morphism `f : X ⟶ T` of algebraic spaces over `S` and an open subspace
`V' ⊆ T' ×_T X` which is quasi-affine over `T'`, and asserts that the image `U` of `V'` in `X`
is a quasi-compact open subspace of `X` which is representable. That tag is proved in
`StacksFrontier.AlgebraicGeometry.Spaces.ImageRepresentableInduction`, where the image is the
canonical open subspace `AlgebraicGeometry.Space.openSubspaceOfPoints` cut out by the image of
the point set of `V'`.

This file restates representability for *any* open subspace `U ⊆ X` whose point set is that
image. That is the form in which the consumers of the tag use it: they produce an open subspace
of `X` by some other route — typically as a union, or as the open subspace underlying an
already-constructed scheme — and know only that its point set is the image of the point set of
`V'`. The two forms are equivalent because part (1) of Tag 03BZ makes an open subspace of an
algebraic space determined by its point set.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.Space.isRepresentable_openSubspace_image`: an open subspace of `X` whose
  point set is the image of the point set of `V'` is representable.

## Implementation notes

The point set of `V'` is open, being the point set of the open subspace `U`
(`AlgebraicGeometry.Space.isOpen_range_pointsMap_of_isOpenImmersion`), so it does cut out an
open subspace (`AlgebraicGeometry.Space.isOpenSubspace_openSubspaceOfPoints`) whose own point
set it is (`AlgebraicGeometry.Space.range_pointsMap_ι_openSubspaceOfPoints`). Hence `U` equals
that canonical one by `AlgebraicGeometry.Space.eq_of_range_pointsMap_ι_eq`, which is part (1) of
Tag 03BZ in the shape of an injectivity statement, and
`AlgebraicGeometry.Space.isRepresentable_image_of_isQuasiAffineHom` applies.

Nothing here carries the tag 03XW: the tag is already carried, on all three of its assertions,
by `AlgebraicGeometry.Space.isOpenSubspace_isQuasiCompactSpace_isRepresentable_image` in
`StacksFrontier.AlgebraicGeometry.Spaces.ImageRepresentableInduction`. This file only transports
the representability assertion of that tag across the identification of open subspaces with
open sets of points, and adds no new mathematical content to it.

Quasi-compactness of `U` is a hypothesis here, as in the source, but it is not used: it is a
consequence of the hypothesis on the point set of `U` together with the quasi-compactness
assertion of the tag, and is carried only so that the statement matches the situation of the
source.

## References

* [Stacks Project, Tag 03XW](https://stacks.math.columbia.edu/tag/03XW)
* [Stacks Project, Tag 03BZ](https://stacks.math.columbia.edu/tag/03BZ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-- Pullbacks of presheaves of types on the site, supplied directly: under Mathlib v4.35.0 the
instance search for `HasPullback` there first tries `Adhesive.hasPullback_of_mono_left` and times
out searching for `Mono`. -/
local instance (priority := high) hasPullback_presheaf_openSubspace
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : F ⟶ H) (g : G ⟶ H) : HasPullback f g :=
  HasLimitsOfShape.has_limit _

/-- **Representability of the image, Stacks 03XW, for an arbitrary open subspace.** Let
`t : T' ⟶ T` be an étale morphism of affine objects of the big fppf category over `S`, let
`f : X ⟶ yoneda.obj T` be a separated and locally quasi-finite morphism of algebraic spaces
over `S`, and let `V'` be an open subspace of `T' ×_T X` which is quasi-affine over `T'`. Then
every quasi-compact open subspace `U` of `X` whose point set is the image of the point set of
`V'` is representable.

An open subspace of an algebraic space is determined by its point set (part (1) of Tag 03BZ,
`AlgebraicGeometry.Space.eq_of_range_pointsMap_ι_eq`), so `U` is the canonical open subspace
cut out by that image, for which representability is
`AlgebraicGeometry.Space.isRepresentable_image_of_isQuasiAffineHom`. -/
theorem isRepresentable_openSubspace_image
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (T' T : BigFppfOver B S hS)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj T')]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
    (t : T' ⟶ T)
    (ht : Etale ((BigFppfOver.toScheme B S hS).map t))
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B S hS X)
    (f : X ⟶ yoneda.obj T)
    (hsep : IsSeparated B S hS f)
    (hlqf : IsLocallyQuasiFinite B S hS f)
    (V : Subfunctor (pullback (yoneda.map t) f))
    (hV : IsOpenSubspace B S hS V)
    (hVqa : IsQuasiAffineHom B S hS (V.ι ≫ pullback.fst (yoneda.map t) f))
    (U : Subfunctor X)
    (hUopen : IsOpenSubspace B S hS U)
    (hUqc : IsQuasiCompactSpace B S hS U.toFunctor)
    (hUimage : Set.range (pointsMap B S hS U.toFunctor U.ι) =
      Set.range (pointsMap B S hS V.toFunctor
        (V.ι ≫ pullback.snd (yoneda.map t) f))) :
    U.toFunctor.IsRepresentable := by
  have _hUqc := hUqc
  have hWopen : IsOpen (Set.range (pointsMap B S hS V.toFunctor
      (V.ι ≫ pullback.snd (yoneda.map t) f))) := by
    rw [← hUimage]
    exact isOpen_range_pointsMap_of_isOpenImmersion B S hS U.ι hUopen.2
  have hP := isOpenSubspace_openSubspaceOfPoints B S hS hX (F := X) _ hWopen
  have hEq : U = openSubspaceOfPoints B S hS X (Set.range (pointsMap B S hS V.toFunctor
      (V.ι ≫ pullback.snd (yoneda.map t) f))) :=
    eq_of_range_pointsMap_ι_eq B S hS hUopen hP
      (by rw [hUimage, range_pointsMap_ι_openSubspaceOfPoints])
  rw [hEq]
  exact isRepresentable_image_of_isQuasiAffineHom (B := B) (S := S) (hS := hS)
    inferInstance inferInstance ht hX hsep hlqf V hV hVqa

end AlgebraicGeometry.Space

end
