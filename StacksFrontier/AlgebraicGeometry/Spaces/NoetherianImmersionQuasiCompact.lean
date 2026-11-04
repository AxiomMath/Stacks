module

public import StacksFrontier.AlgebraicGeometry.Descent.AffineHomEtaleDatum
public import StacksFrontier.AlgebraicGeometry.Properties.NoetherianImmersion
public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedFamiliesForget

/-!
# Immersions of algebraic spaces into a locally Noetherian scheme are quasi-compact

An immersion of algebraic spaces over `S` whose target is the presheaf represented by a scheme of
the site is quasi-compact as soon as that scheme is locally Noetherian. This is the algebraic-space
reading of the scheme-level statement `AlgebraicGeometry.quasiCompact_of_isImmersion`
(**Stacks 01OX**), and it is the input the quasi-compactness half of **Stacks 0CPM**, part (1),
asks for at the level of algebraic spaces: the base change of an immersion of algebraic stacks
along a locally Noetherian scheme atlas of its target is exactly a morphism of this shape.

## Main definitions

There are no new definitions.

## Main results

* `AlgebraicGeometry.Space.isQuasiCompact_of_isImmersion_yoneda`: an immersion of algebraic spaces
  over `S` into the presheaf represented by a locally Noetherian scheme of the site is
  quasi-compact in the sense of **Stacks 03HE**.

## Implementation notes

An immersion in the sense of **Stacks 02YU**, part (5), is in particular relatively representable,
so a morphism `f : F ⟶ yoneda.obj V` which is an immersion has representable *source* as well:
base-changing it along the identity of `yoneda.obj V` exhibits `F` as the presheaf represented by
an object `U` of the site, with `f` induced by a morphism `i : U ⟶ V`. That identification is
`AlgebraicGeometry.Space.descentObjIso`, and the property attached to that one base change says
precisely that the scheme morphism underlying `i` is an immersion. Stacks 01OX then makes it
quasi-compact, `AlgebraicGeometry.Space.isQuasiCompact_yoneda_map` carries quasi-compactness of a
morphism of the site to the represented morphism of algebraic spaces, and
`AlgebraicGeometry.Space.isQuasiCompact_isIso_comp` transports it back along the identification of
the source.

So the arbitrary-affine criterion
`AlgebraicGeometry.Space.isQuasiCompact_of_isQuasiCompactSpace_pullback_affine` is not needed, and
indeed could not be used directly: an affine object of the site mapping to `V` need not have
locally Noetherian underlying scheme, whereas the single base change along the identity has the
locally Noetherian `V` itself as target.

## References

* [Stacks Project, Tag 01OX](https://stacks.math.columbia.edu/tag/01OX)
* [Stacks Project, Tag 02YU](https://stacks.math.columbia.edu/tag/02YU)
* [Stacks Project, Tag 03HE](https://stacks.math.columbia.edu/tag/03HE)
* [Stacks Project, Tag 0CPM](https://stacks.math.columbia.edu/tag/0CPM)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **An immersion of algebraic spaces over `S` into a locally Noetherian scheme of the site is
quasi-compact.** Immersions are the ones of Stacks 02YU, part (5), and quasi-compactness of a
morphism is the one of Stacks 03HE.

This is the algebraic-space reading of Stacks 01OX. The immersion is relatively representable, so
its source is represented by an object `U` of the site and the immersion by a morphism `U ⟶ V`
whose underlying morphism of schemes is an immersion into a locally Noetherian scheme, hence
quasi-compact. -/
theorem isQuasiCompact_of_isImmersion_yoneda {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {V : BigFppfOver B S hS} {f : F ⟶ yoneda.obj V} (hf : IsImmersion B S hS f)
    (hV : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj V)) :
    IsQuasiCompact B S hS f := by
  have : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj V) := hV
  have : _root_.AlgebraicGeometry.IsImmersion
      ((BigFppfOver.toScheme B S hS).map (hf.rep.snd (𝟙 (yoneda.obj V)))) :=
    hf.property_snd (𝟙 _)
  have h := isQuasiCompact_isIso_comp B S hS (descentObjIso hf.rep).hom
    (isQuasiCompact_yoneda_map B S hS (hf.rep.snd (𝟙 (yoneda.obj V))) inferInstance)
  rwa [descentObjIso_hom_comp] at h

end AlgebraicGeometry.Space

end
