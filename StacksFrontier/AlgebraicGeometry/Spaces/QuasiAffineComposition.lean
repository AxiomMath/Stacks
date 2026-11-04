module

public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionQuasiAffineTfae

/-!
# Composition of quasi-affine morphisms of algebraic spaces

A morphism of algebraic spaces over a scheme `S` is quasi-affine when its base change along every
morphism from an affine object of the big fppf site of `S` is represented by an object of the
site with quasi-affine underlying scheme. This file proves that a composite of two such morphisms
is again quasi-affine.

## Main results

* `AlgebraicGeometry.Space.IsQuasiAffineHom.comp`: the composite of two quasi-affine morphisms of
  algebraic spaces over `S` is quasi-affine.

## References

* [Stacks Project, Tag 01SN](https://stacks.math.columbia.edu/tag/01SN)
* [Stacks Project, Tag 03HA](https://stacks.math.columbia.edu/tag/03HA)
* [Stacks Project, Tag 03WK](https://stacks.math.columbia.edu/tag/03WK)
* [Stacks Project, Tag 03WL](https://stacks.math.columbia.edu/tag/03WL)
* [Stacks Project, Tag 03WN](https://stacks.math.columbia.edu/tag/03WN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

/-- The composite of two quasi-affine morphisms of algebraic spaces over a
scheme `S` is quasi-affine. -/
@[stacks 03WN]
theorem IsQuasiAffineHom.comp {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (hZ : IsAlgebraicSpace B S hS Z) {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : IsQuasiAffineHom B S hS f) (hg : IsQuasiAffineHom B S hS g) :
    IsQuasiAffineHom B S hS (f ≫ g) :=
  let : MorphismProperty.IsStableUnderComposition
      (MorphismProperty.inverseImage
        (@_root_.AlgebraicGeometry.IsQuasiAffineHom.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)) :=
    MorphismProperty.IsStableUnderComposition.inverseImage _
  isQuasiAffineHom_of_presheaf (MorphismProperty.comp_mem _ f g
    (presheaf_isQuasiAffineHom_of_isQuasiAffineHom_of_isAlgebraicSpace B S hS hX hY hf)
    (presheaf_isQuasiAffineHom_of_isQuasiAffineHom_of_isAlgebraicSpace B S hS hY hZ hg))

add_to_stacks 03WK "representable case: 03HA-quasi-affine iff affine base changes are quasi-affine"
  AlgebraicGeometry.Space.presheaf_isQuasiAffineHom_iff

end AlgebraicGeometry.Space

end
