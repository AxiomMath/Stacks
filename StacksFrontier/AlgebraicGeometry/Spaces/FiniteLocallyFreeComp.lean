module

public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFree.Comp
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeEtaleLocal

/-!
# Composition of finite locally free morphisms of algebraic spaces

A representable morphism of algebraic spaces over a scheme `S` is finite locally free when each
of its represented base changes is a finite locally free morphism of schemes, which is condition
(1) of Stacks 03ZW.  A composite of two such morphisms is again one.

## Main results

* `AlgebraicGeometry.Space.isFiniteLocallyFree_isStableUnderComposition`: finite local freeness
  of morphisms of schemes is stable under composition (Stacks 02KC).
* `AlgebraicGeometry.Space.isFiniteLocallyFree_inverseImage_isStableUnderComposition`: finite
  local freeness of a morphism of the big fppf site of `S` is stable under composition.
* `AlgebraicGeometry.Space.isFiniteLocallyFree_presheaf_isStableUnderComposition` and
  `AlgebraicGeometry.Space.isFiniteLocallyFree_presheaf_comp`: representable finite locally free
  morphisms of algebraic spaces are stable under composition (Stacks 03ZX).

## Implementation notes

Finite local freeness of a representable morphism of algebraic spaces is
`CategoryTheory.MorphismProperty.presheaf` of the inverse image along
`AlgebraicGeometry.BigFppfOver.toScheme` of finite local freeness of morphisms of schemes.

## References

* [Stacks Project, Tag 02KC](https://stacks.math.columbia.edu/tag/02KC)
* [Stacks Project, Tag 03ZW](https://stacks.math.columbia.edu/tag/03ZW)
* [Stacks Project, Tag 03ZX](https://stacks.math.columbia.edu/tag/03ZX)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

/-! ### The scheme-level fact -/

/-- Finite local freeness of morphisms of schemes is stable under composition. -/
theorem isFiniteLocallyFree_isStableUnderComposition :
    MorphismProperty.IsStableUnderComposition
      (@Stacks.Morphisms.IsFiniteLocallyFree.{u} : MorphismProperty Scheme.{u}) :=
  ⟨fun f g hf hg => @Stacks.Morphisms.isFiniteLocallyFree_comp.{u} _ _ _ f g hf hg⟩

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Composition in the big fppf site -/

/-- Finite local freeness of a morphism of the big fppf site of `S` is stable under composition
in that site. -/
instance isFiniteLocallyFree_inverseImage_isStableUnderComposition :
    (MorphismProperty.inverseImage
      (@Stacks.Morphisms.IsFiniteLocallyFree.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).IsStableUnderComposition :=
  have _ := isFiniteLocallyFree_isStableUnderComposition.{u}
  MorphismProperty.IsStableUnderComposition.inverseImage _

/-! ### Composition of morphisms of algebraic spaces -/

/-- Being representable and finite locally free is a composition-stable class of morphisms of
presheaves on the big fppf site of `S`. -/
@[stacks 03ZX "stability under composition"]
instance isFiniteLocallyFree_presheaf_isStableUnderComposition :
    (MorphismProperty.inverseImage
      (@Stacks.Morphisms.IsFiniteLocallyFree.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf.IsStableUnderComposition :=
  MorphismProperty.relative_isStableUnderComposition _

/-- The composition of representable finite locally free morphisms of algebraic spaces over `S`
is representable and finite locally free. -/
@[stacks 03ZX]
theorem isFiniteLocallyFree_presheaf_comp
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : (MorphismProperty.inverseImage
      (@Stacks.Morphisms.IsFiniteLocallyFree.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf f)
    (hg : (MorphismProperty.inverseImage
      (@Stacks.Morphisms.IsFiniteLocallyFree.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf g) :
    (MorphismProperty.inverseImage
      (@Stacks.Morphisms.IsFiniteLocallyFree.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (f ≫ g) :=
  MorphismProperty.comp_mem _ f g hf hg

end AlgebraicGeometry.Space

end
