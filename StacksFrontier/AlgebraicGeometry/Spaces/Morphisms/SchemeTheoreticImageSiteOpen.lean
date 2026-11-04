module

public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SchemeTheoreticImage

/-!
# Open subobjects of the site, and the range-dependence of the scheme-theoretic image

Two small shared ingredients of the scheme-theoretic-image arguments for algebraic spaces: the
object of the big fppf category cut out by an open subscheme of a given object, and the fact that
the scheme-theoretic image of a morphism depends only on its range.

Both were carried, identically, by
`StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompactImageFlatBaseChange` and
`StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SchemeTheoreticDensity`.

## Main definitions

* `AlgebraicGeometry.Space.siteOpenObject`

## Main results

* `AlgebraicGeometry.Space.schemeTheoreticImageSubfunctor_congr_range`

## Tags

algebraic space, scheme-theoretic image, open subobject
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- An open subscheme of an object of the big fppf category over `S`, as an object of that
category; its size is bounded by that of the ambient object. -/
noncomputable abbrev siteOpenObject (V : BigFppfOver B S hS)
    (W : ((BigFppfOver.toScheme B S hS).obj V).Opens) : BigFppfOver B S hS :=
  Over.mk (B.inclusion.preimage
    (X := B.obj ((Scheme.size_coe_opens_le _ W).trans_lt V.left.property))
    (Y := V.left) W.ι ≫ V.hom)

/-- The scheme-theoretic image of a morphism of algebraic spaces depends only on its range. -/
lemma schemeTheoreticImageSubfunctor_congr_range
    {X X' Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y) (g : X' ⟶ Y)
    (hY : IsAlgebraicSpace B S hS Y) (h : Subfunctor.range f = Subfunctor.range g) :
    schemeTheoreticImageSubfunctor B S hS f = schemeTheoreticImageSubfunctor B S hS g :=
  le_antisymm
    (schemeTheoreticImageSubfunctor_le B S hS f
      (isClosedSubspace_schemeTheoreticImageSubfunctor B S hS g hY)
      (h.trans_le (range_le_schemeTheoreticImageSubfunctor B S hS g)))
    (schemeTheoreticImageSubfunctor_le B S hS g
      (isClosedSubspace_schemeTheoreticImageSubfunctor B S hS f hY)
      (h.symm.trans_le (range_le_schemeTheoreticImageSubfunctor B S hS f)))

/-- A relatively representable etale morphism of presheaves is etale in the sense of Stacks
03FR: compose the given relatively-etale morphism with an arbitrary chart, using that the
inverse image of `Etale` along the forgetful functor is stable under composition. -/
lemma isEtale_of_presheafEtale {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : F ⟶ G)
    (hf : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf f) :
    IsEtale B S hS f :=
  fun _ psi hpsi => MorphismProperty.comp_mem _ psi f hpsi hf

/-- The inverse image of `Etale` along the forgetful functor to schemes, as a property of
morphisms of presheaves, is stable under composition. -/
lemma presheafEtale_comp {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {a : F ⟶ G} {b : G ⟶ H}
    (ha : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (hb : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf b) :
    (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (a ≫ b) :=
  MorphismProperty.comp_mem _ a b ha hb

end Space

end AlgebraicGeometry

end
