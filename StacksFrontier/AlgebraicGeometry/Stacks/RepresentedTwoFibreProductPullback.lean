module

public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentedTwoFibreProduct
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentingMapFunctorial
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentedTwoFibreProductProjections

/-!
# The representing square of a 2-fibre product of represented stacks is cartesian (Stacks 04SD)

Let `f : 𝒳 ⟶ 𝒵` and `g : 𝒴 ⟶ 𝒵` be 1-morphisms of categories fibred in groupoids over the big
fppf site of `S`, with `𝒳`, `𝒴`, `𝒵` represented by presheaves `F`, `G`, `H` and the apex of the
canonical 2-fibre product square represented by a presheaf `T`. Stacks 04SW turns each of the
four 1-morphisms in sight into a morphism of representing presheaves
(`AlgebraicGeometry.Stack.representingMap`), and
`AlgebraicGeometry.Stack.fibreProductIsoRepresenting` identifies `T` with the fibre product
`F ×_H G`. This file records that the identification carries the two projections of the fibre
product to the morphisms induced by the two projections of the square, and concludes that the
square of representing presheaves is a pullback square.

That last statement is what lets a *smooth* base change of morphisms of algebraic spaces be
recognised inside the 2-category: a property of morphisms of algebraic spaces which is only
smooth local on the source-and-target (**Stacks 06F8**) is not stable under arbitrary base
change, so it cannot be transported with
`AlgebraicGeometry.Stack.hasRelativeProperty_baseChange`, and the base change has to be exhibited
as a pullback of presheaves instead.

## Main results

* `AlgebraicGeometry.Stack.isPullback_representingMap_twoFibreProductSquare`: the square of
  representing presheaves of the canonical 2-fibre product square is a pullback square.

The compatibility of the comparison with the two projections, which that result rests on, is
`AlgebraicGeometry.Stack.fibreProductIsoRepresenting_hom_comp_representingMap_fst` and `..._snd` of
`StacksFrontier.AlgebraicGeometry.Stacks.RepresentedTwoFibreProductProjections`.

## Implementation notes

`AlgebraicGeometry.Stack.twoFibreProductIsoClassSectionEquiv_val_snd` is the second-projection
companion of `..._val_fst`; like it, it holds by `rfl` on a representative, since both
sides read off the corresponding component of a quadruple.

The two compatibilities are proved exactly as the first-projection half of
`AlgebraicGeometry.Stack.arrowIsoRelocalizeFibrePullback`: over each object of the site a section
of `T` named by an isomorphism class in the fibre of the 2-fibre product is carried by the induced
morphism to the section named by the class of the projection of that class, which is the
corresponding component of the pair the class names.

## References

* [Stacks Project, Tag 04SD](https://stacks.math.columbia.edu/tag/04SD)
* [Stacks Project, Tag 04SW](https://stacks.math.columbia.edu/tag/04SW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Stack

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 𝒴 𝒵 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
  (F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
  (eF : StacksRepresentableCFG.EquivalenceOver
    𝒳.val.p (presheafOfCategories (F ⋙ typeToCat)).p)
  (eG : StacksRepresentableCFG.EquivalenceOver
    𝒴.val.p (presheafOfCategories (G ⋙ typeToCat)).p)
  (eH : StacksRepresentableCFG.EquivalenceOver
    𝒵.val.p (presheafOfCategories (H ⋙ typeToCat)).p)
  (f : 𝒳 ⟶ 𝒵) (g : 𝒴 ⟶ 𝒵)

section Representing

variable [(twoFibreProductStructureFunctor B S hS 𝒳 𝒴 𝒵 f g).IsFibered]
  (T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
  (eT : StacksRepresentableCFG.EquivalenceOver
    (twoFibreProductStructureFunctor B S hS 𝒳 𝒴 𝒵 f g)
    (presheafOfCategories (T ⋙ typeToCat)).p)

/-- **The representing square of a 2-fibre product is cartesian.** For the canonical 2-fibre
product square of a cospan of categories fibred in groupoids over the big fppf site of `S`, all
four corners represented by presheaves, the square of morphisms of representing presheaves of
Stacks 04SW is a pullback square of presheaves.

This is Stacks 04SD for represented stacks
(`AlgebraicGeometry.Stack.fibreProductIsoRepresenting`), read through the two projections and
transported to the pullback the functor category provides. -/
theorem isPullback_representingMap_twoFibreProductSquare :
    IsPullback
      (representingMap B S hS
        (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f g).pt 𝒳 T F eT eF
        (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f g).fst)
      (representingMap B S hS
        (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f g).pt 𝒴 T G eT eG
        (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f g).snd)
      (representingMap B S hS 𝒳 𝒵 F H eF eH f)
      (representingMap B S hS 𝒴 𝒵 G H eG eH g) := by
  set mF := representingMap B S hS 𝒳 𝒵 F H eF eH f with hmF
  set mG := representingMap B S hS 𝒴 𝒵 G H eG eH g with hmG
  set ι := fibreProductIsoRepresenting B S hS 𝒳 𝒴 𝒵 F G H eF eG eH f g T eT with hι
  set pF := representingMap B S hS
    (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f g).pt 𝒳 T F eT eF
    (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f g).fst with hpF
  set pG := representingMap B S hS
    (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f g).pt 𝒴 T G eT eG
    (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f g).snd with hpG
  have hfst : ι.hom ≫ pF = Presheaf.fibreProductFst mF mG :=
    fibreProductIsoRepresenting_hom_comp_representingMap_fst B S hS 𝒳 𝒴 𝒵 F G H eF eG eH f g T eT
  have hsnd : ι.hom ≫ pG = Presheaf.fibreProductSnd mF mG :=
    fibreProductIsoRepresenting_hom_comp_representingMap_snd B S hS 𝒳 𝒴 𝒵 F G H eF eG eH f g T eT
  exact (Presheaf.isPullback_fibreProduct mF mG).of_iso ι (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by simpa using hfst.symm) (by simpa using hsnd.symm) (by simp) (by simp)

end Representing

end AlgebraicGeometry.Stack

end
