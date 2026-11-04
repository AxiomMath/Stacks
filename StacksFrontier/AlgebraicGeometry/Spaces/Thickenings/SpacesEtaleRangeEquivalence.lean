module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleBaseChangeIso
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SpacesEtaleEssSurj

/-!
# Topological invariance of the étale site at a morphism whose range is a thickening

The statements of **Stacks 05ZH** in this library — faithfulness, fullness and essential
surjectivity of base change at a thickening of arbitrary order — are all indexed by a
*subfunctor*: they speak of `AlgebraicGeometry.Space.IsThickening.inclusion` of a thickening
`G ⊂ Y`. A morphism `f : X ⟶ Y` of algebraic spaces is not of that shape even when its range is
a thickening; the range factorization `CategoryTheory.Subfunctor.toRange` stands in between.

This file absorbs that factorization: for a monomorphism whose range is a thickening, base
change along the morphism itself is an equivalence of spaces-étale sites.

## Main results

* `AlgebraicGeometry.Space.isEquivalence_spacesBaseChange_of_isThickening_range`: base change
  along a monomorphism of algebraic spaces whose range is a thickening of the target is an
  equivalence of the spaces-étale sites.

## Implementation notes

The factorization `f = toRange f ≫ ι` of `CategoryTheory.Subfunctor.toRange_ι` has its first
factor an isomorphism, because `f` is a monomorphism; base change along it is an equivalence by
`AlgebraicGeometry.Space.isEquivalence_spacesBaseChange_of_isIso`, base change along the second
is one by `AlgebraicGeometry.Space.isEquivalence_spacesBaseChange_of_isThickening`, and
`AlgebraicGeometry.Space.spacesBaseChange_comp` identifies their composite with base change
along `f`.

The statement is left unregistered. Stacks 05ZH is already registered on the three clauses it
is the assembly of — `AlgebraicGeometry.Space.faithful_spacesBaseChange_of_isThickening`,
`AlgebraicGeometry.Space.full_spacesBaseChange_of_isThickening` and
`AlgebraicGeometry.Space.essSurj_spacesBaseChange_of_isThickening` — and on their conclusion
`AlgebraicGeometry.Space.isEquivalence_spacesBaseChange_of_isThickening`; this is that
conclusion read along a range factorization, not a further part of the tag.

## References

* [Stacks Project, Tag 05ZH](https://stacks.math.columbia.edu/tag/05ZH)
* [Stacks Project, Tag 05ZK](https://stacks.math.columbia.edu/tag/05ZK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Topological invariance of the étale site along a morphism whose range is a thickening.**
Let `f : X ⟶ Y` be a monomorphism of algebraic spaces over `S` whose range is a thickening of
`Y`, of arbitrary order. Base change along `f` is an equivalence from the spaces-étale site of
`Y` to that of `X`.

This is `AlgebraicGeometry.Space.isEquivalence_spacesBaseChange_of_isThickening` with the range
factorization of `f` absorbed: the first factor `CategoryTheory.Subfunctor.toRange` is an
isomorphism because `f` is a monomorphism, and base change along an isomorphism is an
equivalence. -/
theorem isEquivalence_spacesBaseChange_of_isThickening_range
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) [Mono f.hom]
    (hG : IsThickening B S hS Y (Subfunctor.range f.hom)) :
    (spacesBaseChange B S hS f).functor.IsEquivalence := by
  let r : X ⟶ IsThickening.space B S hS hG := ObjectProperty.homMk (Subfunctor.toRange f.hom)
  have hrmap : IsIso ((ObjectProperty.ι
      (fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u => IsAlgebraicSpace B S hS F)).map r) :=
    inferInstanceAs (IsIso (Subfunctor.toRange f.hom))
  have hr : IsIso r := (ObjectProperty.fullyFaithfulι _).isIso_of_isIso_map r
  have hfac : r ≫ IsThickening.inclusion B S hS hG = f := by
    refine (ObjectProperty.fullyFaithfulι _).map_injective ?_
    rw [Functor.map_comp]
    exact Subfunctor.toRange_ι f.hom
  have := isEquivalence_spacesBaseChange_of_isThickening B S hS hG
  have := isEquivalence_spacesBaseChange_of_isIso B S hS r
  have h := Functor.isEquivalence_of_iso
    (spacesBaseChange_comp B S hS r (IsThickening.inclusion B S hS hG))
  rwa [hfac] at h

end AlgebraicGeometry.Space

end
