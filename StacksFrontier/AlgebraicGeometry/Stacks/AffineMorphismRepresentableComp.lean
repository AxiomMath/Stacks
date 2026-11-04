module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.AffineMorphismStability
public import StacksFrontier.AlgebraicGeometry.Stacks.Algebraic.RepresentableMorphism.Composition
public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalCriteriaAlgebraicSpaceSources

/-!
# Affine 1-morphisms of algebraic stacks, read with "representable" by schemes

Stacks 0CHQ defines a 1-morphism of algebraic stacks to be *affine* if it is *representable* —
in the Stacks project's default sense, representable by schemes (Stacks 02Y7) — and affine in the
sense of Properties of Stacks, Section 04XB. The section then remarks that this is the same as
asking the 1-morphism to be representable by *algebraic spaces* and affine in the sense of 04XB,
and works with that form "without further mention";
`AlgebraicGeometry.Stack.AlgebraicStacks.IsAffineHom` is that form.

This file proves the half of that remark which the composition lemma **Stacks 0CHS** needs, and
then proves Stacks 0CHS for the definition of Stacks 0CHQ read literally.

## Main results

* `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_of_isRepresentableMorphism`: a
  1-morphism of categories fibred in groupoids over the big fppf site of `S` which is
  representable (by schemes, Stacks 02Y7) is representable by algebraic spaces.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isAffineHom_of_isRepresentableMorphism`: a 1-morphism
  of algebraic stacks which is affine in the literal sense of Stacks 0CHQ is affine in the sense
  of `AlgebraicGeometry.Stack.AlgebraicStacks.IsAffineHom`.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isRepresentableMorphism_comp_isAffineHom`:
  **Stacks 0CHS** for the literal definition of Stacks 0CHQ.

## Implementation notes

The representing object that Stacks 02Y7 supplies lives over the slice `𝒞/V` of the big fppf
site of `S` at the scheme `V`, so it is an object `X` of that slice; the iterated-slice
equivalence `𝒞/V/X ≌ 𝒞/X.left` turns its slice into the category represented by the scheme
`X.left` over `S`, which is representable by an algebraic space
(`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpace_schemeFibredCategory`). The pointwise
criterion `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_of_forall_twoFibreProduct`
then gives representability by algebraic spaces.

## References

* [Stacks Project, Tag 02Y7](https://stacks.math.columbia.edu/tag/02Y7)
* [Stacks Project, Tag 02ZS](https://stacks.math.columbia.edu/tag/02ZS)
* [Stacks Project, Tag 02ZW](https://stacks.math.columbia.edu/tag/02ZW)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 0CHQ](https://stacks.math.columbia.edu/tag/0CHQ)
* [Stacks Project, Tag 0CHS](https://stacks.math.columbia.edu/tag/0CHS)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A representable 1-morphism is representable by algebraic spaces.** A 1-morphism of
categories fibred in groupoids over the big fppf site of `S` which is representable in the sense
of Stacks 02Y7 — every 2-fibre product with the category represented by a scheme `V` over `S` is
equivalent over `𝒞/V` to a slice — is representable by algebraic spaces in the sense of
Stacks 02ZW: the representing slice is the category of the scheme it is a slice at, and a scheme
is an algebraic space. -/
theorem isRepresentableByAlgebraicSpaces_of_isRepresentableMorphism
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)} (f : 𝒳 ⟶ 𝒴)
    (hf : Stacks.RepresentableMorphism.IsRepresentableMorphism 𝒳.val.p 𝒴.val.p
      (CatFiberedInGroupoids.homFunctor f)) :
    IsRepresentableByAlgebraicSpaces B S hS f.hom := by
  refine isRepresentableByAlgebraicSpaces_of_forall_twoFibreProduct B S hS 𝒴 𝒳 f.hom
    fun V y => ?_
  obtain ⟨X, E, hE⟩ := hf V y.toFunctor y.w
  let : Category.{u, u + 1}
      (TwoFibreProductOver (Over.forget V) 𝒳.val.p 𝒴.val.p y.toFunctor
        (CatFiberedInGroupoids.homFunctor f)) :=
    TwoFibreProductOver.instCategory
  have hEeq : E.IsEquivalence :=
    Stacks.RepresentableMorphism.SliceEquivalence.isEquivalence_of_isEquivalenceOver _ X E hE
  have hcomm : (E ⋙ (Over.iteratedSliceEquiv X).functor) ⋙
      (schemeFibredCategory B S hS X.left).val.p =
      (twoFibreProduct B S hS 𝒴 (schemeFibredCategory B S hS V) 𝒳 y f.hom).val.p := by
    show E ⋙ (Over.forget X ⋙ Over.forget V) = _
    rw [← Functor.assoc, hE.isCartesianFunctor.comm]
    exact TwoFibreProductOver.fst_comp_eq
  obtain ⟨k⟩ := StacksRepresentableCFG.nonempty_equivalenceOver_of_isEquivalence
    (twoFibreProduct B S hS 𝒴 (schemeFibredCategory B S hS V) 𝒳 y f.hom).isFiberedInGroupoids
    (schemeFibredCategory B S hS X.left).isFiberedInGroupoids
    (E ⋙ (Over.iteratedSliceEquiv X).functor) hcomm
    (Functor.isEquivalence_trans E (Over.iteratedSliceEquiv X).functor)
  exact isRepresentableByAlgebraicSpace_of_equivalenceOver k
    (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS X.left)

namespace AlgebraicStacks

variable {B S hS} {𝒳 𝒴 𝒵 : Stack.AlgebraicStacks.{u, w} B S hS}

/-- **An affine 1-morphism of algebraic stacks in the literal sense of Stacks 0CHQ is affine in
the sense of `AlgebraicGeometry.Stack.AlgebraicStacks.IsAffineHom`.** A 1-morphism which is
representable (by schemes, Stacks 02Y7) and affine in the sense of Stacks 04XB is representable by
algebraic spaces and affine in the sense of Stacks 04XB. -/
theorem isAffineHom_of_isRepresentableMorphism (f : 𝒳 ⟶ 𝒴)
    (hrep : Stacks.RepresentableMorphism.IsRepresentableMorphism 𝒳.val.val.p 𝒴.val.val.p
      (CatFiberedInGroupoids.homFunctor f.hom))
    (haff : Stack.IsAffineHom B S hS f.hom) :
    IsAffineHom B S hS f :=
  ⟨isRepresentableByAlgebraicSpaces_of_isRepresentableMorphism B S hS f.hom hrep, haff⟩

/-- **Stacks 0CHS, for the definition of Stacks 0CHQ read literally.** Call a 1-morphism of
algebraic stacks over `S` affine when it is representable (by schemes, Stacks 02Y7) and affine in
the sense of Stacks 04XB. Then a composite of two affine 1-morphisms of algebraic stacks is
affine: representability composes by Stacks 02ZS, and affineness in the sense of Stacks 04XB
composes by `AlgebraicGeometry.Stack.isAffineHom_comp` (Stacks 045B with Stacks 03WH and the
implication (4) ⇒ (2) of Stacks 03WG), which applies because a representable 1-morphism is
representable by algebraic spaces. -/
@[stacks 0CHS "with 0CHQ read literally: representable by schemes and affine in the sense of 04XB"]
theorem isRepresentableMorphism_comp_isAffineHom (f : 𝒳 ⟶ 𝒴) (g : 𝒴 ⟶ 𝒵)
    (hf : Stacks.RepresentableMorphism.IsRepresentableMorphism 𝒳.val.val.p 𝒴.val.val.p
        (CatFiberedInGroupoids.homFunctor f.hom) ∧ Stack.IsAffineHom B S hS f.hom)
    (hg : Stacks.RepresentableMorphism.IsRepresentableMorphism 𝒴.val.val.p 𝒵.val.val.p
        (CatFiberedInGroupoids.homFunctor g.hom) ∧ Stack.IsAffineHom B S hS g.hom) :
    Stacks.RepresentableMorphism.IsRepresentableMorphism 𝒳.val.val.p 𝒵.val.val.p
        (CatFiberedInGroupoids.homFunctor (f ≫ g).hom) ∧
      Stack.IsAffineHom B S hS (f ≫ g).hom :=
  ⟨Stacks.RepresentableMorphism.isRepresentableMorphism_comp 𝒳.val.val.p 𝒴.val.val.p 𝒵.val.val.p
      𝒳.val.isFiberedInGroupoids 𝒴.val.isFiberedInGroupoids 𝒵.val.isFiberedInGroupoids
      (CatFiberedInGroupoids.homFunctor f.hom) (CatFiberedInGroupoids.homFunctor g.hom)
      (CatFiberedInGroupoids.homFunctor_comp_p f.hom)
      (CatFiberedInGroupoids.homFunctor_comp_p g.hom) hf.1 hg.1,
    (isAffineHom_comp B S hS f g (isAffineHom_of_isRepresentableMorphism f hf.1 hf.2)
      (isAffineHom_of_isRepresentableMorphism g hg.1 hg.2)).2⟩

end AlgebraicStacks

end AlgebraicGeometry.Stack

end
