module

public import StacksFrontier.AlgebraicGeometry.Stacks.SelfIntersectionFlatPresentation

/-!
# A smooth presentation of an algebraic stack is an equivalence

Let `f : 𝒰 ⟶ 𝒳` be a 1-morphism of categories fibred in groupoids over the big fppf site of a
scheme `S`, with `𝒳` an algebraic stack, `𝒰` represented by an algebraic space `U` and the
self-intersection `𝒰 ×_{f, 𝒳, f} 𝒰` represented by an algebraic space `R`. These choices give a
groupoid in algebraic spaces `R ⇉ U` together with a canonical 1-morphism `f_can : [U/R] ⟶ 𝒳`
out of its quotient stack
(`AlgebraicGeometry.Stack.SelfIntersection.selfIntersectionPresentation`). This file shows that
`f_can` is an equivalence over the site when `f` is smooth and surjective.

## Main results

* `AlgebraicGeometry.Stack.SelfIntersection.exists_equivalenceOver_canonicalMap_of_isSmooth`:
  if `f` is smooth and surjective, then `f_can` is the forward 1-morphism of an equivalence over
  the site.

## Implementation notes

The conclusion is an equivalence over the site in the bundled sense
`StacksRepresentableCFG.EquivalenceOver` — a quasi-inverse 1-morphism strictly over the site,
with unit and counit 2-cells over the site — together with the identification of its forward
1-morphism with the canonical one, which makes the statement about `f_can` rather than about an
abstract equivalence between its source and target.

Representability of `f` by algebraic spaces is not a hypothesis: it follows from algebraicity of
`𝒳` together with representability of `𝒰` by an algebraic space, which the chosen equivalence
`eU` supplies.

The index universe `w` of the algebraicity hypothesis is free; at a free index universe the stack
clause of `AlgebraicGeometry.Stack.IsAlgebraicStack` is the stronger hypothesis.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits

namespace AlgebraicGeometry.Stack.SelfIntersection

universe u w

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {𝒰 𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
variable {f : 𝒰 ⟶ 𝒳}
variable {U R : AlgebraicSpaces B S hS}
variable
  (eU : StacksRepresentableCFG.EquivalenceOver
    𝒰.val.p (presheafOfCategories (U.obj ⋙ typeToCat)).p)
  (eR : StacksRepresentableCFG.EquivalenceOver
    (relation B S hS 𝒰 𝒳 f.hom).val.p
    (presheafOfCategories (R.obj ⋙ typeToCat)).p)

/-- Let `𝒳` be an algebraic stack over `S`, let `f : 𝒰 ⟶ 𝒳` be a 1-morphism whose source is
represented by an algebraic space `U` and whose self-intersection is represented by an algebraic
space `R`, and suppose that every algebraic space representing a base change of `f` along a
scheme-valued point of `𝒳` has smooth and surjective structural morphism. Then the canonical
1-morphism `f_can : [U/R] ⟶ 𝒳` out of the quotient stack of the groupoid of
`selfIntersectionPresentation eU eR h𝒳` is the forward 1-morphism of an equivalence over the big
fppf site of `S`. -/
@[stacks 04T5 "part (2): canonical equivalence"]
theorem exists_equivalenceOver_canonicalMap_of_isSmooth
    (h𝒳 : IsAlgebraicStack.{u, w} B S hS 𝒳.val)
    (hsmooth : ∀ (T : BigFppfOver B S hS)
        (y : BigFppfOver B T.left.1 T.left.2 ⥤ 𝒳.val.obj)
        (_hy : y ⋙ 𝒳.val.p = Over.map T.hom)
        (F : (BigFppfOver B T.left.1 T.left.2)ᵒᵖ ⥤ Type u)
        (hF : IsAlgebraicSpace B T.left.1 T.left.2 F),
        Nonempty (StacksRepresentableCFG.EquivalenceOver
          (TwoFibreProductOver.fst (Over.map T.hom) 𝒰.val.p 𝒳.val.p y
            (CatFiberedInGroupoids.homFunctor f))
          (presheafOfCategories (F ⋙ typeToCat)).p) →
        Space.IsSmooth B S hS (algebraicSpaceMap B S hS T
          ((spacesOverSmallerBaseFunctor B T.left.1 S T.left.2 hS T.hom).obj ⟨F, hF⟩)).hom)
    (hsurj : ∀ (T : BigFppfOver B S hS)
        (y : BigFppfOver B T.left.1 T.left.2 ⥤ 𝒳.val.obj)
        (_hy : y ⋙ 𝒳.val.p = Over.map T.hom)
        (F : (BigFppfOver B T.left.1 T.left.2)ᵒᵖ ⥤ Type u)
        (hF : IsAlgebraicSpace B T.left.1 T.left.2 F),
        Nonempty (StacksRepresentableCFG.EquivalenceOver
          (TwoFibreProductOver.fst (Over.map T.hom) 𝒰.val.p 𝒳.val.p y
            (CatFiberedInGroupoids.homFunctor f))
          (presheafOfCategories (F ⋙ typeToCat)).p) →
        Space.IsSurjective B S hS (algebraicSpaceMap B S hS T
          ((spacesOverSmallerBaseFunctor B T.left.1 S T.left.2 hS T.hom).obj ⟨F, hF⟩)).hom) :
    ∃ e : StacksRepresentableCFG.EquivalenceOver
        (Stack.quotientStack (selfIntersectionPresentation eU eR h𝒳).groupoid).p 𝒳.val.p,
      e.hom.functor = (selfIntersectionPresentation eU eR h𝒳).canonicalMap.toFunctor := by
  obtain ⟨E⟩ := nonempty_isEquivalenceOver_canonicalMap eU eR h𝒳
    (fun T y hy F hF hE => by
      have hsm := hsmooth T y hy F hF hE
      exact ⟨hsurj T y hy F hF hE, Space.isFlat_of_isSmooth B S hS _ hsm,
        Space.isLocallyOfFinitePresentation_of_isSmooth B S hS hsm⟩)
  exact ⟨StacksRepresentableCFG.EquivalenceOver.ofFunctorIsEquivalenceOver
    (selfIntersectionPresentation eU eR h𝒳).canonicalMap.w E, rfl⟩

end AlgebraicGeometry.Stack.SelfIntersection

end
