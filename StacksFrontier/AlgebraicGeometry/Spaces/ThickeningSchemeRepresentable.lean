module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeOfIntegralBijection
public import StacksFrontier.AlgebraicGeometry.Spaces.ThickeningMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.EtaleSite

/-!
# A thickening of a scheme is a scheme, through Stacks 07VV for an integral morphism

Let `S` be a scheme and let `X ⊂ X'` be a thickening of algebraic spaces over `S`. If `X` is
(representable by) a scheme, then so is `X'` (Stacks 05ZR). Being a scheme is
`CategoryTheory.Functor.IsRepresentable` for the presheaf underlying the space.

The results of this file are the forms of Stacks 05ZR obtained from Stacks 07VV for an integral
morphism, and they carry the three hypotheses of the library's Stacks 07VT. Stacks 05ZR itself
is proved with no hypotheses, from the closed-immersion form of Stacks 07VV, as
`AlgebraicGeometry.Space.isRepresentable_of_isThickening_of_isRepresentable` and
`AlgebraicGeometry.Space.isRepresentable_of_isThickeningHom_of_isRepresentable` in
`StacksFrontier/AlgebraicGeometry/Spaces/ThickeningSchemeRepresentableClosedImmersion.lean`; the
tag is registered on those, and not on the declarations here.

The inclusion of a thickening is integral and bijective on points, so this is Stacks 07VV in
the direction that goes from the source: the hypotheses of
`AlgebraicGeometry.Space.isRepresentable_of_isIntegralHom_of_bijective` are exactly the three
properties of the inclusion of a thickening already recorded in
`StacksFrontier/AlgebraicGeometry/Spaces/Thickenings/EtaleSite.lean`.

## Main results

* `AlgebraicGeometry.Space.isRepresentable_of_isRepresentable_thickening`: Stacks 05ZR, with
  the three hypotheses of Stacks 07VT, in the subspace form in which Stacks 05ZK, part (1)
  states a thickening — a closed subspace `G ⊂ X'` whose inclusion is surjective on points.
* `AlgebraicGeometry.Space.isRepresentable_of_isThickeningHom`: Stacks 05ZR, with the three
  hypotheses of Stacks 07VT, in the morphism form `AlgebraicGeometry.Space.IsThickeningHom`,
  the shape in which thickenings of algebraic spaces appear in Stacks 05ZS, 07VX and 0AIC.

## Implementation notes

The thin side of a thickening needs none of this: a closed subspace of a scheme is a scheme
with no hypotheses, which is
`AlgebraicGeometry.Space.isRepresentable_of_isThickening` in
`StacksFrontier/AlgebraicGeometry/Spaces/Thickenings/Scheme.lean`.

Both results below carry the three hypotheses `h09YA`, `h07SQ` and `hFinitePresentation`
verbatim from `AlgebraicGeometry.Space.isRepresentable_of_isIntegralHom_of_bijective`, and
hence from `AlgebraicGeometry.Space.isAffineSpace_of_isSurjective_of_universallyClosed`, the
weaker form of Stacks 07VT (Stacks 07VT itself is proved with no hypotheses as
`AlgebraicGeometry.Space.isAffineSpace_of_isSurjective_of_universallyClosed_of_isAffineSpace`).
They are passed straight through and are used for nothing else, so these forms depend on precisely
what that weaker form depends on and on nothing further. The hypotheses are avoidable: the
inclusion of a thickening is a closed immersion, and for a closed immersion the affineness step
needs only the thickening case of Stacks 07VT, which holds with no hypotheses; that is the route
of the forms with no hypotheses named above.

The inclusion `G.ι` of a thickening is injective on points because it is a monomorphism and
surjective on points by definition, which together give the bijectivity that Stacks 07VV
asks for; its integrality is Stacks 081Y, since a thickening is a closed immersion. In the
morphism form the same three facts come from
`AlgebraicGeometry.Space.IsThickeningHom.mono`,
`AlgebraicGeometry.Space.IsThickeningHom.surjective_pointsMap` and
`AlgebraicGeometry.Space.IsThickeningHom.isClosedImmersion`.

## References

* [Stacks Project, Tag 05ZK](https://stacks.math.columbia.edu/tag/05ZK)
* [Stacks Project, Tag 05ZR](https://stacks.math.columbia.edu/tag/05ZR)
* [Stacks Project, Tag 07VT](https://stacks.math.columbia.edu/tag/07VT)
* [Stacks Project, Tag 07VV](https://stacks.math.columbia.edu/tag/07VV)
* [Stacks Project, Tag 081Y](https://stacks.math.columbia.edu/tag/081Y)
-/

@[expose] public section

open CategoryTheory
open Stacks.Thickenings

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 05ZR through Stacks 07VV for an integral morphism.** Let `S` be a scheme and let
`G ⊂ X'` be a thickening of algebraic spaces over `S`, in the subspace form of Stacks 05ZK,
part (1). If `G` is (representable by) a scheme, then so is `X'`, given the three hypotheses of
the library's Stacks 07VT. The same statement with no hypotheses is
`AlgebraicGeometry.Space.isRepresentable_of_isThickening_of_isRepresentable`.

The inclusion `G.ι` is integral by Stacks 081Y, injective on points because it is a
monomorphism, and surjective on points by the definition of a thickening, so Stacks 07VV
applies in the direction that goes from the source. -/
theorem isRepresentable_of_isRepresentable_thickening {X' : AlgebraicSpaces B S hS}
    {G : Subfunctor X'.1} (hG : IsThickening B S hS X' G)
    (hGrep : G.toFunctor.IsRepresentable)
    (h09YA : ∀ {Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : Y ⟶ Z),
      IsAlgebraicSpace B S hS Y → IsAlgebraicSpace B S hS Z → IsIntegralHom B S hS g →
      IsQuasiCompactSpace B S hS Z →
      IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Z →
      IntegralFiniteSystem B S hS g)
    (h07SQ : ∀ {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
      (D : DescentSituation B S hS B.contains_terminal I),
      IsAffineSpace B S hS D.limitCone.pt →
      ∃ i : I, D.base ≤ i ∧ IsAffineSpace B S hS (D.system.obj (Opposite.op i)))
    (hFinitePresentation : ∀ {Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : Y ⟶ Z),
      IsAlgebraicSpace B S hS Y → IsAlgebraicSpace B S hS Z → IsFinite B S hS g →
      IsFinitePresentation B S hS g → IsSurjective B S hS g → IsAffineSpace B S hS Y →
      IsAffineSpace B S hS Z) :
    X'.1.IsRepresentable :=
  isRepresentable_of_isIntegralHom_of_bijective B S hS hG.1.1 X'.property G.ι
    (isIntegralHom_ι_of_isThickening B S hS hG)
    ⟨pointsMap_injective_of_mono B S hS G.ι, hG.2⟩ hGrep h09YA h07SQ hFinitePresentation

/-- **Stacks 05ZR, morphism form, through Stacks 07VV for an integral morphism.** Let `S` be a
scheme and let `i : X ⟶ X'` be a thickening of algebraic spaces over `S`, in the morphism form
of `AlgebraicGeometry.Space.IsThickeningHom`. If `X` is (representable by) a scheme, then so is
`X'`, given the three hypotheses of the library's Stacks 07VT. The same statement with no
hypotheses is `AlgebraicGeometry.Space.isRepresentable_of_isThickeningHom_of_isRepresentable`.

A thickening is a closed immersion, hence integral by Stacks 081Y, it is a monomorphism and
therefore injective on points, and it is surjective on points, so Stacks 07VV applies in the
direction that goes from the source. -/
theorem isRepresentable_of_isThickeningHom {X X' : AlgebraicSpaces B S hS} (i : X ⟶ X')
    (hi : IsThickeningHom B S hS i) (hXrep : X.1.IsRepresentable)
    (h09YA : ∀ {Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : Y ⟶ Z),
      IsAlgebraicSpace B S hS Y → IsAlgebraicSpace B S hS Z → IsIntegralHom B S hS g →
      IsQuasiCompactSpace B S hS Z →
      IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Z →
      IntegralFiniteSystem B S hS g)
    (h07SQ : ∀ {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
      (D : DescentSituation B S hS B.contains_terminal I),
      IsAffineSpace B S hS D.limitCone.pt →
      ∃ j : I, D.base ≤ j ∧ IsAffineSpace B S hS (D.system.obj (Opposite.op j)))
    (hFinitePresentation : ∀ {Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : Y ⟶ Z),
      IsAlgebraicSpace B S hS Y → IsAlgebraicSpace B S hS Z → IsFinite B S hS g →
      IsFinitePresentation B S hS g → IsSurjective B S hS g → IsAffineSpace B S hS Y →
      IsAffineSpace B S hS Z) :
    X'.1.IsRepresentable := by
  have := hi.mono
  exact isRepresentable_of_isIntegralHom_of_bijective B S hS X.property X'.property i.hom
    (isIntegralHom_of_isClosedImmersion B S hS i.hom hi.isClosedImmersion)
    ⟨pointsMap_injective_of_mono B S hS i.hom, hi.surjective_pointsMap⟩ hXrep
    h09YA h07SQ hFinitePresentation

end AlgebraicGeometry.Space

end
