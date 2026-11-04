module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeOfIntegralBijection
public import StacksFrontier.AlgebraicGeometry.Spaces.ThickeningMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.EtaleSite

/-!
# A thickening of a scheme is a scheme (Stacks 05ZR)

Let `S` be a scheme and let `X ⊂ X'` be a thickening of algebraic spaces over `S`. If `X` is
(representable by) a scheme, then so is `X'`. Being a scheme is
`CategoryTheory.Functor.IsRepresentable` for the presheaf underlying the space.

The inclusion of a thickening is integral and bijective on points, so this is Stacks 07VV in
the direction that goes from the source: the hypotheses of
`AlgebraicGeometry.Space.isRepresentable_of_isIntegralHom_of_bijective` are exactly the three
properties of the inclusion of a thickening already recorded in
`StacksFrontier/AlgebraicGeometry/Spaces/Thickenings/EtaleSite.lean`.

## Main results

* `AlgebraicGeometry.Space.isRepresentable_of_isRepresentable_thickening`: **Stacks 05ZR** in
  the subspace form in which Stacks 05ZK, part (1) states a thickening — a closed subspace
  `G ⊂ X'` whose inclusion is surjective on points.
* `AlgebraicGeometry.Space.isRepresentable_of_isThickeningHom`: **Stacks 05ZR** in the
  morphism form `AlgebraicGeometry.Space.IsThickeningHom`, the shape in which thickenings of
  algebraic spaces appear in Stacks 05ZS, 07VX and 0AIC.

## Implementation notes

The thin side of a thickening needs none of this: a closed subspace of a scheme is a scheme
with no hypotheses, which is
`AlgebraicGeometry.Space.isRepresentable_of_isThickening` in
`StacksFrontier/AlgebraicGeometry/Spaces/Thickenings/Scheme.lean`. That file records in its
implementation notes that the direction proved here is absent from the library and that no
declaration in it carries `@[stacks 05ZR]`; that note describes the state of the library
before Stacks 07VV was available and is superseded by this file, which does not alter it.

Both results below carry the three hypotheses `h09YA`, `h07SQ` and `hFinitePresentation`
verbatim from `AlgebraicGeometry.Space.isRepresentable_of_isIntegralHom_of_bijective`, and
hence from `AlgebraicGeometry.Space.isAffineSpace_of_isSurjective_of_universallyClosed`, the
library form of Stacks 07VT. They are passed straight through and are used for nothing else,
so Stacks 05ZR is conditional here on precisely what Stacks 07VT is conditional on and on
nothing further. None of the three is the universally quantified form of the conclusion
below: the first two conclude about inverse systems and the third about affineness of a
target, while the conclusion here is representability of a presheaf. The conditionality is
not avoidable by a different route: the content of Stacks 05ZR beyond topology is that an
algebraic space receiving a surjective universally closed morphism from an affine scheme is
affine, which is Stacks 07VT itself.

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

/-- **Stacks 05ZR.** Let `S` be a scheme and let `G ⊂ X'` be a thickening of algebraic spaces
over `S`, in the subspace form of Stacks 05ZK, part (1). If `G` is (representable by) a
scheme, then so is `X'`.

The inclusion `G.ι` is integral by Stacks 081Y, injective on points because it is a
monomorphism, and surjective on points by the definition of a thickening, so Stacks 07VV
applies in the direction that goes from the source. -/
@[stacks 05ZR "granted the three hypotheses of Stacks 07VT, carried verbatim from Stacks \
07VV and used for nothing else: `h09YA`, the conclusion of Stacks 09YA that an integral \
morphism over a quasi-compact quasi-separated algebraic space is a directed limit of finite \
morphisms of finite presentation; `h07SQ`, the conclusion of Stacks 07SQ that a directed \
system with affine transition morphisms whose limit is affine has an affine stage; and \
`hFinitePresentation`, the case of Stacks 07VT in which the morphism is finite and of finite \
presentation. None is the universally quantified form of this conclusion: the first two \
conclude about inverse systems and the third about affineness of a target, while this \
concludes representability of a presheaf"]
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

/-- **Stacks 05ZR, morphism form.** Let `S` be a scheme and let `i : X ⟶ X'` be a thickening
of algebraic spaces over `S`, in the morphism form of
`AlgebraicGeometry.Space.IsThickeningHom`. If `X` is (representable by) a scheme, then so is
`X'`.

A thickening is a closed immersion, hence integral by Stacks 081Y, it is a monomorphism and
therefore injective on points, and it is surjective on points, so Stacks 07VV applies in the
direction that goes from the source. -/
@[stacks 05ZR "the morphism form, granted the three hypotheses of Stacks 07VT, carried \
verbatim from Stacks 07VV and used for nothing else: `h09YA`, the conclusion of Stacks 09YA \
that an integral morphism over a quasi-compact quasi-separated algebraic space is a directed \
limit of finite morphisms of finite presentation; `h07SQ`, the conclusion of Stacks 07SQ that \
a directed system with affine transition morphisms whose limit is affine has an affine stage; \
and `hFinitePresentation`, the case of Stacks 07VT in which the morphism is finite and of \
finite presentation. None is the universally quantified form of this conclusion: the first \
two conclude about inverse systems and the third about affineness of a target, while this \
concludes representability of a presheaf"]
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
