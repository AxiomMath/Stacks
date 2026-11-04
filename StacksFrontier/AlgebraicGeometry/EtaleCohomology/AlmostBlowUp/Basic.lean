module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Blowup.ReesAlgebra.BlowUp
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentationPoint
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.AlmostBlowUp.SupportedSections

/-!
# Almost blowup squares

An almost blowup square has a finitely presented closed centre, a locally principal
inverse-image centre, and a proper finitely presented modification: removing from the
modification the sections of its structure sheaf supported on the inverse-image centre leaves
the blowup of the centre.

## Main definitions

* `AlgebraicGeometry.IsAlmostBlowUpSquare` describes the square.

## Implementation notes

The upper-left corner of the square is the inverse-image closed subscheme defined by `I.comap b`.
The blowup identification is an isomorphism *over* the base scheme, not merely an isomorphism of
underlying schemes, which is why it is phrased in the category of schemes over `X`.

## References

* [Stacks Project, Tag 0EWM](https://stacks.math.columbia.edu/tag/0EWM)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- An almost blowup square with centre `I.subscheme` and modification `b`. The exceptional
closed subscheme is `(I.comap b).subscheme`. -/
@[stacks 0EWM]
public structure IsAlmostBlowUpSquare {X X' : Scheme.{u}}
    (I : X.IdealSheafData) (b : X' ⟶ X) : Prop where
  /-- The centre is a finitely presented closed subscheme. -/
  center_finitePresentation : FinitePresentation I.subschemeι
  /-- The inverse-image centre is locally principal. -/
  exceptional_locallyPrincipal : Stacks.Divisors.IsLocallyPrincipal (I.comap b)
  /-- The modification is proper. -/
  proper : IsProper b
  /-- The modification is of finite presentation. -/
  finitePresentation : FinitePresentation b
  /-- Removing the sections supported on the inverse-image centre gives the blowup of the
  centre, as a scheme over `X`. -/
  blowUp : Nonempty
    (Over.mk ((supportedSectionsIdeal (I.comap b).support).subschemeι ≫ b) ≅
      Over.mk (blowUpToBase I))

add_to_stacks 0EV6 "almost_blow_up_square" AlgebraicGeometry.IsAlmostBlowUpSquare

end AlgebraicGeometry

end
