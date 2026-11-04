module

public import StacksFrontier.AlgebraicGeometry.Descent.Germs.CohenMacaulayFiber
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.FibreStalk
public import StacksFrontier.AlgebraicGeometry.Morphisms.Smooth.DimensionFormula
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.CohenMacaulay.Defs
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.CohenMacaulay.Representable
public import StacksFrontier.AlgebraicGeometry.Spaces.Smooth

/-!
# A smooth morphism of algebraic spaces is Cohen–Macaulay

Smoothness and Cohen–Macaulayness of a morphism of algebraic spaces over a scheme `S` are both
tested on pointed étale scheme charts, so the implication between them transfers chartwise from
the corresponding statement about schemes: a smooth morphism of schemes is flat and its fibres
are smooth over residue fields, hence Cohen–Macaulay.

## Main results

* `AlgebraicGeometry.Space.isCohenMacaulay_of_isSmooth`: a smooth morphism of algebraic spaces
  over `S` is Cohen–Macaulay in the sense of Tag 0E0V.

## Implementation notes

Nothing here needs the source or the target to be an algebraic space: both conditions are
quantifiers over the same charts, and the algebraic-space axioms enter only where a chart is
produced, which this implication never does.

On a pointed chart the flatness conjunct is `MorphismOfGerms.isFlat_ofSchemeHom`, a smooth
morphism of schemes being flat, and the fibre conjunct is Cohen–Macaulayness of the stalk of the
fibre: the fibre is locally Noetherian because a smooth morphism is locally of finite
presentation, and Cohen–Macaulay by `AlgebraicGeometry.isCohenMacaulay_fiber_of_smooth`, which is
Tags 00T5 and 00SB.

## References

* [Stacks Project, Tag 00SB](https://stacks.math.columbia.edu/tag/00SB)
* [Stacks Project, Tag 00T5](https://stacks.math.columbia.edu/tag/00T5)
* [Stacks Project, Tag 0E0V](https://stacks.math.columbia.edu/tag/0E0V)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **A smooth morphism of algebraic spaces over `S` is Cohen–Macaulay.** On each pointed étale
chart the morphism of schemes is smooth, hence flat with Cohen–Macaulay locally Noetherian
fibres, which are the two conjuncts of Cohen–Macaulayness at the selected point. -/
theorem isCohenMacaulay_of_isSmooth (f : X ⟶ Y) (hf : IsSmooth B S hS f) :
    IsCohenMacaulay B S hS f := by
  intro x
  constructor <;> intro c <;>
    have _ : Smooth ((BigFppfOver.toScheme B S hS).map c.h) :=
      hf c.U c.V c.a c.b c.h c.a_etale c.b_etale c.comm
  · exact MorphismOfGerms.isFlat_ofSchemeHom _ (c.sourcePoint B S hS)
  · have _ : IsLocallyNoetherian
        (((BigFppfOver.toScheme B S hS).map c.h).fiber
          ((BigFppfOver.toScheme B S hS).map c.h (c.sourcePoint B S hS))) :=
      isLocallyNoetherian_fiber_of_locallyOfFinitePresentation _ _
    rw [hasCohenMacaulayFiberLocalRing_ofSchemeHom_iff_of_isNoetherianRing]
    exact isCohenMacaulayLocalRing_stalk _
      (isCohenMacaulay_fiber_of_smooth ((BigFppfOver.toScheme B S hS).map c.h) _) _

end AlgebraicGeometry.Space

end
