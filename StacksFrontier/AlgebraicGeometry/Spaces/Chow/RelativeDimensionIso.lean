module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.EtalePullbackIdentity
public import StacksFrontier.AlgebraicGeometry.Spaces.EtalePermanence

/-!
# An isomorphism of algebraic spaces has relative dimension zero

An isomorphism `f : X ⟶ Y` of presheaves on the big fppf site of `S`, with `Y` an algebraic
space, has relative dimension `0` in the sense of Stacks 06LR, part (2): it is étale, and an
étale morphism with algebraic target has relative dimension `0` at every point of its source
(Stacks 06LT, 03XU and 04NV, through
`AlgebraicGeometry.Space.hasRelativeDimension_zero_of_isEtale`).  In particular an identity has
relative dimension `0`.

## Main results

* `AlgebraicGeometry.Space.hasRelativeDimension_zero_of_isIso`
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **An isomorphism of algebraic spaces has relative dimension `0`**: it is étale
(`AlgebraicGeometry.Space.isEtale_of_isIso`), and an étale morphism with algebraic target has
relative dimension `0` (`AlgebraicGeometry.Space.hasRelativeDimension_zero_of_isEtale`). -/
theorem hasRelativeDimension_zero_of_isIso (f : X ⟶ Y) [IsIso f]
    (hY : IsAlgebraicSpace B S hS Y) : HasRelativeDimension 0 B S hS f :=
  hasRelativeDimension_zero_of_isEtale B S hS f hY (isEtale_of_isIso B S hS f)

end AlgebraicGeometry.Space

end
