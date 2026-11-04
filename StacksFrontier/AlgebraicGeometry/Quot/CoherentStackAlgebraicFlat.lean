module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackAlgebraicUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat

/-!
# Algebraicity of the stack of coherent sheaves, flat case (Stacks 08WC)

Let `S` be a scheme and `f : X ⟶ B` a morphism of algebraic spaces over `S` which is of finite
presentation, separated and flat. Then `Coh_{X/B}` is an algebraic stack over `S`.

As the footnote of the source says, flatness is not needed: the statement is the case of a flat
`f` of `AlgebraicGeometry.Space.CoherentSituation.isAlgebraicStack_coherentCFG` (the general case,
Stacks 09DS, see Section 08WB).

## Main results

* `AlgebraicGeometry.Space.CoherentSituation.isAlgebraicStack_coherentCFG_of_isFlat`: for `f` of
  finite presentation, separated and flat, `Coh_{X/B}` is an algebraic stack.

## References

* [Stacks Project, Tag 08WC](https://stacks.math.columbia.edu/tag/08WC)
* [Stacks Project, Tag 08WB](https://stacks.math.columbia.edu/tag/08WB)
* [Stacks Project, Tag 09DS](https://stacks.math.columbia.edu/tag/09DS)
-/

@[expose] public noncomputable section

namespace AlgebraicGeometry.Space.CoherentSituation

universe u

/-- **Algebraicity of the stack of coherent sheaves, flat case.** Let `S` be a scheme and
`f : X ⟶ B` a morphism of algebraic spaces over `S` which is of finite presentation (a field of the
standing datum `D` of Situation 08KB), separated and flat. Then `Coh_{X/B}` is an algebraic stack
over `S`. -/
@[stacks 08WC]
theorem isAlgebraicStack_coherentCFG_of_isFlat.{w} {B : BigFppfSite.{u}} {S : Scheme.{u}}
    {hS : B.Contains S} (D : CoherentSituation B S hS) (hsep : IsSeparated B S hS D.f.hom)
    (hflat : IsFlat B S hS D.f.hom) :
    Stack.IsAlgebraicStack.{u, w} B S hS D.coherentCFG.val := by
  clear hflat
  exact D.isAlgebraicStack_coherentCFG hsep

end AlgebraicGeometry.Space.CoherentSituation

end
