module

public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackAlgebraic
public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.FlatAlgebraizationExists

/-!
# The stack of coherent sheaves is algebraic

Let `S` be a scheme and `f : X ⟶ Y` a morphism of algebraic spaces over `S` which is of finite
presentation and separated. Then `Coh_{X/Y}` is an algebraic stack over `S` ([Stacks, Tag 09DS]).

The proof is
`AlgebraicGeometry.Space.CoherentSituation.isAlgebraicStack_coherentCFG_of_existence`, whose one
input, Grothendieck's existence theorem for algebraic spaces ([Stacks, Tag 0CXB]), is
`AlgebraicGeometry.Space.InverseSystemExistenceSituation.exists_flat_algebraization`.

## Main results

* `AlgebraicGeometry.Space.CoherentSituation.isAlgebraicStack_coherentCFG`: `Coh_{X/Y}` is an
  algebraic stack, for `f` of finite presentation and separated. It carries no `@[stacks]`
  attribute here; it is the input of the proof of Stacks 0D04.

## References

* [Stacks Project, Tag 09DS](https://stacks.math.columbia.edu/tag/09DS)
* [Stacks Project, Tag 0CXB](https://stacks.math.columbia.edu/tag/0CXB)
-/

@[expose] public section

namespace AlgebraicGeometry.Space.CoherentSituation

universe u

/-- **The stack of coherent sheaves is algebraic.** Let `S` be a scheme and `f : X ⟶ Y` a
morphism of algebraic spaces over `S` which is of finite presentation (a field of the standing
datum `D` of Situation 08KB) and separated. Then `Coh_{X/Y}` is an algebraic stack over `S`. -/
theorem isAlgebraicStack_coherentCFG.{w} {B : BigFppfSite.{u}} {S : Scheme.{u}}
    {hS : B.Contains S} (D : CoherentSituation B S hS) (hsep : IsSeparated B S hS D.f.hom) :
    Stack.IsAlgebraicStack.{u, w} B S hS D.coherentCFG.val :=
  D.isAlgebraicStack_coherentCFG_of_existence hsep
    InverseSystemExistenceSituation.exists_flat_algebraization

end AlgebraicGeometry.Space.CoherentSituation

end
