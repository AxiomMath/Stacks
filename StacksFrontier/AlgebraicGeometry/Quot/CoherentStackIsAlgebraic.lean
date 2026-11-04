module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackAlgebraicUnconditional
public import StacksFrontier.AlgebraicGeometry.Quot.PicardStackOpenImmersion

/-!
# Algebraicity of the stack of coherent sheaves (Stacks 09DS)

Let `S` be a scheme and `f : X ⟶ Y` a morphism of algebraic spaces over `S`. Stacks 09DS says that
if `f` is of finite presentation and separated, the stack `Coh_{X/Y}` of Situation 08KB is an
algebraic stack over `S`.

## Main results

* `AlgebraicGeometry.Space.isAlgebraicStack_coherentCFG`: for `f` of finite presentation and
  separated, `Coh_{X/Y}` is an algebraic stack.

## References

* [Stacks Project, Tag 09DS](https://stacks.math.columbia.edu/tag/09DS)
* [Stacks Project, Tag 08KB](https://stacks.math.columbia.edu/tag/08KB)
-/

@[expose] public noncomputable section

namespace AlgebraicGeometry.Space

universe u

/-- **Algebraicity of the stack of coherent sheaves.** Let `S` be a scheme and let `f : X ⟶ Y` be a
morphism of algebraic spaces over `S`, of finite presentation (part of the standing datum `D` of
Situation 08KB) and separated. Then `Coh_{X/Y}` is an algebraic stack over `S`. -/
@[stacks 09DS]
theorem isAlgebraicStack_coherentCFG.{w} {B : BigFppfSite.{u}} {S : Scheme.{u}}
    {hS : B.Contains S} (D : CoherentSituation B S hS) (hsep : IsSeparated B S hS D.f.hom) :
    Stack.IsAlgebraicStack.{u, w} B S hS (coherentCFG D).val :=
  D.isAlgebraicStack_coherentCFG hsep

end AlgebraicGeometry.Space

end
