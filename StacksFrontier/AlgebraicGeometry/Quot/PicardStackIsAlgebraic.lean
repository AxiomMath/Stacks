module

public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackAlgebraicUnconditional
public import StacksFrontier.AlgebraicGeometry.Quot.PicardStackAlgebraic

/-!
# The Picard stack is algebraic

Let `S` be a scheme and `f : X ⟶ Y` a morphism of algebraic spaces over `S`. If `f` is flat, of
finite presentation and proper, then `Picardstack_{X/Y}` is an algebraic stack
([Stacks, Tag 0D04]).

The source's proof: the map `Pic_{X/Y} ⟶ Coh_{X/Y}` is representable by open immersions
([Stacks, Tag 0D03]), `Coh_{X/Y}` is algebraic ([Stacks, Tag 09DS]; a proper morphism is
separated), and a category with a morphism representable by algebraic spaces to an algebraic stack
is algebraic ([Stacks, Tag 05UM]). This is
`AlgebraicGeometry.Space.isAlgebraicStack_picardCFG_of_h09DS` with Stacks 09DS supplied by
`AlgebraicGeometry.Space.CoherentSituation.isAlgebraicStack_coherentCFG`.

## Main results

* `AlgebraicGeometry.Space.isAlgebraicStack_picardCFG`: `Picardstack_{X/Y}` is an algebraic
  stack for `f` flat, of finite presentation and proper (Stacks 0D04).

## References

* [Stacks Project, Tag 0D04](https://stacks.math.columbia.edu/tag/0D04)
* [Stacks Project, Tag 09DS](https://stacks.math.columbia.edu/tag/09DS)
-/

@[expose] public section

namespace AlgebraicGeometry.Space

universe u w

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Stacks 0D04: the Picard stack is algebraic.** Let `S` be a scheme and `f : X ⟶ Y` a
morphism of algebraic spaces over `S` which is flat, of finite presentation (a field of the
standing datum `D` of Situation 08KB) and proper. Then `Picardstack_{X/Y}` is an algebraic
stack. -/
theorem isAlgebraicStack_picardCFG (D : CoherentSituation B S hS) (hflat : IsFlat B S hS D.f.hom)
    (hproper : IsProper B S hS D.f.hom) :
    Stack.IsAlgebraicStack.{u, w} B S hS
      (picardCFG (modulePushforwardCoherence B S hS) D.toPicardSituation).val :=
  isAlgebraicStack_picardCFG_of_h09DS (fun D' h => D'.isAlgebraicStack_coherentCFG h) D hflat
    hproper

end AlgebraicGeometry.Space

end
