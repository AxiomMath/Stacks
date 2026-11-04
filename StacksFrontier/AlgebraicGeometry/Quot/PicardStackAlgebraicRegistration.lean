module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.PicardStackIsAlgebraic

/-!
# The Picard stack is algebraic

Let `S` be a scheme and `f : X ⟶ B` a morphism of algebraic spaces over `S`. If `f` is flat, of
finite presentation and proper, then `Picardstack_{X/B}` is an algebraic stack
([Stacks, Tag 0D04]).

This is `AlgebraicGeometry.Space.isAlgebraicStack_picardCFG`, whose hypotheses are the standing
datum `D` of Situation 08KB, which contains `f` and its finite presentation, together with the
flatness `hflat` and the properness `hproper` of `f`. Stacks 0D03 and 05UM give
`AlgebraicGeometry.Space.isAlgebraicStack_picardCFG_of_h09DS`, and Stacks 09DS is
`AlgebraicGeometry.Space.CoherentSituation.isAlgebraicStack_coherentCFG`, which applies because a
proper morphism is separated.

## References

* [Stacks Project, Tag 0D04](https://stacks.math.columbia.edu/tag/0D04)
* [Stacks Project, Tag 0D03](https://stacks.math.columbia.edu/tag/0D03)
* [Stacks Project, Tag 05UM](https://stacks.math.columbia.edu/tag/05UM)
* [Stacks Project, Tag 09DS](https://stacks.math.columbia.edu/tag/09DS)
-/

@[expose] public section

add_to_stacks 0D04 "the full statement. f : X ⟶ B is flat (hflat), of finite presentation \
(a field of the standing datum D of Situation 08KB) and proper (hproper); then Picardstack_{X/B} \
is an algebraic stack. Nothing is assumed beyond the source's hypotheses."
  AlgebraicGeometry.Space.isAlgebraicStack_picardCFG

end
