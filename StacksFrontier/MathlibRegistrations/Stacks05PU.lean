module

public import StacksFrontier.CategoryTheory.EssentiallyConstant.IndObject
public import StacksFrontier.CategoryTheory.EssentiallyConstant.ProObject

/-! Stacks tag 05PU is stated in `StacksFrontier.CategoryTheory.EssentiallyConstant.IndObject`
(clause (1), the filtered case,
as `CategoryTheory.EssentiallyConstantInd.IsEssentiallyConstantWith` and
`CategoryTheory.EssentiallyConstantInd.IsEssentiallyConstantInd`) and in
`StacksFrontier.CategoryTheory.EssentiallyConstant.ProObject` (clause (2), the cofiltered case, as
`CategoryTheory.EssentiallyConstantPro.IsEssentiallyConstantPro`), both of which this module
re-exports.

The routing that formerly stood here, onto `CategoryTheory.Functor.IsEventuallyConstantFrom` and
`CategoryTheory.Functor.IsEventuallyConstantTo`, was incorrect. Mathlib's
`F.IsEventuallyConstantFrom i` asks that `F.map f` be an *isomorphism* for every `f : i ⟶ j`,
whereas Stacks 05PU asks only for a morphism `X → M_i` that is a *retraction* of the cocone leg
`M_i → X`, together with a cofinality condition making the composite
`M_j → X → M_i → M_k` a transition map of the diagram. The Stacks condition is strictly weaker:
it is satisfied whenever the colimit is attained up to a retract, while Mathlib's forces the
diagram to be constant on the coslice at `i`. Dually for `IsEventuallyConstantTo` and clause (2).

The two implications that Mathlib's notions *do* give are proved, in the correct direction, in
`StacksFrontier.CategoryTheory.EssentiallyConstant.Defs` as
`CategoryTheory.isEssentiallyConstantInd_of_isEventuallyConstantFrom` and
`CategoryTheory.isEssentiallyConstantInd_op_of_isEventuallyConstantTo`. -/
