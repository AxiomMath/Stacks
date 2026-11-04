module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Algebraization.DepthInequalities
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionCriteria.AffineExistence
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionCriteria.PrincipalNonzerodivisor
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.PrincipalFormalLocusDimensionCriterion
public import StacksFrontier.RingTheory.Dualizing.UniversallyCatenary

/-!
# Extending a coherent formal module over a principal ideal under the `(2, 3)`-inequalities

Fix an algebraization situation: a Noetherian ring `A` with ideals `I ⊆ 𝔞`, the affine scheme
`X = Spec(A)`, its closed subschemes `Y = V(I)` and `Z = V(𝔞)`, and the open complement
`U = X ∖ Z`.  Let `(ℱₙ)` be an object of `Coh(U, I𝒪_U)`.  [Stacks, Tag 0EJ9] asserts that
`(ℱₙ)` extends to `X` in the sense of [Stacks, Tag 0EIM] as soon as

1. `A` is local and `𝔞 = 𝔪` is the maximal ideal,
2. `A` has a dualizing complex,
3. `I = (f)` is a principal ideal, and
4. `(ℱₙ)` satisfies the `(2, 3)`-inequalities of [Stacks, Tag 0EJ3];

and that, in particular, over an `I`-adically complete `A` the system is then the completion of
a coherent `𝒪_U`-module.

Both assertions are proved without carried hypotheses in the sibling module
`ExtensionPrincipalLocalTheorem`, as
`Stacks.Algebraization.extendsToX_of_isLocalRing_of_eq_span_singleton` and
`Stacks.Algebraization.essImage_completionFunctor_of_isLocalRing_of_eq_span_singleton`.  This
file no longer contains declarations; its imports are kept for the modules that import it.

## References

* [Stacks Project, Tag 0EJ9](https://stacks.math.columbia.edu/tag/0EJ9)
* [Stacks Project, Tag 0EHC](https://stacks.math.columbia.edu/tag/0EHC), the situation.
* [Stacks Project, Tag 0EIM](https://stacks.math.columbia.edu/tag/0EIM), the conclusion.
* [Stacks Project, Tag 0EJ3](https://stacks.math.columbia.edu/tag/0EJ3), the inequalities.
-/
