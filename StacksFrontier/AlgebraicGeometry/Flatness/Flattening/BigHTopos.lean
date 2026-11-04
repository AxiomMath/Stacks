module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.Localization.OverPullbackMorphism

/-!
# Agreement of the two big h morphisms of topoi

For a morphism in a big h site, postcomposition between the slice sites and its right
adjoint, base change, induce the same morphism of topoi.

## Main results

* `StacksRelocalization.sheafPushforwardOverMapIso` is the canonical natural isomorphism
  between the direct images induced by these functors.

## Implementation notes

The big h slice topology is the topology induced on a slice category, so the general
relocalization isomorphism is the statement to record here; it also retains naturality in
the sheaf. It is stated for a site whose category is small in Lean's sense, which the
size-bounded category of schemes underlying a big h site is not — its objects form a type
one universe above its morphisms — so the big h instance is obtained separately, as
`AlgebraicGeometry.bigHMorphismOfTopoi_pushforwardIso`, from the universe-polymorphic
comparison `CategoryTheory.Adjunction.sheafPushforwardCocontinuousIso` that both rest on.

## References

* [Stacks Project, Tag 0EU6](https://stacks.math.columbia.edu/tag/0EU6)
-/

@[expose] public section

add_to_stacks 0EU6 "same_topos" StacksRelocalization.sheafPushforwardOverMapIso
