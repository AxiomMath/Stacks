module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Localization.AbelianSheavesOnALocalizedSite
import StacksCore.Tactic.StacksAttribute

/-!
# Derived base change for the big étale topology on algebraic spaces

For a cartesian square of algebraic spaces over a base scheme, the inverse image of a derived
direct image taken in the big étale topology is naturally isomorphic to the derived direct image
of the inverse image. The statement applies in particular when the base-change morphism is
étale.

The category of algebraic spaces over the base scheme, equipped with its big étale topology, is
a site, and the fibre product in the source is a cartesian square in that site. The base-change
isomorphism `Stacks.Cohomology.Localization.derivedOverPushforwardBaseChangeIso` applies to that
square without any further hypothesis on the base-change morphism. Its conclusion is an
isomorphism of functors, natural in the derived object.

## Main results

* `Stacks.Cohomology.Localization.derivedOverPushforwardBaseChangeIso`, from
  `StacksFrontier.CategoryTheory.Sites.Cohomology.Localization.AbelianSheavesOnALocalizedSite`: the
  base-change isomorphism for derived direct images along a cartesian square of a site.

## References

* [Stacks Project, Tag 0DGA](https://stacks.math.columbia.edu/tag/0DGA)
* [Stacks Project, Tag 0EZ0](https://stacks.math.columbia.edu/tag/0EZ0)
-/

@[expose] public section

add_to_stacks 0DGA "big_base_change_abelian"
  Stacks.Cohomology.Localization.derivedOverPushforwardBaseChangeIso

end
