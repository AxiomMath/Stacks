module

public import StacksFrontier.CategoryTheory.FiberedInSets.TwoCategory
public import StacksCore.Tactic.StacksAttribute

/-!
# Categories fibred in sets (Stacks 0043)

Stacks Tag `0043`: a *category fibred in sets*, or *category fibred in
discrete categories*, is a category fibred in groupoids all of whose fibre categories are
discrete.

The library's predicate is `CategoryTheory.Functor.IsFiberedInSets`, stated through the equivalent
unique-lift property (a discrete fibration). `CategoryTheory.Functor.isFiberedInSets_iff` proves it
is exactly Stacks' definition: `p` is fibred in groupoids (`IsFiberedInGroupoids`, Stacks `003T`)
and every fibre `p.Fiber U` is discrete (`CategoryTheory.IsDiscrete`: its only morphisms are
identities). This file registers the predicate for the tag.

## References

* [Stacks Project, Tag 0043](https://stacks.math.columbia.edu/tag/0043)
-/

add_to_stacks 0043 "Stated through the equivalent unique-lift property; \
`Functor.isFiberedInSets_iff` identifies it with Stacks' definition: fibred in groupoids with \
discrete fibre categories." CategoryTheory.Functor.IsFiberedInSets
