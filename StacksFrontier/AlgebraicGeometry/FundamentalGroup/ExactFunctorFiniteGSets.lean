module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GaloisCategories.Exactness

/-!
# Exact functors on finite continuous group actions

Let `G` be a topological group. The category `Finite-G-Sets` of finite discrete sets with a
continuous `G`-action is a Galois category, with the underlying-set functor as a fibre functor.
Stacks Tag 0BMV says that an *exact* functor `F : Finite-G-Sets ⥤ Type` — one preserving
finite limits and finite colimits — all of whose values are finite, is isomorphic to the
underlying-set functor.

The proof has two halves. First, exactness forces `F` to reflect isomorphisms: a mono `i` which
`F` inverts splits off a direct summand whose `F`-image is empty, and a nonempty object of a
Galois category has nonempty image under any exact functor, so that summand is initial. Hence `F`
factors through `FintypeCat` as a second fibre functor on `Finite-G-Sets`. Second, any two fibre
functors on a Galois category are isomorphic: natural transformations `F ⟶ H` are the sections of
`H` over the cofiltered system of pointed Galois objects of `F`, that system has nonempty finite
values, so a section exists; a transformation in each direction composes to an endomorphism of a
fibre functor, which is automatically invertible.

That `Finite-G-Sets` is itself a Galois category is obtained by exhibiting
`Action.IsContinuous` as a Galois subcategory of `Action FintypeCat G`: continuity is inherited by
subobjects along injections, and closed under finite limits and finite colimits because the
underlying-set functor creates them and the index diagram's actions are continuous.

## Main results

* `Stacks.FundamentalGroup.nonempty_iso_forget_of_preservesFiniteLimits_and_colimits` — an exact
  functor on `Finite-G-Sets` with finite values is isomorphic to the underlying-set functor.

## Implementation notes

Nothing is declared here. Both halves of the argument above are the repository's canonical
declarations in `CategoryTheory`: the Galois-subcategory structure of the finite continuous
`G`-sets is in
`StacksFrontier/AlgebraicGeometry/FundamentalGroup/GaloisCategories/ContinuousActions.lean`, and
the exactness argument, with `@[stacks 0BMV]` registered on it, is in
`StacksFrontier/AlgebraicGeometry/FundamentalGroup/GaloisCategories/Exactness.lean`. The conclusion
is re-exported into `Stacks.FundamentalGroup` here so that the consumers spelling it with this
prefix name that constant.

## References

* [Stacks Project, Tag 0BMV](https://stacks.math.columbia.edu/tag/0BMV)
-/

@[expose] public section

namespace Stacks.FundamentalGroup

export CategoryTheory (nonempty_iso_forget_of_preservesFiniteLimits_and_colimits)

end Stacks.FundamentalGroup

end
