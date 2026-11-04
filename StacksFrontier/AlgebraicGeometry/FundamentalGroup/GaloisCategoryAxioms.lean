module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GaloisCategories.Defs
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GaloisCategories.FiberFunctor

/-!
# Galois categories with a fixed fibre functor

A category `C` together with a functor `F : C ⥤ Type w` is a *Galois category* when `C` has finite
limits and finite colimits, every object of `C` is a finite coproduct of connected objects, every
fibre `F.obj X` is finite, `F` is exact, and `F` reflects isomorphisms. This is the axiom system
of Stacks Tag 0BMY, and it retains the fibre functor as part of the data, unlike Mathlib's
`CategoryTheory.GaloisCategory`, which only asserts that some fibre functor exists.

From the axioms one reads off immediately that an object is initial exactly when its fibre is
empty (Stacks Tag 0BN0): initiality is a colimit over the empty diagram, exactness means `F`
preserves it, and reflecting isomorphisms means `F` reflects it; on the side of types, an initial
object is an empty type.

## Main definitions

The notion is *not* declared here. `CategoryTheory.IsGaloisCategory` in
`StacksFrontier.AlgebraicGeometry.FundamentalGroup.GaloisCategories.Defs` is the repository's
canonical declaration, and it carries the Tag 0BMY attribute. This file does
not declare a second copy of the class: a copy with the same fields would be a distinct constant,
and theorems stated about one would not compose with the other even though both read as the
Tag 0BMY axioms. This file aliases the canonical class and
the initial-object criterion into the `Stacks.FundamentalGroup` namespace, so the two spellings
are one constant.

* `Stacks.FundamentalGroup.IsGaloisCategory` — the Galois category axioms for a fixed
  type-valued functor; an alias of `CategoryTheory.IsGaloisCategory`.

## Main results

* `Stacks.FundamentalGroup.isInitial_iff_isEmpty_fiber` — an object of a Galois category is
  initial if and only if its fibre is empty; an alias of
  `CategoryTheory.isInitial_iff_isEmpty_fiber`.

## References

* [Stacks Project, Tag 0BMY](https://stacks.math.columbia.edu/tag/0BMY)
* [Stacks Project, Tag 0BN0](https://stacks.math.columbia.edu/tag/0BN0)
* [SGA1, Exposé V, Definition 5.1]
-/

@[expose] public section

namespace Stacks.FundamentalGroup

export CategoryTheory (IsGaloisCategory isInitial_iff_isEmpty_fiber)

end Stacks.FundamentalGroup
