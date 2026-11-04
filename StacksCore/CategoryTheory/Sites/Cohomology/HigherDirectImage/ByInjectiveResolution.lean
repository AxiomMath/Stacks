module

public import Mathlib.CategoryTheory.Abelian.RightDerived
import StacksCore.Tactic.StacksAttribute

/-!
# Computing higher direct images from an injective resolution

Let `f : X ⟶ Y` be a continuous map of topological spaces, or more generally a morphism of
sites. The higher direct images `R^i f_*` are the right derived functors of the direct image
functor `f_*` on abelian sheaves, and Stacks 071F records how they are computed: choose an
injective resolution `F ⟶ I^•` of an abelian sheaf `F`, apply `f_*` degreewise, and take
cohomology. The Stacks Project writes the result as the equality
`R^i f_* F = H^i (f_* I^•)`.

Mathlib already proves this, in the generality of an arbitrary additive functor between
abelian categories with enough injectives, as the canonical isomorphism
`CategoryTheory.InjectiveResolution.isoRightDerivedObj` between the value of the right derived
functor and the cohomology of the image of a chosen injective resolution. Specialising the
functor to the direct image of abelian sheaves gives exactly the displayed equation, so this
file only records the tag against Mathlib's isomorphism rather than restating it.

## Main results

* `CategoryTheory.InjectiveResolution.isoRightDerivedObj` (in Mathlib): the value of the
  `n`-th right derived functor of an additive functor `F` at an object `X` is canonically
  isomorphic to the `n`-th cohomology of `F` applied to any injective resolution of `X`.

## Implementation notes

The source states an equality of objects; a formalisation can only produce a canonical
isomorphism, since the right derived functor is defined through a *chosen* injective
resolution and the statement compares it with an *arbitrary* one. That isomorphism is
natural in the object, by `InjectiveResolution.isoRightDerivedObj_hom_naturality`, which is
the content the equality is used for.

## References

* [Stacks Project, Tag 071F](https://stacks.math.columbia.edu/tag/071F)
-/

@[expose] public section

add_to_stacks 071F "The canonical computation by a chosen injective resolution."
  CategoryTheory.InjectiveResolution.isoRightDerivedObj
