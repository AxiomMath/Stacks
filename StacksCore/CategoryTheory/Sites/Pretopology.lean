module

public import Mathlib.CategoryTheory.Sites.Sheaf
import StacksCore.Tactic.StacksAttribute

/-!
# The chaotic (indiscrete) site

Mathlib coverage for Stacks chapter 7 (Sites and Sheaves), section 6 (Sites).

For a category `C`, the *chaotic* or *indiscrete* topology is the one whose coverings are the
singleton isomorphisms. Stacks 07GE asserts that these coverings form a pretopology, and that the
sheaves on the resulting site are exactly the presheaves on `C`.

Both assertions are Mathlib's. `CategoryTheory.Pretopology.trivial` is the chaotic pretopology,
and Mathlib already tags it `@[stacks 07GE]`. For the second assertion,
`CategoryTheory.Pretopology.toGrothendieck_bot` says the chaotic pretopology generates the bottom
topology, in which only the maximal sieve covers, and `CategoryTheory.sheafBotEquivalence` is the
equivalence between sheaves for the bottom topology and presheaves.

## References

* [Stacks Project, Tag 07GE](https://stacks.math.columbia.edu/tag/07GE)
-/

@[expose] public section

add_to_stacks 07GE "the chaotic pretopology generates the bottom topology, in which only the
  maximal sieve covers" CategoryTheory.Pretopology.toGrothendieck_bot
add_to_stacks 07GE "sheaves on the chaotic site are the presheaves: the forgetful functor from
  sheaves for the bottom topology to presheaves is an equivalence of categories"
  CategoryTheory.sheafBotEquivalence
add_to_sga "3 IV 4.4.2" "final observation" CategoryTheory.sheafBotEquivalence
