module

public import Mathlib.CategoryTheory.Sites.Coverage

import StacksCore.Tactic.StacksAttribute

/-!
# The topology associated to a site

Stacks 00ZD constructs the topology associated to a site: given the coverings of `C`, the
associated Grothendieck topology is the smallest topology for which every covering generates a
covering sieve.

With the coverings packaged as a coverage, that is Mathlib's
`CategoryTheory.Coverage.toGrothendieck`.
-/

@[expose] public section

-- The former @[stacks 00ZD] declarations are now the Mathlib declaration.
add_to_stacks 00ZD "the Grothendieck topology associated to a site, i.e. the smallest topology for
  which every covering of the site generates a covering sieve"
  CategoryTheory.Coverage.toGrothendieck
add_to_sga "3 IV 4.2.2" "special case" CategoryTheory.Coverage.toGrothendieck
add_to_sga "4 II 1.1.6" "special case" CategoryTheory.Coverage.toGrothendieck
add_to_sga "4 II 1.3.1" "generated topology" CategoryTheory.Coverage.toGrothendieck
