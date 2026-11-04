module

public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
import StacksCore.Tactic.StacksAttribute

/-!
# Sheaves on the Zariski site of a topological space

Stacks 00VO asserts that for `Type`-valued presheaves on a topological space `X` the
site-theoretic sheaf condition for the Grothendieck topology on the opens of `X` and the classical
unique-gluing condition of Stacks 006T coincide, so that a sheaf on the site `X_Zar` is the same
thing as a sheaf on the space `X`.

That equivalence is Mathlib's `TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing_types`, whose two
sides are `TopCat.Presheaf.IsSheaf` and `TopCat.Presheaf.IsSheafUniqueGluing`.

## References

* [Stacks Project, Tag 00VO](https://stacks.math.columbia.edu/tag/00VO)
-/

@[expose] public section

add_to_stacks 00VO "the site-theoretic and the classical (unique gluing) sheaf conditions for a
  `Type`-valued presheaf on a topological space coincide"
  TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing_types
