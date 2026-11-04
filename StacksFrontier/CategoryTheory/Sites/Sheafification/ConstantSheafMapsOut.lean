module

public import Mathlib.CategoryTheory.Sites.GlobalSections
public import StacksCore.Tactic.StacksAttribute

/-!
# Morphisms out of a constant sheaf

Stacks tag 0H7J: the constant sheaf `⟨E⟩` with value `E` on a site `(C, J)` is the
sheafification of the constant presheaf with value `E`, and it is characterized by the rule
that morphisms `⟨E⟩ ⟶ F` into a sheaf `F` are the same as maps of sets `E → Γ(C, F)`. The
construction is Mathlib's `CategoryTheory.constantSheaf` and the characterization is its
adjunction `CategoryTheory.constantSheafΓAdj`, whose hom-set bijection is exactly the stated
rule, so nothing is reproved here. That Mathlib's `Γ` agrees with the `Mor(*, F)` description
of global sections used by the source is `CategoryTheory.Sheaf.ΓNatIsoCoyoneda`, and the global
sections functor exists for sheaves of types by
`CategoryTheory.hasGlobalSectionsFunctor_of_hasLimitsOfShape`.

## References

* [Stacks Project, Tag 0H7J](https://stacks.math.columbia.edu/tag/0H7J)
-/

@[expose] public section

add_to_stacks 0H7J "the constant sheaf" CategoryTheory.constantSheaf
add_to_stacks 0H7J "maps out of the constant sheaf" CategoryTheory.constantSheafΓAdj
