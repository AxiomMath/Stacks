module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FppfEtaleComparison.Situation
import StacksCore.Tactic.StacksAttribute

/-!
# The properties of Situation 0EZ3 in Stacks 0F0H, as Stacks tags

Stacks 0F0H shows that the fppf and étale sites of a big site of schemes, with the class of
finite morphisms and the subcategories `𝒜'_X` of abelian sheaves on the big étale sites pulled
back from the small étale sites, form an instance of Situation 0EZ3. The ingredients are
proved in `StacksFrontier.AlgebraicGeometry.EtaleCohomology.FppfEtaleComparison.Situation`; this
file records the tag on each of them.

## Main results

* `AlgebraicGeometry.fppfEtaleWeakSerre_isWeakSerreClass` — `𝒜'_X` is a weak Serre subcategory.
* `AlgebraicGeometry.fppfEtaleFinite_baseChange` — property (0EZ4).
* `AlgebraicGeometry.fppfEtaleWeakSerre_overMapPullback` — property (0EZ5).
* `AlgebraicGeometry.fppfEtaleWeakSerre_isSheaf_fppf` — property (0EZ6).
* `AlgebraicGeometry.fppfCovering_refinement_etale_finite` — property (0EZ8).

## References

* [Stacks Project, Tag 0F0H](https://stacks.math.columbia.edu/tag/0F0H)
* [Stacks Project, Tag 0EZ3](https://stacks.math.columbia.edu/tag/0EZ3)
-/

@[expose] public section

add_to_stacks 0F0H "`𝒜'_X` is a weak Serre subcategory"
  AlgebraicGeometry.fppfEtaleWeakSerre_isWeakSerreClass

add_to_stacks 0F0H "property (0EZ4) of Situation 0EZ3" AlgebraicGeometry.fppfEtaleFinite_baseChange

add_to_stacks 0F0H "property (0EZ5) of Situation 0EZ3"
  AlgebraicGeometry.fppfEtaleWeakSerre_overMapPullback

add_to_stacks 0F0H "property (0EZ6) of Situation 0EZ3"
  AlgebraicGeometry.fppfEtaleWeakSerre_isSheaf_fppf

add_to_stacks 0F0H "property (0EZ8) of Situation 0EZ3"
  AlgebraicGeometry.fppfCovering_refinement_etale_finite

end
