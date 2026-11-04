module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.DerivedPullbackOfModules.DerivedSections
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.DerivedPullbackOfModules.CoevaluationMates
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.DerivedPullbackOfModules.RestrictionMaps

/-!
# The derived pullback of modules on a chaotic site

The derived pullback `Lg^*` of presheaves of modules along a morphism of ringed topoi on chaotic
sites, in three parts:

* `DerivedSections`: the derived inverse image, the derived extension of scalars, the
  coevaluation, the derived pullback `Lg^*` and the computation of its derived sections
  (Stacks 0D6D);
* `CoevaluationMates`: the mates of the restriction transformation under the coevaluation
  adjunctions and the chain-level restriction square for the coevaluations;
* `RestrictionMaps`: the derived restriction square, the compatibility of the sections
  computations with the derived restriction maps, and Stacks 0GZ1 for the derived pullback.
-/
