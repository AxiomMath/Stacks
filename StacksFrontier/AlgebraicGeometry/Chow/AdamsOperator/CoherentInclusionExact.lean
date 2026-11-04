module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoherentWeakSerre
public import StacksCore.CategoryTheory.Abelian.SerreClass.Weak
public import StacksCore.Tactic.StacksAttribute

/-!
# Exactness of the inclusion of coherent modules

For a ringed space, the inclusion of coherent sheaves of modules into all sheaves of modules
preserves finite limits and finite colimits, hence is exact.

## Main results

* `Stacks.SheafOfModules.coherentModules_inclusion_preservesFiniteLimits` gives left exactness.
* `Stacks.SheafOfModules.coherentModules_inclusion_preservesFiniteColimits` gives right
  exactness.

## Implementation notes

Both statements are instances of the exactness of the inclusion of a weak Serre subcategory,
applied to the weak Serre property `Stacks.SheafOfModules.coherentModules_isWeakSerreClass` of
coherence.

## References

* [Stacks Project, Tag 01BY](https://stacks.math.columbia.edu/tag/01BY)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.SheafOfModules

/-- The inclusion of coherent modules preserves finite limits. -/
@[stacks 01BY "coherent_inclusion_exact"]
instance coherentModules_inclusion_preservesFiniteLimits
    {X : Type u} [TopologicalSpace X]
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) :
    PreservesFiniteLimits (ObjectProperty.ι (coherentModules R)) :=
  ObjectProperty.preservesFiniteLimits_ι_of_isWeakSerreClass _

/-- The inclusion of coherent modules preserves finite colimits. -/
@[stacks 01BY "coherent_inclusion_exact"]
instance coherentModules_inclusion_preservesFiniteColimits
    {X : Type u} [TopologicalSpace X]
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) :
    PreservesFiniteColimits (ObjectProperty.ι (coherentModules R)) :=
  ObjectProperty.preservesFiniteColimits_ι_of_isWeakSerreClass _

end Stacks.SheafOfModules
