module

public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjective
public import StacksFrontier.CategoryTheory.Preadditive.Injective.Adjunction
public import StacksFrontier.Topology.Sheaves.OpenImmersion.ModuleExtensionByZeroExact
import StacksCore.Tactic.StacksAttribute

/-!
# Restriction of K-injective complexes to an open subspace

Let `X` be a topological space, `O` a sheaf of rings on `X` and `U ⊆ X` an open subset, with
`j_! ⊣ j^*` the extension-by-zero/restriction adjunction of `ExtensionByZeroModules` between
sheaves of `O|_U`-modules on `U` and sheaves of `O`-modules on `X`. The restriction `j^* I` of
a K-injective complex `I` of `O`-modules is again K-injective ([Stacks, Tag 08BS]), and the
restriction of an injective `O`-module is injective.

Both follow from `j_!` being exact: the right adjoint of an exact functor carries K-injective
complexes to K-injective complexes ([Stacks, Tag 08BJ]), and injective objects to injective
objects.

## Main results

* `ExtensionByZeroModules.isKInjective_jStar`: restriction to an open subspace preserves
  K-injective complexes of sheaves of modules.
* `ExtensionByZeroModules.preservesInjectiveObjects_jStar`: restriction to an open subspace
  preserves injective objects.

## Implementation notes

The sheaf of rings is only required to be `RingCat`-valued. Restriction is
`ExtensionByZeroModules.jStar`, whose target is the category of modules over the restricted sheaf
of rings `ExtensionByZeroModules.resRing U O`.

## References

* [Stacks Project, Tag 08BS](https://stacks.math.columbia.edu/tag/08BS)
* [Stacks Project, Tag 08BJ](https://stacks.math.columbia.edu/tag/08BJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace ExtensionByZeroModules

variable {X : TopCat.{u}} (U : Opens X)
variable (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u})

/-- Restriction to an open subspace preserves K-injective complexes of sheaves of modules. -/
@[stacks 08BS]
instance isKInjective_jStar
    (I : CochainComplex (SheafOfModules.{u} O) ℤ) [I.IsKInjective] :
    CochainComplex.IsKInjective
      (((jStar U O).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) :=
  CochainComplex.isKInjective_mapHomologicalComplex_of_exact
    (jStar U O) (jShriek U O) (jShriekAdjunction U O) I

/-- **Restriction to an open subspace preserves injective objects.** -/
instance preservesInjectiveObjects_jStar : (jStar U O).PreservesInjectiveObjects :=
  preservesInjectiveObjects_of_isExact _ (jShriek U O) (jShriekAdjunction U O)
    ⟨jShriek_preservesFiniteLimits U O, inferInstance⟩

end ExtensionByZeroModules
