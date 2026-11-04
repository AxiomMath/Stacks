module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.SheafOfModules
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjective
public import StacksFrontier.Topology.Sheaves.OpenImmersion.ModuleExtensionByZero

/-!
# Derived objects supported on a subset

For a sheaf of rings on a topological space and a subset `T` of that space, an object of the
derived category of sheaves of modules is cohomologically supported on `T` when every one of
its cohomology sheaves has all its stalks outside `T` equal to zero.

## Main definitions

* `AlgebraicGeometry.CohomologySupportedOn`: the predicate itself.

## Implementation notes

Stating the condition stalkwise rather than through the support of the cohomology sheaves is
what makes it usable in the derived category, where the cohomology sheaves are only defined up
to isomorphism. Vanishing of each cohomology stalk outside the subset is equivalent to
containment of its support, by the stalkwise definition of sheaf support.

The predicate is stated for sheaves of modules on a ringed topological space and arbitrary
subsets, so it applies in particular to a closed subset of a scheme.

## References

* [Stacks Project, Tag 08DF](https://stacks.math.columbia.edu/tag/08DF)
* [Stacks Project, Tag 08DA](https://stacks.math.columbia.edu/tag/08DA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor TopologicalSpace

universe u

namespace AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

/-- Every cohomology sheaf of `E` has support contained in `T`, expressed equivalently by
vanishing of all stalks at points outside `T`. -/
noncomputable abbrev CohomologySupportedOn {X : TopCat.{u}}
    (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) (T : Set X)
    (E : DerivedCategory (SheafOfModules.{u} O)) : Prop :=
  ∀ (i : ℤ) (x : X), x ∉ T →
    IsZero (TopCat.Presheaf.stalk (X := X)
      (((DerivedCategory.homologyFunctor (SheafOfModules.{u} O) i).obj E).val.presheaf) x)

end AlgebraicGeometry

add_to_stacks 08DA AlgebraicGeometry.CohomologySupportedOn
