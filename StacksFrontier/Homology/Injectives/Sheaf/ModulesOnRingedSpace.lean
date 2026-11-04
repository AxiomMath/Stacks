module

public import Mathlib.CategoryTheory.Sites.Spaces
public import StacksFrontier.Homology.Injectives.Sheaf.ModulesOnRingedSite
import StacksCore.Tactic.StacksAttribute

/-!
# Injectives in the category of sheaves of modules on a ringed space

Let `X` be a topological space and let `O : Sheaf (Opens.grothendieckTopology X) RingCat` be a
sheaf of rings on `X`, not necessarily commutative. The category of sheaves of `O`-modules on `X`
has enough injectives, and in fact the injective embeddings can be chosen functorially.

## Main results

* `Stacks.Injectives.sheafOfModules_hasFunctorialInjectiveEmbeddings_of_space`: sheaves of
  `O`-modules on `X` admit functorial injective embeddings.
* `Stacks.Injectives.sheafOfModules_enoughInjectives_of_space`: sheaves of `O`-modules on `X`
  have enough injectives.

## References

* [Stacks Project, Tag 01DI](https://stacks.math.columbia.edu/tag/01DI)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace Stacks.Injectives

variable {X : TopCat.{u}} (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u})

/-- The category of sheaves of modules over a sheaf of rings on a topological space has functorial
injective embeddings. -/
@[stacks 01DI "functorial injective embeddings"]
theorem sheafOfModules_hasFunctorialInjectiveEmbeddings_of_space :
    HasFunctorialInjectiveEmbeddings (SheafOfModules.{u} O) :=
  sheafOfModules_hasFunctorialInjectiveEmbeddings (Opens.grothendieckTopology X) O

/-- The category of sheaves of modules over a sheaf of rings on a topological space has enough
injectives. -/
@[stacks 01DI "enough injectives"]
theorem sheafOfModules_enoughInjectives_of_space : EnoughInjectives (SheafOfModules.{u} O) :=
  enoughInjectives_of_hasFunctorialInjectiveEmbeddings _
    (sheafOfModules_hasFunctorialInjectiveEmbeddings_of_space O)

end Stacks.Injectives
