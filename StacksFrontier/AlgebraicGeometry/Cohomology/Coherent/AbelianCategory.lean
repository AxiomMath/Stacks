module

public import Mathlib.CategoryTheory.Abelian.Subcategory
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoherentWeakSerre
public import StacksCore.CategoryTheory.Abelian.SerreClass.Weak
public import StacksCore.Tactic.StacksAttribute

/-!
# Coherent sheaves of modules form an abelian category

Coherent sheaves of modules on a ringed space are closed under kernels, cokernels and
extensions, and their full subcategory is abelian. Specialized to a locally Noetherian scheme
this is the statement that coherent modules form an abelian subcategory of all modules which is
moreover closed under the three operations.

## Main results

* `Stacks.SheafOfModules.coherentModulesAbelian` is the abelian category structure on coherent
  sheaves of modules.
* `Stacks.SheafOfModules.isCoherent_kernel` and
  `Stacks.SheafOfModules.coherentModules_isClosedUnderCokernels` give coherence of the kernel
  and of the cokernel of a map of coherent modules.
* `Stacks.SheafOfModules.isCoherent_X₂_of_shortExact` gives closure under extensions.

## References

* [Stacks Project, Tag 01Y0](https://stacks.math.columbia.edu/tag/01Y0)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace Stacks.SheafOfModules

/-- Coherent sheaves of modules on a ringed space form an abelian category. -/
instance coherentModulesAbelian {X : Type u} [TopologicalSpace X]
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) :
    Abelian (CoherentModules R) where

add_to_stacks 01Y0 "abelian category" Stacks.SheafOfModules.coherentModulesAbelian
add_to_stacks 01Y0 "kernel" Stacks.SheafOfModules.isCoherent_kernel
add_to_stacks 01Y0 "cokernel" Stacks.SheafOfModules.coherentModules_isClosedUnderCokernels
add_to_stacks 01Y0 "extensions" Stacks.SheafOfModules.isCoherent_X₂_of_shortExact

end Stacks.SheafOfModules
