module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.CategoryTheory.Preadditive.LeftExact
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedModuleDegreeLimits

/-!
# Monomorphisms of graded modules in a fixed degree

Let `R` be a sheaf of rings on a site and let `A` be a sheaf of `ℤ`-graded `R`-algebras. The
functor `SheafOfModules.GradedModule.pieceFunctor A n` sends a right graded `A`-module to its
degree-`n` component. It commutes with all limits
(`SheafOfModules.GradedModule.pieceFunctor_preservesLimitsOfSize`, in
`GradedModuleDegreeLimits`); this file records the consequence that a monomorphism of graded
modules is a monomorphism in every degree, and the form of limit preservation stated at the
module universe for which `PreservesLimits` is the right size.

## Main results

* `SheafOfModules.GradedModule.mono_app_of_mono`: a monomorphism of graded modules has
  monomorphic homogeneous components. This is the converse of
  `SheafOfModules.GradedModule.mono_of_mono_app`.
* `SheafOfModules.GradedModule.pieceFunctor_preservesLimits`: limit preservation at the module
  universe for which `PreservesLimits` is the size of the diagrams.

## Implementation notes

Products and kernels of graded modules are both formed degreewise and neither involves
sheafification, so nothing here needs a hypothesis on the site: in particular
`mono_app_of_mono` holds with no `HasSheafify` assumption.

`PreservesLimits F` abbreviates `PreservesLimitsOfSize.{v', v'} F` for `v'` the hom universe of
the target, and a graded module has products only of families indexed by the module universe, so
the content is proved at size `m` and specialized here. This is the same phenomenon, and the same
resolution, as for `pieceFunctor_preservesColimitsOfSize'`.

The base is an arbitrary sheaf of rings on an arbitrary site rather than the structure sheaf of
a ringed site, and the universes of the site, the ring, the algebra pieces and the module pieces
are independent; a ringed site `X` is the case `R := X.ringSheaf`.

This is the limit half of Tag 0FR0. It carries no `@[stacks]` attribute: the tag sits on
`pieceFunctor_preservesLimitsOfSize`.

## References

* [Stacks Project, Tag 0FR0](https://stacks.math.columbia.edu/tag/0FR0)
* [Stacks Project, Tag 0FQZ](https://stacks.math.columbia.edu/tag/0FQZ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe t a m v u

namespace SheafOfModules

namespace GradedModule

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}

/-- **A monomorphism of graded modules is a monomorphism in every degree.**

This is the converse of `SheafOfModules.GradedModule.mono_of_mono_app`, and it needs no
hypothesis on the site. -/
theorem mono_app_of_mono {A : GradedAlgebra.{t, a} R} {M N : GradedModule.{t, a, m} A}
    (f : M ⟶ N) [Mono f] (n : ℤ) : Mono (f.app n) := by
  have : PreservesFiniteLimits (pieceFunctor.{t, a, m} A n) :=
    PreservesLimitsOfSize.preservesFiniteLimits _
  exact (pieceFunctor.{t, a, m} A n).map_mono f

section

universe m'

/-- **Taking a fixed homogeneous component of a graded module commutes with all limits.**

The module universe is `max u m'` for a site `C : Type u`, the hom universe of
`SheafOfModules.{max u m'} R`; `pieceFunctor_preservesLimitsOfSize` is the same statement with the
size universe free. -/
instance pieceFunctor_preservesLimits (A : GradedAlgebra.{t, a} R) (n : ℤ) :
    PreservesLimits (pieceFunctor.{t, a, max u m'} A n) :=
  pieceFunctor_preservesLimitsOfSize n

end

end GradedModule

end SheafOfModules
