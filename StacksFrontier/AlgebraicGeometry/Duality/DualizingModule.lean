module

public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.DualizingComplexScheme
public import StacksFrontier.Topology.Sheaves.Modules.Coherent
public import StacksCore.Tactic.StacksAttribute

/-!
# Dualizing modules

A coherent sheaf of modules on a locally Noetherian scheme is *dualizing* when placing it in some
cohomological degree gives a dualizing complex; a finite module over a Noetherian ring is dualizing
in the same sense. This is the terminology used for normal surfaces and for normal local domains of
dimension two.

## Main definitions

* `Stacks.Duality.IsDualizingModule` — a coherent sheaf of modules on a locally Noetherian scheme
  which becomes a dualizing complex in some degree.
* `Stacks.Duality.IsDualizingRingModule` — a finite module over a Noetherian ring which becomes a
  dualizing complex in some degree.

## Implementation notes

Neither definition asks for integrality, normality or dimension two: those are conditions on the
schemes and local domains to which the source applies the terminology, not part of the meaning of
a dualizing module. The unspecified shift is expressed by placing the module in an arbitrary
integer degree, which since the degree is existentially quantified is the same as allowing an
arbitrary shift of the degree-zero complex. Both predicates are abbreviations, so their coherence
and dualizing-complex components are available to clients by unfolding.

As in `Stacks.Duality.IsDualizingComplex`, the derived category is pinned to the standard model by
a local instance rather than left to whichever model is in scope.

## References

* [Stacks Project, Tag 0B4R](https://stacks.math.columbia.edu/tag/0B4R)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Stacks.Duality

/-- A sheaf of modules on a locally Noetherian scheme is a **dualizing module** when it is
coherent and becomes a dualizing complex once placed in some cohomological degree. -/
@[stacks 0B4R "dualizing_module_terminology"]
abbrev IsDualizingModule {X : Scheme.{u}} [IsLocallyNoetherian X] (ω : X.Modules) : Prop :=
  ω.IsCoherent ∧
    ∃ n : ℤ, IsDualizingComplex ((DerivedCategory.singleFunctor X.Modules n).obj ω)

/-- A module over a Noetherian ring is a **dualizing module** when it is finite and becomes a
dualizing complex once placed in some cohomological degree. -/
@[stacks 0B4R "dualizing_module_terminology"]
abbrev IsDualizingRingModule (A : Type u) [CommRing A] [IsNoetherianRing A] (M : Type v)
    [AddCommGroup M] [Module A M] : Prop :=
  Module.Finite A M ∧ ∃ n : ℤ, Dualizing.IsDualizingComplex
    ((DerivedCategory.singleFunctor (ModuleCat.{v} A) n).obj (ModuleCat.of A M))

end Stacks.Duality

end
