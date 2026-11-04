module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Submodule
public import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# The complete lattice of submodules of a module on a scheme

For a scheme `X` and `M : X.Modules`, the submodules of `M` form a complete lattice. The lattice
itself is `AlgebraicGeometry.SheafOfModules.Submodule.instCompleteLattice`; what this file adds is
that instance under a name instance resolution finds when the module is presented as `X.Modules`
rather than as a `SheafOfModules` over the structure sheaf.

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice` — the complete lattice structure on
  `M.Submodule` for `M : X.Modules`.

## Implementation notes

Several modules independently declared this as an anonymous `local instance` with identical
bodies — `FormalGeometry/CoherentAdicSystem.lean`, `FormalGeometry/CoherentAdicPro.lean` and
`FormalGeometry/IdealPowerQuotient.lean` among them. An
anonymous instance still receives an automatically generated global name, so all of them received
the same one and the library failed to build once they shared an import closure, with
`environment already contains 'instCompleteLatticeSubmoduleOpens…'`. Being `local` prevents the
instance from firing outside its module; it does not prevent the *declaration* from existing, in
exactly the way `private` does not. Hence one named declaration here, imported by all of them.

It is deliberately a plain `def` with `attribute [local instance]` left to the consumer, matching
how those modules used it: made available where it is needed rather than globally, since
`X.Modules` and `SheafOfModules X.ringCatSheaf` are definitionally equal with separately declared
instances and a global instance invites loops between the two views.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- The submodules of a module on a scheme form a complete lattice.

This is `AlgebraicGeometry.SheafOfModules.Submodule.instCompleteLattice`, restated for a module
presented as `X.Modules`; instance resolution does not find the original through that presentation.
-/
@[instance_reducible]
def submoduleCompleteLattice {X : Scheme.{u}} {M : X.Modules} : CompleteLattice M.Submodule :=
  SheafOfModules.Submodule.instCompleteLattice

end AlgebraicGeometry.Scheme.Modules

end
