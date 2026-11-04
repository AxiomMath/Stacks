module

public import StacksFrontier.Homology.DerivedCategory.StandardModuleCatModel
public import StacksFrontier.Homology.Tor.DerivedExtensionScalars

/-!
# Derived extension of scalars at the standard model

This file defines the total derived extension of scalars `D(R) ⥤ D(A)` along a ring map
`f : R →+* A` (`CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars`) as a functor
between the derived categories `StacksDraft.ringDerivedCategory` at the standard model.

## Main definitions

* `StacksDraft.ringExtendScalars f`: derived extension of scalars `D(R) ⥤ D(A)` along `f`, at the
  standard model on both sides.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace StacksDraft

/-- Derived extension of scalars `D(R) ⥤ D(A)` along `f : R →+* A`, at the standard model on both
sides. -/
abbrev ringExtendScalars {R A : Type u} [CommRing R] [CommRing A] (f : R →+* A) :
    ringDerivedCategory R ⥤ ringDerivedCategory A :=
  letI := ringHasDerivedCategory A
  letI := ringHasDerivedCategory R
  (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u} f).functor

end StacksDraft
