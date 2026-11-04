module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import StacksFrontier.AlgebraicGeometry.CoherentAbelian.Basic

/-!
# Coherence of modules on a scheme transfers along an isomorphism

Coherence of an `𝒪_X`-module is a property of isomorphism classes, so it transfers along any
isomorphism of modules.

## Main results

* `AlgebraicGeometry.isCoherent_of_moduleIso`: an isomorphic copy of a coherent module is
  coherent.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- An isomorphic copy of a coherent module on a scheme is coherent. -/
theorem isCoherent_of_moduleIso {X : Scheme.{u}} {M N : X.Modules} (e : M ≅ N)
    (hM : M.IsCoherent) : N.IsCoherent :=
  have := AlgebraicGeometry.CoherentAbelian.coherentModules_isClosedUnderIsomorphisms
    (R := X.ringCatSheaf)
  ObjectProperty.prop_of_iso (P := fun M : SheafOfModules X.ringCatSheaf => M.IsCoherent) e hM

end AlgebraicGeometry

end
