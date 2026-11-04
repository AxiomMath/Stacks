module

public import Mathlib.CategoryTheory.ObjectProperty.Kernels
public import StacksFrontier.AlgebraicGeometry.QcohLimits.Basic

/-!
# Quasi-coherence as an object property closed under kernels

`Stacks.AlgebraicGeometry.QcohLimits.isQuasicoherent_kernel` says that a kernel of a morphism of
quasi-coherent modules is quasi-coherent. This file states that fact in the form instance search
uses, as `CategoryTheory.ObjectProperty.IsClosedUnderKernels` of the quasi-coherence property.

It is a file of its own rather than a declaration in
`StacksFrontier/AlgebraicGeometry/QcohLimits/Basic.lean` because the object-property form needs
`Mathlib.CategoryTheory.ObjectProperty.Kernels`, and adding that import to `Basic.lean` would
invalidate the reverse-dependency cone of a module much of the library imports.

## Main results

* `AlgebraicGeometry.isClosedUnderKernels_isQuasicoherent`: the quasi-coherent modules on a
  scheme are closed under kernels.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **Quasi-coherence is closed under kernels.** The object-property form of
`Stacks.AlgebraicGeometry.QcohLimits.isQuasicoherent_kernel`, which is the shape instance
search can use. -/
public instance isClosedUnderKernels_isQuasicoherent (X : Scheme.{u}) :
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).IsClosedUnderKernels where
  kernels_le := by
    rintro _ ⟨f, k, hk, ⟨hX, hY⟩⟩
    exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
      (IsLimit.conePointUniqueUpToIso (kernelIsKernel f) hk)
      (@Stacks.AlgebraicGeometry.QcohLimits.isQuasicoherent_kernel X _ _ f hX hY)

end AlgebraicGeometry

end
