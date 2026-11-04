module

public import Mathlib.CategoryTheory.ObjectProperty.Kernels
public import StacksFrontier.AlgebraicGeometry.AffineQcohPushforward.Colimits

/-!
# Quasi-coherence as an object property closed under cokernels

`Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_cokernel` says that a cokernel of
a morphism of quasi-coherent modules is quasi-coherent. This file states that fact in the form
instance search uses, as `CategoryTheory.ObjectProperty.IsClosedUnderCokernels` of the
quasi-coherence property.

It is a file of its own, next to
`StacksFrontier/AlgebraicGeometry/QcohLimits/ClosedUnderKernels.lean`, for the same reason: the
object-property form needs `Mathlib.CategoryTheory.ObjectProperty.Kernels`, and adding that
import to the module proving the cokernel statement would invalidate that module's whole
reverse-dependency cone.

## Main results

* `AlgebraicGeometry.isClosedUnderCokernels_isQuasicoherent`: the quasi-coherent modules on a
  scheme are closed under cokernels.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **Quasi-coherence is closed under cokernels.** The object-property form of
`Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_cokernel`, which is the shape
instance search can use. -/
public instance isClosedUnderCokernels_isQuasicoherent (X : Scheme.{u}) :
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).IsClosedUnderCokernels where
  cokernels_le := by
    rintro _ ⟨f, c, hc, ⟨hX, hY⟩⟩
    exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
      (IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel f) hc)
      (@Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_cokernel X _ _ f hX hY)

end AlgebraicGeometry

end
