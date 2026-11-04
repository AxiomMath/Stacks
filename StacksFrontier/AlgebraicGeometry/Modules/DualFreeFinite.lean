module

public import StacksFrontier.AlgebraicGeometry.InternalHomLocalKernel.Basic

/-!
# The dual of a finite free module on a scheme

Let `X` be a scheme and let `I` be a finite index type.  The dual
`(𝒪_X^{⊕I})^∨ = SheafHom(𝒪_X^{⊕I}, 𝒪_X)` of the free `𝒪_X`-module on `I` is again the free
`𝒪_X`-module on `I`. The dual of a zero module is zero.

## Main definitions

* `Stacks.AlgebraicGeometry.ReflexiveModules.dualSheafFreeIso`: the dual of the free
  `𝒪_X`-module on a finite index type `I` is the free `𝒪_X`-module on `I`.

## Main results

* `Stacks.AlgebraicGeometry.ReflexiveModules.isZero_dualSheaf_of_isZero`: the dual of a zero
  module is zero.

## References

* [Stacks Project, Tag 03EM](https://stacks.math.columbia.edu/tag/03EM)
* [Stacks Project, Tag 03EN](https://stacks.math.columbia.edu/tag/03EN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry Stacks.SheafOfModules.InternalHom
open Stacks.AlgebraicGeometry.InternalHomLocalKernel

universe u

namespace Stacks.AlgebraicGeometry.ReflexiveModules

/-- **The dual of a free module on a finite index set is free on that index set.**  For a scheme
`X` and a finite index type `I`, the dual `(𝒪_X^{⊕I})^∨ = SheafHom(𝒪_X^{⊕I}, 𝒪_X)` is
`𝒪_X^{⊕I}`. -/
def dualSheafFreeIso (X : Scheme.{u}) (I : Type u) [Finite I] :
    dualSheaf (SheafOfModules.free (R := X.ringCatSheaf) I) ≅
      SheafOfModules.free (R := X.ringCatSheaf) I :=
  freeSheafInternalHomIso X.sheaf (SheafOfModules.unit X.ringCatSheaf) I

/-- **The dual of a zero module is zero.**  If `M` is a zero object of the category of
`𝒪_X`-modules then so is its dual `M^∨`. -/
theorem isZero_dualSheaf_of_isZero (X : Scheme.{u}) {M : X.Modules} (hM : IsZero M) :
    IsZero (dualSheaf M) := by
  rw [IsZero.iff_id_eq_zero]
  ext U t
  apply eq_zero_of_dualPairing_eq_zero
  intro W x
  obtain rfl : x = 0 := by
    simpa using congrArg (fun f ↦ Scheme.Modules.Hom.app f W.left x)
      ((IsZero.iff_id_eq_zero M).1 hM)
  exact map_zero _

end Stacks.AlgebraicGeometry.ReflexiveModules

end
