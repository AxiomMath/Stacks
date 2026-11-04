module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-!
# Extension of scalars on the ring itself

Extension of scalars along a ring map `φ : R →+* S` carries `R`, viewed as a module over itself,
to `S` viewed as a module over itself. The statement mentions only `ModuleCat.extendScalars`, so
it lives here rather than being restated in each development that needs it.

## Main results

* `RingHom.extendScalarsRingIso`: extension of scalars takes the source ring to the target ring.
-/

@[expose] public section

open CategoryTheory

universe u

namespace RingHom

/-- Extension of scalars along a ring map takes the source, viewed as a module over itself, to
the target. -/
def extendScalarsRingIso {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S) :
    (ModuleCat.extendScalars φ).obj (ModuleCat.of R R) ≅ ModuleCat.of S S := by
  let := φ.toAlgebra
  exact (TensorProduct.AlgebraTensorModule.rid R S S).toModuleIso

end RingHom

end
