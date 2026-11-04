module

public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.TensorProduct.Quotient

/-!
# The map induced by a flat ring map on quotients is flat

If `f : B →+* A` is flat then so is `B ⧸ J → A ⧸ JA`: the target is `(B ⧸ J) ⊗[B] A` by
`Algebra.TensorProduct.quotIdealMapEquivQuotTensor`, and flatness is stable under base change.
-/

@[expose] public section

namespace RingHom

/-- If `f : B →+* A` is flat, so is the induced map `B ⧸ J → A ⧸ JA`: indeed `A ⧸ JA` is
`(B ⧸ J) ⊗[B] A`, and flatness is stable under base change. -/
theorem flat_quotientMap {B A : Type*} [CommRing B] [CommRing A] (f : B →+* A) (hf : f.Flat)
    (J : Ideal B) : (Ideal.quotientMap (J.map f) f Ideal.le_comap_map).Flat := by
  let : Algebra B A := f.toAlgebra
  have : Module.Flat B A := hf
  exact RingHom.flat_algebraMap_iff.mpr <| Module.Flat.of_linearEquiv
    (Algebra.TensorProduct.quotIdealMapEquivQuotTensor A J).toLinearEquiv

end RingHom
