module

public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Length along a ring equivalence

A ring equivalence `e : R ≃+* S`, which moves the base ring, preserves the length of a ring over
itself and of its quotients.

## Main results

* `Module.length_eq_of_ringEquiv`: `Module.length R R = Module.length S S` for `e : R ≃+* S`.
* `Module.quotient_length_eq_of_ringEquiv`: the same for the quotients by an ideal and its image.
-/

@[expose] public section

namespace Module

/-- The length of a commutative ring over itself is invariant under a ring equivalence. -/
public theorem length_eq_of_ringEquiv {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S) :
    Module.length R R = Module.length S S := by
  have := RingHomInvPair.of_ringEquiv e
  have := RingHomInvPair.symm (e : R →+* S) (e.symm : S →+* R)
  apply WithBot.coe_injective
  rw [Module.coe_length, Module.coe_length,
    Order.krullDim_eq_of_orderIso (Submodule.orderIsoMapComap e.toSemilinearEquiv)]

/-- The length of a quotient is invariant under a ring equivalence, the ideal being carried over
by the equivalence. -/
public theorem quotient_length_eq_of_ringEquiv {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) (I : Ideal R) :
    Module.length R (R ⧸ I) = Module.length S (S ⧸ I.map e.toRingHom) := by
  let eQ := Ideal.quotientEquiv I (I.map e.toRingHom) e rfl
  let : RingHomSurjective e.toRingHom := ⟨e.surjective⟩
  let f : (R ⧸ I) →ₛₗ[e.toRingHom] (S ⧸ I.map e.toRingHom) :=
    { toFun := eQ
      map_add' := eQ.map_add
      map_smul' := by
        intro a z
        change eQ (Ideal.Quotient.mk I a * z) =
          Ideal.Quotient.mk (I.map e.toRingHom) (e a) * eQ z
        rw [map_mul]
        rfl }
  rw [Module.length, Module.length, WithBot.unbot_inj,
    Order.krullDim_eq_of_orderIso
      (Submodule.orderIsoMapComapOfBijective f eQ.bijective)]

end Module

end
