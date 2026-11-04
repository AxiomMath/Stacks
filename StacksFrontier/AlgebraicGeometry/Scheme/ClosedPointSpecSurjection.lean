module

public import Mathlib.AlgebraicGeometry.Scheme

/-!
# The closed point under `Spec` of a surjection of local rings

A surjective homomorphism of local rings is automatically local, so the morphism of affine
schemes it induces carries the closed point to the closed point.

## Main results

* `AlgebraicGeometry.specMap_base_closedPoint_of_surjective`: `Spec` of a surjection of local
  rings sends the closed point to the closed point.
* `AlgebraicGeometry.specMap_base_closedPoint_of_ringEquiv`: the same for `Spec` of a ring
  isomorphism.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- **`Spec` of a surjection of local rings carries the closed point to the closed point.** -/
theorem specMap_base_closedPoint_of_surjective {R T : Type u} [CommRing R] [CommRing T]
    [IsLocalRing R] [IsLocalRing T] (f : R →+* T) (hf : Function.Surjective f) :
    (Spec.map (CommRingCat.ofHom f)).base (IsLocalRing.closedPoint T) =
      IsLocalRing.closedPoint R :=
  let : IsLocalHom f := IsLocalHom.of_surjective f hf
  Spec_closedPoint (f := CommRingCat.ofHom f)

/-- **`Spec` of a ring isomorphism of local rings carries the closed point to the closed
point.** -/
theorem specMap_base_closedPoint_of_ringEquiv {R T : Type u} [CommRing R] [CommRing T]
    [IsLocalRing R] [IsLocalRing T] (e : R ≃+* T) :
    (Spec.map (CommRingCat.ofHom e.toRingHom)).base (IsLocalRing.closedPoint T) =
      IsLocalRing.closedPoint R :=
  specMap_base_closedPoint_of_surjective e.toRingHom e.surjective

end AlgebraicGeometry

end
