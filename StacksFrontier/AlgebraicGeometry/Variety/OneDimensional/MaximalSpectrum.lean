module

public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Spectrum.Maximal.Basic

/-!
# Transport of the maximal spectrum along a ring isomorphism

An isomorphism of commutative rings carries maximal ideals to maximal ideals, so it induces an
equivalence between the maximal spectra.

## Main definitions

* `MaximalSpectrum.congr` is the equivalence of maximal spectra induced by a ring isomorphism.
-/

@[expose] public section

namespace MaximalSpectrum

/-- A ring isomorphism induces an equivalence of maximal spectra, by pushing forward and
pulling back maximal ideals along it. -/
public def congr {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S) :
    MaximalSpectrum R ≃ MaximalSpectrum S where
  toFun m := ⟨Ideal.map e.toRingHom m.asIdeal, m.isMaximal.map_bijective e.toRingHom e.bijective⟩
  invFun m := ⟨Ideal.comap e.toRingHom m.asIdeal, m.isMaximal.comap_bijective e.toRingHom
    e.bijective⟩
  left_inv m := MaximalSpectrum.ext (m.asIdeal.comap_map_of_bijective e.toRingHom e.bijective)
  right_inv m := MaximalSpectrum.ext (m.asIdeal.map_comap_of_surjective e.toRingHom e.surjective)

/-- The maximal ideal `congr e m` is the image of `m` under `e`. -/
@[simp]
public theorem congr_asIdeal {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S)
    (m : MaximalSpectrum R) : (congr e m).asIdeal = Ideal.map e.toRingHom m.asIdeal :=
  rfl

end MaximalSpectrum

end
