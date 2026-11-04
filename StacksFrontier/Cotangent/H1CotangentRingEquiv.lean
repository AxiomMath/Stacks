module

public import Mathlib.RingTheory.Extension.Cotangent.Basic

/-!
# `H¹` of the naive cotangent complex under ring isomorphisms

For an `R`-algebra `S` and an `R'`-algebra `S'`, ring isomorphisms `R ≃ R'` and `S ≃ S'`
compatible with the algebra maps identify `H¹(L_{S/R})` with `H¹(L_{S'/R'})`; in particular one
vanishes exactly when the other does. The four rings may live in arbitrary universes.

## Main results

* `Algebra.injective_h1Cotangent_map_of_ringEquiv`: the induced map on `H¹` is injective.
* `Algebra.subsingleton_h1Cotangent_iff_of_ringEquiv`: `H¹(L_{S/R}) = 0` if and only if
  `H¹(L_{S'/R'}) = 0`.
-/

@[expose] public section

namespace Algebra

/-- A pair of ring isomorphisms `R ≃ R'`, `S ≃ S'` compatible with the algebra maps induces an
injective map `H¹(L_{S/R}) → H¹(L_{S'/R'})`. -/
theorem injective_h1Cotangent_map_of_ringEquiv {R S R' S' : Type*} [CommRing R] [CommRing S]
    [CommRing R'] [CommRing S'] [Algebra R S] [Algebra R' S'] (eR : R ≃+* R') (eS : S ≃+* S')
    (h : ∀ r, eS (algebraMap R S r) = algebraMap R' S' (eR r)) :
    letI := eR.toRingHom.toAlgebra
    letI := eS.toRingHom.toAlgebra
    letI : Algebra R S' := (eS.toRingHom.comp (algebraMap R S)).toAlgebra
    haveI : IsScalarTower R R' S' := .of_algebraMap_eq fun r ↦ h r
    haveI : IsScalarTower R S S' := .of_algebraMap_eq fun _ ↦ rfl
    Function.Injective (H1Cotangent.map R R' S S') := by
  let := eR.toRingHom.toAlgebra
  let := eS.toRingHom.toAlgebra
  let : Algebra R S' := (eS.toRingHom.comp (algebraMap R S)).toAlgebra
  have : IsScalarTower R R' S' := .of_algebraMap_eq fun r ↦ h r
  have : IsScalarTower R S S' := .of_algebraMap_eq fun _ ↦ rfl
  let : Algebra R' R := eR.symm.toRingHom.toAlgebra
  let : Algebra S' S := eS.symm.toRingHom.toAlgebra
  let : Algebra R' S := (eS.symm.toRingHom.comp (algebraMap R' S')).toAlgebra
  have : IsScalarTower R' R S := .of_algebraMap_eq fun r ↦
    eS.symm_apply_eq.2 <| (congrArg _ (eR.apply_symm_apply r)).symm.trans (h _).symm
  have : IsScalarTower R' S' S := .of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower R R' R := .of_algebraMap_eq fun r ↦ (eR.symm_apply_apply r).symm
  have : IsScalarTower S S' S := .of_algebraMap_eq fun s ↦ (eS.symm_apply_apply s).symm
  refine Function.LeftInverse.injective (g := H1Cotangent.map R' R S' S) fun x ↦ ?_
  change ((H1Cotangent.map R' R S' S).restrictScalars S ∘ₗ H1Cotangent.map R R' S S') x = x
  rw [H1Cotangent.map, H1Cotangent.map, ← Extension.H1Cotangent.map_comp,
    Extension.H1Cotangent.map_eq _ (Extension.Hom.id _), Extension.H1Cotangent.map_id,
    LinearMap.id_apply]

/-- **`H¹` of the naive cotangent complex is invariant under ring isomorphisms**: for ring
isomorphisms `R ≃ R'` and `S ≃ S'` compatible with the algebra maps, in arbitrary universes,
`H¹(L_{S/R})` vanishes exactly when `H¹(L_{S'/R'})` does. -/
theorem subsingleton_h1Cotangent_iff_of_ringEquiv {R S R' S' : Type*} [CommRing R] [CommRing S]
    [CommRing R'] [CommRing S'] [Algebra R S] [Algebra R' S'] (eR : R ≃+* R') (eS : S ≃+* S')
    (h : ∀ r, eS (algebraMap R S r) = algebraMap R' S' (eR r)) :
    Subsingleton (H1Cotangent R S) ↔ Subsingleton (H1Cotangent R' S') := by
  refine ⟨fun _ ↦ ?_, fun _ ↦ (injective_h1Cotangent_map_of_ringEquiv eR eS h).subsingleton⟩
  exact (injective_h1Cotangent_map_of_ringEquiv eR.symm eS.symm fun r ↦
    eS.symm_apply_eq.2 <| by rw [h, eR.apply_symm_apply]).subsingleton

end Algebra

end
