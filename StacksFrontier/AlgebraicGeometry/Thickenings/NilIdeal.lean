module

public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import StacksFrontier.AlgebraicGeometry.Thickenings
public import StacksFrontier.RingTheory.Nilpotent.UnitsLifting

/-!
# The thickening cut out by an ideal of nilpotent elements

Let `A` be a commutative ring and `I ⊆ A` an ideal all of whose elements are nilpotent. The
quotient map `A → A ⧸ I` is surjective, so `Spec (A ⧸ I) ⟶ Spec A` is a closed immersion, and
`I` is contained in the nilradical of `A`, so that same morphism is a homeomorphism on points.
Hence it is a thickening. Units are detected modulo such an ideal, so units also lift along the
induced map of global sections.

## Main results

* `Stacks.Thickenings.isThickening_specMap_quotientMk`: the spectrum of the quotient by an ideal
  of nilpotent elements is a thickening of the spectrum of the ring.
* `Stacks.Thickenings.surjective_units_map_appTop_specMap_quotientMk`: units lift along the map
  of global sections induced by that thickening.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Thickenings

/-- If every element of an ideal `I` of a commutative ring `A` is nilpotent, then the induced
morphism `Spec (A ⧸ I) ⟶ Spec A` is a thickening: it is a closed immersion because the quotient
map is surjective, and it is surjective on points because `I` lies in the nilradical. -/
theorem isThickening_specMap_quotientMk {A : Type u} [CommRing A] (I : Ideal A)
    (hI : ∀ x ∈ I, IsNilpotent x) :
    IsThickening (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) := by
  refine ⟨IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective, ?_⟩
  change Function.Surjective (PrimeSpectrum.comap (Ideal.Quotient.mk I))
  exact (PrimeSpectrum.comap_quotientMk_bijective_of_le_nilradical
    (fun x hx => mem_nilradical.mpr (hI x hx))).surjective

/-- A bijective monoid homomorphism induces a surjection on unit groups. -/
private theorem surjective_units_map_of_bijective {M N : Type*} [Monoid M] [Monoid N]
    (f : M →* N) (hf : Function.Bijective f) : Function.Surjective (Units.map f) :=
  (Units.mapEquiv (MulEquiv.ofBijective f hf)).surjective

/-- If every element of an ideal `I` of a commutative ring `A` is nilpotent, then every unit of
the global sections of `Spec (A ⧸ I)` is the image of a unit of the global sections of
`Spec A`. -/
theorem surjective_units_map_appTop_specMap_quotientMk {A : Type u} [CommRing A] (I : Ideal A)
    (hI : ∀ x ∈ I, IsNilpotent x) :
    Function.Surjective (Units.map
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).appTop.hom.toMonoidHom) := by
  have h : (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).appTop
      = (Scheme.ΓSpecIso (CommRingCat.of A)).hom ≫ CommRingCat.ofHom (Ideal.Quotient.mk I) ≫
        (Scheme.ΓSpecIso (CommRingCat.of (A ⧸ I))).inv := by
    simp
  rw [h]
  change Function.Surjective (Units.map
    (((Scheme.ΓSpecIso (CommRingCat.of (A ⧸ I))).inv.hom.comp
      ((Ideal.Quotient.mk I).comp
        (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom)).toMonoidHom))
  rw [show ((Scheme.ΓSpecIso (CommRingCat.of (A ⧸ I))).inv.hom.comp
      ((Ideal.Quotient.mk I).comp
        (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom)).toMonoidHom
      = ((Scheme.ΓSpecIso (CommRingCat.of (A ⧸ I))).inv.hom.toMonoidHom).comp
        (((Ideal.Quotient.mk I).toMonoidHom).comp
          ((Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom.toMonoidHom)) from rfl,
    Units.map_comp, Units.map_comp]
  rw [MonoidHom.coe_comp, MonoidHom.coe_comp]
  exact (surjective_units_map_of_bijective _
      (Scheme.ΓSpecIso (CommRingCat.of (A ⧸ I))).symm.commRingCatIsoToRingEquiv.bijective).comp
    ((Stacks.NilpotentIdeal.PowerMap.units_map_surjective I hI).comp
      (surjective_units_map_of_bijective _
        (Scheme.ΓSpecIso (CommRingCat.of A)).commRingCatIsoToRingEquiv.bijective))

end Stacks.Thickenings

end
