module

public import Mathlib.AlgebraicGeometry.Limits

/-!
# Naturality of the comparison between a coproduct of spectra and the spectrum of a product

`AlgebraicGeometry.sigmaSpec` compares the coproduct `∐ᵢ Spec (R i)` of the spectra of a family
of rings with the spectrum `Spec (∏ᵢ R i)` of their product; for a finite index type it is an
isomorphism. This file records that the comparison is natural in the family: a family of ring
maps `φ i : R i ⟶ R' i` induces both a morphism `∐ᵢ Spec (R' i) ⟶ ∐ᵢ Spec (R i)` of coproducts
and a morphism `Spec (∏ᵢ R' i) ⟶ Spec (∏ᵢ R i)` of spectra of products, and the square they
form with the two comparison morphisms commutes.

## Main results

* `AlgebraicGeometry.sigmaSpec_naturality`: the naturality square of
  `AlgebraicGeometry.sigmaSpec` in the family of rings.
-/

@[expose] public section

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- The comparison morphism `AlgebraicGeometry.sigmaSpec` from a coproduct of spectra to the
spectrum of the product is natural in the family of rings: for ring maps `φ i : R i ⟶ R' i` the
square formed by the induced morphism of coproducts, the induced morphism of spectra of the
products, and the two comparison morphisms commutes. -/
@[reassoc]
theorem sigmaSpec_naturality {ι : Type*} (R R' : ι → CommRingCat) (φ : ∀ i, R i ⟶ R' i) :
    Limits.Sigma.map (fun i ↦ Spec.map (φ i)) ≫ sigmaSpec R =
      sigmaSpec R' ≫ Spec.map (CommRingCat.ofHom
        (RingHom.pi fun i ↦ (φ i).hom.comp (Pi.evalRingHom (fun i ↦ (R i : Type _)) i))) := by
  refine Sigma.hom_ext _ _ fun i ↦ ?_
  rw [ι_sigmaSpec_assoc, Sigma.ι_map_assoc, ι_sigmaSpec, ← Spec.map_comp, ← Spec.map_comp]
  rfl

end AlgebraicGeometry
