module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.AffineCompletionTypes

/-!
# The morphism of affine schemes induced by a ring map, over a base

Let `S` be a scheme in a big fppf site `B`, let `s : Spec A ⟶ S` and let `φ : A →+* R` be a ring
map. Then `Spec R` lies over `S` through `Spec A`, and `Spec(φ)` is a morphism
`affineOver (Spec(φ) ≫ s) ⟶ affineOver s` of the big fppf site of `S`. This file names that
morphism and computes the inverse image along it of the zero locus `V(I) ⊆ |Spec A|`: it is the
zero locus `V(IR) ⊆ |Spec R|`.

These are the data needed to compare the category (0AS2) of finite-type modifications of
`Spec A` outside `V(I)` with that of `Spec R` outside `V(IR)` by base change, as in Stacks 0AE5
and 0AF7.

## Main definitions

* `AlgebraicGeometry.FormalSpace.affineOverMap`: the morphism `Spec R ⟶ Spec A` over `S`.

## Main results

* `AlgebraicGeometry.FormalSpace.preimage_zeroLocusPoints`: the inverse image of `V(I)` along
  it is `V(IR)`.

## Implementation notes

The points of a represented presheaf are compared with the points of the representing scheme
through `AlgebraicGeometry.Space.pointsToScheme` (Stacks 03BV), which is natural in the site
object; on prime spectra the map induced by `Spec(φ)` is `PrimeSpectrum.comap φ`.

## References

* [Stacks Project, Tag 0AE5](https://stacks.math.columbia.edu/tag/0AE5)
* [Stacks Project, Tag 0AF7](https://stacks.math.columbia.edu/tag/0AF7)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.FormalSpace

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The morphism `Spec R ⟶ Spec A` induced by `φ : A →+* R`, as a morphism of the big fppf
site of `S` from `Spec R`, structured through `Spec A`, to `Spec A`. -/
def affineOverMap {A R : Type u} [CommRing A] [CommRing R] (φ : A →+* R)
    (hA : B.Contains (Spec (.of A))) (hR : B.Contains (Spec (.of R)))
    (s : Spec (.of A) ⟶ S) :
    affineOver B S hS hR (Spec.map (CommRingCat.ofHom φ) ≫ s) ⟶ affineOver B S hS hA s :=
  Over.homMk (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom φ))) rfl

/-- The inverse image of `V(I) ⊆ |Spec A|` along `Spec R ⟶ Spec A` is `V(IR)`. -/
theorem preimage_zeroLocusPoints {A R : Type u} [CommRing A] [CommRing R] (φ : A →+* R)
    (hA : B.Contains (Spec (.of A))) (hR : B.Contains (Spec (.of R)))
    (s : Spec (.of A) ⟶ S) (I : Ideal A) :
    Space.pointsMap B S hS _ (yoneda.map (affineOverMap φ hA hR s)) ⁻¹'
        zeroLocusPoints B S hS hA s I =
      zeroLocusPoints B S hS hR (Spec.map (CommRingCat.ofHom φ) ≫ s) (I.map φ) := by
  ext x
  rw [zeroLocusPoints_eq_preimage_pointsToScheme, zeroLocusPoints_eq_preimage_pointsToScheme]
  have h : (Space.pointsToScheme B S hS (affineOver B S hS hA s)
      (Space.pointsMap B S hS _ (yoneda.map (affineOverMap φ hA hR s)) x) : PrimeSpectrum A) =
      PrimeSpectrum.comap φ (Space.pointsToScheme B S hS _ x : PrimeSpectrum R) :=
    Space.pointsToScheme_pointsMap_yoneda B S hS (affineOverMap φ hA hR s) x
  have key (p : PrimeSpectrum R) : PrimeSpectrum.comap φ p ∈ PrimeSpectrum.zeroLocus (I : Set A) ↔
      p ∈ PrimeSpectrum.zeroLocus ((I.map φ : Ideal R) : Set R) := by
    simp only [PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe, PrimeSpectrum.comap_asIdeal,
      Ideal.map_le_iff_le_comap]
  exact (congrArg (· ∈ PrimeSpectrum.zeroLocus (I : Set A)) h).to_iff.trans (key _)

end AlgebraicGeometry.FormalSpace

end
