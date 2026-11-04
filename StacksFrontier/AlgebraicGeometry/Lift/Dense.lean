module

public import StacksFrontier.AlgebraicGeometry.BlowUpUniversal.Basic

/-!
# Scheme-theoretic density is inherited by open subschemes

An open subscheme `U` of `X` is scheme-theoretically dense when, for *every* open `V` of `X`,
the inclusion of `V ∩ U` into `V` is scheme-theoretically dominant
(`AlgebraicGeometry.Scheme.Opens.IsSchemeTheoreticallyDense`, Tag 01RB (2)). Because the
definition already quantifies over all opens of `X`, its restriction to an open subscheme `W` is
formal: an open of `W` is an open of `X` contained in `W`, and the two inclusions agree up to the
canonical isomorphism `AlgebraicGeometry.Scheme.Hom.isoImage`.

This is exactly what the uniqueness half of [Stacks, Tag 0806] needs on the overlaps of a cover
of the source. `Stacks.AlgebraicGeometry.BlowUpUniversal.over_hom_unique` asks for the stronger
input that the inverse image of the centre is an effective Cartier divisor on the overlap, and
uses it *only* to produce this density; `over_hom_unique_of_dense` below takes the density
directly, so no restriction-stability statement about
`Stacks.Divisors.IsEffectiveCartierDivisor` is needed.

## Main results

* `Stacks.Tag0806Lift.isSchemeTheoreticallyDense_preimage_ι`: a scheme-theoretically dense open
  stays scheme-theoretically dense after restriction to an open subscheme.
* `Stacks.Tag0806Lift.over_hom_unique_of_dense`: the uniqueness half of [Stacks, Tag 0806] with
  the Cartier hypothesis on the source replaced by the density it is used for.

## Implementation notes

`AlgebraicGeometry.IsSchemeTheoreticallyDominant` is a class closed under composition and
holding for every isomorphism, so the transport across `isoImage` and
`AlgebraicGeometry.Scheme.Hom.preimageIso` is discharged by instance search once the morphism
has been rewritten into a composite of an isomorphism, the known dominant inclusion, and an
isomorphism.

## References

* [Stacks Project, Tag 01RB](https://stacks.math.columbia.edu/tag/01RB)
* [Stacks Project, Tag 01RH](https://stacks.math.columbia.edu/tag/01RH)
* [Stacks Project, Tag 0806](https://stacks.math.columbia.edu/tag/0806)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.BlowUpUniversal

universe u

namespace Stacks.Tag0806Lift

/-- **Scheme-theoretic density is inherited along an open immersion.** If `D` is a
scheme-theoretically dense open of `Y` and `h : P ⟶ Y` is an open immersion, then `h⁻¹(D)` is a
scheme-theoretically dense open of `P`.

The proof is a transport. An open `V'` of `P` gives an open immersion `V'.ι ≫ h` of `Y`, which
is isomorphic to the inclusion of its open range by
`AlgebraicGeometry.IsOpenImmersion.isoOfRangeEq`; under that isomorphism the inclusion of
`V' ∩ h⁻¹(D)` becomes the inclusion of `(V'.ι ≫ h)(V') ∩ D`, which is dominant by hypothesis.
`AlgebraicGeometry.IsSchemeTheoreticallyDominant` holds for isomorphisms and is closed under
composition, so the transport is discharged by instance search. -/
theorem isSchemeTheoreticallyDense_preimage {P Y : Scheme.{u}} (h : P ⟶ Y) [IsOpenImmersion h]
    {D : Y.Opens} (hD : Scheme.Opens.IsSchemeTheoreticallyDense D) :
    Scheme.Opens.IsSchemeTheoreticallyDense (h ⁻¹ᵁ D) := by
  intro V'
  have hrange : Set.range (V'.ι ≫ h) = Set.range (V'.ι ≫ h).opensRange.ι := by simp
  set j := IsOpenImmersion.isoOfRangeEq (V'.ι ≫ h) (V'.ι ≫ h).opensRange.ι hrange with hj
  set T : (V'.ι ≫ h).opensRange.toScheme.Opens := (V'.ι ≫ h).opensRange.ι ⁻¹ᵁ D with hT
  have hdom : IsSchemeTheoreticallyDominant T.ι := hD _
  have hfacj : j.hom ≫ (V'.ι ≫ h).opensRange.ι = V'.ι ≫ h :=
    IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  have hopen : V'.ι ⁻¹ᵁ (h ⁻¹ᵁ D) = j.hom ⁻¹ᵁ T := by
    rw [hT, ← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, hfacj]
  rw [hopen]
  have hfac : (j.hom ⁻¹ᵁ T).ι = (j.hom.preimageIso T).hom ≫ T.ι ≫ j.inv := by
    rw [← Category.assoc, Scheme.Hom.preimageIso_hom_ι, Category.assoc, j.hom_inv_id,
      Category.comp_id]
  rw [hfac]
  infer_instance

/-- **Scheme-theoretic density is local on the ambient scheme.** The case of
`isSchemeTheoreticallyDense_preimage` for the inclusion of an open subscheme. -/
theorem isSchemeTheoreticallyDense_preimage_ι {X : Scheme.{u}} {U : X.Opens}
    (hU : Scheme.Opens.IsSchemeTheoreticallyDense U) (W : X.Opens) :
    Scheme.Opens.IsSchemeTheoreticallyDense (W.ι ⁻¹ᵁ U) :=
  isSchemeTheoreticallyDense_preimage W.ι hU

/-- **The uniqueness half of [Stacks, Tag 0806], from the density directly.** An object of
`Over X` admits at most one morphism to the blowup over the base, as soon as the inverse image
of the complement of the centre is a scheme-theoretically dense open of the source.

This is `Stacks.AlgebraicGeometry.BlowUpUniversal.over_hom_unique` with its hypothesis
`IsCartierOver I Y` replaced by the one consequence of it that the proof uses. The weaker
hypothesis is what makes the gluing step of the existence half work: on the overlap of two
members of an open cover of the source, the density is supplied by
`isSchemeTheoreticallyDense_preimage_ι`, whereas the Cartier property of the restricted divisor
would have to be proved. -/
theorem over_hom_unique_of_dense {X : Scheme.{u}} (I : X.IdealSheafData)
    (hmono : Mono (blowUpToBase I ∣_ supportCompl I))
    (hsep : IsSeparated (blowUpToBase I))
    {Y : Over X}
    (hdense : Scheme.Opens.IsSchemeTheoreticallyDense (Y.hom ⁻¹ᵁ supportCompl I))
    (g₁ g₂ : Y ⟶ Over.mk (blowUpToBase I)) : g₁ = g₂ := by
  have hsep' : IsSeparated (Over.mk (blowUpToBase I)).hom := hsep
  exact AlgebraicGeometry.eq_of_isSchemeTheoreticallyDense g₁ g₂
    (Y.hom ⁻¹ᵁ supportCompl I) hdense
    (ι_comp_eq_of_mono I hmono g₁.left g₂.left (Over.w g₁) (Over.w g₂))

end Stacks.Tag0806Lift

end
