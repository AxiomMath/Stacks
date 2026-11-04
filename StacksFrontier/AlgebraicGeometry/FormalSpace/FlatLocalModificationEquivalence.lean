module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.AffineModificationBaseChange
public import StacksFrontier.RingTheory.AdicCompletion.AdicCompletionMapUniqueness

/-!
# Stacks 0AF7: modifications under a flat local map with the same closed fibre

Let `A → R` be a local homomorphism of Noetherian local rings such that

1. `A → R` is flat,
2. `𝔪_R = 𝔪_A R`, and
3. `κ(𝔪_A) = κ(𝔪_R)`.

Then base change along `Spec R ⟶ Spec A` is an equivalence from the category (0AS2) for
`(A, 𝔪_A)` to the category (0AS2) for `(R, 𝔪_R)`: the morphisms `X' ⟶ Spec A` of algebraic
spaces which are locally of finite type and an isomorphism over the punctured spectrum
`Spec A ∖ {𝔪_A}`, respectively the same for `R`.

## Main results

* `bijective_adicCompletionMap_maximalIdeal_of_flat`: the three conditions make
  `A^∧ → R^∧` an isomorphism (Stacks 0AGX).
* `AlgebraicGeometry.FormalSpace.isEquivalence_finiteTypeBaseChange_of_flat_localHom`:
  **Stacks 0AF7**.

## Implementation notes

The proof is the source's: by Stacks 0AGX (`exists_adicCompletion_ringEquiv_of_flat`) the map
on completions is an isomorphism, so the lemma is the special case `I = 𝔪_A` of Stacks 0AE5
(`AlgebraicGeometry.FormalSpace.isEquivalence_affineModificationBaseChange`).

Both categories are the categories `AlgebraicGeometry.Space.FiniteTypeModification` of
Stacks 0AS2 over the spaces represented by `Spec A` and `Spec R` in the big fppf site of a
base scheme `S`, outside the open subspaces with point sets the complements of `V(𝔪_A)` and
`V(𝔪_R)`. The functor is the base-change functor
`AlgebraicGeometry.Space.finiteTypeBaseChangeFunctorOfEq` along
`AlgebraicGeometry.FormalSpace.affineOverMap`, which is the pullback of slice categories by
`AlgebraicGeometry.Space.finiteTypeBaseChangeFunctorOfEqCompιIso`. Its target is the category
for `(R, 𝔪_R)` as in the source, and not that for `(R, 𝔪_A R)` of 0AE5; the two are
identified by condition (2).

## References

* [Stacks Project, Tag 0AF7](https://stacks.math.columbia.edu/tag/0AF7)
* [Stacks Project, Tag 0AE5](https://stacks.math.columbia.edu/tag/0AE5)
* [Stacks Project, Tag 0AGX](https://stacks.math.columbia.edu/tag/0AGX)
-/

@[expose] public noncomputable section

open CategoryTheory IsLocalRing

universe u

/-- A flat local homomorphism of Noetherian local rings `A → R` with `𝔪_R = 𝔪_A R` and
`κ(𝔪_A) = κ(𝔪_R)` induces a bijection from the `𝔪_A`-adic completion of `A` to the
`𝔪_A R`-adic completion of `R` (Stacks 0AGX). -/
theorem bijective_adicCompletionMap_maximalIdeal_of_flat {A R : Type u} [CommRing A]
    [CommRing R] [IsLocalRing A] [IsLocalRing R] [IsNoetherianRing A] [Algebra A R]
    [IsLocalHom (algebraMap A R)] [Module.Flat A R]
    (hmax : (maximalIdeal A).map (algebraMap A R) = maximalIdeal R)
    (hres : Function.Bijective (ResidueField.map (algebraMap A R))) :
    Function.Bijective (adicCompletionMap (algebraMap A R) (maximalIdeal A)
      ((maximalIdeal A).map (algebraMap A R)) le_rfl) := by
  obtain ⟨e, he⟩ := exists_adicCompletion_ringEquiv_of_flat
    (maximalIdeal A).fg_of_isNoetherianRing hmax hres
  generalize maximalIdeal R = J at hmax e he
  subst hmax
  exact bijective_adicCompletionMap_of_exists_ringEquiv _ _ _ le_rfl
    (maximalIdeal A).fg_of_isNoetherianRing e he

namespace AlgebraicGeometry.FormalSpace

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Stacks 0AF7.** Let `A → R` be a local homomorphism of Noetherian local rings which is
flat, with `𝔪_R = 𝔪_A R` and `κ(𝔪_A) = κ(𝔪_R)`. Then the base-change functor along
`Spec R ⟶ Spec A`, from the category (0AS2) for `(A, 𝔪_A)` to the category (0AS2) for
`(R, 𝔪_R)`, is an equivalence. Here `Spec A` lies over a base scheme `S` through `s`, and the
categories are the finite-type modifications of the represented spaces outside the complements
of `V(𝔪_A)` and `V(𝔪_R)`. -/
@[stacks 0AF7]
theorem isEquivalence_finiteTypeBaseChange_of_flat_localHom {A R : Type u} [CommRing A]
    [CommRing R] [IsLocalRing A] [IsLocalRing R] [IsNoetherianRing A] [IsNoetherianRing R]
    [Algebra A R] [IsLocalHom (algebraMap A R)] [Module.Flat A R]
    (hmax : (maximalIdeal A).map (algebraMap A R) = maximalIdeal R)
    (hres : Function.Bijective (ResidueField.map (algebraMap A R)))
    (hA : B.Contains (Spec (.of A))) (hR : B.Contains (Spec (.of R)))
    (s : Spec (.of A) ⟶ S) :
    (Space.finiteTypeBaseChangeFunctorOfEq
      (isAlgebraicSpace_yoneda B S hS
        (affineOver B S hS hR (Spec.map (CommRingCat.ofHom (algebraMap A R)) ≫ s)))
      (isAlgebraicSpace_yoneda B S hS (affineOver B S hS hA s))
      (yoneda.map (affineOverMap (algebraMap A R) hA hR s))
      (Space.openSubspaceOfPoints B S hS _ (zeroLocusPoints B S hS hA s (maximalIdeal A))ᶜ)
      (Space.openSubspaceOfPoints B S hS _
        (zeroLocusPoints B S hS hR _ (maximalIdeal R))ᶜ)
      (by rw [Space.preimage_openSubspaceOfPoints_compl, preimage_zeroLocusPoints, hmax])
      ).IsEquivalence := by
  have h0AE5 := isEquivalence_affineModificationBaseChange B S hS (algebraMap A R)
    (maximalIdeal A) hA hR s (bijective_adicCompletionMap_maximalIdeal_of_flat hmax hres)
  have key : ∀ J : Ideal R, (maximalIdeal A).map (algebraMap A R) = J →
      ∀ h, (Space.finiteTypeBaseChangeFunctorOfEq
        (isAlgebraicSpace_yoneda B S hS
          (affineOver B S hS hR (Spec.map (CommRingCat.ofHom (algebraMap A R)) ≫ s)))
        (isAlgebraicSpace_yoneda B S hS (affineOver B S hS hA s))
        (yoneda.map (affineOverMap (algebraMap A R) hA hR s))
        (Space.openSubspaceOfPoints B S hS _ (zeroLocusPoints B S hS hA s (maximalIdeal A))ᶜ)
        (Space.openSubspaceOfPoints B S hS _ (zeroLocusPoints B S hS hR _ J)ᶜ) h
        ).IsEquivalence := by
    rintro J rfl h
    exact h0AE5
  exact key _ hmax _

end AlgebraicGeometry.FormalSpace

end
