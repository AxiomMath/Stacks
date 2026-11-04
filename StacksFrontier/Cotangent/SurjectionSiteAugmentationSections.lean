module

public import StacksFrontier.Cotangent.SurjectionSiteAugmentationGraded
public import StacksFrontier.RingTheory.AugmentationIdealGraded

/-!
# The sections of the augmentation filtration, in coordinates

Over an object `U` of the small model of the polynomial site `C_{B/A}` the sections of
`Ō = 𝒪 ⊗_A B̲` are a polynomial ring `B[S]` over `B`
(`CommAlgCat.smallPolynomialQuotientAlgEquiv`) and the augmentation is evaluation at the point
`g : S → B` naming `U` (`CommAlgCat.smallPolynomialQuotientAug_eq`). This file transports the
filtration `𝒦ⁿ` across that identification: the sections of `𝒦ⁿ` over `U` are the `n`-th power
of `MvPolynomial.augmentationIdeal g`.

That is the form in which `MvPolynomial.symmetricPowerEquivAugmentationGraded` — the
identification of `Kⁿ/Kⁿ⁺¹` with the `n`-th symmetric power of the free `B`-module on the
variables — applies to the graded pieces of the filtration.

## Main definitions

* `CommAlgCat.smallSitePoint`: the point `g : S → B` naming an object of the small model.

## Main results

* `CommAlgCat.smallPolynomialAugmentationIdeal_eq_comap`,
  `CommAlgCat.map_smallPolynomialAugmentationIdeal` and
  `CommAlgCat.map_smallPolynomialAugmentationIdeal_pow`: the augmentation ideal and its powers
  correspond to `MvPolynomial.augmentationIdeal g` and its powers.
* `CommAlgCat.map_smallPolynomialAugmentationIdealPowSubmodule`: the same as `B`-submodules.
* `CommAlgCat.smallPolynomialAugmentationIdealPowLinearEquiv`: the resulting `B`-linear
  identification of the sections of `𝒦ⁿ`.

## References

* [Stacks Project, Tag 08RF](https://stacks.math.columbia.edu/tag/08RF)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace CommAlgCat

variable (A : Type u) [CommRing A] (B : CommAlgCat.{u} A) (κ : Cardinal.{u})

/-- The point of `B` naming an object of the small model of the polynomial site: the object
`(S, g)` names the polynomial algebra `A[S]` augmented by `X s ↦ g s`. -/
abbrev smallSitePoint (X : ((smallBoundedPolynomialSite A B κ)ᵒᵖ)) :
    ↥(X.unop.unop.1) → (B : Type u) :=
  fun s => (X.unop.unop.2 s : (B : Type u))

/-- The augmentation ideal of `Ō` over an object is the augmentation ideal of the polynomial
ring `B[S]` at the point naming that object. -/
lemma smallPolynomialAugmentationIdeal_eq_comap
    (X : ((smallBoundedPolynomialSite A B κ)ᵒᵖ)) :
    smallPolynomialAugmentationIdeal A B κ X =
      Ideal.comap (smallPolynomialQuotientAlgEquiv A B κ X)
        (MvPolynomial.augmentationIdeal (smallSitePoint A B κ X)) := by
  ext x
  rw [mem_smallPolynomialAugmentationIdeal, Ideal.mem_comap,
    MvPolynomial.mem_augmentationIdeal, smallPolynomialQuotientAug_apply]

/-- The identification `Ō(U) = B[S]` carries the augmentation ideal onto the augmentation ideal
of `B[S]` at the point naming `U`. -/
lemma map_smallPolynomialAugmentationIdeal (X : ((smallBoundedPolynomialSite A B κ)ᵒᵖ)) :
    Ideal.map (smallPolynomialQuotientAlgEquiv A B κ X)
        (smallPolynomialAugmentationIdeal A B κ X) =
      MvPolynomial.augmentationIdeal (smallSitePoint A B κ X) := by
  rw [smallPolynomialAugmentationIdeal_eq_comap]
  exact Ideal.map_comap_of_surjective _
    (smallPolynomialQuotientAlgEquiv A B κ X).surjective _

/-- The identification `Ō(U) = B[S]` carries the `n`-th power of the augmentation ideal onto the
`n`-th power of the augmentation ideal of `B[S]`. -/
lemma map_smallPolynomialAugmentationIdeal_pow (n : ℕ)
    (X : ((smallBoundedPolynomialSite A B κ)ᵒᵖ)) :
    Ideal.map (smallPolynomialQuotientAlgEquiv A B κ X)
        (smallPolynomialAugmentationIdeal A B κ X ^ n) =
      MvPolynomial.augmentationIdeal (smallSitePoint A B κ X) ^ n := by
  rw [Ideal.map_pow, map_smallPolynomialAugmentationIdeal]

/-- The `n`-th power of the augmentation ideal is the preimage of the `n`-th power of the
augmentation ideal of `B[S]`. -/
lemma smallPolynomialAugmentationIdeal_pow_eq_comap (n : ℕ)
    (X : ((smallBoundedPolynomialSite A B κ)ᵒᵖ)) :
    smallPolynomialAugmentationIdeal A B κ X ^ n =
      Ideal.comap (smallPolynomialQuotientAlgEquiv A B κ X)
        (MvPolynomial.augmentationIdeal (smallSitePoint A B κ X) ^ n) := by
  rw [← map_smallPolynomialAugmentationIdeal_pow]
  exact (Ideal.comap_map_of_bijective _
    (smallPolynomialQuotientAlgEquiv A B κ X).bijective).symm

/-- The identification `Ō(U) = B[S]`, read on `B`-submodules, carries the `n`-th step of the
filtration onto the `n`-th power of the augmentation ideal of `B[S]`. -/
lemma map_smallPolynomialAugmentationIdealPowSubmodule (n : ℕ)
    (X : ((smallBoundedPolynomialSite A B κ)ᵒᵖ)) :
    Submodule.map (smallPolynomialQuotientAlgEquiv A B κ X).toLinearMap
        (smallPolynomialAugmentationIdealPowSubmodule A B κ n X) =
      Submodule.restrictScalars (B : Type u)
        (MvPolynomial.augmentationIdeal (smallSitePoint A B κ X) ^ n) := by
  refine le_antisymm ?_ fun y hy => ?_
  · rintro _ ⟨x, hx, rfl⟩
    have hx' : x ∈ smallPolynomialAugmentationIdeal A B κ X ^ n := hx
    have := Ideal.mem_map_of_mem (smallPolynomialQuotientAlgEquiv A B κ X) hx'
    rwa [map_smallPolynomialAugmentationIdeal_pow] at this
  · refine ⟨(smallPolynomialQuotientAlgEquiv A B κ X).symm y, ?_, by simp⟩
    have hy' : y ∈ MvPolynomial.augmentationIdeal (smallSitePoint A B κ X) ^ n := hy
    show (smallPolynomialQuotientAlgEquiv A B κ X).symm y ∈
      smallPolynomialAugmentationIdeal A B κ X ^ n
    rw [smallPolynomialAugmentationIdeal_pow_eq_comap, Ideal.mem_comap]
    simpa using hy'

/-- **The sections of `𝒦ⁿ`**, identified with the `n`-th power of the augmentation ideal of the
polynomial ring `B[S]`. -/
def smallPolynomialAugmentationIdealPowLinearEquiv (n : ℕ)
    (X : ((smallBoundedPolynomialSite A B κ)ᵒᵖ)) :
    ↥(smallPolynomialAugmentationIdealPowSubmodule A B κ n X) ≃ₗ[(B : Type u)]
      ↥(Submodule.restrictScalars (B : Type u)
        (MvPolynomial.augmentationIdeal (smallSitePoint A B κ X) ^ n)) :=
  (Submodule.equivMapOfInjective (smallPolynomialQuotientAlgEquiv A B κ X).toLinearMap
      (smallPolynomialQuotientAlgEquiv A B κ X).injective _).trans
    (LinearEquiv.ofEq _ _ (map_smallPolynomialAugmentationIdealPowSubmodule A B κ n X))

end CommAlgCat

end
