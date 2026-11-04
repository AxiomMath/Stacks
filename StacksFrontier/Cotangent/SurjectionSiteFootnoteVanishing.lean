module

public import StacksFrontier.Cotangent.SurjectionSiteAugmentationSymmetricPower
public import StacksFrontier.Cotangent.SurjectionSiteProNilpotent
public import StacksFrontier.Cotangent.SurjectionSymmetricPowerVanishing

/-!
# The footnote vanishing of [Stacks, Tag 08RF]

Let `A → B` be a **surjective** ring map, let `C_{B/A}` be the small model
`CommAlgCat.smallBoundedPolynomialSite A B (standardResolutionVarCardinal A B)` of the
polynomial site, write `H_i(C_{B/A}, ℱ) = (L_i colim)(ℱ)` for the homology of the site
([Stacks, Tag 08PF]) and let `𝒦ⁿ` be the `n`-th power of the augmentation ideal of
`Ō = 𝒪 ⊗_A B̲`.  The footnote in the proof of [Stacks, Tag 08RF] reads

> A posteriori the "correct" vanishing `H_i(C_{B/A}, 𝒦ⁿ) = 0` for `i < n` can be concluded.

This file proves that vanishing for a surjective `A → B`.

## Main results

* `CommAlgCat.isZero_leftDerivedColim_smallPolynomialAugmentationGraded_of_surjective`: the
  dévissage input `H_i(C_{B/A}, 𝒦ᵏ/𝒦ᵏ⁺¹) = 0` for `i < k`, for a surjective `A → B`.
* `CommAlgCat.isZero_leftDerivedColim_smallPolynomialAugmentationIdealPow_of_surjective`: the
  footnote vanishing `H_i(C_{B/A}, 𝒦ⁿ) = 0` for `i < n`, for a surjective `A → B`, assuming the
  pro-nilpotence `CommAlgCat.SmallPolynomialAugmentationProNilpotent`.
* `isZero_leftDerivedColim_smallPolynomialAugmentationIdealPow_of_surjective_unconditional`:
  **the footnote vanishing** for a surjective `A → B`, with no further hypothesis.

## Implementation notes

The vanishing is the dévissage
`CommAlgCat.isZero_leftDerivedColim_smallPolynomialAugmentationIdealPow` applied to two inputs:
the graded pieces vanish in low degree (`hgr`), and the filtration is pro-nilpotent on homology
(`hpro`, which is `CommAlgCat.smallPolynomialAugmentationProNilpotent`). The graded input is the
composite of

* `CommAlgCat.smallPolynomialAugmentationGradedSymmetricPowerIso`, the identification
  `𝒦ᵏ/𝒦ᵏ⁺¹ ≅ Sym^k_{B̲}(Ω)` of the graded pieces with the symmetric powers of
  `Ω = Ω_{𝒪/A} ⊗_𝒪 B̲`, which needs no hypothesis on `A → B`; and
* `CommAlgCat.isZero_leftDerivedColim_symmetricPower_polynomialCotangent_of_surjective`, the
  vanishing clause of [Stacks, Tag 08RF] itself, `H_i(C_{B/A}, Sym^k_{B̲}(Ω)) = 0` for `i < k`,
  for a surjective `A → B`.

The cardinal is `standardResolutionVarCardinal A B` because the second of these goes through
[Stacks, Tag 08RD], which needs a point resolution of the site, here the standard resolution.

## References

* [Stacks Project, Tag 08RF](https://stacks.math.columbia.edu/tag/08RF)
* [Stacks Project, Tag 08PF](https://stacks.math.columbia.edu/tag/08PF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace CommAlgCat

variable (A : Type u) [CommRing A] (B : CommAlgCat.{u} A)

/-- **The graded pieces of the augmentation filtration vanish in low degree**, for a surjective
`A → B`: `H_i(C_{B/A}, 𝒦ᵏ/𝒦ᵏ⁺¹) = 0` for `i < k`.

The graded piece is the `k`-th symmetric power of `Ω` by
`CommAlgCat.smallPolynomialAugmentationGradedSymmetricPowerIso`, which asks nothing of `A → B`,
and the symmetric powers vanish in low degree by the vanishing clause of [Stacks, Tag 08RF],
`CommAlgCat.isZero_leftDerivedColim_symmetricPower_polynomialCotangent_of_surjective`. -/
theorem isZero_leftDerivedColim_smallPolynomialAugmentationGraded_of_surjective
    (hsurj : Function.Surjective (algebraMap A (B : Type u))) (k i : ℕ) (hi : i < k) :
    IsZero (((colim :
          ((smallBoundedPolynomialSite A B (standardResolutionVarCardinal A B))ᵒᵖ ⥤
            ModuleCat.{u} (B : Type u)) ⥤ ModuleCat.{u} (B : Type u)).leftDerived i).obj
      (smallPolynomialAugmentationGraded A B (standardResolutionVarCardinal A B) k)) :=
  (isZero_leftDerivedColim_symmetricPower_polynomialCotangent_of_surjective A B hsurj k i
    hi).of_iso (((colim :
      ((smallBoundedPolynomialSite A B (standardResolutionVarCardinal A B))ᵒᵖ ⥤
        ModuleCat.{u} (B : Type u)) ⥤
          ModuleCat.{u} (B : Type u)).leftDerived i).mapIso
    (smallPolynomialAugmentationGradedSymmetricPowerIso A B
      (standardResolutionVarCardinal A B) k))

/-- **The footnote vanishing of [Stacks, Tag 08RF]**, `H_i(C_{B/A}, 𝒦ⁿ) = 0` for `i < n`, for a
surjective `A → B`, assuming the pro-nilpotence of the augmentation filtration. -/
theorem isZero_leftDerivedColim_smallPolynomialAugmentationIdealPow_of_surjective
    (hsurj : Function.Surjective (algebraMap A (B : Type u)))
    (hpro : SmallPolynomialAugmentationProNilpotent A B (standardResolutionVarCardinal A B))
    (i n : ℕ) (hi : i < n) :
    IsZero (((colim :
          ((smallBoundedPolynomialSite A B (standardResolutionVarCardinal A B))ᵒᵖ ⥤
            ModuleCat.{u} (B : Type u)) ⥤ ModuleCat.{u} (B : Type u)).leftDerived i).obj
      (smallPolynomialAugmentationIdealPow A B (standardResolutionVarCardinal A B) n)) :=
  isZero_leftDerivedColim_smallPolynomialAugmentationIdealPow A B
    (standardResolutionVarCardinal A B)
    (isZero_leftDerivedColim_smallPolynomialAugmentationGraded_of_surjective A B hsurj) hpro i n hi

/-- **The footnote vanishing of [Stacks, Tag 08RF]**, `H_i(C_{B/A}, 𝒦ⁿ) = 0` for `i < n`, for a
surjective `A → B`, with no further hypothesis. -/
theorem isZero_leftDerivedColim_smallPolynomialAugmentationIdealPow_of_surjective_unconditional
    (hsurj : Function.Surjective (algebraMap A (B : Type u))) (i n : ℕ) (hi : i < n) :
    IsZero (((colim :
          ((smallBoundedPolynomialSite A B (standardResolutionVarCardinal A B))ᵒᵖ ⥤
            ModuleCat.{u} (B : Type u)) ⥤ ModuleCat.{u} (B : Type u)).leftDerived i).obj
      (smallPolynomialAugmentationIdealPow A B (standardResolutionVarCardinal A B) n)) :=
  isZero_leftDerivedColim_smallPolynomialAugmentationIdealPow_of_surjective A B hsurj
    (smallPolynomialAugmentationProNilpotent hsurj) i n hi

end CommAlgCat

end
