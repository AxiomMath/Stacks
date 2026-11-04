module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatIntegralDeltaDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatPullbackSectionWeilDivisor
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatPullbackSectionWeilDivisorIntegral
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.MultiplicativeTorsorCycles
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.MultiplicativeTorsorIntegral

/-!
# The divisor of a meromorphic section pulled back to the multiplicative torsor

In Situation 0EDT let `X/B` be good and integral, let `ℒ` be an invertible `𝒪_X`-module, let `s`
be a nonzero meromorphic section of `ℒ`, and let

  `q : T = \underline{Spec}_X(⨁_{n ∈ ℤ} ℒ^{⊗ n}) ⟶ X`

be the morphism of Stacks 0EQG (`AlgebraicGeometry.Space.torsorOfInvertibleProjection`), which is
flat of relative dimension one with `T/B` good and `T` integral. **Stacks 0EQH** asserts

  `q^* div_ℒ(s) = div_T(q^*(s))`,

where `q^*(s)` is viewed as a nonzero meromorphic function on `T` through an isomorphism
`α : q^*ℒ ≅ 𝒪_T`.

## Main results

* `AlgebraicGeometry.Space.deltaDimensionClosed_torsorOfInvertibleSpace`: `dim_δ(T) = n + 1`.
* `AlgebraicGeometry.Space.flatPullbackMap_sectionWeilDivisor_torsorOfInvertible`: **Stacks
  0EQH**.

## Implementation notes

The statement is proved in two forms, and the registered declaration asserts both:

1. `q^* div_ℒ(s) = div_{q^*ℒ}(q^*s)` in `Z_n(T)`, the right-hand side being the Weil divisor of
   Stacks 0EQE of the pulled-back section (Stacks 0ENC) of the invertible module `q^*ℒ` on the
   integral space `T`;
2. for **every** isomorphism `α : q^*ℒ ≅ 𝒪_T`, `q^* div_ℒ(s) = div_{𝒪_T}(α(q^*s))`, where
   `α(q^*s)` is the image of `q^*s` under `𝒦_T(q^*ℒ) ≅ 𝒦_T(𝒪_T) = 𝒦_T`, a nonzero meromorphic
   function on `T`, and `div_{𝒪_T}` is the Weil divisor of Stacks 0EQE for `𝒪_T`, which is the
   `div_T` of meromorphic functions. Quantifying over `α` covers the isomorphism of Stacks 0EQG,
   part (2), whichever it is.

Both sides are cycles: the left-hand side is the flat pullback of Stacks 0EP8
(`AlgebraicGeometry.Space.flatPullbackMap`) along `q` of relative dimension one, so it lies in
`Z_{(n - 1) + 1}(T)`, written `Z_{n + 1 - 1}(T)` to match the divisors on `T`, whose δ-dimension
is `n + 1`.

## References

* [Stacks Project, Tag 0EQH](https://stacks.math.columbia.edu/tag/0EQH)
* [Stacks Project, Tag 0EQG](https://stacks.math.columbia.edu/tag/0EQG)
* [Stacks Project, Tag 0EQQ](https://stacks.math.columbia.edu/tag/0EQQ)
* [Stacks Project, Tag 0EQE](https://stacks.math.columbia.edu/tag/0EQE)
* [Stacks Project, Tag 0EP8](https://stacks.math.columbia.edu/tag/0EP8)
* [Stacks Project, Tag 0ENC](https://stacks.math.columbia.edu/tag/0ENC)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (p : X ⟶ D.space) (hp : D.IsGood p) (hint : IsIntegralSpace D.site D.base D.base_mem X)
    (L : Modules.{u, u} D.site D.base D.base_mem X hp.1) (hL : IsInvertibleSheaf D p hp L)

include hint in
/-- The δ-dimension of the multiplicative torsor of `ℒ` on an integral `X` of δ-dimension `n` is
`n + 1`. -/
theorem deltaDimensionClosed_torsorOfInvertibleSpace {n : ℤ}
    (hn : deltaDimensionClosed D p hp Set.univ isClosed_univ = (n : EInt)) :
    deltaDimensionClosed D ((torsorOfInvertibleProjection D p hp L hL).hom ≫ p)
        (isGood_torsorOfInvertible D p hp L hL) Set.univ isClosed_univ =
      ((n + ((1 : ℕ) : ℤ) : ℤ) : EInt) := by
  have := hint.irreducibleSpace
  have := (isIntegralSpace_torsorOfInvertibleSpace D p hp L hL hint).irreducibleSpace
  exact deltaDimensionClosed_univ_eq_add_of_isFlat D
    ((torsorOfInvertibleProjection D p hp L hL).hom ≫ p) (isGood_torsorOfInvertible D p hp L hL)
    p hp rfl 1 (isFlat_torsorOfInvertibleProjection D p hp L hL)
    (hasRelativeDimension_torsorOfInvertibleProjection D p hp L hL) inferInstance hn

include hint in
/-- In Situation 0EDT let `X/B` be good and integral with `n = dim_δ(X)`, let
`ℒ` be an invertible `𝒪_X`-module, let `s` be a nonzero meromorphic section of `ℒ`, and let
`q : T ⟶ X` be the morphism of Stacks 0EQG. Then

  `q^* div_ℒ(s) = div_T(q^*(s))`

in `Z_n(T)`: the left-hand side is the flat pullback along `q` (flat of relative dimension one) of
the Weil divisor of `s`; on the right `q^*(s)` is the pullback of `s`, and the identity holds both
with `div_{q^*ℒ}(q^*s)` and, for every isomorphism `α : q^*ℒ ≅ 𝒪_T`, with the divisor
`div_{𝒪_T}(α(q^*s))` of the meromorphic function `α(q^*s)` on `T`. -/
@[stacks 0EQH "q^* div_L(s) = div_T(q^*(s)) as cycles on T, for X/B good and integral, L
invertible, s a nonzero meromorphic section and q : T -> X the morphism of 0EQG
(torsorOfInvertibleProjection: flat of relative dimension 1, T/B good, T integral, all proved).
Stated with div_{q^*L}(q^*s) and, for EVERY isomorphism alpha : q^*L ≅ O_T, with the divisor
div_{O_T}(alpha(q^*s)) of the nonzero meromorphic function alpha(q^*s); q^* on cycles is the flat
pullback of 0EP8, div is 0EQE, q^*s is the pullback of 0ENC. Proved from 0EQQ for q (T integral,
so the component sum collapses) and the invariance of div under an isomorphism of modules"]
theorem flatPullbackMap_sectionWeilDivisor_torsorOfInvertible {n : ℤ}
    (hn : deltaDimensionClosed D p hp Set.univ isClosed_univ = (n : EInt))
    (s : MeromorphicSection.{u, u} D.site D.base D.base_mem X hp.1 L) (hs : s ≠ 0) :
    flatPullbackMap D ((torsorOfInvertibleProjection D p hp L hL).hom ≫ p)
        (isGood_torsorOfInvertible D p hp L hL) p hp (torsorOfInvertibleProjection D p hp L hL).hom
        rfl 1 (isFlat_torsorOfInvertibleProjection D p hp L hL)
        (hasRelativeDimension_torsorOfInvertibleProjection D p hp L hL) (n - 1) (n + (1 : ℕ) - 1)
        (by push_cast; ring) (sectionWeilDivisor D p hp hint L hL hn s hs) =
      sectionWeilDivisor D ((torsorOfInvertibleProjection D p hp L hL).hom ≫ p)
        (isGood_torsorOfInvertible D p hp L hL)
        (isIntegralSpace_torsorOfInvertibleSpace D p hp L hL hint)
        ((modulePullback D.site D.base D.base_mem (torsorOfInvertibleProjection D p hp L hL)).obj L)
        (isInvertibleSheaf_modulePullback D p hp _ (isGood_torsorOfInvertible D p hp L hL)
          (torsorOfInvertibleProjection D p hp L hL) hL)
        (deltaDimensionClosed_torsorOfInvertibleSpace D p hp hint L hL hn)
        (pullbackMeromorphicSection D.site D.base D.base_mem
          (torsorOfInvertibleProjection D p hp L hL) L
          (pullbacksMeromorphicSections_of_flat D.site D.base D.base_mem _
            (isFlat_torsorOfInvertibleProjection D p hp L hL)) s)
        (pullbackMeromorphicSection_ne_zero_of_isFlat D p hp hint _
          (isGood_torsorOfInvertible D p hp L hL)
          (isIntegralSpace_torsorOfInvertibleSpace D p hp L hL hint) _
          (isFlat_torsorOfInvertibleProjection D p hp L hL) hL s hs) ∧
    ∀ α : (modulePullback D.site D.base D.base_mem
          (torsorOfInvertibleProjection D p hp L hL)).obj L ≅
        SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite D.site
          D.base D.base_mem (torsorOfInvertibleSpace D p hp L hL).obj
          (isGood_torsorOfInvertible D p hp L hL).1).O),
      flatPullbackMap D ((torsorOfInvertibleProjection D p hp L hL).hom ≫ p)
          (isGood_torsorOfInvertible D p hp L hL) p hp
          (torsorOfInvertibleProjection D p hp L hL).hom
          rfl 1 (isFlat_torsorOfInvertibleProjection D p hp L hL)
          (hasRelativeDimension_torsorOfInvertibleProjection D p hp L hL) (n - 1) (n + (1 : ℕ) - 1)
          (by push_cast; ring) (sectionWeilDivisor D p hp hint L hL hn s hs) =
        sectionWeilDivisor D ((torsorOfInvertibleProjection D p hp L hL).hom ≫ p)
          (isGood_torsorOfInvertible D p hp L hL)
          (isIntegralSpace_torsorOfInvertibleSpace D p hp L hL hint) _
          (isInvertibleSheaf_unit D _ (isGood_torsorOfInvertible D p hp L hL))
          (deltaDimensionClosed_torsorOfInvertibleSpace D p hp hint L hL hn)
          (SheafOfModules.sectionsMap
            (meromorphicSectionSheafMap D.site D.base D.base_mem _
              (isGood_torsorOfInvertible D p hp L hL).1 α.hom)
            (pullbackMeromorphicSection D.site D.base D.base_mem
              (torsorOfInvertibleProjection D p hp L hL) L
              (pullbacksMeromorphicSections_of_flat D.site D.base D.base_mem _
                (isFlat_torsorOfInvertibleProjection D p hp L hL)) s))
          (sectionsMap_meromorphicSectionSheafMap_inv_ne_zero D _
            (isGood_torsorOfInvertible D p hp L hL)
            (isIntegralSpace_torsorOfInvertibleSpace D p hp L hL hint)
            (isInvertibleSheaf_unit D _ (isGood_torsorOfInvertible D p hp L hL))
            (isInvertibleSheaf_modulePullback D p hp _ (isGood_torsorOfInvertible D p hp L hL)
              (torsorOfInvertibleProjection D p hp L hL) hL) α.symm _
            (pullbackMeromorphicSection_ne_zero_of_isFlat D p hp hint _
              (isGood_torsorOfInvertible D p hp L hL)
              (isIntegralSpace_torsorOfInvertibleSpace D p hp L hL hint) _
              (isFlat_torsorOfInvertibleProjection D p hp L hL) hL s hs)) := by
  have hmain := (flatPullbackMap_sectionWeilDivisor_eq_componentDivisorSum D _
      (isGood_torsorOfInvertible D p hp L hL) p hp _ rfl 1
      (isFlat_torsorOfInvertibleProjection D p hp L hL)
      (hasRelativeDimension_torsorOfInvertibleProjection D p hp L hL) hint hn L hL s hs).trans
    (componentDivisorSum_eq_sectionWeilDivisor_of_isIntegralSpace D _
      (isGood_torsorOfInvertible D p hp L hL) p hp _ rfl 1
      (isFlat_torsorOfInvertibleProjection D p hp L hL)
      (hasRelativeDimension_torsorOfInvertibleProjection D p hp L hL) hint hn L hL s hs
      (isIntegralSpace_torsorOfInvertibleSpace D p hp L hL hint)
      (deltaDimensionClosed_torsorOfInvertibleSpace D p hp hint L hL hn))
  exact ⟨hmain, fun α => hmain.trans
    (sectionWeilDivisor_sectionsMap_meromorphicSectionSheafMap_inv D _
      (isGood_torsorOfInvertible D p hp L hL)
      (isIntegralSpace_torsorOfInvertibleSpace D p hp L hL hint)
      (isInvertibleSheaf_unit D _ (isGood_torsorOfInvertible D p hp L hL))
      (isInvertibleSheaf_modulePullback D p hp _ (isGood_torsorOfInvertible D p hp L hL)
        (torsorOfInvertibleProjection D p hp L hL) hL)
      (deltaDimensionClosed_torsorOfInvertibleSpace D p hp hint L hL hn) α.symm _ _).symm⟩

end AlgebraicGeometry.Space

end
