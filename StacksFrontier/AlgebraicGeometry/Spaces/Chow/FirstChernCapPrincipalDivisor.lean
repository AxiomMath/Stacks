module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.CanonicalFirstChernCapAdditive
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormulaProof.Headline
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrincipalDivisorCycleOfGood
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PrimeDivisorFunctionFieldMeromorphic
public import StacksFrontier.AlgebraicGeometry.Spaces.PicardWeilDivisorClass

/-!
# Capping a principal divisor with the first Chern class of an invertible sheaf

In Situation 0EDT let `X/B` be good and **integral** with `dim_δ(X) = n`, let `ℒ` be an
invertible `𝒪_X`-module and let `f ∈ R(X)^*`.  Then

`c₁(ℒ) ∩ div(f) = 0`  in  `CH_{n-2}(X)`,

for the cap product of Stacks 0EQJ at the canonical choices
(`AlgebraicGeometry.Space.canonicalFirstChernCap`), the principal divisor of Stacks 0EQ1 at the
canonical choices (`AlgebraicGeometry.Space.canonicalPrincipalDivisorCycleAt`) and the Chow
group of Stacks 0EQ6, part (4).

## Main results

* `AlgebraicGeometry.Space.canonicalFirstChernCap_canonicalDivisorCycleAt_tensorUnit_eq_zero`:
  `c₁(ℒ) ∩ div_{𝒪_X}(σ) = 0` for a regular meromorphic section `σ` of the structure sheaf.
* `AlgebraicGeometry.Space.exists_canonicalPrincipalDivisorCycleAt_eq_sub`: the principal
  divisor `div(f)` of Stacks 0EQ1 is a difference of two Weil divisors of Stacks 0EQE taken on
  the structure sheaf.
* `AlgebraicGeometry.Space.canonicalFirstChernCap_canonicalPrincipalDivisorCycleAt_eq_zero`:
  `c₁(ℒ) ∩ div(f) = 0` in `CH_{n-2}(X)`.
* `AlgebraicGeometry.Space.canonicalFirstChernCap_eq_zero_of_isPrincipalDivisorCycle`:
  `c₁(ℒ) ∩ c = 0` in `CH_{n-2}(X)` for a principal divisor cycle `c` in the sense of part (1)
  of Stacks 0EQ6.

## References

* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
* [Stacks Project, Tag 0EQ1](https://stacks.math.columbia.edu/tag/0EQ1)
* [Stacks Project, Tag 0EQ6](https://stacks.math.columbia.edu/tag/0EQ6)
* [Stacks Project, Tag 0EQE](https://stacks.math.columbia.edu/tag/0EQE)
* [Stacks Project, Tag 0EQJ](https://stacks.math.columbia.edu/tag/0EQJ)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology
attribute [local instance] modulesMonoidalCategory

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (sX : X ⟶ D.space)
    (hX : D.IsGood sX) (hint : IsIntegralSpace D.site D.base D.base_mem X)
    (L : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    (hL : IsInvertibleModule (B := D.site) ⟨X, hX.1⟩ L)

/-- In Situation 0EDT let `X/B` be good and integral with `dim_δ(X) = n`, let `ℒ` be invertible
and let `σ` be a regular meromorphic section of the structure sheaf `𝒪_X`, the tensor unit of
`AlgebraicGeometry.Space.Modules`.  Then

`c₁(ℒ) ∩ div_{𝒪_X}(σ) = 0`  in  `CH_{n-2}(X)`. -/
theorem canonicalFirstChernCap_canonicalDivisorCycleAt_tensorUnit_eq_zero
    (σ : MeromorphicSection.{u, u} D.site D.base D.base_mem X hX.1
      (𝟙_ (Modules.{u, u} D.site D.base D.base_mem X hX.1)))
    (hσ : IsRegularMeromorphicSection.{u, u} D.site D.base D.base_mem X hX.1
      (𝟙_ (Modules.{u, u} D.site D.base D.base_mem X hX.1)) σ)
    {n : ℤ} (hn : deltaDimensionClosed D sX hX Set.univ isClosed_univ = (n : EInt)) :
    canonicalFirstChernCap.{u, u + 1} D sX hX L hL (n - 2)
      (canonicalDivisorCycleAt D sX hX hint
        (𝟙_ (Modules.{u, u} D.site D.base D.base_mem X hX.1))
        (isInvertibleModule_tensorUnit hX) σ hσ
        (deltaDimensionClosed_eq_sub_two_add_one_add_one D sX hX hn)) = 0 := by
  have hN := hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sX hX
  obtain ⟨t, ht⟩ :=
    exists_meromorphicSection_ne_zero D.site D.base D.base_mem hX.1 hint hN L hL
  have hσ0 : σ ≠ 0 := ne_zero_of_isRegularMeromorphicSection D.site D.base D.base_mem hX.1 hint
    hN (𝟙_ (Modules.{u, u} D.site D.base D.base_mem X hX.1)) σ hσ
  exact (canonicalFirstChernCap_divisor_comm D sX hX hint
      (𝟙_ (Modules.{u, u} D.site D.base D.base_mem X hX.1))
      (isInvertibleModule_tensorUnit hX) L hL σ hσ0 t ht hn).trans
    (canonicalFirstChernCap_tensorUnit_eq_zero hX (n - 2) _)

/-- **The principal divisor of Stacks 0EQ1 is a difference of two Weil divisors of Stacks 0EQE
on the structure sheaf.**  On a good integral algebraic space `X/B` of δ-dimension `k + 1` and
for `f ∈ R(X)^*` there are regular meromorphic sections `σ`, `τ` of `𝒪_X` with

`div(f) = div_{𝒪_X}(σ) - div_{𝒪_X}(τ)`  in  `Z_k(X)`. -/
theorem exists_canonicalPrincipalDivisorCycleAt_eq_sub
    (f : (rationalFunctions D.site D.base D.base_mem hX.1)ˣ) {k : ℤ}
    (hk : deltaDimensionClosed D sX hX Set.univ isClosed_univ = ((k + 1 : ℤ) : EInt)) :
    ∃ (σ τ : MeromorphicSection.{u, u} D.site D.base D.base_mem X hX.1
        (𝟙_ (Modules.{u, u} D.site D.base D.base_mem X hX.1)))
      (hσ : IsRegularMeromorphicSection.{u, u} D.site D.base D.base_mem X hX.1
        (𝟙_ (Modules.{u, u} D.site D.base D.base_mem X hX.1)) σ)
      (hτ : IsRegularMeromorphicSection.{u, u} D.site D.base D.base_mem X hX.1
        (𝟙_ (Modules.{u, u} D.site D.base D.base_mem X hX.1)) τ),
      canonicalPrincipalDivisorCycleAt D sX hX hint f hk =
        canonicalDivisorCycleAt D sX hX hint
            (𝟙_ (Modules.{u, u} D.site D.base D.base_mem X hX.1))
            (isInvertibleModule_tensorUnit hX) σ hσ hk -
          canonicalDivisorCycleAt D sX hX hint
            (𝟙_ (Modules.{u, u} D.site D.base D.base_mem X hX.1))
            (isInvertibleModule_tensorUnit hX) τ hτ hk := by
  have hN := hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sX hX
  have hdec := isDecentSpace_of_isGood D sX hX
  set O := 𝟙_ (Modules.{u, u} D.site D.base D.base_mem X hX.1) with hO
  set E := genericFractionEmbedding D.site D.base D.base_mem hX.1 hdec hint hN with hE
  let := E.nontrivial
  let := E.isNoetherianRing
  let := E.krullDimLE
  obtain ⟨τ, hτ, hratio⟩ :=
    exists_isRegularMeromorphicSection_canonicalLocalRatio_eq_genericEmb_mul D.site D.base
      D.base_mem hX.1 hdec hint hN O (isInvertibleModule_tensorUnit hX) f
  have hσ := isRegularMeromorphicSection_regularMeromorphicSection D.site D.base D.base_mem hX.1
    hint hN O (isInvertibleModule_tensorUnit hX)
  set σ := regularMeromorphicSection D.site D.base D.base_mem hX.1 hint hN O
    (isInvertibleModule_tensorUnit hX)
  refine ⟨σ, τ, hσ, hτ, Subtype.ext (funext fun Z => ?_)⟩
  have hsub : (canonicalDivisorCycleAt D sX hX hint O (isInvertibleModule_tensorUnit hX) σ hσ hk -
        canonicalDivisorCycleAt D sX hX hint O (isInvertibleModule_tensorUnit hX) τ hτ hk).1 Z =
      divisorCycleCoefficients D sX hX hdec O σ _ Z -
        divisorCycleCoefficients D sX hX hdec O τ _ Z :=
    rfl
  rw [hsub, show (canonicalPrincipalDivisorCycleAt D sX hX hint f hk).1 Z =
      principalDivisorCycleCoefficients D sX hX hdec E.emb
        (f : rationalFunctions D.site D.base D.base_mem hX.1)
        (fun W => f.isUnit.map (E.emb W)) Z from rfl]
  by_cases hcod : codimension
      (integralClosedSubspaceSupport D.site D.base D.base_mem hX.1 Z) = 1
  · rw [divisorCycleCoefficients_of_codimension_eq_one D sX hX _ O σ _ hcod,
      divisorCycleCoefficients_of_codimension_eq_one D sX hX _ O τ _ hcod]
    have hord := orderOfVanishingSection_eq_add_ord_of_ratio_eq D.site D.base D.base_mem hX.1
      hdec E (Z.toPrimeDivisor D.site D.base D.base_mem hX.1 hcod) O O σ τ _ _ f
      (hratio (Z.toPrimeDivisor D.site D.base D.base_mem hX.1 hcod))
    simp only [divisorCoefficients, principalDivisorCycleCoefficients, dite_eq_left hcod]
    rw [hord]
    exact (add_sub_cancel_left _ _).symm
  · rw [divisorCycleCoefficients_of_codimension_ne_one D sX hX _ O σ _ hcod,
      divisorCycleCoefficients_of_codimension_ne_one D sX hX _ O τ _ hcod]
    simp only [principalDivisorCycleCoefficients, dite_eq_right hcod, sub_self]

/-- **`c₁(ℒ) ∩ div(f) = 0` in `CH_{n-2}(X)`**, for `X/B` good and integral with
`dim_δ(X) = n`, `ℒ` an invertible `𝒪_X`-module and `f ∈ R(X)^*`: the cap product of Stacks 0EQJ
kills the principal divisor of Stacks 0EQ1. -/
theorem canonicalFirstChernCap_canonicalPrincipalDivisorCycleAt_eq_zero
    (f : (rationalFunctions D.site D.base D.base_mem hX.1)ˣ) {n : ℤ}
    (hn : deltaDimensionClosed D sX hX Set.univ isClosed_univ = (n : EInt)) :
    canonicalFirstChernCap.{u, u + 1} D sX hX L hL (n - 2)
      (canonicalPrincipalDivisorCycleAt D sX hX hint f
        (deltaDimensionClosed_eq_sub_two_add_one_add_one D sX hX hn)) = 0 := by
  obtain ⟨σ, τ, hσ, hτ, heq⟩ := exists_canonicalPrincipalDivisorCycleAt_eq_sub D sX hX hint f
    (deltaDimensionClosed_eq_sub_two_add_one_add_one D sX hX hn)
  rw [heq, map_sub,
    canonicalFirstChernCap_canonicalDivisorCycleAt_tensorUnit_eq_zero D sX hX hint L hL σ hσ hn,
    canonicalFirstChernCap_canonicalDivisorCycleAt_tensorUnit_eq_zero D sX hX hint L hL τ hτ hn,
    sub_zero]

/-- **The cap product of Stacks 0EQJ kills a principal divisor cycle on a good integral
algebraic space.**  If `X/B` is good and integral with `dim_δ(X) = n` and `c ∈ Z_{n-1}(X)` is a
principal divisor cycle in the sense of part (1) of Stacks 0EQ6
(`AlgebraicGeometry.Space.IsPrincipalDivisorCycleOfGood`), that is, its coefficients are those of
`div(f)` for some `f ∈ R(X)^*`, then `c₁(ℒ) ∩ c = 0` in `CH_{n-2}(X)`. -/
theorem canonicalFirstChernCap_eq_zero_of_isPrincipalDivisorCycle {n : ℤ}
    (hn : deltaDimensionClosed D sX hX Set.univ isClosed_univ = (n : EInt))
    (c : CycleGroup D sX (n - 2 + 1))
    (hc : IsPrincipalDivisorCycleOfGood D sX hX hint (n - 2 + 1) c) :
    canonicalFirstChernCap.{u, u + 1} D sX hX L hL (n - 2) c = 0 := by
  obtain ⟨g, hg, hcoe⟩ := hc
  rw [show c = canonicalPrincipalDivisorCycleAt D sX hX hint hg.unit
      (deltaDimensionClosed_eq_sub_two_add_one_add_one D sX hX hn) from Subtype.ext hcoe]
  exact canonicalFirstChernCap_canonicalPrincipalDivisorCycleAt_eq_zero D sX hX hint L hL _ hn

end AlgebraicGeometry.Space

end
