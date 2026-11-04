module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormulaSection
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PrimeDivisorGlobalSectionCoefficient

/-!
# "`s` generates `ℒ_ξ`" for a global section is the germ being a unit

In Situation 0EDT let `X/B` be good and integral, let `ℒ` be an invertible `𝒪_X`-module, let
`σ ∈ Γ(X, ℒ)` be a global section and let `Z ⊂ X` be a prime divisor with generic point `ξ` and
chosen affine elementary étale neighbourhood `(U, u)`.  Section 0EQU's condition that `σ`
generate `ℒ_ξ` is `AlgebraicGeometry.Space.PrimeDivisor.SectionGenerates`: the ratio `σ / s_ξ` of
Stacks 0EPR is the image of a unit of `B = 𝒪^h_{X,ξ}`.

For a *global* section that ratio is the image of the germ at `u` of the coefficient of `σ`
against the generator `s_ξ` on `Spec 𝒪_{U,u}`
(`AlgebraicGeometry.Space.PrimeDivisor.canonicalGenericRatio_globalSectionMeromorphic`), so the
condition follows from that germ being a unit of `𝒪_{U,u}`.

## Main results

* `AlgebraicGeometry.Space.PrimeDivisor.sectionGenerates_globalSectionMeromorphic_of_isUnit`:
  `σ` generates `ℒ_ξ` as soon as its germ against `s_ξ` is a unit of `𝒪_{U,u}`.

## References

* [Stacks Project, Section 0EQU](https://stacks.math.columbia.edu/tag/0EQU)
* [Stacks Project, Tag 0EPR](https://stacks.math.columbia.edu/tag/0EPR)
* [Stacks Project, Tag 0845](https://stacks.math.columbia.edu/tag/0845)
* [Stacks Project, Tag 0ER9](https://stacks.math.columbia.edu/tag/0ER9)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (sX : X ⟶ D.space)
    (hX : D.IsGood sX) (hint : IsIntegralSpace D.site D.base D.base_mem X)
    (Z : PrimeDivisor D.site D.base D.base_mem X)
    (L : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    (hL : IsInvertibleModule (B := D.site) ⟨X, hX.1⟩ L)

include hint in
/-- **A global section generates `ℒ_ξ` as soon as its germ against `s_ξ` is a unit.**  Let `σ` be
a global section of an invertible `𝒪_X`-module on a good integral algebraic space and let `Z` be
a prime divisor with generic point `ξ` and chosen affine elementary étale neighbourhood `(U, u)`.
If the coefficient of `σ` against the generator `s_ξ`, read as a germ in `𝒪_{U,u}`
(`AlgebraicGeometry.Space.PrimeDivisor.globalSectionGerm`), is a unit, then the meromorphic
section of `σ` satisfies `AlgebraicGeometry.Space.PrimeDivisor.SectionGenerates`. -/
theorem PrimeDivisor.sectionGenerates_globalSectionMeromorphic_of_isUnit (σ : L.sections)
    (hu : IsUnit (Z.globalSectionGerm D.site D.base D.base_mem hX.1
      (isDecentSpace_of_isGood D sX hX) L hL σ)) :
    Z.SectionGenerates D sX hX hint L hL
      (globalSectionMeromorphic D.site D.base D.base_mem hX.1 L σ) :=
  ⟨stalkToHenselianLocalRing D.site D.base D.base_mem X hX.1 (Z.genericPoint _ _ _ X)
      (isDecentSpace_of_isGood D sX hX) (Z.genericChart D.site D.base D.base_mem hX.1
        (isDecentSpace_of_isGood D sX hX))
      (Z.globalSectionGerm D.site D.base D.base_mem hX.1 (isDecentSpace_of_isGood D sX hX) L hL σ),
    hu.map _,
    Z.canonicalGenericRatio_globalSectionMeromorphic D.site D.base D.base_mem hX.1
      (isDecentSpace_of_isGood D sX hX) L hL hint
      (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sX hX) σ⟩

end AlgebraicGeometry.Space

end
