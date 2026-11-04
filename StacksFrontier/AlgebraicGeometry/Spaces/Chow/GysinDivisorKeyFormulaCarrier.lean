module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FirstChernCapPrincipalDivisorCanonical
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FirstChernCapRuleDifferenceCanonical
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.GysinDivisorKeyFormula

/-!
# The key formula against a principal divisor, with the carrier inside the divisor

In Situation 0EDT let `Y/B` be good and integral with `dim_δ(Y) = k + 2`, let `ℒ` be an invertible
`𝒪_Y`-module with a nonzero global section `σ`, and let `D = Z(σ)` be its vanishing locus.  For
a principal divisor `div(f)` on `Y` (`f ∈ R(Y)^*`, read at the canonical embeddings of Stacks
0ENK) the cap product of Stacks 0EQJ

`c₁(ℒ) ∩ div(f)`

formed at the generator rule of the source's choice `s_i = σ` off `D` is rationally equivalent to
zero at the canonical embeddings **within `|D|`**.

This is the case `𝒩 = 𝒪_Y`, `t = f` of the proof of Stacks 0ER9, stopped before the descent to
`D`, and with nothing about `c₁(𝒪_Y)` needed: `div(f)` is the difference `div_{𝒪_Y}(τ₁) -
div_{𝒪_Y}(τ₂)` of the Weil divisors of two regular meromorphic sections of `𝒪_Y`
(`AlgebraicGeometry.Space.exists_canonicalPrincipalDivisorCycleAt_eq_sub`), and for each of them
the key formula of Stacks 0EQV gives

`c₁(𝒪_Y) ∩ div_ℒ(σ) - c₁(ℒ) ∩ div_{𝒪_Y}(τ_i) = (key formula cycle)_i`,

each key formula cycle being rationally equivalent to zero within `|D|`
(`AlgebraicGeometry.Space.isRationallyEquivalentToZeroWithinCanonical_keyFormulaDivisorSum`,
the members at which the generator of `ℒ_ξ` is not `σ` being the ones inside `D`).  The common
term `c₁(𝒪_Y) ∩ div_ℒ(σ)` — formed at one and the same generator rule for both `i` — cancels in
the difference.

## Main results

* `isRationallyEquivalentToZeroWithinCanonical_firstChernCapCycleMap_generatorChernRule`: the
  statement above.

## References

* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
* [Stacks Project, Tag 0ENK](https://stacks.math.columbia.edu/tag/0ENK)
* [Stacks Project, Tag 0EQJ](https://stacks.math.columbia.edu/tag/0EQJ)
* [Stacks Project, Tag 0EQU](https://stacks.math.columbia.edu/tag/0EQU)
* [Stacks Project, Tag 0EQV](https://stacks.math.columbia.edu/tag/0EQV)
* [Stacks Project, Tag 0ER9](https://stacks.math.columbia.edu/tag/0ER9)
* [Stacks Project, Tag 0ERA](https://stacks.math.columbia.edu/tag/0ERA)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology
attribute [local instance] modulesMonoidalCategory

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX)
    (hint : IsIntegralSpace D.site D.base D.base_mem X)
    (L : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    (hL : IsInvertibleModule (B := D.site) ⟨X, hX.1⟩ L)
    {k : ℤ}
    (hn : deltaDimensionClosed D sX hX Set.univ isClosed_univ = ((k + 1 + 1 : ℤ) : EInt))
    (σ : L.sections) (hσ : σ ≠ 0)

include hint hn hσ in
/-- **One key formula, carried inside the divisor.**  For a regular meromorphic section `τ` of
`𝒪_X` and any family `w` of generators of `𝒪_{X,ξ}`, the difference

`c₁(𝒪_X) ∩ div_ℒ(σ) - c₁(ℒ) ∩ div_{𝒪_X}(τ)`

of the cap products at the generator rules of `w` and of the source's choice `s_i = σ` off
`D = Z(σ)` is rationally equivalent to zero at the canonical embeddings within `|D|`. -/
theorem isRationallyEquivalentToZeroWithinCanonical_keyFormula_tensorUnit
    (τ : MeromorphicSection.{u, u} D.site D.base D.base_mem X hX.1
      (𝟙_ (Modules.{u, u} D.site D.base D.base_mem X hX.1)))
    (hτ : IsRegularMeromorphicSection.{u, u} D.site D.base D.base_mem X hX.1
      (𝟙_ (Modules.{u, u} D.site D.base D.base_mem X hX.1)) τ)
    (w : GenericUnitFamily D sX hX) :
    IsRationallyEquivalentToZeroWithinCanonical.{u + 1} D sX hX k
      (firstChernCapCycleMap D sX hX k
          (generatorChernRule D sX hX hint (𝟙_ (Modules.{u, u} D.site D.base D.base_mem X hX.1))
            (isInvertibleModule_tensorUnit hX) hn w)
          (canonicalDivisorCycleAt D sX hX hint L hL
            (globalSectionMeromorphic D.site D.base D.base_mem hX.1 L σ)
            (isRegularMeromorphicSection_of_ne_zero_of_isGood D sX hX hint L hL
              (globalSectionMeromorphic_ne_zero_of_isInvertibleSheaf D sX hX L hL hσ)) hn) -
        firstChernCapCycleMap D sX hX k
          (generatorChernRule D sX hX hint L hL hn (sectionGeneratorUnit D sX hX hint L hL σ))
          (canonicalDivisorCycleAt D sX hX hint
            (𝟙_ (Modules.{u, u} D.site D.base D.base_mem X hX.1))
            (isInvertibleModule_tensorUnit hX) τ hτ hn))
      (subspacePointSet D.site D.base D.base_mem X (vanishingLocus D sX hX L σ).1) := by
  have hsr := isRegularMeromorphicSection_of_ne_zero_of_isGood D sX hX hint L hL
    (globalSectionMeromorphic_ne_zero_of_isInvertibleSheaf D sX hX L hL hσ)
  have hcov : ∀ W : PrimeDivisor D.site D.base D.base_mem X,
      (∀ i : {W : PrimeDivisor D.site D.base D.base_mem X //
          ¬ (W.SectionGenerates D sX hX hint L hL
              (globalSectionMeromorphic D.site D.base D.base_mem hX.1 L σ) ∧
            W.SectionGenerates D sX hX hint
              (𝟙_ (Modules.{u, u} D.site D.base D.base_mem X hX.1))
              (isInvertibleModule_tensorUnit hX) τ)},
        (i : PrimeDivisor D.site D.base D.base_mem X) ≠ W) →
        W.SectionGenerates D sX hX hint L hL
            (globalSectionMeromorphic D.site D.base D.base_mem hX.1 L σ) ∧
          W.SectionGenerates D sX hX hint (𝟙_ (Modules.{u, u} D.site D.base D.base_mem X hX.1))
            (isInvertibleModule_tensorUnit hX) τ :=
    fun W hW => not_not.1 fun h => hW ⟨W, h⟩ rfl
  have hfin := locallyFinite_primeDivisor_not_sectionGenerates D sX hX hint L hL _ hsr
    (𝟙_ (Modules.{u, u} D.site D.base D.base_mem X hX.1)) (isInvertibleModule_tensorUnit hX) τ hτ
  rw [firstChernCapCycleMap_generatorChernRule_sub_eq_keyFormulaDivisorSum D sX hX hint L hL
      hn σ hσ (𝟙_ (Modules.{u, u} D.site D.base D.base_mem X hX.1))
      (isInvertibleModule_tensorUnit hX) τ hτ Subtype.val hfin Subtype.val_injective
      (fun W hW => (hcov W hW).1) (fun W hW => (hcov W hW).2)
      (sectionGeneratorUnit D sX hX hint L hL σ) w]
  exact isRationallyEquivalentToZeroWithinCanonical_keyFormulaDivisorSum D sX hX hint L hL
    (globalSectionMeromorphic D.site D.base D.base_mem hX.1 L σ) _
    (𝟙_ (Modules.{u, u} D.site D.base D.base_mem X hX.1)) (isInvertibleModule_tensorUnit hX) τ
    hτ hn Subtype.val hfin _ _ Subtype.val_injective hcov
    (fun i => (i.1).subspace ≤ (vanishingLocus D sX hX L σ).1)
    (fun i hi => canonicalGenericRatio_globalSectionMeromorphic_sectionGeneratorUnit D sX hX hint
      L hL σ i.1 hi)
    (subspacePointSet D.site D.base D.base_mem X (vanishingLocus D sX hX L σ).1)
    fun _ hi => subspacePointSet_mono_of_le D hi

include hint hσ in
/-- **`c₁(ℒ) ∩ div(f)` is rationally equivalent to zero within the divisor.**  In Situation 0EDT
let `X/B` be good and integral of δ-dimension `k + 2`, let `ℒ` be invertible with a nonzero global
section `σ`, and let `d ∈ Z_{k+1}(X)` be a principal divisor cycle at the canonical embeddings of
Stacks 0ENK.  Then the cap product of Stacks 0EQJ of `d`, formed at the generator rule of the
source's choice `s_i = σ` off `D = Z(σ)`, is rationally equivalent to zero at the canonical
embeddings within `|D|`. -/
theorem isRationallyEquivalentToZeroWithinCanonical_firstChernCapCycleMap_generatorChernRule
    (d : CycleGroup D sX (k + 1))
    (hd : IsPrincipalDivisorCycleOfGood D sX hX hint (k + 1) d) :
    IsRationallyEquivalentToZeroWithinCanonical.{u + 1} D sX hX k
      (firstChernCapCycleMap D sX hX k
        (generatorChernRule D sX hX hint L hL hn (sectionGeneratorUnit D sX hX hint L hL σ)) d)
      (subspacePointSet D.site D.base D.base_mem X (vanishingLocus D sX hX L σ).1) := by
  obtain ⟨g, hg, hcoe⟩ := hd
  rw [show d = canonicalPrincipalDivisorCycleAt D sX hX hint hg.unit hn from Subtype.ext hcoe]
  obtain ⟨τ₁, τ₂, hτ₁, hτ₂, heq⟩ :=
    exists_canonicalPrincipalDivisorCycleAt_eq_sub D sX hX hint hg.unit hn
  rw [heq, map_sub]
  simpa only [sub_sub_sub_cancel_left] using
    (isRationallyEquivalentToZeroWithinCanonical_keyFormula_tensorUnit D sX hX hint L hL hn σ hσ τ₂
      hτ₂ fun _ => 1).sub
    (isRationallyEquivalentToZeroWithinCanonical_keyFormula_tensorUnit D sX hX hint L hL hn σ hσ τ₁
      hτ₁ fun _ => 1)

end AlgebraicGeometry.Space

end
