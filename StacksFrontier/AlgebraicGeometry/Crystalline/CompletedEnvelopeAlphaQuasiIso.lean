module

public import StacksFrontier.AlgebraicGeometry.Crystalline.CompletedConnectionBaseChangeIsoValues
public import StacksFrontier.AlgebraicGeometry.Crystalline.CompletedEnvelopeFactorizationComplexes

/-!
# The automorphism `α` of the source's proof of 07LH is invertible on the de Rham complexes

The proof of [Stacks, Lemma 60.21.4, Tag 07LH] factors an augmentation-compatible divided power
`A`-algebra endomorphism `ρ` of `D` as `D --σ--> D⟨ξ_i⟩^∧ --τ--> D` and uses the automorphism `α`
of `D⟨ξ_i⟩^∧` with `α(x_i) = x_i - ξ_i`, `α(ξ_i) = ξ_i`, for which `α ∘ σ = ν`.  Reading `α` on
the completed de Rham complexes gives
`Crystalline.envelopeCompletionAlphaComplexHom`, and the source's sentence "using that `α` is an
isomorphism" asks for that map to be invertible.

Until now that was the hypothesis `halpha` of
`Crystalline.isIso_homologyMap_sigmaComplexHom` and of
`Crystalline.isIso_homologyMap_of_sigmaFactorization`.  This module **proves it**, with no
hypothesis beyond the two square-zero conditions that make the two complexes exist: `α` is a
divided power automorphism (`Crystalline.envelopeCompletionAlpha_comp_alphaInv` and
`Crystalline.envelopeCompletionAlphaInv_comp_alpha`), the comparisons of completed forms along
`α` and `α⁻¹` are mutually inverse
(`Crystalline.envelopeCompletionAlphaForms_alphaInvForms` and
`Crystalline.envelopeCompletionAlphaInvForms_alphaForms`), and the base change of a completed de
Rham complex along such a map is an isomorphism of complexes by
`Crystalline.CompletedDeRham.isIso_baseChangeComplexHom_of_inverse`.

## Main definitions

* `Crystalline.algebraEnvelopeCompletionAlphaInv` — `α⁻¹` as the algebra structure of the `σ`
  copy of `D⟨ξ_i⟩^∧` over `D⟨ξ_i⟩^∧` itself, the structure in the opposite direction to
  `Crystalline.algebraEnvelopeCompletionAlpha`.
* `Crystalline.envelopeCompletionAlphaInvFormsOfAlgebra` — the comparison of completed forms
  along `α⁻¹`, read over that algebra structure.

## Main results

* `Crystalline.isScalarTower_envelopeCompletionAlphaInv_comp_alpha` and
  `Crystalline.isScalarTower_envelopeCompletionAlpha_comp_alphaInv` — the two round trips of `α`
  as scalar towers.
* `Crystalline.isIso_envelopeCompletionAlphaComplexHom` — **the base change map of completed de
  Rham complexes along `α` is an isomorphism of complexes.**
* `Crystalline.isIso_homologyMap_envelopeCompletionAlphaComplexHom` — **it is therefore
  invertible on homology in every degree**, which is `halpha`.

## What this does and does not do to Tag 07LH

No `@[stacks 07LH]` attribute is placed.  This discharges one of the three inputs of
`Crystalline.isIso_homologyMap_of_sigmaFactorization`, namely `halpha`.  The other two remain:
`hnu`, the completed clause of [Stacks, Lemma 60.20.2, Tag 07LD] read as the invertibility on
homology of `Crystalline.envelopeCompletionNuComplexHom`, and `ht`, the invertibility on homology
of the base change along `τ` out of the complex base changed along `σ`.

## References

* [Stacks Project, Lemma 60.21.4, Tag 07LH](https://stacks.math.columbia.edu/tag/07LH)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace Crystalline

open DividedPowers

universe u

section AlphaIso

variable {A : DividedPowerRing.{u}} {ι : Type u} {J : Ideal (MvPolynomial ι A)}
  {hJ : A.ideal.map (algebraMap A (MvPolynomial ι A)) ≤ J}
  (E : DividedPowerEnvelope A (algebraMap A (MvPolynomial ι A)) J hJ) (p : ℕ)
  (hp : IsNilpotent (Ideal.Quotient.mk E.object.ideal (p : E.object)))
  [Fact p.Prime] [Algebra (IntegersAtPrime p) (E.object : Type u)]

/-- **`α⁻¹` as the algebra structure of the `σ` copy of `D⟨ξ_i⟩^∧` over `D⟨ξ_i⟩^∧`.**  This is
the structure in the direction opposite to `Crystalline.algebraEnvelopeCompletionAlpha`, which
carries `α`; the two are mutually inverse because `α` is an automorphism. -/
@[instance_reducible]
public def algebraEnvelopeCompletionAlphaInv :
    Algebra (envelopeCompletionVariableRing E p hp : Type u)
      (envelopeCompletionSigmaTarget E p hp) :=
  (envelopeCompletionAlphaInv E p hp).toRingHom.toAlgebra

attribute [local instance] algebraEnvelopeCompletionAlphaInv

/-- **The comparison of completed forms along `α⁻¹`, read over that algebra structure.** -/
public abbrev envelopeCompletionAlphaInvFormsOfAlgebra (i : ℕ) :
    envelopeCompletionVariableForms E p hp i →ₛₗ[algebraMap
        (envelopeCompletionVariableRing E p hp : Type u)
        (envelopeCompletionSigmaTarget E p hp)]
      envelopeCompletionVariableForms E p hp i :=
  envelopeCompletionAlphaInvForms E p hp i

/-- **`α⁻¹ ∘ α = id` as a scalar tower**, from
`Crystalline.envelopeCompletionAlphaInv_comp_alpha`. -/
public theorem isScalarTower_envelopeCompletionAlphaInv_comp_alpha :
    @IsScalarTower (envelopeCompletionSigmaTarget E p hp)
      (envelopeCompletionVariableRing E p hp : Type u) (envelopeCompletionSigmaTarget E p hp)
      Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
  IsScalarTower.of_algebraMap_eq fun x ↦
    (DFunLike.congr_fun (envelopeCompletionAlphaInv_comp_alpha E p hp) x).symm

/-- **`α ∘ α⁻¹ = id` as a scalar tower**, from
`Crystalline.envelopeCompletionAlpha_comp_alphaInv`. -/
public theorem isScalarTower_envelopeCompletionAlpha_comp_alphaInv :
    @IsScalarTower (envelopeCompletionVariableRing E p hp : Type u)
      (envelopeCompletionSigmaTarget E p hp) (envelopeCompletionVariableRing E p hp : Type u)
      Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
  IsScalarTower.of_algebraMap_eq fun x ↦
    (DFunLike.congr_fun (envelopeCompletionAlpha_comp_alphaInv E p hp) x).symm

attribute [local instance] isScalarTower_envelopeCompletionAlphaInv_comp_alpha
  isScalarTower_envelopeCompletionAlpha_comp_alphaInv

variable (M : Type u) [AddCommGroup M] [Module (envelopeCompletion E p hp : Type u) M]
  (nabla : CompletedConnection p (envelopeCompletion E p hp : Type u)
    (envelopeCompletionForms E p hp 1) (envelopeCompletionFormsDifferential E p hp) M)
  (hsqSigma : CompletedDeRham.IsSquareZero p (envelopeCompletionSigmaTarget E p hp)
    (envelopeCompletionVariableForms E p hp) (envelopeCompletionSigmaTargetFormsWedge E p hp)
    (envelopeCompletionVariableFormsDeRham E p hp) _
    (envelopeCompletionSigmaConnection E p hp M nabla)
    (isGradedLeibniz_envelopeCompletionSigmaTargetForms E p hp))
  (hsqSigmaAlpha : CompletedDeRham.IsSquareZero p
    (envelopeCompletionVariableRing E p hp : Type u) (envelopeCompletionVariableForms E p hp)
    (envelopeCompletionVariableFormsWedge E p hp)
    (envelopeCompletionVariableFormsDeRham E p hp) _
    (envelopeCompletionSigmaAlphaConnection E p hp M nabla)
    (isGradedLeibniz_envelopeCompletionVariableForms E p hp))

/-- **The base change map of completed de Rham complexes along the automorphism `α` is an
isomorphism of complexes.**

This is the source's "using that `α` is an isomorphism" of the proof of
[Stacks, Lemma 60.21.4, Tag 07LH], read on the complexes.  Nothing is assumed about the module
beyond what the complexes need: the base-changed module is `p`-adically complete by
`Crystalline.CompletedConnection.isPAdicallyComplete_baseChangeCarrier`, which is what
`Crystalline.CompletedDeRham.isIso_baseChangeComplexHom_of_inverse` asks for. -/
public theorem isIso_envelopeCompletionAlphaComplexHom :
    IsIso (envelopeCompletionAlphaComplexHom E p hp M nabla hsqSigma hsqSigmaAlpha) :=
  CompletedDeRham.isIso_baseChangeComplexHom_of_inverse p
    (envelopeCompletionSigmaTarget E p hp) (envelopeCompletionVariableRing E p hp : Type u)
    (CompletedConnection.baseChangeCarrier p (envelopeCompletion E p hp : Type u)
      (envelopeCompletionSigmaTarget E p hp) M)
    (envelopeCompletionVariableForms E p hp) (envelopeCompletionVariableForms E p hp)
    (envelopeCompletionAlphaFormsOfAlgebra E p hp)
    (envelopeCompletionAlphaInvFormsOfAlgebra E p hp)
    (envelopeCompletionSigmaTargetFormsWedge E p hp)
    (envelopeCompletionVariableFormsWedge E p hp)
    (envelopeCompletionVariableFormsDeRham E p hp)
    (envelopeCompletionVariableFormsDeRham E p hp)
    (envelopeCompletionVariableFormsDifferential E p hp)
    (envelopeCompletionSigmaConnection E p hp M nabla)
    (envelopeCompletionVariableFormsDifferential_add E p hp)
    (envelopeCompletionVariableFormsDifferential_mul E p hp)
    (envelopeCompletionAlphaForms_differential E p hp)
    (isGradedLeibniz_envelopeCompletionSigmaTargetForms E p hp)
    (isGradedLeibniz_envelopeCompletionVariableForms E p hp)
    (envelopeCompletionAlphaForms_wedge E p hp) (envelopeCompletionAlphaForms_deRham E p hp)
    (envelopeCompletionAlphaInvForms_alphaForms E p hp)
    (envelopeCompletionAlphaForms_alphaInvForms E p hp)
    (CompletedConnection.isPAdicallyComplete_baseChangeCarrier p
      (envelopeCompletion E p hp : Type u) (envelopeCompletionSigmaTarget E p hp) M)
    hsqSigma hsqSigmaAlpha

/-- **The base change map along `α` is invertible on homology in every degree.**

This is the hypothesis `halpha` of `Crystalline.isIso_homologyMap_sigmaComplexHom` and of
`Crystalline.isIso_homologyMap_of_sigmaFactorization`, now a theorem. -/
public theorem isIso_homologyMap_envelopeCompletionAlphaComplexHom (j : ℕ) :
    IsIso (HomologicalComplex.homologyMap
      (envelopeCompletionAlphaComplexHom E p hp M nabla hsqSigma hsqSigmaAlpha) j) := by
  have : IsIso (envelopeCompletionAlphaComplexHom E p hp M nabla hsqSigma hsqSigmaAlpha) :=
    isIso_envelopeCompletionAlphaComplexHom E p hp M nabla hsqSigma hsqSigmaAlpha
  exact CompletedDeRham.isIso_homologyMap_isoHom
    (asIso (envelopeCompletionAlphaComplexHom E p hp M nabla hsqSigma hsqSigmaAlpha)) j

end AlphaIso

end Crystalline

end
