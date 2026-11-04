module

public import StacksFrontier.AlgebraicGeometry.Curves.Models.SemistableReduction.BaseChange

/-!
# An extension of discrete valuation rings inside a finite separable extension

Let `R` be a discrete valuation ring with fraction field `K`, let `K'/K` be a finite separable
extension and let `R'` be the integral closure of `R` in `K'`. Then `R'` is a Dedekind domain
which is not a field, and its localization at any maximal ideal is a discrete valuation ring with
fraction field `K'` dominating `R`. So semistable reduction of `C_{K'}` over every `R'_𝔪`
(`Stacks.Models.HasSemistableReductionAtMaximalIdeals`) gives the first assertion of
[Stacks, Tag 0CDN]: an extension of discrete valuation rings `R ⊆ R'` inducing `K'/K` over which
`C_{K'}` has semistable reduction.

## Main results

* `Stacks.Models.exists_hasSemistableReduction_of_hasSemistableReductionAtMaximalIdeals`: if `C'`
  has semistable reduction over the localization of `R'` at every maximal ideal, then there is a
  discrete valuation ring with fraction field `K'` dominating `R` over which `C'` has semistable
  reduction.

## References

* [Stacks Project, Tag 0CDN](https://stacks.math.columbia.edu/tag/0CDN)
* [Stacks Project, Tag 09E8](https://stacks.math.columbia.edu/tag/09E8)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.Models

/-- **Semistable reduction over every localization of the integral closure gives an extension
of discrete valuation rings with semistable reduction.** Let `R` be a discrete valuation ring with
fraction field `K`, `K'/K` a finite separable extension and `C'` a smooth projective curve over
`K'` with `H⁰(C', 𝒪) = K'`, with semistable reduction over `R'_𝔪` for every maximal ideal `𝔪` of
the integral closure `R'` of `R` in `K'`. Then there is a discrete valuation ring `R''` with
fraction field `K'`, a local homomorphism `R ⟶ R''` compatible with `K ⟶ K'`, over which `C'`
has semistable reduction. -/
theorem exists_hasSemistableReduction_of_hasSemistableReductionAtMaximalIdeals
    (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] (K' : Type u) [Field K'] [Algebra K K'] [Algebra R K']
    [IsScalarTower R K K'] [FiniteDimensional K K'] [Algebra.IsSeparable K K']
    {C' : Scheme.{u}} (c' : C' ⟶ Spec (.of K')) [IsCurve K' c'] [Smooth c']
    (hproj : IsProjective c') [IsIso ((Scheme.ΓSpecIso (.of K')).inv ≫ c'.appTop)]
    (h : HasSemistableReductionAtMaximalIdeals R K' c' hproj) :
    ∃ (R'' : Type u) (_ : CommRing R'') (_ : IsDomain R'') (_ : IsDiscreteValuationRing R'')
      (_ : Algebra R'' K') (_ : IsFractionRing R'' K') (_ : Algebra R R'')
      (_ : IsScalarTower R R'' K'), IsLocalHom (algebraMap R R'') ∧
      HasSemistableReduction R'' c' hproj := by
  classical
  set R' := integralClosure R K'
  have : IsFractionRing R' K' := integralClosure.isFractionRing_of_finite_extension K K'
  have : IsDedekindDomain R' := integralClosure.isDedekindDomain R K K'
  have hinjR : Function.Injective (algebraMap R R') := by
    intro a b hab
    have := congrArg (algebraMap R' K') hab
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_apply R K K', IsScalarTower.algebraMap_apply R K K'] at this
    exact IsFractionRing.injective R K ((algebraMap K K').injective this)
  have hnf : ¬ IsField R' := fun hF =>
    IsDiscreteValuationRing.not_isField R (isField_of_isIntegral_of_isField hinjR hF)
  obtain ⟨𝔪, h𝔪⟩ := Ideal.exists_maximal R'
  have h𝔪0 : 𝔪 ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField h𝔪 hnf
  set A := Localization.AtPrime 𝔪
  have : IsDiscreteValuationRing A :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain R' h𝔪0 A
  have hunit : ∀ y : 𝔪.primeCompl, IsUnit (algebraMap R' K' y) := fun y =>
    isUnit_iff_ne_zero.mpr fun h0 =>
      y.2 (by
        rw [(IsFractionRing.injective R' K').eq_iff.mp (h0.trans (map_zero _).symm)]
        exact 𝔪.zero_mem)
  let : Algebra A K' := (IsLocalization.lift (M := 𝔪.primeCompl) (S := A) hunit).toAlgebra
  have : IsScalarTower R' A K' := IsScalarTower.of_algebraMap_eq fun x =>
    (IsLocalization.lift_eq (M := 𝔪.primeCompl) (S := A) hunit x).symm
  have : IsFractionRing A K' :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization 𝔪.primeCompl A K'
  have : IsScalarTower R A K' := IsScalarTower.of_algebraMap_eq fun x => by
    rw [IsScalarTower.algebraMap_apply R R' K', IsScalarTower.algebraMap_apply R' A K',
      ← IsScalarTower.algebraMap_apply R R' A]
  refine ⟨A, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, ⟨fun r hr => ?_⟩, h 𝔪 A⟩
  by_contra hr'
  have hmem : r ∈ Ideal.comap (algebraMap R R') 𝔪 := by
    have hmax := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := R) 𝔪
    rw [IsLocalRing.eq_maximalIdeal hmax]
    exact (IsLocalRing.mem_maximalIdeal r).mpr hr'
  rw [IsScalarTower.algebraMap_apply R R' A,
    IsLocalization.AtPrime.isUnit_to_map_iff A 𝔪] at hr
  exact hr hmem

end Stacks.Models

end
