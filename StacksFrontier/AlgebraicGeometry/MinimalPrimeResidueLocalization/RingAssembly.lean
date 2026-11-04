module

public import StacksFrontier.AlgebraicGeometry.MinimalPrimeResidueLocalization.IntegralClosure
public import StacksFrontier.AlgebraicGeometry.MinimalPrimeResidueLocalization.Localization

/-!
# Localizing the integral closure in the minimal-prime residue fields

Let `A` be a commutative ring with finitely many minimal primes, `M ⊆ A` a submonoid and `Aₘ` a
localization of `A` at `M`.  Suppose `S` is an `A`-algebra identified with the integral closure
of `A` in the product of the residue fields of the minimal primes of `A`, and `T` is a
localization of `S` at the image of `M`.  Then `T` is the integral closure of `Aₘ` in the product
of the residue fields of the minimal primes of `Aₘ`, as an `Aₘ`-algebra.

## Main results

* `Stacks.MinimalPrimeResidueLocalization.algEquivIntegralClosureOfIsLocalization`: `T` is the
  integral closure of `Aₘ` in the product of the residue fields of the minimal primes of `Aₘ`.

## References

* [Stacks Project, Tag 0C3B](https://stacks.math.columbia.edu/tag/0C3B)
-/

@[expose] public noncomputable section

open Stacks.NormalizationStalkAmbient

universe u

namespace Stacks.MinimalPrimeResidueLocalization

/-- Let `Aₘ` be a localization of `A` at `M`, let `S` be the integral closure of `A` in the
product of the residue fields of the minimal primes of `A`, and let `T` be a localization of `S` at
the image of `M` whose `Aₘ`-algebra structure extends its `A`-algebra structure. Then `T` is the
integral closure of `Aₘ` in the product of the residue fields of the minimal primes of `Aₘ`, as an
`Aₘ`-algebra. -/
public noncomputable def algEquivIntegralClosureOfIsLocalization
    (A : Type u) [CommRing A] (M : Submonoid A) (hA : (minimalPrimes A).Finite)
    (Aₘ : Type u) [CommRing Aₘ] [Algebra A Aₘ] [IsLocalization M Aₘ]
    (S : Type u) [CommRing S] [Algebra A S]
    (T : Type u) [CommRing T] [Algebra S T] [Algebra Aₘ T]
    [IsLocalization (Algebra.algebraMapSubmonoid S M) T]
    (θ :
      letI : Algebra A (minimalPrimeResidueFieldProduct A) :=
        (minimalPrimeResidueFieldProductHom A).toAlgebra
      S ≃ₐ[A] ↥(integralClosure A (minimalPrimeResidueFieldProduct A)))
    (hT : ∀ a : A, algebraMap Aₘ T (algebraMap A Aₘ a) = algebraMap S T (algebraMap A S a)) :
    letI : Algebra Aₘ (minimalPrimeResidueFieldProduct Aₘ) :=
      (minimalPrimeResidueFieldProductHom Aₘ).toAlgebra
    T ≃ₐ[Aₘ] ↥(integralClosure Aₘ (minimalPrimeResidueFieldProduct Aₘ)) := by
  letI : Algebra A (minimalPrimeResidueFieldProduct A) :=
    (minimalPrimeResidueFieldProductHom A).toAlgebra
  letI : Algebra Aₘ (minimalPrimeResidueFieldProduct Aₘ) :=
    (minimalPrimeResidueFieldProductHom Aₘ).toAlgebra
  letI : Algebra A (minimalPrimeResidueFieldProduct Aₘ) :=
    ((minimalPrimeResidueFieldProductHom Aₘ).comp (algebraMap A Aₘ)).toAlgebra
  letI := residueFieldProductAlgebra A M Aₘ
  have := IsScalarTower.of_algebraMap_eq' (R := A) (S := Aₘ)
    (A := minimalPrimeResidueFieldProduct Aₘ) rfl
  have := IsScalarTower.of_algebraMap_eq (R := A) (S := minimalPrimeResidueFieldProduct A)
    (A := minimalPrimeResidueFieldProduct Aₘ)
    fun a ↦ (residueFieldProductAlgebra_algebraMap A M Aₘ a).symm
  have : IsLocalization (Algebra.algebraMapSubmonoid (minimalPrimeResidueFieldProduct A) M)
      (minimalPrimeResidueFieldProduct Aₘ) :=
    isLocalization_minimalPrimeResidueFieldProduct A M Aₘ hA
  letI := Stacks.IntegralClosureLocalization.integralClosureAlgebra A
    (minimalPrimeResidueFieldProduct A) Aₘ (minimalPrimeResidueFieldProduct Aₘ)
  have := Stacks.IntegralClosureLocalization.isScalarTower_integralClosure_left A
    (minimalPrimeResidueFieldProduct A) Aₘ (minimalPrimeResidueFieldProduct Aₘ)
  have := Stacks.IntegralClosureLocalization.isScalarTower_integralClosure_base A Aₘ
    (minimalPrimeResidueFieldProduct Aₘ)
  have : IsLocalization (Algebra.algebraMapSubmonoid
      ↥(integralClosure A (minimalPrimeResidueFieldProduct A)) M)
      ↥(integralClosure Aₘ (minimalPrimeResidueFieldProduct Aₘ)) :=
    Stacks.IntegralClosureLocalization.isLocalization_integralClosure A
      (minimalPrimeResidueFieldProduct A) Aₘ (minimalPrimeResidueFieldProduct Aₘ) M
  letI : Algebra ↥(integralClosure A (minimalPrimeResidueFieldProduct A)) T :=
    ((algebraMap S T).comp θ.symm.toRingHom).toAlgebra
  have hM : (Algebra.algebraMapSubmonoid
      ↥(integralClosure A (minimalPrimeResidueFieldProduct A)) M).map θ.symm.toRingEquiv
      = Algebra.algebraMapSubmonoid S M := by
    refine Submonoid.ext fun z ↦ ⟨?_, ?_⟩
    · rintro ⟨-, ⟨a, ha, rfl⟩, rfl⟩
      exact ⟨a, ha, (θ.symm.commutes a).symm⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨algebraMap A _ a, ⟨a, ha, rfl⟩, θ.symm.commutes a⟩
  have : IsLocalization (Algebra.algebraMapSubmonoid
      ↥(integralClosure A (minimalPrimeResidueFieldProduct A)) M) T :=
    IsLocalization.of_ringEquiv_left θ.symm.toRingEquiv hM fun _ ↦ rfl
  set ψ := IsLocalization.algEquiv (Algebra.algebraMapSubmonoid
    ↥(integralClosure A (minimalPrimeResidueFieldProduct A)) M) T
    ↥(integralClosure Aₘ (minimalPrimeResidueFieldProduct Aₘ))
  have hcomm : ∀ a : A, ψ (algebraMap Aₘ T (algebraMap A Aₘ a))
      = algebraMap Aₘ ↥(integralClosure Aₘ (minimalPrimeResidueFieldProduct Aₘ))
        (algebraMap A Aₘ a) := by
    intro a
    have e1 : algebraMap Aₘ T (algebraMap A Aₘ a)
        = algebraMap ↥(integralClosure A (minimalPrimeResidueFieldProduct A)) T
          (algebraMap A ↥(integralClosure A (minimalPrimeResidueFieldProduct A)) a) :=
      (hT a).trans (congrArg (algebraMap S T) (θ.symm.commutes a).symm)
    rw [e1, ψ.commutes, ← IsScalarTower.algebraMap_apply A
        ↥(integralClosure A (minimalPrimeResidueFieldProduct A))
        ↥(integralClosure Aₘ (minimalPrimeResidueFieldProduct Aₘ)),
      IsScalarTower.algebraMap_apply A Aₘ
        ↥(integralClosure Aₘ (minimalPrimeResidueFieldProduct Aₘ))]
  have hext : ψ.toAlgHom.toRingHom.comp (algebraMap Aₘ T)
      = algebraMap Aₘ ↥(integralClosure Aₘ (minimalPrimeResidueFieldProduct Aₘ)) :=
    IsLocalization.ringHom_ext M (RingHom.ext hcomm)
  exact AlgEquiv.ofRingEquiv (f := ψ.toRingEquiv) fun b ↦ DFunLike.congr_fun hext b

end Stacks.MinimalPrimeResidueLocalization

end
