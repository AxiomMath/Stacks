module

public import Mathlib.RingTheory.Localization.Integral
public import StacksFrontier.RingTheory.FormallySmooth.LocalizationBase

/-!
# The integral closure of a localized base, as a localization of the integral closure

Let `A` be a domain with fraction field `K`, let `K₁/K` be a field extension and let `A'` be a
localization of `A` at a submonoid `M` of nonzero elements. Then the integral closure of `A'` in
`K₁` is the localization of the integral closure of `A` in `K₁` at the image of `M`.

## Main results

* `isLocalization_integralClosure_of_forall_isUnit`: the integral closure of `A'` in `K₁` is a
  localization of the integral closure of `A` in `K₁`, whenever `M` maps into the units of `K₁`.
* `isLocalization_integralClosure_primeCompl`: the same for `M` the complement of a prime of a
  domain and `K₁` an extension field of its fraction field, where the unit hypothesis is
  automatic.
* `RingHom.formallySmoothNAdic_localRingHom_integralClosure_primeCompl`: adic formal smoothness
  of a localization of `integralClosure A' K₁ → T` descends to `integralClosure A K₁ → T`.

## References

* [Stacks Project, Tag 09EN](https://stacks.math.columbia.edu/tag/09EN)
* [Stacks Project, Tag 0307](https://stacks.math.columbia.edu/tag/0307)
* [Stacks Project, Tag 09IL](https://stacks.math.columbia.edu/tag/09IL)
-/

public section

universe t u v w

/-- Let `A'` be a localization of `A` at a submonoid `M` whose image in `K₁` consists of units.
Then `integralClosure A' K₁` is the localization of `integralClosure A K₁` at the image of `M`. -/
theorem isLocalization_integralClosure_of_forall_isUnit {A : Type u} {A' : Type v} {K₁ : Type w}
    [CommRing A] [CommRing A'] [CommRing K₁] [Algebra A A'] [Algebra A K₁] [Algebra A' K₁]
    [IsScalarTower A A' K₁]
    [Algebra ↥(integralClosure A K₁) ↥(integralClosure A' K₁)]
    [IsScalarTower ↥(integralClosure A K₁) ↥(integralClosure A' K₁) K₁]
    [IsScalarTower A ↥(integralClosure A K₁) ↥(integralClosure A' K₁)]
    (M : Submonoid A) [IsLocalization M A']
    (hM : ∀ m ∈ M, IsUnit (algebraMap A K₁ m)) :
    IsLocalization (Algebra.algebraMapSubmonoid ↥(integralClosure A K₁) M)
      ↥(integralClosure A' K₁) := by
  have : IsLocalization (Algebra.algebraMapSubmonoid K₁ M) K₁ :=
    IsLocalization.of_le_isUnit (by rintro _ ⟨m, hm, rfl⟩; exact hM m hm)
  exact IsLocalization.integralClosure (S := K₁) (Rf := A') (Sf := K₁) M

/-- For `A` a domain with fraction field `K`, `K₁` an extension field of `K` and `A'` the
localization of `A` at a prime `p`, the integral closure of `A'` in `K₁` is the localization of
the integral closure of `A` in `K₁` at the image of the complement of `p`. -/
theorem isLocalization_integralClosure_primeCompl {A : Type u} {A' : Type v}
    (K : Type w) {K₁ : Type w}
    [CommRing A] [IsDomain A] [CommRing A'] [Field K] [Field K₁]
    [Algebra A K] [IsFractionRing A K] [Algebra K K₁] [Algebra A K₁] [IsScalarTower A K K₁]
    [Algebra A A'] [Algebra A' K₁] [IsScalarTower A A' K₁]
    [Algebra ↥(integralClosure A K₁) ↥(integralClosure A' K₁)]
    [IsScalarTower ↥(integralClosure A K₁) ↥(integralClosure A' K₁) K₁]
    [IsScalarTower A ↥(integralClosure A K₁) ↥(integralClosure A' K₁)]
    (p : Ideal A) [p.IsPrime] [IsLocalization.AtPrime A' p] :
    IsLocalization (Algebra.algebraMapSubmonoid ↥(integralClosure A K₁) p.primeCompl)
      ↥(integralClosure A' K₁) := by
  refine isLocalization_integralClosure_of_forall_isUnit p.primeCompl fun m hm => ?_
  have hinj : Function.Injective (algebraMap A K₁) := by
    rw [IsScalarTower.algebraMap_eq A K K₁]
    exact (algebraMap K K₁).injective.comp (IsFractionRing.injective A K)
  refine isUnit_iff_ne_zero.mpr fun h => hm ?_
  rw [hinj (h.trans (map_zero _).symm)]
  exact p.zero_mem

namespace RingHom

/-- In the situation of `isLocalization_integralClosure_primeCompl`, let `T` be an algebra over
both integral closures, compatibly, and let `q` be a prime of `T`. If the localization
`(integralClosure A' K₁)_{q ∩ -} → T_q` is formally smooth for the maximal-ideal-adic topology,
then so is `(integralClosure A K₁)_{q ∩ -} → T_q`. -/
theorem formallySmoothNAdic_localRingHom_integralClosure_primeCompl {A : Type u} {A' : Type v}
    (K : Type w) {K₁ : Type w} {T : Type w}
    [CommRing A] [IsDomain A] [CommRing A'] [Field K] [Field K₁] [CommRing T]
    [Algebra A K] [IsFractionRing A K] [Algebra K K₁] [Algebra A K₁] [IsScalarTower A K K₁]
    [Algebra A A'] [Algebra A' K₁] [IsScalarTower A A' K₁]
    [Algebra ↥(integralClosure A K₁) ↥(integralClosure A' K₁)]
    [IsScalarTower ↥(integralClosure A K₁) ↥(integralClosure A' K₁) K₁]
    [IsScalarTower A ↥(integralClosure A K₁) ↥(integralClosure A' K₁)]
    [Algebra ↥(integralClosure A K₁) T] [Algebra ↥(integralClosure A' K₁) T]
    [IsScalarTower ↥(integralClosure A K₁) ↥(integralClosure A' K₁) T]
    (p : Ideal A) [p.IsPrime] [IsLocalization.AtPrime A' p]
    (q : Ideal T) [q.IsPrime] :
    letI : (q.comap (algebraMap ↥(integralClosure A' K₁) T)).IsPrime := Ideal.IsPrime.comap _
    letI : (q.comap (algebraMap ↥(integralClosure A K₁) T)).IsPrime := Ideal.IsPrime.comap _
    FormallySmoothNAdic.{t, w, w}
        (Localization.localRingHom (q.comap (algebraMap ↥(integralClosure A' K₁) T)) q
          (algebraMap ↥(integralClosure A' K₁) T) rfl)
        (IsLocalRing.maximalIdeal (Localization.AtPrime q)) →
      FormallySmoothNAdic.{t, w, w}
        (Localization.localRingHom (q.comap (algebraMap ↥(integralClosure A K₁) T)) q
          (algebraMap ↥(integralClosure A K₁) T) rfl)
        (IsLocalRing.maximalIdeal (Localization.AtPrime q)) :=
  let := isLocalization_integralClosure_primeCompl (A := A) (A' := A') (K := K) (K₁ := K₁) p
  formallySmoothNAdic_localRingHom_of_isLocalization
    (Algebra.algebraMapSubmonoid ↥(integralClosure A K₁) p.primeCompl) q

end RingHom

end
