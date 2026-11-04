module

public import StacksFrontier.AlgebraicGeometry.SemistableReduction.StandardNodalModelOrigin
public import StacksFrontier.RingTheory.NodalChart.QuotientLocalization

/-!
# The singular point of the standard nodal model of exponent at least two

Let `R` be a discrete valuation ring with uniformizer `π` and let `m ≥ 2`. The standard nodal
model `X = Spec R[x, y]/(xy - πᵐ)` is singular at its origin `𝔪 = (π, x, y)`: the local ring of
`X` at any point whose prime ideal is the origin is not regular.

## Main results

* `Stacks.not_isRegularLocalRing_localization_nodalModelOrigin` — the localization of
  `R[x, y]/(xy - πᵐ)` at the origin is not a regular local ring, for `m ≥ 2`.
* `Stacks.not_isRegularLocalRing_stalk_of_asIdeal_eq_nodalModelOrigin` — **the local ring of the
  standard nodal model at the origin is not regular**, for `m ≥ 2`.

## References

* [Stacks Project, Tag 0CDC](https://stacks.math.columbia.edu/tag/0CDC)
* [Stacks Project, Tag 07PF](https://stacks.math.columbia.edu/tag/07PF)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing MvPolynomial

universe u

namespace Stacks

variable {R : Type u} [CommRing R]

/-- Regularity of the localization at a prime transports along an equality of primes. -/
private theorem isRegularLocalRing_localization_congr {A : Type u} [CommRing A] {p q : Ideal A}
    [p.IsPrime] [q.IsPrime] (h : p = q)
    (hp : IsRegularLocalRing (Localization.AtPrime p)) :
    IsRegularLocalRing (Localization.AtPrime q) := by
  subst h
  exact hp

/-- If the stalk of `Spec A` at a point is a regular local ring, then so is the localization of
`A` at the corresponding prime. -/
private theorem isRegularLocalRing_localization_of_isRegularLocalRing_stalk {A : Type u}
    [CommRing A] (z : PrimeSpectrum (CommRingCat.of A))
    (hreg : IsRegularLocalRing ↑((Spec (CommRingCat.of A)).presheaf.stalk z)) :
    IsRegularLocalRing (Localization.AtPrime z.asIdeal) := by
  have : IsRegularLocalRing
      ↑((structurePresheafInCommRingCat (CommRingCat.of A)).stalk z) := hreg
  exact IsRegularLocalRing.of_ringEquiv
    (StructureSheaf.stalkIso (CommRingCat.of A) z).toRingEquiv.symm

variable [IsDomain R] [IsDiscreteValuationRing R]

/-- **The localization of the standard nodal model of exponent at least two at its origin is not
a regular local ring.** For `m ≥ 2` the localization of `R[x, y]/(xy - πᵐ)` at `(π, x, y)` is not
a regular local ring. -/
public theorem not_isRegularLocalRing_localization_nodalModelOrigin {π : R}
    (hπ : Irreducible π) {m : ℕ} (hm : 2 ≤ m) [(nodalModelOrigin R π m).IsPrime] :
    ¬ IsRegularLocalRing (Localization.AtPrime (nodalModelOrigin R π m)) := by
  intro hX
  have hmax : (Ideal.span {π}).IsMaximal := isMaximal_span_singleton_of_irreducible hπ
  have hp : (nodalOriginIdeal R π).IsPrime := (isMaximal_nodalOriginIdeal hmax).isPrime
  have hregP : IsRegularLocalRing (Localization.AtPrime (nodalOriginIdeal R π)) :=
    isRegularLocalRing_localization_of_isRegular_spec _
      (isRegular_spec_of_isRegularRing (MvPolynomial (Fin 2) R))
  have hf2 : nodalEquation R (π ^ m) ∈ nodalOriginIdeal R π ^ 2 :=
    nodalEquation_mem_sq_nodalOriginIdeal π hm
  have hf : nodalEquation R (π ^ m) ∈ nodalOriginIdeal R π :=
    Ideal.pow_le_self two_ne_zero hf2
  have hsq : algebraMap (MvPolynomial (Fin 2) R)
      (Localization.AtPrime (nodalOriginIdeal R π)) (nodalEquation R (π ^ m))
      ∈ maximalIdeal (Localization.AtPrime (nodalOriginIdeal R π)) ^ 2 := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal (nodalOriginIdeal R π), ← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ hf2
  have hne : nodalEquation R (π ^ m) ≠ 0 :=
    (prime_nodalEquation (pow_ne_zero m hπ.ne_zero)).ne_zero
  have hnzd : algebraMap (MvPolynomial (Fin 2) R)
      (Localization.AtPrime (nodalOriginIdeal R π)) (nodalEquation R (π ^ m))
      ∈ nonZeroDivisors (Localization.AtPrime (nodalOriginIdeal R π)) := by
    refine mem_nonZeroDivisors_of_ne_zero fun h ↦ hne ?_
    refine IsLocalization.injective (Localization.AtPrime (nodalOriginIdeal R π))
      (Ideal.primeCompl_le_nonZeroDivisors (nodalOriginIdeal R π)) ?_
    rw [h, map_zero]
  have hkerle : RingHom.ker (Ideal.Quotient.mk
      (Ideal.span ({nodalEquation R (π ^ m)} : Set (MvPolynomial (Fin 2) R))))
      ≤ nodalOriginIdeal R π := by
    rw [Ideal.mk_ker, Ideal.span_le]
    simpa using hf
  have hq : ((nodalOriginIdeal R π).map (Ideal.Quotient.mk
      (Ideal.span ({nodalEquation R (π ^ m)} : Set (MvPolynomial (Fin 2) R))))).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective hkerle
  have hcomap : ((nodalOriginIdeal R π).map (Ideal.Quotient.mk
      (Ideal.span ({nodalEquation R (π ^ m)} : Set (MvPolynomial (Fin 2) R))))).comap
      (Ideal.Quotient.mk
        (Ideal.span ({nodalEquation R (π ^ m)} : Set (MvPolynomial (Fin 2) R))))
      = nodalOriginIdeal R π := by
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot]
    exact sup_eq_left.mpr hkerle
  have : IsLocalization ((nodalOriginIdeal R π).map (Ideal.Quotient.mk
      (Ideal.span ({nodalEquation R (π ^ m)} : Set (MvPolynomial (Fin 2) R))))).primeCompl
      (Localization.AtPrime (nodalOriginIdeal R π) ⧸
        (Ideal.span ({nodalEquation R (π ^ m)} : Set (MvPolynomial (Fin 2) R))).map
          (algebraMap (MvPolynomial (Fin 2) R)
            (Localization.AtPrime (nodalOriginIdeal R π)))) :=
    isLocalization_quotient_atPrime_of_mem_iff (nodalEquation R (π ^ m))
      (fun r ↦ by rw [← Ideal.mem_comap, hcomap])
  have hqeq : nodalModelOrigin R π m = (nodalOriginIdeal R π).map (Ideal.Quotient.mk
      (Ideal.span ({nodalEquation R (π ^ m)} : Set (MvPolynomial (Fin 2) R)))) :=
    nodalModelOrigin_eq_map π m
  have hX' := isRegularLocalRing_localization_congr hqeq hX
  have hJ : (Ideal.span ({nodalEquation R (π ^ m)} : Set (MvPolynomial (Fin 2) R))).map
        (algebraMap (MvPolynomial (Fin 2) R) (Localization.AtPrime (nodalOriginIdeal R π)))
      = Ideal.span {algebraMap (MvPolynomial (Fin 2) R)
        (Localization.AtPrime (nodalOriginIdeal R π)) (nodalEquation R (π ^ m))} := by
    simp [Ideal.map_span]
  refine not_isRegularLocalRing_quotient_span_singleton_of_mem_sq hnzd hsq ?_
  rw [← hJ]
  exact IsRegularLocalRing.of_ringEquiv
    (IsLocalization.algEquiv ((nodalOriginIdeal R π).map (Ideal.Quotient.mk
        (Ideal.span ({nodalEquation R (π ^ m)} : Set (MvPolynomial (Fin 2) R))))).primeCompl
      (Localization.AtPrime (nodalOriginIdeal R π) ⧸
        (Ideal.span ({nodalEquation R (π ^ m)} : Set (MvPolynomial (Fin 2) R))).map
          (algebraMap (MvPolynomial (Fin 2) R)
            (Localization.AtPrime (nodalOriginIdeal R π))))
      (Localization.AtPrime ((nodalOriginIdeal R π).map (Ideal.Quotient.mk
        (Ideal.span ({nodalEquation R (π ^ m)} : Set (MvPolynomial (Fin 2) R))))))).toRingEquiv.symm

/-- The local ring at the origin of the standard nodal model of exponent at least two is not
regular. -/
public theorem not_isRegularLocalRing_stalk_of_asIdeal_eq_nodalModelOrigin
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {π : R}
    (hπ : Irreducible π) {m : ℕ} (hm : 2 ≤ m) (z : nodalModel R π m)
    (hz : z.asIdeal = nodalModelOrigin R π m) :
    ¬ IsRegularLocalRing ((nodalModel R π m).presheaf.stalk z) := by
  intro hreg
  have : (nodalModelOrigin R π m).IsPrime :=
    (isMaximal_nodalModelOrigin (isMaximal_span_singleton_of_irreducible hπ)
      (by omega : 1 ≤ m)).isPrime
  have := z.isPrime
  exact not_isRegularLocalRing_localization_nodalModelOrigin hπ hm
    (isRegularLocalRing_localization_congr hz
      (isRegularLocalRing_localization_of_isRegularLocalRing_stalk
        (A := nodalChartRing R (π ^ m)) z hreg))

end Stacks

end
