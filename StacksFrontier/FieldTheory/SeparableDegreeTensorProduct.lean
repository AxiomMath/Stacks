module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.FieldTheory.SeparableDegree
public import Mathlib.RingTheory.TensorProduct.Finite
public import Mathlib.RingTheory.TensorProduct.Maps
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The spectrum of `L ⊗[k] E` for an algebraically closed `L`

Let `k` be a field, `E` a finite extension of `k` and `L` an algebraically closed extension
of `k`. This file proves that `Spec (L ⊗[k] E)` has exactly `[E : k]_s` points, each with
residue field `L`, where `[E : k]_s` is the separable degree `Field.finSepDegree k E`.

The two halves are proved separately. For any finite-dimensional algebra `A` over an
algebraically closed field `L` the `L`-points of `A` are exactly its primes, the point
attached to a prime `p` being the quotient map `A → A ⧸ p ≃ L`; this already gives the
residue fields. The count then comes from the correspondence between `L`-algebra maps
`L ⊗[k] E → L` and `k`-algebra maps `E → L`, together with the fact that the latter are
counted by the separable degree.

## Main definitions

* `IsAlgClosed.algHomOfPrime`: the `L`-algebra map `A →ₐ[L] L` cutting out a given prime of a
  finite-dimensional algebra `A` over an algebraically closed field `L`.
* `IsAlgClosed.algHomEquivPrimeSpectrum`: the bijection `(A →ₐ[L] L) ≃ PrimeSpectrum A`
  sending a map to its kernel.
* `Field.algHomEquivTensorProductAlgHom`: the bijection `(E →ₐ[k] L) ≃ (L ⊗[k] E →ₐ[L] L)`.
* `Field.primeSpectrumTensorProductEquivAlgHom`: the resulting bijection between the points of
  `Spec (L ⊗[k] E)` and the `k`-algebra maps `E →ₐ[k] L`.

## Main results

* `AlgHom.eq_of_ker_eq`: two `R`-algebra maps `A →ₐ[R] R` with the same kernel are equal.
* `IsAlgClosed.bijective_algebraMap_quotient`: if `A` is a finite-dimensional algebra over an
  algebraically closed field `L`, every residue field of `A` is `L`.
* `Field.bijective_algebraMap_quotient_tensorProduct`: every point of `Spec (L ⊗[k] E)` has
  residue field `L`.
* `Field.nat_card_primeSpectrum_tensorProduct_eq_finSepDegree`: `Spec (L ⊗[k] E)` has
  `[E : k]_s` points.

## Implementation notes

Mathlib's `Algebra.IsFiniteSplit.algHomEquivPrimeSpectrum` is the same bijection under the
hypothesis that `A` is a split `L`-algebra, i.e. `A ≃ₐ[L] Fin n → L`. That hypothesis fails
here: for an inseparable extension `E / k` the algebra `L ⊗[k] E` has nilpotents, so it is not
split, even though its spectrum is still a finite set of `L`-points. The bijection is therefore
reproved for an arbitrary finite-dimensional algebra over an algebraically closed field, where
the input is that a quotient of such an algebra by a prime is a domain integral over `L`, hence
equal to `L` because `L` is algebraically closed.

## References

* [Stacks Project, Tag 0CE5](https://stacks.math.columbia.edu/tag/0CE5)
* [Stacks Project, Tag 09HJ](https://stacks.math.columbia.edu/tag/09HJ)
-/

@[expose] public section

open TensorProduct

universe u v w

namespace AlgHom

/-- Two `R`-algebra maps from `A` to the base ring `R` with the same kernel are equal: such a
map is determined on `x` by the unique scalar with `x - algebraMap R A (f x)` in its kernel. -/
theorem eq_of_ker_eq {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] {f g : A →ₐ[R] R}
    (h : RingHom.ker f = RingHom.ker g) : f = g := by
  ext x
  have hx : x - algebraMap R A (f x) ∈ RingHom.ker f := by simp [RingHom.mem_ker]
  rw [h, RingHom.mem_ker, map_sub, AlgHom.commutes, sub_eq_zero] at hx
  exact hx.symm

end AlgHom

namespace IsAlgClosed

variable (L : Type u) {A : Type v} [Field L] [IsAlgClosed L] [CommRing A] [Algebra L A]
  [Module.Finite L A]

/-- Every residue field of a finite-dimensional algebra `A` over an algebraically closed field
`L` is `L` itself: the quotient of `A` by a prime is a domain integral over `L`. -/
theorem bijective_algebraMap_quotient (p : Ideal A) [p.IsPrime] :
    Function.Bijective (algebraMap L (A ⧸ p)) := by
  have : Module.Finite L (A ⧸ p) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ L p).toLinearMap
      (Ideal.Quotient.mkₐ_surjective L p)
  have : Algebra.IsIntegral L (A ⧸ p) := Algebra.IsIntegral.of_finite L _
  exact IsAlgClosed.algebraMap_bijective_of_isIntegral

/-- The `L`-point of a finite-dimensional algebra `A` over an algebraically closed field `L`
attached to a prime `p` of `A`: the quotient map `A → A ⧸ p`, followed by the identification
of `A ⧸ p` with `L`. -/
noncomputable def algHomOfPrime (p : PrimeSpectrum A) : A →ₐ[L] L :=
  (AlgEquiv.ofBijective (Algebra.ofId L (A ⧸ p.asIdeal))
    (bijective_algebraMap_quotient L p.asIdeal)).symm.toAlgHom.comp
      (Ideal.Quotient.mkₐ L p.asIdeal)

/-- The `L`-point attached to a prime `p` cuts out `p`. -/
theorem ker_algHomOfPrime (p : PrimeSpectrum A) :
    RingHom.ker (algHomOfPrime L p) = p.asIdeal := by
  rw [algHomOfPrime, ← AlgHom.comap_ker, ← RingHom.ker_coe_toRingHom,
    AlgEquiv.toAlgHom_toRingHom, AlgHom.ker_coe_equiv, ← RingHom.ker_eq_comap_bot,
    ← RingHom.ker_coe_toRingHom, Ideal.Quotient.mkₐ_ker]

/-- For a finite-dimensional algebra `A` over an algebraically closed field `L`, taking the
kernel is a bijection from the `L`-points of `A` to the points of `Spec A`. -/
noncomputable def algHomEquivPrimeSpectrum : (A →ₐ[L] L) ≃ PrimeSpectrum A where
  toFun f := ⟨RingHom.ker f, RingHom.ker_isPrime f⟩
  invFun p := algHomOfPrime L p
  left_inv f := AlgHom.eq_of_ker_eq (g := f) (ker_algHomOfPrime L _)
  right_inv p := PrimeSpectrum.ext (ker_algHomOfPrime L p)

/-- The prime corresponding to an `L`-point of `A` is its kernel. -/
@[simp]
theorem algHomEquivPrimeSpectrum_asIdeal (f : A →ₐ[L] L) :
    (algHomEquivPrimeSpectrum L f).asIdeal = RingHom.ker f :=
  rfl

end IsAlgClosed

namespace Field

variable (k : Type u) (E : Type v) (L : Type w) [Field k] [Field E] [Algebra k E]
  [FiniteDimensional k E] [Field L] [Algebra k L] [IsAlgClosed L]

/-- Every point of `Spec (L ⊗[k] E)` has residue field `L`, for `E / k` a finite extension and
`L / k` an algebraically closed extension. -/
@[ega "IV 4.3.7" "special case"]
theorem bijective_algebraMap_quotient_tensorProduct (p : PrimeSpectrum (L ⊗[k] E)) :
    Function.Bijective (algebraMap L ((L ⊗[k] E) ⧸ p.asIdeal)) :=
  IsAlgClosed.bijective_algebraMap_quotient L p.asIdeal

/-- The `L`-points of `L ⊗[k] E` are the `k`-algebra maps `E →ₐ[k] L`. This is
`Algebra.TensorProduct.liftEquivRight` in the case at hand. -/
def algHomEquivTensorProductAlgHom : (E →ₐ[k] L) ≃ (L ⊗[k] E →ₐ[L] L) :=
  Algebra.TensorProduct.liftEquivRight k L E L

/-- The points of `Spec (L ⊗[k] E)` are the `k`-algebra maps `E →ₐ[k] L`, for `E / k` a finite
extension and `L / k` an algebraically closed extension. -/
noncomputable def primeSpectrumTensorProductEquivAlgHom :
    PrimeSpectrum (L ⊗[k] E) ≃ (E →ₐ[k] L) :=
  ((algHomEquivTensorProductAlgHom k E L).trans
    (IsAlgClosed.algHomEquivPrimeSpectrum L)).symm

/-- For `E / k` a finite extension and `L / k` an algebraically closed extension, the scheme
`Spec (L ⊗[k] E)` has exactly `[E : k]_s` points. -/
theorem nat_card_primeSpectrum_tensorProduct_eq_finSepDegree :
    Nat.card (PrimeSpectrum (L ⊗[k] E)) = Field.finSepDegree k E :=
  (Nat.card_congr (primeSpectrumTensorProductEquivAlgHom k E L)).trans
    (Field.finSepDegree_eq_of_isAlgClosed k E L).symm

end Field

end
