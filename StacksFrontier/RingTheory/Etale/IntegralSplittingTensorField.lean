module

public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.Spectrum.Prime.Homeomorph
public import Mathlib.RingTheory.Localization.AtPrime.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# One prime after a field base change of a purely inseparable fibre

Let `C` be an `R`-algebra with a single prime `r` over a prime `p` of `R`, whose residue field
`κ(r)` is a purely inseparable extension of `κ(p)`.  For every field `Ω` which is an `R`-algebra
with kernel `p`, the ring `C ⊗[R] Ω` has at most one prime ideal.

This is the form in which the conclusion of Stacks 0BSR is used for Stacks 0E1D: the factors of
the étale-local splitting of an integral algebra contribute one point each to a geometric fibre.

## Main results

* `Algebra.subsingleton_primeSpectrum_tensorProduct_field_of_isPurelyInseparable`.

## Implementation notes

Every prime `Q` of `C ⊗[R] Ω` contracts to a prime of `C` over `p` (its contraction to the field
`Ω` is zero, and `Ω` has kernel `p` over `R`), hence to `r`.  The primes over `r` are the primes
of the fibre `κ(r) ⊗[C] (C ⊗[R] Ω) ≅ κ(r) ⊗[R] Ω`
(`PrimeSpectrum.preimageHomeomorphFiber`, `Algebra.TensorProduct.cancelBaseChange`), and since
`κ(r)/κ(p)` is purely inseparable, `Spec (κ(r) ⊗[R] Ω) ⟶ Spec (κ(p) ⊗[R] Ω)` is a
homeomorphism (`PrimeSpectrum.isHomeomorph_comap_tensorProductMap_of_isPurelyInseparable`).
Finally `Spec (κ(p) ⊗[R] Ω)` is the fibre of `Spec Ω ⟶ Spec R` over `p`, a subset of a point.

## References

* [Stacks Project, Tag 0BSR](https://stacks.math.columbia.edu/tag/0BSR)
* [Stacks Project, Tag 0E1D](https://stacks.math.columbia.edu/tag/0E1D)
-/

@[expose] public section

open TensorProduct

universe u

namespace Algebra

/-- **One prime after a field base change of a purely inseparable fibre.**  Let `C` be an
`R`-algebra whose only prime over the prime `p` of `R` is `r`, with `κ(r)/κ(p)` purely
inseparable, and let `Ω` be a field which is an `R`-algebra with kernel `p`.  Then `C ⊗[R] Ω`
has at most one prime ideal. -/
@[ega "0 22.5.5" "Locality of K ⊗_k k′"]
theorem subsingleton_primeSpectrum_tensorProduct_field_of_isPurelyInseparable
    {R C Ω : Type u} [CommRing R] [CommRing C] [Field Ω] [Algebra R C] [Algebra R Ω]
    (p : Ideal R) [p.IsPrime] (hker : RingHom.ker (algebraMap R Ω) = p)
    (r : Ideal C) [r.IsPrime] [r.LiesOver p]
    (huniq : ∀ q : Ideal C, q.IsPrime → q.LiesOver p → q = r)
    (hpi : letI := Localization.AtPrime.algebraOfLiesOver p r
      IsPurelyInseparable p.ResidueField r.ResidueField) :
    Subsingleton (PrimeSpectrum (C ⊗[R] Ω)) := by
  let := Localization.AtPrime.algebraOfLiesOver p r
  -- every prime contracts to `r`
  have hcontr : ∀ Q : PrimeSpectrum (C ⊗[R] Ω),
      PrimeSpectrum.comap (algebraMap C (C ⊗[R] Ω)) Q = ⟨r, inferInstance⟩ := by
    intro Q
    have hΩ : Q.asIdeal.comap (Algebra.TensorProduct.includeRight.toRingHom :
        Ω →+* C ⊗[R] Ω) = ⊥ := Ideal.eq_bot_of_prime _
    have hover : (Q.asIdeal.comap (algebraMap C (C ⊗[R] Ω))).LiesOver p := by
      constructor
      have hR : (algebraMap C (C ⊗[R] Ω)).comp (algebraMap R C) =
          (Algebra.TensorProduct.includeRight.toRingHom : Ω →+* C ⊗[R] Ω).comp
            (algebraMap R Ω) := by
        ext x
        simp [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_one_eq_one_tmul]
      rw [Ideal.under, Ideal.comap_comap, hR, ← Ideal.comap_comap, hΩ,
        ← RingHom.ker_eq_comap_bot, hker]
    exact PrimeSpectrum.ext (huniq _ inferInstance hover)
  -- the fibre over `r` has at most one point
  have hfib : Subsingleton (PrimeSpectrum (r.Fiber (C ⊗[R] Ω))) := by
    let e : r.Fiber (C ⊗[R] Ω) ≃ₐ[r.ResidueField] r.ResidueField ⊗[R] Ω :=
      Algebra.TensorProduct.cancelBaseChange R C r.ResidueField r.ResidueField Ω
    have hpt : Subsingleton (PrimeSpectrum (p.Fiber Ω)) := ⟨fun a b =>
      (PrimeSpectrum.preimageHomeomorphFiber R Ω ⟨p, inferInstance⟩).symm.injective
        (Subtype.ext (Subsingleton.elim _ _))⟩
    have hL : Subsingleton (PrimeSpectrum (r.ResidueField ⊗[R] Ω)) := ⟨fun a b =>
      (PrimeSpectrum.isHomeomorph_comap_tensorProductMap_of_isPurelyInseparable
        (K := p.ResidueField) (R := R) (S := Ω) r.ResidueField).injective
          (Subsingleton.elim _ _)⟩
    exact (PrimeSpectrum.comapEquiv e.toRingEquiv).toEquiv.subsingleton
  refine ⟨fun Q Q' => ?_⟩
  have h := (PrimeSpectrum.preimageHomeomorphFiber C (C ⊗[R] Ω) ⟨r, inferInstance⟩).injective
    (a₁ := ⟨Q, hcontr Q⟩) (a₂ := ⟨Q', hcontr Q'⟩) (Subsingleton.elim _ _)
  exact congrArg Subtype.val h

end Algebra
