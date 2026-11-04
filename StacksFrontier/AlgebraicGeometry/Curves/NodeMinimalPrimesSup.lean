module

public import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
public import StacksFrontier.AlgebraicGeometry.Curves.NodeQuadraticAlgebra.Conductor
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.TotalFractionRing

/-!
# Two minimal primes of a node sum to the maximal ideal

Let `A` be a Noetherian nodal local algebra over a field `k` and let `p ≠ q` be two minimal
primes of `A`. Then `p + q = 𝔪`.

The normalization `A'` of a reduced ring with finitely many minimal primes is the product, over
those primes, of the normalizations of the quotients `A ⧸ s` (Tag 035P). For a node the
conductor contains the maximal ideal: `𝔪 A' ⊆ A`
(`Stacks.Curves.map_maximalIdeal_le_range_algebraMap_integralClosure`). Given `w ∈ 𝔪`, the
element of the product which is `w` in the factor at `p` and zero everywhere else lies in
`𝔪 A'`, hence is the image of some `a ∈ A`; reading that equality off in the two factors gives
`a - w ∈ p` and `a ∈ q`, so `w = (w - a) + a ∈ p + q`.

The hypothesis that the node has *exactly* two minimal primes is not needed: any two distinct
minimal primes of a node already sum to the maximal ideal. (A node has at most two, since it has
at most two geometric branches, but that is not used.)

## Main results

* `Stacks.Curves.sup_eq_maximalIdeal_of_isNodalAlgebra` — two distinct minimal primes of a node
  sum to its maximal ideal.

## Implementation notes

The `A`-algebra structures on the factors of the product decomposition are the ones the statement
of `minimalPrimes.integralClosure_fractionRing_algEquiv_pi_quotient` fixes, so they are
introduced here in the same shape before that result is invoked.

## References

* [Stacks Project, Tag 0C4A](https://stacks.math.columbia.edu/tag/0C4A)
* [Stacks Project, Tag 035P](https://stacks.math.columbia.edu/tag/035P)
-/

@[expose] public noncomputable section

open IsLocalRing

universe u v

namespace Stacks.Curves

/-- **Two distinct minimal primes of a node sum to the maximal ideal.** The normalization of `A`
is the product of the normalizations of its minimal-prime quotients, and for a node the maximal
ideal of `A` multiplied into that product lands back in `A`. Applying this to the element which
is `w ∈ 𝔪` in the factor belonging to `p` and zero in every other factor produces an `a ∈ A`
congruent to `w` modulo `p` and to zero modulo `q`, whence `w ∈ p + q`. -/
theorem sup_eq_maximalIdeal_of_isNodalAlgebra
    (k : Type u) (A : Type v) [Field k] [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [Algebra k A] (hA : IsNodalAlgebra k A)
    {p q : Ideal A} (hp : p ∈ minimalPrimes A) (hq : q ∈ minimalPrimes A) (hpq : p ≠ q) :
    p ⊔ q = maximalIdeal A := by
  classical
  have hred : _root_.IsReduced A := hA.2.1
  have := hred
  have hfin : (minimalPrimes A).Finite := minimalPrimes.finite_of_isNoetherianRing A
  have : Finite (minimalPrimes A) := hfin
  have hprime : ∀ s : minimalPrimes A, (s : Ideal A).IsPrime := fun s => s.property.left.left
  have hdomain : ∀ s : minimalPrimes A, IsDomain (A ⧸ (s : Ideal A)) := fun s =>
    have := hprime s
    Ideal.Quotient.isDomain (s : Ideal A)
  let (s : minimalPrimes A) : Algebra A (FractionRing (A ⧸ (s : Ideal A))) :=
    ((algebraMap (A ⧸ (s : Ideal A)) (FractionRing (A ⧸ (s : Ideal A)))).comp
      (Ideal.Quotient.mk (s : Ideal A))).toAlgebra
  let (s : minimalPrimes A) : Algebra A
      (integralClosure (A ⧸ (s : Ideal A)) (FractionRing (A ⧸ (s : Ideal A)))) :=
    ((algebraMap (A ⧸ (s : Ideal A))
      (integralClosure (A ⧸ (s : Ideal A)) (FractionRing (A ⧸ (s : Ideal A))))).comp
        (Ideal.Quotient.mk (s : Ideal A))).toAlgebra
  obtain ⟨e⟩ := minimalPrimes.integralClosure_fractionRing_algEquiv_pi_quotient (A := A) hfin
  -- the quotients inject into their normalizations
  have hcompinj : ∀ s : minimalPrimes A, Function.Injective
      (algebraMap (A ⧸ (s : Ideal A))
        (integralClosure (A ⧸ (s : Ideal A)) (FractionRing (A ⧸ (s : Ideal A))))) := by
    intro s x y hxy
    have := hdomain s
    refine IsFractionRing.injective (A ⧸ (s : Ideal A)) (FractionRing (A ⧸ (s : Ideal A))) ?_
    exact congrArg Subtype.val hxy
  refine le_antisymm (sup_le (le_maximalIdeal (hp.1.1.ne_top)) (le_maximalIdeal (hq.1.1.ne_top)))
    fun w hw => ?_
  set P : minimalPrimes A := ⟨p, hp⟩ with hP
  set Q : minimalPrimes A := ⟨q, hq⟩ with hQ
  have hPQ : Q ≠ P := fun h => hpq (congrArg Subtype.val h).symm
  -- the idempotent of the factor belonging to `p`, scaled by `w`
  let η : ∀ s : minimalPrimes A,
      integralClosure (A ⧸ (s : Ideal A)) (FractionRing (A ⧸ (s : Ideal A))) :=
    Pi.single P 1
  have hξ : ∀ s : minimalPrimes A,
      (algebraMap A (∀ s : minimalPrimes A,
        integralClosure (A ⧸ (s : Ideal A)) (FractionRing (A ⧸ (s : Ideal A)))) w * η) s =
          algebraMap A _ w * η s := fun _ => rfl
  -- it lies in `𝔪 A'`, hence in the image of `A`
  have hmem : e.symm (algebraMap A _ w * η) ∈
      (maximalIdeal A).map (algebraMap A ↥(integralClosure A (FractionRing A))) := by
    have hw' : algebraMap A ↥(integralClosure A (FractionRing A)) w ∈
        (maximalIdeal A).map (algebraMap A ↥(integralClosure A (FractionRing A))) :=
      Ideal.mem_map_of_mem _ hw
    have : e.symm (algebraMap A _ w * η) =
        algebraMap A ↥(integralClosure A (FractionRing A)) w * e.symm η := by
      rw [map_mul, e.symm.commutes]
    rw [this]
    exact Ideal.mul_mem_right _ _ hw'
  obtain ⟨a, ha⟩ := map_maximalIdeal_le_range_algebraMap_integralClosure k A hA hmem
  have hae : algebraMap A (∀ s : minimalPrimes A,
      integralClosure (A ⧸ (s : Ideal A)) (FractionRing (A ⧸ (s : Ideal A)))) a =
        algebraMap A _ w * η := by
    have h1 : e (algebraMap A ↥(integralClosure A (FractionRing A)) a) =
        algebraMap A _ w * η := by
      rw [show algebraMap A ↥(integralClosure A (FractionRing A)) a =
        e.symm (algebraMap A _ w * η) from ha, e.apply_symm_apply]
    exact (e.commutes a).symm.trans h1
  -- read the equality off in the two factors
  have hatP : (Ideal.Quotient.mk (p : Ideal A)) a = (Ideal.Quotient.mk (p : Ideal A)) w := by
    have h := congrFun hae P
    rw [hξ P] at h
    simp only [η, Pi.single_eq_same, mul_one] at h
    exact hcompinj P h
  have hatQ : (Ideal.Quotient.mk (Q : Ideal A)) a = 0 := by
    have h := congrFun hae Q
    rw [hξ Q] at h
    simp only [η, Pi.single_eq_of_ne hPQ, mul_zero] at h
    exact hcompinj Q (h.trans (map_zero _).symm)
  have hwa : w - a ∈ p := by simpa using Ideal.Quotient.eq.mp hatP.symm
  have haq : a ∈ q := Ideal.Quotient.eq_zero_iff_mem.mp hatQ
  simpa using Submodule.add_mem_sup hwa haq

end Stacks.Curves

end
