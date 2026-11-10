module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.TotalFractionRing
public import StacksFrontier.RingTheory.GeometricallyNormal.Separable
public import StacksFrontier.RingTheory.GeometricallyNormal.TensorProduct
public import StacksFrontier.RingTheory.IntegrallyClosed.Stability
public import StacksCore.Tactic.StacksAttribute

/-!
# Normalization and a separable extension of the ground field

Let `A` be a reduced ring with finitely many minimal primes and let `A'` be the integral closure
of `A` in its total ring of fractions.  For a separable extension `K/k` of the ground field,
`K ⊗[k] A'` is again normal, and hence reduced.

Normality of `K ⊗[k] A'` is the step of the separable half of Tag 0C3N that forces
`K ⊗[k] A'` to be the integral closure of `K ⊗[k] A` in the total ring of fractions of
`K ⊗[k] A`; that identification itself is not proved here.  The scheme-level comparison
morphism of Tag 0C3N is built in
`StacksFrontier.AlgebraicGeometry.NormalizationBaseChange.Basic`.

## Main results

* `IsNormalRing.tensorProduct_of_isSeparableExtension`: the base change of a normal ring along a
  separable extension of fields is normal.  This is the ring-level form of Tag 0C3M.
* `isNormalRing_integralClosure_fractionRing_of_finite_minimalPrimes`: the integral closure of a
  reduced ring with
  finitely many minimal primes in its total ring of fractions is normal.
* `isNormalRing_tensorProduct_integralClosure_fractionRing` combines the two.
* `includeRight_mem_nonZeroDivisors_tensorProduct`: extension of the ground field carries
  non-zerodivisors to non-zerodivisors.

## References

* [Stacks Project, Tag 0C3M](https://stacks.math.columbia.edu/tag/0C3M)
* [Stacks Project, Tag 0C3N](https://stacks.math.columbia.edu/tag/0C3N)
-/

@[expose] public section

open scoped TensorProduct

universe u v w

/-! ### Base change of a normal ring along a separable extension -/

/-- The base change of a normal ring along a separable extension of fields is normal.  This is
the ring-level content of **Stacks Project, Tag 0C3M**: a separable extension is geometrically
normal (Tag 0C30), and the tensor product of a geometrically normal algebra with a normal
algebra is normal (Tag 06DF). -/
theorem IsNormalRing.tensorProduct_of_isSeparableExtension
    (k : Type u) (K : Type v) (B : Type w) [Field k] [Field K] [Algebra k K]
    [Algebra.IsSeparableExtension k K] [CommRing B] [Algebra k B] (hB : IsNormalRing B) :
    IsNormalRing (K ⊗[k] B) :=
  let : Algebra.IsGeometricallyNormal k K :=
    Algebra.IsGeometricallyNormal.of_isSeparableExtension
  Algebra.IsGeometricallyNormal.isNormalRing_tensorProduct_of_isNormalRing k K B hB

/-! ### Normality of the integral closure in the total ring of fractions -/

/-- The integral closure of a domain in its fraction field is integrally closed. -/
theorem isIntegrallyClosed_integralClosure_of_isDomain
    (R : Type*) [CommRing R] [IsDomain R] (F : Type*) [Field F] [Algebra R F]
    [IsFractionRing R F] : IsIntegrallyClosed (integralClosure R F) :=
  let : IsFractionRing (integralClosure R F) F :=
    Localization.subalgebra.instIsFractionRingSubtypeMemSubalgebra F (integralClosure R F)
  (IsIntegrallyClosed.integralClosure_eq_bot_iff F).mp integralClosure_idem

/-- The integral closure of a reduced ring with finitely many minimal primes in its total ring of
fractions is a normal ring.  It is a finite product of integral closures of domains in their
fraction fields (Tag 035P), each of which is a normal domain.

The name carries the `_of_finite_minimalPrimes` suffix because the plain name
`isNormalRing_integralClosure_fractionRing` is already taken, in the **root namespace**, by
`StacksFrontier/AlgebraicGeometry/Variety/DeltaInvariant/Normalization.lean` (which carries
`@[stacks 0C3S "normality"]` and assumes `[IsNoetherianRing A]`).  Co-importing the two files
without this rename is an ambiguity error, which is what regenerating the library's import list
exposed.  This statement is **strictly more general** than the tagged one -- finitely many minimal
primes rather than Noetherian -- so the tagged one is derivable from it via
`minimalPrimes.finite_of_isNoetherianRing`. -/
theorem isNormalRing_integralClosure_fractionRing_of_finite_minimalPrimes
    {A : Type*} [CommRing A] [IsReduced A] (hA : (minimalPrimes A).Finite) :
    IsNormalRing (integralClosure A (FractionRing A)) := by
  have : Finite (minimalPrimes A) := hA
  -- The `A`-algebra structures on the factors are the ones fixed in the statement of Tag 035P(3).
  let _ : ∀ p : minimalPrimes A,
      Algebra A (integralClosure (A ⧸ (p : Ideal A)) (FractionRing (A ⧸ (p : Ideal A)))) :=
    fun p =>
      ((algebraMap (A ⧸ (p : Ideal A))
        (integralClosure (A ⧸ (p : Ideal A)) (FractionRing (A ⧸ (p : Ideal A))))).comp
        (Ideal.Quotient.mk (p : Ideal A))).toAlgebra
  obtain ⟨e⟩ := minimalPrimes.integralClosure_fractionRing_algEquiv_pi_quotient hA
  refine IsNormalRing.congr e.symm.toRingEquiv (isNormalRing_pi fun p ↦ ?_)
  have : (p : Ideal A).IsPrime := p.2.1.1
  have := isIntegrallyClosed_integralClosure_of_isDomain (A ⧸ (p : Ideal A))
    (FractionRing (A ⧸ (p : Ideal A)))
  exact IsNormalRing.of_isIntegrallyClosed _

/-- The base change along a separable extension of the ground field of the integral closure of a
reduced ring with finitely many minimal primes in its total ring of fractions is normal, hence
reduced.  This is the hypothesis under which the comparison morphism of Tag 0C3N is an
isomorphism. -/
@[ega "IV 4.3.5" "more general"]
theorem isNormalRing_tensorProduct_integralClosure_fractionRing
    (k : Type u) (K : Type v) (A : Type w) [Field k] [Field K] [Algebra k K]
    [Algebra.IsSeparableExtension k K] [CommRing A] [IsReduced A] [Algebra k A]
    (hA : (minimalPrimes A).Finite) :
    letI : Algebra k (integralClosure A (FractionRing A)) :=
      ((algebraMap A (integralClosure A (FractionRing A))).comp (algebraMap k A)).toAlgebra
    IsNormalRing (K ⊗[k] integralClosure A (FractionRing A)) :=
  let : Algebra k (integralClosure A (FractionRing A)) :=
    ((algebraMap A (integralClosure A (FractionRing A))).comp (algebraMap k A)).toAlgebra
  IsNormalRing.tensorProduct_of_isSeparableExtension k K _
    (isNormalRing_integralClosure_fractionRing_of_finite_minimalPrimes hA)

/-! ### Non-zerodivisors after extension of the ground field -/

/-- Extension of the ground field carries non-zerodivisors to non-zerodivisors: a field extension
is flat, so multiplication by a non-zerodivisor stays injective after tensoring. -/
@[ega "IV 20.6.9" "partial"]
theorem includeRight_mem_nonZeroDivisors_tensorProduct
    {k : Type u} (K : Type v) {A : Type w} [Field k] [Field K] [Algebra k K]
    [CommRing A] [Algebra k A] {s : A} (hs : s ∈ nonZeroDivisors A) :
    (Algebra.TensorProduct.includeRight s : K ⊗[k] A) ∈ nonZeroDivisors (K ⊗[k] A) := by
  have hmul : Function.Injective (LinearMap.mulLeft k s) := fun a b h ↦ by
    refine sub_eq_zero.mp ((mem_nonZeroDivisors_iff.mp hs).1 _ ?_)
    rw [mul_sub, sub_eq_zero]
    exact h
  have hlt : Function.Injective (LinearMap.lTensor K (LinearMap.mulLeft k s)) :=
    Module.Flat.lTensor_preserves_injective_linearMap _ hmul
  have heq : ∀ z : K ⊗[k] A,
      (Algebra.TensorProduct.includeRight s : K ⊗[k] A) * z =
        LinearMap.lTensor K (LinearMap.mulLeft k s) z := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul x a =>
      simp [Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul]
    | add z w hz hw => rw [mul_add, map_add, hz, hw]
  have hz0 : ∀ z : K ⊗[k] A,
      (Algebra.TensorProduct.includeRight s : K ⊗[k] A) * z = 0 → z = 0 := fun z hz ↦
    hlt (by rw [map_zero, ← heq z]; exact hz)
  exact mem_nonZeroDivisors_iff.mpr ⟨hz0, fun z hz ↦ hz0 z (by rw [mul_comm]; exact hz)⟩

end
