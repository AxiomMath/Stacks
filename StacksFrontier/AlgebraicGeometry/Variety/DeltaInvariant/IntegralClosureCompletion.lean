module

public import StacksFrontier.AlgebraicGeometry.Variety.DeltaInvariant.Completion
public import StacksFrontier.AlgebraicGeometry.Variety.DeltaInvariant.IntegralClosureHenselization
public import StacksFrontier.RingTheory.AdicCompletion.Algebraization
public import StacksFrontier.RingTheory.AdicCompletion.FiniteAlgebra
public import StacksCore.Tactic.StacksAttribute

/-!
# The integral closure in the total ring of fractions after completion

Let `A` be a reduced one-dimensional Nagata local ring and let `B` be its completion at the
maximal ideal. **The base change to `B` of the integral closure of `A` in its total ring of
fractions is the integral closure of `B` in its own total ring of fractions.**

## Main results

* `IsLocalRing.isNormalRing_tensorProduct_adicCompletion`: a normal finite extension of `A`,
  base changed to the completion of `A`, is normal.
* `IsLocalRing.exists_fractionRing_map_and_tensorProduct_range_eq_integralClosure_completion`
  identifies the base-changed integral closure with the integral closure of the completion
  inside its total ring of fractions.

## References

* [Stacks Project, Tag 0C3V](https://stacks.math.columbia.edu/tag/0C3V)
-/

@[expose] public section

open IsLocalRing
open scoped TensorProduct

universe u

namespace IsLocalRing

/-- **A normal finite extension of a reduced one-dimensional Noetherian local ring stays normal
after base change to the completion of that local ring.** -/
public theorem isNormalRing_tensorProduct_adicCompletion
    {A : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [IsReduced A]
    (hdim : ringKrullDim A = 1)
    (S : Type*) [CommRing S] [Algebra A S] [Module.Finite A S]
    (hnormalS : IsNormalRing S) (hinj : Function.Injective (algebraMap A S))
    {f : A} (hfm : f ∈ maximalIdeal A)
    (hSf : algebraMap A S f ∈ nonZeroDivisors S) :
    IsNormalRing (S ⊗[A] AdicCompletion (maximalIdeal A) A) := by
  classical
  have : IsNoetherianRing S := IsNoetherianRing.of_finite A S
  have : Module.Flat A (AdicCompletion (maximalIdeal A) A) :=
    AdicCompletion.flat_of_isNoetherian (maximalIdeal A)
  have : FaithfulSMul A S := ⟨fun {x y} hxy => hinj (by
    simpa [Algebra.smul_def] using hxy (1 : S))⟩
  have hdimS : ringKrullDim S = 1 := by
    rw [← Algebra.IsIntegral.ringKrullDim_eq A S, hdim]
  have : Finite ((maximalIdeal A).primesOver S) :=
    Algebra.QuasiFinite.finite_primesOver (S := S) (maximalIdeal A)
  have : IsLocalization.AtPrime A (maximalIdeal A) :=
    IsLocalization.of_le_isUnit fun a ha => (notMem_maximalIdeal (R := A)).mp ha
  obtain ⟨e⟩ := AdicCompletion.nonempty_algEquiv_pi_primesOver (S := S)
    (maximalIdeal A) A (fun q => Localization.AtPrime q.1)
  refine IsNormalRing.congr e.symm.toRingEquiv (isNormalRing_pi fun q => ?_)
  let Sq := Localization.AtPrime q.1
  have : IsNoetherianRing Sq :=
    IsLocalization.isNoetherianRing q.1.primeCompl Sq ‹IsNoetherianRing S›
  have hqOver : q.1.comap (algebraMap A S) = maximalIdeal A := by
    simpa [Ideal.under_def] using q.2.2.over.symm
  have hqf : algebraMap A S f ∈ q.1 := by rwa [← Ideal.mem_comap, hqOver]
  have hqheight : q.1.height = 1 := by
    refine le_antisymm ?_ ((Ideal.one_le_height_span_singleton_of_mem_nonZeroDivisors hSf).trans
      (Ideal.height_mono ((Ideal.span_singleton_le_iff_mem _).mpr hqf)))
    have hh := Ideal.height_le_ringKrullDim_of_isPrime (I := q.1)
    rw [hdimS] at hh
    exact_mod_cast hh
  have hdimSq : ringKrullDim Sq = 1 := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height q.1 Sq]
    exact_mod_cast hqheight
  have : q.1.IsPrime := q.2.1
  obtain ⟨hdomQ, hclosedQ⟩ := hnormalS q.1
  obtain ⟨_, _⟩ := (isDiscreteValuationRing_iff_adicCompletion_maximalIdeal (A := Sq)).mp
    (((isDiscreteValuationRing_tfae Sq).out 5 1).mp
      (by exact ⟨inferInstance, inferInstance, hdomQ, hclosedQ, hdimSq⟩))
  exact IsNormalRing.of_isIntegrallyClosed (AdicCompletion (maximalIdeal Sq) Sq)

/-- The base change to the completion of the integral closure of a reduced one-dimensional
Nagata local ring in its total ring of fractions is the integral closure of the completion in its
total ring of fractions. -/
@[stacks 0C3V "completion_integral_closure"]
public lemma exists_fractionRing_map_and_tensorProduct_range_eq_integralClosure_completion
    {A : Type u} [CommRing A] [IsLocalRing A] [IsReduced A]
    (hA : IsNagataRing A) (hdim : ringKrullDim A = 1) :
    let B := AdicCompletion (maximalIdeal A) A
    ∃ q : FractionRing A →ₐ[A] FractionRing B,
      ∃ g : (integralClosure A (FractionRing A) ⊗[A] B) →ₐ[A] FractionRing B,
        Function.Injective g ∧
          g.range = (integralClosure B (FractionRing B)).restrictScalars A ∧
          g.comp
              (Algebra.TensorProduct.includeLeft :
                integralClosure A (FractionRing A) →ₐ[A]
                  (integralClosure A (FractionRing A) ⊗[A] B)) =
            q.comp (integralClosure A (FractionRing A)).val ∧
          g.comp
              (Algebra.TensorProduct.includeRight :
                B →ₐ[A] (integralClosure A (FractionRing A) ⊗[A] B)) =
            IsScalarTower.toAlgHom A B (FractionRing B) := by
  dsimp only
  let B := AdicCompletion (maximalIdeal A) A
  have : IsNoetherianRing A := hA.1
  have : Module.Finite A (integralClosure A (FractionRing A)) :=
    module_finite_integralClosure_fractionRing hA
  have : Module.Flat A B := AdicCompletion.flat_of_isNoetherian (maximalIdeal A)
  have hredB : IsReduced B := isReduced_adicCompletion_maximalIdeal_of_isNagataRing hA
  have hdimB : ringKrullDim B = 1 :=
    (ringKrullDim_adicCompletion_maximalIdeal (A := A)).trans hdim
  obtain ⟨f, hfm, hLA, hLAC, hBlocal⟩ :=
    exists_common_fractionRing_localization_and_injective_tensorProduct hA hdim
  have hfreg : f ∈ nonZeroDivisors A :=
    localization_submonoid_le_nonZeroDivisors (S := FractionRing A) (Submonoid.powers f)
      (IsFractionRing.injective A (FractionRing A)) (Submonoid.mem_powers f)
  have hfmB : algebraMap A B f ∈ maximalIdeal B := by
    rw [AdicCompletion.maximalIdeal_eq_map]
    exact Ideal.mem_map_of_mem (algebraMap A B) hfm
  have hradB : (Ideal.span {algebraMap A B f} : Ideal B).radical = maximalIdeal B :=
    radical_span_regular_eq_maximalIdeal B (nonZeroDivisor_algebraMap_of_flat hfreg) hfmB hdimB
  obtain ⟨hLB, ⟨q, g, hg, hcompLeft, hcompRight⟩⟩ := hBlocal B hredB hdimB hradB
  have hinjAS : Function.Injective (algebraMap A (integralClosure A (FractionRing A))) :=
    fun x y hxy => IsFractionRing.injective A (FractionRing A) (congrArg Subtype.val hxy)
  have hSf : algebraMap A (integralClosure A (FractionRing A)) f ∈
      nonZeroDivisors (integralClosure A (FractionRing A)) :=
    nonZeroDivisor_integralClosure_of_powerLocalization hLA
  have hnormalR : IsNormalRing (integralClosure A (FractionRing A) ⊗[A] B) :=
    isNormalRing_tensorProduct_adicCompletion hdim (integralClosure A (FractionRing A))
      (isNormalRing_integralClosure_fractionRing (A := A)) hinjAS hfm hSf
  have hcompat (b : B) : g (Algebra.TensorProduct.includeRight b) =
      algebraMap B (FractionRing B) b :=
    congrArg (fun k : B →ₐ[A] FractionRing B => k b) hcompRight
  refine ⟨q, g, hg, ?_, hcompLeft, hcompRight⟩
  ext x
  exact (isIntegral_iff_mem_range_tensorProduct g hg hcompat hnormalR
    (algebraMap A B f) hLB x).symm

end IsLocalRing

end
