module

public import StacksFrontier.RingTheory.DividedPowers.TateResolution.DegreeZero
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.SetVariableExtension.Construction

/-!
# A graded divided-power polynomial algebra on prescribed variables over any base

Over a commutative ring `R` and for an arbitrary family `ind : ℕ → Type*` of index types there is
a graded divided-power polynomial algebra over the polynomial ring `MvPolynomial σ R` carrying one
homogeneous variable of degree `n + 1` for each element of `ind n`.

## Main results

* `DividedPowers.TateResolution.exists_gradedDividedPowerPolynomial_mvPolynomial`.
-/

@[expose] public section

namespace DividedPowers.TateResolution

universe u v w

/-- Over any commutative ring `R` and for any family of index types `ind` there is a graded
divided-power polynomial algebra over `MvPolynomial σ R`, placed in degree zero, with one
homogeneous variable of degree `n + 1` for each element of `ind n`. -/
public theorem exists_gradedDividedPowerPolynomial_mvPolynomial
    (R : Type u) [CommRing R] (σ : Type v) (ind : ℕ → Type w) :
    ∃ (B : Type (max u v w)) (ringB : Ring B),
      letI : Ring B := ringB
      ∃ algebraB : Algebra R B,
        letI : Algebra R B := algebraB
        ∃ (ℬ : ℕ → Submodule R B) (gradedB : GradedAlgebra ℬ),
          letI : GradedAlgebra ℬ := gradedB
          ∃ strictB : IsStrictlyGradedComm ℬ,
            letI : IsStrictlyGradedComm ℬ := strictB
            ∃ (δ : DividedPowerStructure ℬ) (ι : MvPolynomial σ R →ₐ[R] B)
              (hpoly : GradedDividedPowerPolynomial ℬ δ ι),
              ∀ n : ℕ, Nonempty (hpoly.indices n ≃ ind n) := by
  obtain ⟨C, ringC, algebraC, Cᵢ, gradedC, strictC, δ, ιC, T, hinj, hgrade, -, hmem, hfinite,
      hsucc, -⟩ :=
    exists_setVariableDividedPowerExtension.{u, max u v, max u v w, 0}
      (degreeZeroGrade R (MvPolynomial σ R))
      (degreeZeroDividedPowers R (MvPolynomial σ R))
      (Σ n : ℕ, ULift.{max u v, w} (ind n)) (fun j => j.1 + 1) (fun j => Nat.succ_pos j.1)
  let _ringC : Ring C := ringC
  let _algebraC : Algebra R C := algebraC
  let _gradedC : GradedAlgebra Cᵢ := gradedC
  let _strictC : IsStrictlyGradedComm Cᵢ := strictC
  refine ⟨C, ringC, algebraC, Cᵢ, gradedC, strictC, δ, ιC,
    { indices := fun n => ULift.{max u v, w} (ind n)
      generator := T
      generator_mem := hmem
      coefficient_mem := fun p => hgrade 0 p Submodule.mem_top
      coefficient_injective := hinj
      finite_support := hfinite
      successor := hsucc }, fun _ => ⟨Equiv.ulift⟩⟩

end DividedPowers.TateResolution

end
