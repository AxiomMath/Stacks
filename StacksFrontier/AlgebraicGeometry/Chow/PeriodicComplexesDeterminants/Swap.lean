module

public import StacksFrontier.AlgebraicGeometry.Chow.PeriodicComplexesDeterminants.Basic

/-!
# The periodic determinant under a shift

For an exact two-periodic complex on a finite-length module over a local ring, interchanging
its two differentials inverts its periodic determinant.

## Main results

* `AlgebraicGeometry.periodicDeterminant_mul_swap` says that the periodic determinants before
  and after interchanging the differentials multiply to one.

## Implementation notes

The two-periodic complex is represented by two endomorphisms and exactness in both directions,
as in the definition of `AlgebraicGeometry.periodicDeterminant`.

## References

* [Stacks Project, Tag 02PL](https://stacks.math.columbia.edu/tag/02PL)
-/

@[expose] public section

open scoped TensorProduct

open Module.FiniteLength

namespace AlgebraicGeometry

universe u v

/-- **Stacks Project, Tag 02PL.** Interchanging the two maps of an exact two-periodic complex
inverts its periodic determinant. -/
@[stacks 02PL]
theorem periodicDeterminant_mul_swap
    {R : Type u} {M : Type v} [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M]
    (φ ψ : M →ₗ[R] M) (hφψ : Function.Exact φ ψ)
    (hψφ : Function.Exact ψ φ) (hM : IsFiniteLength R M) :
    periodicDeterminant φ ψ hφψ hψφ hM *
        periodicDeterminant ψ φ hψφ hφψ hM = 1 := by
  let d := periodicDeterminant φ ψ hφψ hψφ hM
  let e := periodicDeterminant ψ φ hψφ hφψ hM
  let s : IsLocalRing.ResidueField R := (-1 : IsLocalRing.ResidueField R) ^
    (moduleLength R (LinearMap.range φ) * moduleLength R (LinearMap.range ψ))
  have hbij : Function.Bijective (periodicGamma φ ψ hψφ hM) := by
    unfold periodicGamma
    apply determinantExactSequenceMap_bijective
  have : Nontrivial (determinant R M) :=
    Module.nontrivial_of_finrank_pos (by
      rw [finrank_determinant_eq_one (R := R) (M := M) hM]
      exact Nat.zero_lt_one)
  obtain ⟨y, hy⟩ : ∃ y : determinant R M, y ≠ 0 := exists_ne (0 : determinant R M)
  obtain ⟨x, hx⟩ := hbij.2 y
  let c := (TensorProduct.comm (IsLocalRing.ResidueField R)
    (determinant R (LinearMap.range ψ)) (determinant R (LinearMap.range φ))).toLinearMap
  let c' := (TensorProduct.comm (IsLocalRing.ResidueField R)
    (determinant R (LinearMap.range φ)) (determinant R (LinearMap.range ψ))).toLinearMap
  have h1 : periodicGamma ψ φ hφψ hM ∘ₗ c =
      (s * (d : IsLocalRing.ResidueField R)) • periodicGamma φ ψ hψφ hM := by
    simpa [IsPeriodicDeterminant, c, s] using periodicDeterminant_spec φ ψ hφψ hψφ hM
  have h2 : periodicGamma φ ψ hψφ hM ∘ₗ c' =
      (s * (e : IsLocalRing.ResidueField R)) • periodicGamma ψ φ hφψ hM := by
    simpa [IsPeriodicDeterminant, c', s, Nat.mul_comm] using
      periodicDeterminant_spec ψ φ hψφ hφψ hM
  have hpoint : y = ((s * (e : IsLocalRing.ResidueField R)) *
      (s * (d : IsLocalRing.ResidueField R))) • y := by
    calc
      y = periodicGamma φ ψ hψφ hM x := hx.symm
      _ = periodicGamma φ ψ hψφ hM (c' (c x)) := by
        congr 1
        simp [c, c']
      _ = (s * (e : IsLocalRing.ResidueField R)) • periodicGamma ψ φ hφψ hM (c x) := by
        simpa [LinearMap.comp_apply] using congrArg (fun f => f (c x)) h2
      _ = ((s * (e : IsLocalRing.ResidueField R)) *
          (s * (d : IsLocalRing.ResidueField R))) • periodicGamma φ ψ hψφ hM x := by
        have hh := congrArg (fun f => f x) h1
        rw [LinearMap.comp_apply] at hh
        rw [hh]
        exact smul_smul _ _ _
      _ = ((s * (e : IsLocalRing.ResidueField R)) *
          (s * (d : IsLocalRing.ResidueField R))) • y :=
        congrArg (fun z : determinant R M => _ • z) hx
  have hscalar : (s * (e : IsLocalRing.ResidueField R)) *
      (s * (d : IsLocalRing.ResidueField R)) = 1 :=
    (smul_left_injective (IsLocalRing.ResidueField R) hy).eq_iff.mp (by simpa using hpoint.symm)
  have hs : s * s = 1 := by
    dsimp [s]
    rw [← pow_add, ← two_mul, pow_mul]
    norm_num
  have hde : (d : IsLocalRing.ResidueField R) * (e : IsLocalRing.ResidueField R) = 1 := by
    rw [← hscalar, ← one_mul ((d : IsLocalRing.ResidueField R) * e), ← hs]
    ring
  exact Units.ext (by simpa [d, e] using hde)

end AlgebraicGeometry
