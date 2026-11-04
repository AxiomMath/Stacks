module

public import Mathlib.FieldTheory.IsAlgClosed.Spectrum
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
public import Mathlib.RingTheory.Trace.Basic

/-!
# Integrality of the trace over a field

Let `K` be a field, `L` a finite-dimensional `K`-algebra and `R` a subring of `K`. The trace
`Trace_{L/K}` carries elements integral over `R` to elements integral over `R`. Unlike
`Algebra.isIntegral_trace` the algebra `L` is not assumed to be a field.

## Main results

* `Algebra.isIntegral_trace_of_finiteDimensional`: the trace of an element integral over `R`
  is integral over `R`.
-/

@[expose] public section

open Polynomial

/-- Over a field `K`, the trace of a finite-dimensional `K`-algebra `L` carries an element
integral over a base ring `R` to an element integral over `R`. -/
theorem Algebra.isIntegral_trace_of_finiteDimensional
    {R K L : Type*} [CommRing R] [Field K] [CommRing L]
    [Algebra R K] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
    [FiniteDimensional K L] {x : L} (hx : IsIntegral R x) :
    IsIntegral R (Algebra.trace K L x) := by
  classical
  obtain ⟨p, hp, hpx⟩ := hx
  have hpx' : Polynomial.aeval x p = 0 := hpx
  set n := Module.finrank K L
  let b : Module.Basis (Fin n) K L := Module.finBasis K L
  rcases isEmpty_or_nonempty (Fin n) with hempty | hne
  · rw [Algebra.trace_eq_matrix_trace b, Matrix.trace]
    simpa using isIntegral_zero
  · let C := AlgebraicClosure K
    let φ : L →ₐ[K] Matrix (Fin n) (Fin n) C :=
      (AlgHom.mapMatrix (Algebra.ofId K C)).comp (Algebra.leftMulMatrix b)
    let M : Matrix (Fin n) (Fin n) C := φ x
    have hMtrace : M.trace = algebraMap K C (Algebra.trace K L x) := by
      rw [Algebra.trace_eq_matrix_trace b, Matrix.trace, Matrix.trace, map_sum]
      rfl
    have hMzero : Polynomial.aeval M p = 0 := by
      have := Polynomial.aeval_algHom_apply (φ.restrictScalars R) x p
      rw [show (φ.restrictScalars R) x = M from rfl, hpx'] at this
      simpa using this
    have hroot (r : C) (hr : r ∈ M.charpoly.roots) : IsIntegral R r := by
      have hspec : r ∈ spectrum C M :=
        Matrix.mem_spectrum_iff_isRoot_charpoly.mpr (Polynomial.isRoot_of_mem_roots hr)
      have hmem : Polynomial.eval r (p.map (algebraMap R C)) ∈
          spectrum C (Polynomial.aeval M (p.map (algebraMap R C))) :=
        spectrum.subset_polynomial_aeval M (p.map (algebraMap R C)) ⟨r, hspec, rfl⟩
      rw [Polynomial.aeval_map_algebraMap, hMzero, spectrum.zero_eq,
        Set.mem_singleton_iff, Polynomial.eval_map] at hmem
      exact ⟨p, hp, hmem⟩
    rw [← isIntegral_algebraMap_iff (B := C), ← hMtrace, Matrix.trace_eq_sum_roots_charpoly]
    exact IsIntegral.multiset_sum hroot
