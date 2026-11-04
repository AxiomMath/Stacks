module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.PadicIntegerRingModel
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RepresentationCommutantCohomology
public import Mathlib.RingTheory.Trace.Basic

/-!
# Traces over the ring of integers and determination by twisted traces

For a finite extension `E` of `ℚ_ℓ` with ring of integers `O_E`, the trace of `O_E` over `ℤ_ℓ` is
the restriction of the trace of `E` over `ℚ_ℓ`. An element `z ∈ E` is determined by the values
`Tr_{E/ℚ_ℓ}(c z)` for `c` in any subset containing a nonzero `ℚ_ℓ`-multiple of every element of
`E`, the trace form being nondegenerate; for an order `O ⊆ E` with `E = O[1/ℓ]`, such a subset is
`O ∩ O_E`.

## Main results

* `Stacks.EtaleCohomology.algebraMap_trace_padicIntegerRing`: the trace of `O_E` over `ℤ_ℓ` is
  the restriction of the trace of `E` over `ℚ_ℓ`.
* `Stacks.EtaleCohomology.eq_of_forall_trace_mul_eq`: an element of `E` is determined by its
  traces against a set containing a nonzero multiple of every element.
* `Stacks.EtaleCohomology.exists_smul_mem_conjIntegralSubring_padicIntegerRing`: every element of
  `E` has a nonzero multiple in `O ∩ O_E`.
-/

@[expose] public noncomputable section

open Module Matrix

namespace Stacks.EtaleCohomology

variable {ℓ : ℕ} [Fact ℓ.Prime] {E : Type} [Field E] [Algebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]

attribute [local instance] padicIntAlgebraOfRat

local notation "𝒪" => integralClosure ℤ_[ℓ] E

/-- **The trace of `O_E` over `ℤ_ℓ` is the restriction of the trace of `E` over `ℚ_ℓ`.** -/
public theorem algebraMap_trace_padicIntegerRing {d : ℕ} (b : Basis (Fin d) ℚ_[ℓ] E) (z : 𝒪) :
    algebraMap ℤ_[ℓ] ℚ_[ℓ] (Algebra.trace ℤ_[ℓ] 𝒪 z) = Algebra.trace ℚ_[ℓ] E (z : E) := by
  rw [Algebra.trace_eq_matrix_trace (padicIntegerRingBasisOf b) z,
    Algebra.trace_eq_matrix_trace (padicIntegerRingBasisRatOf b) (z : E)]
  have h : Algebra.leftMulMatrix (padicIntegerRingBasisRatOf b) (z : E) =
      (Algebra.leftMulMatrix (padicIntegerRingBasisOf b) z).map (algebraMap ℤ_[ℓ] ℚ_[ℓ]) := by
    ext l l'
    rw [Matrix.map_apply, Algebra.leftMulMatrix_eq_repr_mul, Algebra.leftMulMatrix_eq_repr_mul,
      padicIntegerRingBasisRatOf_apply]
    show (padicIntegerRingBasisRatOf b).repr ((z * padicIntegerRingBasisOf b l' : 𝒪) : E) l = _
    rw [padicIntegerRingBasisRatOf_repr]
    rfl
  rw [h]
  exact AddMonoidHom.map_trace (algebraMap ℤ_[ℓ] ℚ_[ℓ]) _

omit [FiniteDimensional ℚ_[ℓ] E] in
/-- **An element of `E` is determined by its traces against a set containing a nonzero multiple
of every element**, the trace form being nondegenerate. -/
public theorem eq_of_forall_trace_mul_eq [FiniteDimensional ℚ_[ℓ] E] (S : Set E)
    (hS : ∀ e : E, ∃ t : ℚ_[ℓ], t ≠ 0 ∧ t • e ∈ S) (X Y : E)
    (h : ∀ c ∈ S, Algebra.trace ℚ_[ℓ] E (c * X) = Algebra.trace ℚ_[ℓ] E (c * Y)) : X = Y := by
  have hZ : ∀ e : E, Algebra.trace ℚ_[ℓ] E ((X - Y) * e) = 0 := by
    intro e
    obtain ⟨t, ht, hte⟩ := hS e
    have h1 := h _ hte
    have h2 : Algebra.trace ℚ_[ℓ] E ((t • e) * (X - Y)) = 0 := by
      rw [mul_sub, map_sub, h1, sub_self]
    rw [smul_mul_assoc, map_smul, smul_eq_mul] at h2
    rw [mul_comm]
    exact (mul_eq_zero.1 h2).resolve_left ht
  have hnd := traceForm_nondegenerate ℚ_[ℓ] E
  exact sub_eq_zero.1 (hnd.1 _ fun e => by rw [Algebra.traceForm_apply]; exact hZ e)

/-- **Nonzero multiples of every element lie in `O ∩ O_E`**, for the integral part `O` of `E`
along a matrix representation. -/
public theorem exists_smul_mem_conjIntegralSubring_padicIntegerRing {r : ℕ}
    (P : GL (Fin r) ℚ_[ℓ]) (α : E →ₐ[ℚ_[ℓ]] Matrix (Fin r) (Fin r) ℚ_[ℓ]) (e : E) :
    ∃ t : ℚ_[ℓ], t ≠ 0 ∧ t • e ∈ conjIntegralSubring P α ∧ IsIntegral ℤ_[ℓ] (t • e) := by
  obtain ⟨N, hN⟩ := exists_pow_mul_mem_conjIntegralSubring P α e
  obtain ⟨⟨x, s⟩, hx⟩ := IsLocalization.surj
    (Algebra.algebraMapSubmonoid 𝒪 (nonZeroDivisors ℤ_[ℓ])) e
  obtain ⟨s0, hs0, hs⟩ := s.2
  have hs0' : s0 ≠ 0 := nonZeroDivisors.ne_zero hs0
  have hse : ((s : 𝒪) : E) = algebraMap ℚ_[ℓ] E (s0 : ℚ_[ℓ]) := by
    rw [← hs]
    rfl
  have h : ((s0 : ℚ_[ℓ]) * (ℓ : ℚ_[ℓ]) ^ N) • e =
      algebraMap ℚ_[ℓ] E (s0 : ℚ_[ℓ]) * ((ℓ : E) ^ N * e) := by
    rw [Algebra.smul_def, map_mul, map_pow, map_natCast, mul_assoc]
  refine ⟨(s0 : ℚ_[ℓ]) * (ℓ : ℚ_[ℓ]) ^ N, mul_ne_zero (PadicInt.coe_ne_zero.2 hs0')
    (pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : ℓ.Prime).ne_zero)), ?_, ?_⟩
  · rw [h]
    exact mul_mem (algebraMap_mem_conjIntegralSubring P α s0) hN
  · have h' : ((s0 : ℚ_[ℓ]) * (ℓ : ℚ_[ℓ]) ^ N) • e = (ℓ : E) ^ N * ((x : 𝒪) : E) := by
      show _ = (ℓ : E) ^ N * algebraMap 𝒪 E x
      rw [h, ← hx, ← hse]
      show _ = (ℓ : E) ^ N * (e * ((s : 𝒪) : E))
      ring
    rw [h']
    have hl : IsIntegral ℤ_[ℓ] (ℓ : E) := by
      rw [← map_natCast (algebraMap ℤ_[ℓ] E) ℓ]
      exact isIntegral_algebraMap
    exact (hl.pow N).mul x.2

end Stacks.EtaleCohomology

end
