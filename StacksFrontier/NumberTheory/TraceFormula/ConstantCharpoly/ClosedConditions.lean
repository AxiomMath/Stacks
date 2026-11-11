module

public import Mathlib.Data.Matrix.Basis
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Localization.Integer
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Instances.Matrix

/-!
# Linear conditions over the fraction field are closed on matrices over the ring

Let `R` be a Hausdorff topological ring with fraction field `F`. A matrix `A` over `R` is also a
matrix over `F`, and an `F`-linear functional `L` on matrices over `F` becomes, after clearing
the finitely many denominators of its values on the matrix units, a continuous function of the
entries of `A` with values in `R`. Hence every condition `L A = c` cuts out a closed set of
matrices over `R`, and so does every condition `Φ A = e` for an `F`-linear map `Φ` into a
finite-dimensional `F`-vector space, read coordinatewise in a basis.

This is what makes the conditions on the entries of `P⁻¹ ρ(g) P`, for `P` invertible over a
finite extension of `F`, closed conditions on `g` when `ρ` is a continuous representation over
`R`.

## Main results

* `Stacks.TraceFormula.exists_continuous_algebraMap_eq_mul`: an `F`-linear functional on
  matrices over `F`, multiplied by a suitable nonzero element of `R`, is a continuous `R`-valued
  function of matrices over `R`.
* `Stacks.TraceFormula.isClosed_setOf_map_eq`: the condition `L A = c` is closed.
* `Stacks.TraceFormula.isClosed_setOf_map_eq_of_finiteDimensional`: the condition `Φ A = e`, for
  `Φ` with values in a finite-dimensional `F`-vector space, is closed.
-/

@[expose] public noncomputable section

open Matrix

namespace Stacks.TraceFormula

variable {R F ι : Type*} [CommRing R] [Field F] [Algebra R F] [IsFractionRing R F] [Finite ι]

/-- **Clearing denominators of a linear functional on matrices.** An `F`-linear functional `L`
on matrices over the fraction field `F` of a topological ring `R` is, after multiplication by a
suitable nonzero element `r` of `R`, a continuous `R`-valued function `f` of matrices over `R`:
`f A = r · L A` for every matrix `A` over `R`. -/
theorem exists_continuous_algebraMap_eq_mul [TopologicalSpace R] [IsTopologicalRing R]
    (L : Matrix ι ι F →ₗ[F] F) :
    ∃ r ∈ nonZeroDivisors R, ∃ f : Matrix ι ι R → R, Continuous f ∧
      ∀ A, algebraMap R F (f A) = algebraMap R F r * L (A.map (algebraMap R F)) := by
  classical
  have := Fintype.ofFinite ι
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors R)
    (Finset.univ : Finset (ι × ι)) (fun p => L (Matrix.single p.1 p.2 1))
  choose c hc using fun p => RingHom.mem_rangeS.mp (hb p (Finset.mem_univ p))
  refine ⟨b, b.2, fun A => ∑ p : ι × ι, A p.1 p.2 * c p, ?_, fun A => ?_⟩
  · exact continuous_finsetSum _ fun p _ =>
      (continuous_id.matrix_elem p.1 p.2).mul continuous_const
  · conv_rhs => rw [Matrix.matrix_eq_sum_single (A.map (algebraMap R F))]
    simp only [map_sum, map_mul, hc, Algebra.smul_def, Finset.mul_sum, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have : Matrix.single i j (algebraMap R F (A i j)) =
        algebraMap R F (A i j) • Matrix.single i j (1 : F) := by
      rw [Matrix.smul_single, smul_eq_mul, mul_one]
    rw [Matrix.map_apply, this, map_smul, smul_eq_mul]
    ring

/-- **A linear condition over the fraction field is closed.** For an `F`-linear functional `L`
on matrices over the fraction field `F` of a Hausdorff topological ring `R`, the matrices `A`
over `R` with `L A = c` form a closed set. -/
theorem isClosed_setOf_map_eq [TopologicalSpace R] [IsTopologicalRing R] [T2Space R]
    [Nontrivial R] (L : Matrix ι ι F →ₗ[F] F) (c : F) :
    IsClosed {A : Matrix ι ι R | L (A.map (algebraMap R F)) = c} := by
  obtain ⟨r, hr, f, hf, hfL⟩ := exists_continuous_algebraMap_eq_mul (R := R) L
  have hr0 : algebraMap R F r ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hr
  by_cases h : ∃ a, algebraMap R F a = algebraMap R F r * c
  · obtain ⟨a, ha⟩ := h
    convert (isClosed_singleton (x := a)).preimage hf using 1
    ext A
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff]
    rw [← (IsFractionRing.injective R F).eq_iff, hfL, ha, mul_right_inj' hr0]
  · convert isClosed_empty
    ext A
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    intro hA
    exact h ⟨f A, by rw [hfL, hA]⟩

/-- **A linear condition with values in a finite-dimensional space is closed.** For an
`F`-linear map `Φ` from matrices over the fraction field `F` of a Hausdorff topological ring `R`
to a finite-dimensional `F`-vector space `V`, the matrices `A` over `R` with `Φ A = e` form a
closed set: in a basis of `V` the condition is finitely many conditions `L A = c`. -/
theorem isClosed_setOf_map_eq_of_finiteDimensional [TopologicalSpace R] [IsTopologicalRing R]
    [T2Space R] [Nontrivial R] {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (Φ : Matrix ι ι F →ₗ[F] V) (e : V) :
    IsClosed {A : Matrix ι ι R | Φ (A.map (algebraMap R F)) = e} := by
  set b := Module.finBasis F V
  have : {A : Matrix ι ι R | Φ (A.map (algebraMap R F)) = e} =
      ⋂ k, {A : Matrix ι ι R | ((b.coord k).comp Φ) (A.map (algebraMap R F)) = b.coord k e} := by
    ext A
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, LinearMap.comp_apply,
      Module.Basis.coord_apply]
    exact b.ext_elem_iff
  rw [this]
  exact isClosed_iInter fun k => isClosed_setOf_map_eq (R := R) _ _

end Stacks.TraceFormula

end
