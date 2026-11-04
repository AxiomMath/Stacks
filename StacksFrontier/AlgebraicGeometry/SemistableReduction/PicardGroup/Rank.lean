module

public import StacksFrontier.AlgebraicGeometry.SemistableReduction.PicardGroup.Defs
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.LinearAlgebra.DiagonallyDominant
public import Mathlib.Algebra.EuclideanDomain.Int
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.Dimension.Localization
public import Mathlib.SetTheory.Cardinal.Arithmetic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The rank of the Picard group of a numerical type

The Picard group of a numerical type is a finitely generated abelian group of
rank one: its relation matrix has corank one, the kernel of the associated real
matrix being the line spanned by the multiplicity vector.

## Main results

* `AlgebraicGeometry.NumericalType.rank_picardGroup`.

## References

* [Stacks Project, Tag 0C7I](https://stacks.math.columbia.edu/tag/0C7I)
-/

@[expose] public section

open Matrix

namespace AlgebraicGeometry.NumericalType

add_to_stacks 0C7I "finite generation" Module.Finite.quotient
add_to_sga "6 I 3.2" "special case" Module.Finite.quotient
add_to_ega "0 5.2.1" "special case" Module.Finite.quotient

private theorem scaled_intersection_sum_eq_zero_iff (T : NumericalType)
    (j : Fin T.componentCount) (v : Fin T.componentCount → ℤ) :
    (∑ i, (T.intersection i j / T.weight j) * v i = 0) ↔
      ∑ i, T.intersection i j * v i = 0 := by
  have hmul :
      (∑ i, (T.intersection i j / T.weight j) * v i) * T.weight j =
        ∑ i, T.intersection i j * v i := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hdvd : T.weight j ∣ T.intersection i j :=
      (T.intersection_symm j i) ▸ T.weight_dvd_intersection j i
    rw [mul_assoc, mul_comm (v i), ← mul_assoc, Int.ediv_mul_cancel hdvd]
  rw [← hmul]
  exact (mul_eq_zero.trans (or_iff_left (T.weight_pos j).ne')).symm

private theorem picardRelationMap_eq_zero_iff (T : NumericalType)
    (v : Fin T.componentCount → ℤ) :
    picardRelationMap T v = 0 ↔ ∀ j, ∑ i, T.intersection i j * v i = 0 := by
  rw [funext_iff]
  refine forall_congr' fun j => ?_
  simpa [picardRelationMap, picardRelationMatrix, Matrix.toLin'_apply,
    Matrix.mulVec_apply, dotProduct] using scaled_intersection_sum_eq_zero_iff T j v

private theorem multiplicity_mem_picardRelationMap_ker (T : NumericalType) :
    (fun i => T.multiplicity i) ∈ LinearMap.ker (picardRelationMap T) := by
  rw [LinearMap.mem_ker, picardRelationMap_eq_zero_iff]
  intro j
  simpa only [T.intersection_symm] using T.intersection_mul_multiplicity j

private def intersectionMatrixReal (T : NumericalType) :
    Matrix (Fin T.componentCount) (Fin T.componentCount) ℝ :=
  fun i j => T.intersection i j

private def multiplicityReal (T : NumericalType) : Fin T.componentCount → ℝ :=
  fun i => T.multiplicity i

/-- A real vector lies in the kernel of the real intersection matrix iff its rows sum to zero. -/
private theorem mem_ker_intersectionMatrixReal_iff (T : NumericalType)
    (v : Fin T.componentCount → ℝ) :
    v ∈ LinearMap.ker (intersectionMatrixReal T).mulVecLin ↔
      ∀ i, ∑ j, (T.intersection i j : ℝ) * v j = 0 := by
  simp [LinearMap.mem_ker, funext_iff, intersectionMatrixReal, Matrix.mulVec_apply, dotProduct]

private theorem intersectionMatrixReal_ker_eq_span (T : NumericalType) :
    LinearMap.ker (intersectionMatrixReal T).mulVecLin =
      Submodule.span ℝ {multiplicityReal T} := by
  let A := intersectionMatrixReal T
  let m := multiplicityReal T
  have hA : A.IsSymm := by
    apply Matrix.IsSymm.ext
    intro i j
    change (T.intersection j i : ℝ) = (T.intersection i j : ℝ)
    exact_mod_cast T.intersection_symm j i
  have hoff : ∀ i j, i ≠ j → 0 ≤ A i j := by
    intro i j hij
    change (0 : ℝ) ≤ (T.intersection i j : ℝ)
    exact_mod_cast T.intersection_nonneg i j hij
  have hm : ∀ i, 0 < m i := by
    intro i
    change (0 : ℝ) < (T.multiplicity i : ℝ)
    exact_mod_cast T.multiplicity_pos i
  have hsum : ∀ i, ∑ j, (T.intersection i j : ℝ) * (T.multiplicity j : ℝ) = 0 :=
    fun i => mod_cast T.intersection_mul_multiplicity i
  have hdom : ∀ i, ∑ j ∈ Finset.univ.erase i, A i j * m j ≤ -A i i * m i := by
    intro i
    have hdecomp := Finset.sum_erase_add Finset.univ (fun j => A i j * m j)
      (Finset.mem_univ i)
    have hz : (∑ j, A i j * m j) = 0 := by
      simpa [A, m, intersectionMatrixReal, multiplicityReal] using hsum i
    linarith
  have hrec := ker_mulVecLin_eq_span_indicator A m hA hoff hm hdom
  have hleft : LinearMap.ker A.mulVecLin ≤ Submodule.span ℝ {m} := by
    rw [hrec]
    refine Submodule.span_le.mpr ?_
    rintro x ⟨I, rfl, hcut, -⟩
    rcases I.eq_empty_or_nonempty with rfl | hInonempty
    · rw [Set.indicator_empty']
      exact Submodule.zero_mem _
    · have hI : I = Set.univ := by
        by_contra hI
        have hcutZ : ∀ i ∈ I, ∀ j ∉ I, T.intersection i j = 0 := fun i hi j hj => by
          exact_mod_cast (show (T.intersection i j : ℝ) = 0 from hcut i hi j hj)
        exact T.connected ⟨I, hInonempty, hI, hcutZ⟩
      subst I
      simp [m]
  have hmker : m ∈ LinearMap.ker A.mulVecLin :=
    (mem_ker_intersectionMatrixReal_iff T m).mpr hsum
  exact le_antisymm hleft ((Submodule.span_singleton_le_iff_mem _ _).mpr hmker)

private theorem picardKernel_intersection_row (T : NumericalType)
    (x : LinearMap.ker (picardRelationMap T)) (j : Fin T.componentCount) :
    ∑ i, T.intersection i j * x.1 i = 0 :=
  (picardRelationMap_eq_zero_iff T x.1).mp x.2 j

private theorem picardKernel_cross (T : NumericalType)
    (x : LinearMap.ker (picardRelationMap T)) (i j : Fin T.componentCount) :
    x.1 j * T.multiplicity i = x.1 i * T.multiplicity j := by
  let xR : Fin T.componentCount → ℝ := fun k => x.1 k
  have hxR : xR ∈ LinearMap.ker (intersectionMatrixReal T).mulVecLin := by
    refine (mem_ker_intersectionMatrixReal_iff T xR).mpr fun k => ?_
    have hzR : ∑ i, (T.intersection i k : ℝ) * (x.1 i : ℝ) = 0 := by
      exact_mod_cast picardKernel_intersection_row T x k
    simpa [xR, T.intersection_symm] using hzR
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp
    (by rwa [← intersectionMatrixReal_ker_eq_span T] : xR ∈ Submodule.span ℝ {multiplicityReal T})
  have hi := congrFun hc i
  have hj := congrFun hc j
  simp only [Pi.smul_apply, multiplicityReal, smul_eq_mul, xR] at hi hj
  have hcross : (x.1 j : ℝ) * (T.multiplicity i : ℝ) =
      (x.1 i : ℝ) * (T.multiplicity j : ℝ) := by
    rw [← hj, ← hi]
    ring
  exact_mod_cast hcross

private theorem picardKernel_rank_eq_one (T : NumericalType) :
    Module.rank ℤ (LinearMap.ker (picardRelationMap T)) = 1 := by
  let K := LinearMap.ker (picardRelationMap T)
  let i₀ : Fin T.componentCount := ⟨0, T.componentCount_pos⟩
  let m₀ := T.multiplicity i₀
  have hm₀ : m₀ ≠ 0 := (T.multiplicity_pos i₀).ne'
  let mK : K := ⟨T.multiplicity, multiplicity_mem_picardRelationMap_ker T⟩
  let lower : ℤ →ₗ[ℤ] K := LinearMap.toSpanSingleton ℤ K mK
  have hlower : Function.Injective lower := fun a b hab => mul_right_cancel₀ hm₀ <| by
    simpa [lower, LinearMap.toSpanSingleton_apply, mK, m₀] using congrArg (fun v : K => v.1 i₀) hab
  have hlowrank : 1 ≤ Module.rank ℤ K := by
    simpa only [CommSemiring.rank_self] using LinearMap.rank_le_of_injective lower hlower
  let coeff : K →ₗ[ℤ] ℤ := (LinearMap.proj i₀).comp K.subtype
  have hcoeff : Function.Injective coeff := by
    intro x y hxy
    refine Subtype.ext (funext fun j => mul_right_cancel₀ hm₀ ?_)
    calc
      x.1 j * m₀ = x.1 i₀ * T.multiplicity j := picardKernel_cross T x i₀ j
      _ = y.1 i₀ * T.multiplicity j := by rw [show x.1 i₀ = y.1 i₀ from hxy]
      _ = y.1 j * m₀ := (picardKernel_cross T y i₀ j).symm
  have hupper : Module.rank ℤ K ≤ 1 := by
    simpa only [CommSemiring.rank_self] using LinearMap.rank_le_of_injective coeff hcoeff
  exact le_antisymm hupper hlowrank

/-- The Picard group of a numerical type has rank one. -/
@[stacks 0C7I "rank one"]
public theorem rank_picardGroup (T : NumericalType) :
    Module.rank ℤ (picardGroup T) = 1 := by
  let f := picardRelationMap T
  have hq := rank_quotient_add_rank_of_isDomain (LinearMap.range f)
  have hr := LinearMap.rank_range_add_rank_ker f
  have hfinite : Module.rank ℤ (LinearMap.range f) < Cardinal.aleph0 := by
    calc
      Module.rank ℤ (LinearMap.range f) ≤ Module.rank ℤ (Fin T.componentCount → ℤ) :=
        Submodule.rank_le _
      _ = T.componentCount := rank_fin_fun T.componentCount
      _ < Cardinal.aleph0 := Cardinal.natCast_lt_aleph0
  have hadd :
      Module.rank ℤ (LinearMap.range f) + Module.rank ℤ (picardGroup T) =
        Module.rank ℤ (LinearMap.range f) +
          Module.rank ℤ (LinearMap.ker f) := by
    calc
      _ = Module.rank ℤ (picardGroup T) + Module.rank ℤ (LinearMap.range f) := add_comm _ _
      _ = Module.rank ℤ (Fin T.componentCount → ℤ) := by simpa [picardGroup, f] using hq
      _ = Module.rank ℤ (LinearMap.range f) + Module.rank ℤ (LinearMap.ker f) := by
        simpa [f] using hr.symm
  exact (Cardinal.eq_of_add_eq_add_left hadd hfinite).trans (picardKernel_rank_eq_one T)

end AlgebraicGeometry.NumericalType
