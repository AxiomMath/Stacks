module

public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.Algebra.Polynomial.Eval.Coeff
public import Mathlib.RingTheory.GradedAlgebra.RingHom

/-!
# Adjoining a variable of degree one to a graded ring

Let `A = ⨁_{n ≥ 0} Aₙ` be a graded ring. The polynomial ring `A[S]` is graded with `S` placed in
degree `1`: its degree-`n` piece consists of the polynomials `∑ⱼ aⱼ Sʲ` with `aⱼ ∈ A_{n-j}` for
`j ≤ n` and `aⱼ = 0` for `j > n`. This is the graded ring written `A[S]` in [Stacks, Tag 0FBG],
clause (5), for the conormal algebra.

## Main definitions

* `Stacks.PolynomialGrading.grading`: the degree-`n` piece of `A[S]`.
* `Stacks.PolynomialGrading.instGradedRing`: `A[S]` is a graded ring.
* `Stacks.PolynomialGrading.includeC`: the inclusion `A ⟶ A[S]` of graded rings.
* `Stacks.PolynomialGrading.map`: the graded ring homomorphism `A[S] ⟶ B[S]` induced by a graded
  ring homomorphism `A ⟶ B`.

## Main results

* `Stacks.PolynomialGrading.monomial_mem_grading`: `a Sʲ` has degree `k + j` for `a ∈ A_k`.
* `Stacks.PolynomialGrading.X_mem_grading`: `S` has degree one.

## References

* [Stacks Project, Tag 0FBG](https://stacks.math.columbia.edu/tag/0FBG)
-/

@[expose] public noncomputable section

open Polynomial DirectSum

namespace Stacks.PolynomialGrading

variable {A : Type*} [CommRing A] {σ : Type*} [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- The degree-`n` piece of `A[S]`, with `S` in degree one: the polynomials whose coefficient of
`Sʲ` lies in `A_{n-j}` for `j ≤ n` and vanishes for `j > n`. -/
def grading (n : ℕ) : AddSubgroup A[X] where
  carrier := {p | ∀ j, (j ≤ n → p.coeff j ∈ 𝒜 (n - j)) ∧ (n < j → p.coeff j = 0)}
  add_mem' {p q} hp hq j :=
    ⟨fun h => by rw [coeff_add]; exact add_mem ((hp j).1 h) ((hq j).1 h),
      fun h => by rw [coeff_add, (hp j).2 h, (hq j).2 h, add_zero]⟩
  zero_mem' j := ⟨fun _ => by rw [coeff_zero]; exact zero_mem _, fun _ => coeff_zero j⟩
  neg_mem' {p} hp j :=
    ⟨fun h => by rw [coeff_neg]; exact neg_mem ((hp j).1 h),
      fun h => by rw [coeff_neg, (hp j).2 h, neg_zero]⟩

variable {𝒜}

omit [GradedRing 𝒜] in
theorem mem_grading {n : ℕ} {p : A[X]} :
    p ∈ grading 𝒜 n ↔ ∀ j, (j ≤ n → p.coeff j ∈ 𝒜 (n - j)) ∧ (n < j → p.coeff j = 0) :=
  Iff.rfl

omit [GradedRing 𝒜] in
/-- `a Sʲ` is homogeneous of degree `k + j` for `a ∈ A_k`. -/
theorem monomial_mem_grading {j k : ℕ} {a : A} (ha : a ∈ 𝒜 k) :
    monomial j a ∈ grading 𝒜 (k + j) := by
  intro m
  rw [coeff_monomial]
  refine ⟨fun hm => ?_, fun hm => ?_⟩
  · split_ifs with h
    · subst h
      rw [Nat.add_sub_cancel]
      exact ha
    · exact zero_mem _
  · exact ite_eq_right_iff.mpr fun h => by omega

omit [GradedRing 𝒜] in
/-- A constant of degree `k` is homogeneous of degree `k`. -/
theorem C_mem_grading {k : ℕ} {a : A} (ha : a ∈ 𝒜 k) : C a ∈ grading 𝒜 k := by
  rw [← monomial_zero_left]
  exact monomial_mem_grading (j := 0) ha

variable (𝒜) in
/-- The variable `S` is homogeneous of degree one. -/
theorem X_mem_grading : (X : A[X]) ∈ grading 𝒜 1 := by
  have h := monomial_mem_grading (j := 1) (SetLike.one_mem_graded 𝒜)
  rwa [monomial_one_one_eq_X, Nat.zero_add] at h

omit [GradedRing 𝒜] in
/-- A homogeneous polynomial of degree `n` has degree at most `n` in `S`. -/
theorem natDegree_le_of_mem_grading {n : ℕ} {p : A[X]} (hp : p ∈ grading 𝒜 n) :
    p.natDegree ≤ n :=
  natDegree_le_iff_coeff_eq_zero.2 fun N hN => (hp N).2 hN

variable (𝒜) in
instance gradedMonoid : SetLike.GradedMonoid (grading 𝒜) where
  one_mem := by
    rw [← C_1]
    exact C_mem_grading (SetLike.one_mem_graded 𝒜)
  mul_mem := fun i j p q hp hq k => by
    rw [coeff_mul]
    refine ⟨fun hk => ?_, fun hk => ?_⟩
    · refine sum_mem fun x hx => ?_
      rw [Finset.mem_antidiagonal] at hx
      by_cases h1 : x.1 ≤ i
      · by_cases h2 : x.2 ≤ j
        · have h := SetLike.mul_mem_graded ((hp x.1).1 h1) ((hq x.2).1 h2)
          have e : i - x.1 + (j - x.2) = i + j - k := by omega
          rwa [e] at h
        · rw [(hq x.2).2 (by omega), mul_zero]
          exact zero_mem _
      · rw [(hp x.1).2 (by omega), zero_mul]
        exact zero_mem _
    · refine Finset.sum_eq_zero fun x hx => ?_
      rw [Finset.mem_antidiagonal] at hx
      by_cases h1 : x.1 ≤ i
      · rw [(hq x.2).2 (by omega), mul_zero]
      · rw [(hp x.1).2 (by omega), zero_mul]

/-! ### The decomposition -/

variable (𝒜) in
/-- `a ↦ a Sʲ` from `A_k` to the degree-`(k + j)` piece of `A[S]`. -/
def monomialPiece (j k : ℕ) : 𝒜 k →+ grading 𝒜 (k + j) where
  toFun a := ⟨monomial j (a : A), monomial_mem_grading a.2⟩
  map_zero' := Subtype.ext (by simp)
  map_add' a b := Subtype.ext (by simp)

variable (𝒜) in
/-- `a ↦ a Sʲ`, decomposed into homogeneous pieces. -/
def coeffDecompose (j : ℕ) : A →+ ⨁ n, grading 𝒜 n :=
  (DirectSum.toAddMonoid fun k =>
      (DirectSum.of (fun n => grading 𝒜 n) (k + j)).comp (monomialPiece 𝒜 j k)).comp
    (DirectSum.decomposeAddEquiv 𝒜).toAddMonoidHom

variable (𝒜) in
/-- The decomposition of a polynomial into its homogeneous pieces. -/
def decomposeHom : A[X] →+ ⨁ n, grading 𝒜 n where
  toFun p := p.sum fun j a => coeffDecompose 𝒜 j a
  map_zero' := Polynomial.sum_zero_index _
  map_add' p q := Polynomial.sum_add_index p q _ (fun _ => map_zero _) (fun _ a b => map_add _ a b)

theorem decomposeHom_monomial (j : ℕ) (a : A) :
    decomposeHom 𝒜 (monomial j a) = coeffDecompose 𝒜 j a := by
  change (monomial j a).sum (fun j a => coeffDecompose 𝒜 j a) = _
  rw [Polynomial.sum_monomial_index]
  exact map_zero _

omit [GradedRing 𝒜] in
/-- Two inclusions of one homogeneous polynomial into the direct sum agree along an equality of
degrees. -/
theorem of_eq_of_eq {a b : ℕ} (h : a = b) (y : A[X]) (ha : y ∈ grading 𝒜 a)
    (hb : y ∈ grading 𝒜 b) :
    DirectSum.of (fun n => grading 𝒜 n) a ⟨y, ha⟩ =
      DirectSum.of (fun n => grading 𝒜 n) b ⟨y, hb⟩ := by
  subst h
  rfl

theorem coeffDecompose_of_mem {j k : ℕ} {a : A} (ha : a ∈ 𝒜 k) :
    coeffDecompose 𝒜 j a =
      DirectSum.of (fun n => grading 𝒜 n) (k + j) ⟨monomial j a, monomial_mem_grading ha⟩ := by
  rw [coeffDecompose, AddMonoidHom.comp_apply]
  change DirectSum.toAddMonoid _ (DirectSum.decompose 𝒜 a) = _
  rw [DirectSum.decompose_of_mem 𝒜 ha, DirectSum.toAddMonoid_of]
  rfl

theorem coe_comp_decomposeHom :
    (DirectSum.coeAddMonoidHom (grading 𝒜)).comp (decomposeHom 𝒜) = .id _ := by
  refine Polynomial.addHom_ext fun j a => ?_
  rw [AddMonoidHom.comp_apply, decomposeHom_monomial, AddMonoidHom.id_apply]
  have hcomp : (DirectSum.coeAddMonoidHom (grading 𝒜)).comp
      (DirectSum.toAddMonoid fun k =>
        (DirectSum.of (fun n => grading 𝒜 n) (k + j)).comp (monomialPiece 𝒜 j k)) =
      (monomial j).toAddMonoidHom.comp (DirectSum.coeAddMonoidHom 𝒜) := by
    refine DirectSum.addHom_ext fun k x => ?_
    simp [monomialPiece]
  have h := DFunLike.congr_fun hcomp (DirectSum.decompose 𝒜 a)
  simp only [AddMonoidHom.comp_apply] at h
  rw [coeffDecompose, AddMonoidHom.comp_apply]
  change DirectSum.coeAddMonoidHom (grading 𝒜) (DirectSum.toAddMonoid _
    (DirectSum.decompose 𝒜 a)) = _
  rw [h]
  change monomial j ((DirectSum.decompose 𝒜).symm (DirectSum.decompose 𝒜 a)) = _
  rw [Equiv.symm_apply_apply]

theorem decomposeHom_of_mem {n : ℕ} (p : grading 𝒜 n) :
    decomposeHom 𝒜 (p : A[X]) = DirectSum.of (fun n => grading 𝒜 n) n p := by
  have hdeg : (p : A[X]).natDegree < n + 1 := Nat.lt_succ_of_le (natDegree_le_of_mem_grading p.2)
  have hmem : ∀ j, monomial j ((p : A[X]).coeff j) ∈ grading 𝒜 n := fun j => by
    by_cases hjn : j ≤ n
    · have h := monomial_mem_grading (j := j) ((p.2 j).1 hjn)
      rwa [Nat.sub_add_cancel hjn] at h
    · rw [(p.2 j).2 (by omega), monomial_zero_right]
      exact zero_mem _
  have hterm : ∀ j ∈ Finset.range (n + 1),
      decomposeHom 𝒜 (monomial j ((p : A[X]).coeff j)) =
        DirectSum.of (fun n => grading 𝒜 n) n ⟨monomial j ((p : A[X]).coeff j), hmem j⟩ := by
    intro j hj
    have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    rw [decomposeHom_monomial, coeffDecompose_of_mem ((p.2 j).1 hjn)]
    exact of_eq_of_eq (Nat.sub_add_cancel hjn) _ _ _
  have hsum : (p : A[X]) = ∑ j ∈ Finset.range (n + 1), monomial j ((p : A[X]).coeff j) :=
    as_sum_range' (p : A[X]) (n + 1) hdeg
  conv_lhs => rw [hsum]
  rw [map_sum, Finset.sum_congr rfl hterm, ← map_sum]
  congr 1
  refine Subtype.ext ?_
  rw [AddSubmonoidClass.coe_finsetSum]
  exact hsum.symm

theorem decomposeHom_comp_coe :
    (decomposeHom 𝒜).comp (DirectSum.coeAddMonoidHom (grading 𝒜)) = .id _ := by
  refine DirectSum.addHom_ext fun n p => ?_
  rw [AddMonoidHom.comp_apply, DirectSum.coeAddMonoidHom_of, AddMonoidHom.id_apply]
  exact decomposeHom_of_mem p

variable (𝒜) in
/-- **`A[S]` is a graded ring**, with `S` in degree one. -/
instance instGradedRing : GradedRing (grading 𝒜) where
  __ := gradedMonoid 𝒜
  decompose' := decomposeHom 𝒜
  left_inv := DFunLike.congr_fun coe_comp_decomposeHom
  right_inv := DFunLike.congr_fun decomposeHom_comp_coe

/-! ### Graded ring homomorphisms -/

variable (𝒜) in
/-- The inclusion `A ⟶ A[S]` of constants, as a homomorphism of graded rings. -/
def includeC : 𝒜 →+*ᵍ grading 𝒜 where
  toRingHom := C
  map_mem hx := C_mem_grading hx

omit [GradedRing 𝒜] in
@[simp]
theorem includeC_apply (a : A) : includeC 𝒜 a = C a := rfl

variable {B : Type*} [CommRing B] {τ : Type*} [SetLike τ B] [AddSubgroupClass τ B]
  {ℬ : ℕ → τ} [GradedRing ℬ]

/-- The graded ring homomorphism `A[S] ⟶ B[S]` induced by `f : A ⟶ B` on coefficients, with
`S ↦ S`. -/
def map (f : 𝒜 →+*ᵍ ℬ) : grading 𝒜 →+*ᵍ grading ℬ where
  toRingHom := Polynomial.mapRingHom f.toRingHom
  map_mem {n p} hp j := by
    refine ⟨fun h => ?_, fun h => ?_⟩
    · change (p.map f.toRingHom).coeff j ∈ ℬ (n - j)
      rw [coeff_map]
      exact f.map_mem ((hp j).1 h)
    · change (p.map f.toRingHom).coeff j = 0
      rw [coeff_map, (hp j).2 h, map_zero]

omit [GradedRing 𝒜] [GradedRing ℬ] in
@[simp]
theorem map_apply (f : 𝒜 →+*ᵍ ℬ) (p : A[X]) : map f p = p.map f.toRingHom := rfl

end Stacks.PolynomialGrading

end
