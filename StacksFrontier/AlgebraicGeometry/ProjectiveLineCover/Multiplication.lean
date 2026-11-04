module

public import StacksFrontier.AlgebraicGeometry.ProjModelStructureMap.ComparisonNatural
public import StacksFrontier.AlgebraicGeometry.ProjPolyChart.MapDomain
public import StacksFrontier.AlgebraicGeometry.ProjShared.MapDomain
public import StacksFrontier.AlgebraicGeometry.ProjectiveLineCover.UnitScaling
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceSections.HomogeneousRescale
public import StacksFrontier.AlgebraicGeometry.RelativeProjChain.PolynomialSurjection

/-!
# Multiplying a binary form by a linear form, on a chart of the projective line

A binary form `A(T) = a₀ Tⁿ + … + aₙ` of degree `n` and a linear form `p T + q` multiply to the
binary form `(p T + q) A(T)` of degree `n + 1`, whose coefficients are `c_k = p a_k + q a_{k-1}`
(with `a_{-1} = a_{n+1} = 0`). Over a ring `B` with `p = 1` or `q = 1` these coefficients never
vanish simultaneously when the `a_k` do not, so the substitution `c_k ↦ p a_k + q a_{k-1}`
induces a morphism `ℙⁿ_B ⟶ ℙⁿ⁺¹_ℤ`. On the chart `x ≠ 0` of the projective line the linear form
is `(p, q) = (1, t)` with `t = y / x`, and on the chart `y ≠ 0` it is `(σ, 1)` with `σ = x / y`. The
two resulting morphisms agree over a ring in which `t σ = 1`, and so glue to the multiplication
morphism `ℙ¹ × ℙⁿ ⟶ ℙⁿ⁺¹`.

## Main definitions

* `Stacks.ProjectiveLineCover.mulForm`: the linear form `p a_k + q a_{k-1}`.
* `Stacks.ProjectiveLineCover.mulHom`: the graded ring homomorphism
  `ℤ[c₀, …, c_{n+1}] → B[a₀, …, aₙ]`, `c_k ↦ p a_k + q a_{k-1}`.
* `Stacks.ProjectiveLineCover.mulMapX`, `Stacks.ProjectiveLineCover.mulMapY`: the induced
  morphisms `Proj B[a₀, …, aₙ] ⟶ Proj ℤ[c₀, …, c_{n+1}]` for `(p, q) = (1, t)` and `(σ, 1)`.

## Main results

* `Stacks.ProjectiveLineCover.polyGradedMap_comp_mulHom`: the construction is natural in the
  coefficient ring.
* `Stacks.ProjectiveLineCover.projModelMap_comp_mulMapX_eq`: over a ring in which `t σ = 1` the
  two morphisms agree.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry MvPolynomial
open Stacks.ProjectiveCohomology

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

namespace Stacks.ProjectiveLineCover

variable {B : Type u} [CommRing B] (n : ℕ)

/-- The `m`-th variable of `B[a₀, …, aₙ]`, read as zero when `m > n`. -/
def var (m : ℕ) : MvPolynomial (Fin (n + 1)) B :=
  if h : m < n + 1 then X ⟨m, h⟩ else 0

/-- The `m`-th variable `var n m` is homogeneous of degree `1`. -/
theorem var_mem (m : ℕ) : var (B := B) n m ∈ homogeneousSubmodule (Fin (n + 1)) B 1 := by
  unfold var
  split_ifs
  · exact (mem_homogeneousSubmodule _ _).2 (isHomogeneous_X _ _)
  · exact zero_mem _

/-- A constant `C r` is homogeneous of degree `0`. -/
private theorem C_mem_homogeneousSubmodule_zero {σ : Type*} (r : B) :
    (C r : MvPolynomial σ B) ∈ homogeneousSubmodule σ B 0 :=
  (mem_homogeneousSubmodule _ _).2 (isHomogeneous_C _ _)

/-- **The coefficient `c_k = p a_k + q a_{k-1}` of `(p T + q) (a₀ Tⁿ + … + aₙ)`.** -/
def mulForm (p q : B) (k : Fin (n + 2)) : MvPolynomial (Fin (n + 1)) B :=
  C p * var n k + C q * (if (k : ℕ) = 0 then 0 else var n ((k : ℕ) - 1))

/-- The linear form `mulForm n p q k` is homogeneous of degree `1`. -/
theorem mulForm_mem (p q : B) (k : Fin (n + 2)) :
    mulForm n p q k ∈ homogeneousSubmodule (Fin (n + 1)) B 1 := by
  refine add_mem ?_ ?_
  · simpa using SetLike.mul_mem_graded (C_mem_homogeneousSubmodule_zero p) (var_mem n k)
  · split_ifs
    · simp
    · simpa using SetLike.mul_mem_graded (C_mem_homogeneousSubmodule_zero q) (var_mem n _)

/-- **The substitution `c_k ↦ p a_k + q a_{k-1}`**, as a graded ring homomorphism
`ℤ[c₀, …, c_{n+1}] → B[a₀, …, aₙ]`. -/
def mulHom (p q : B) : polyGrading (ULift.{u} ℤ) (n + 1) →+*ᵍ polyGrading B n :=
  letI : Algebra (ULift.{u} ℤ) (MvPolynomial (Fin (n + 1)) B) :=
    ((C : B →+* MvPolynomial (Fin (n + 1)) B).comp (fromULiftInt B)).toAlgebra
  Stacks.AlgebraicGeometry.RelativeProjChain.polyGradedHom (R := ULift.{u} ℤ) (polyGrading B n)
    (fun _ => (mem_homogeneousSubmodule _ _).2 (isHomogeneous_C _ _)) (mulForm n p q)
    (mulForm_mem n p q)

/-- `mulHom n p q` sends the variable `c_k` to `mulForm n p q k`. -/
@[simp] theorem mulHom_X (p q : B) (k : Fin (n + 2)) :
    mulHom n p q (X k) = mulForm n p q k := by
  simp [mulHom, Stacks.AlgebraicGeometry.RelativeProjChain.polyGradedHom]

/-- `mulHom n p q` sends a constant `r` to the constant `C r` of `B[a₀, …, aₙ]`. -/
@[simp] theorem mulHom_C (p q : B) (r : ULift.{u} ℤ) :
    mulHom n p q (C r) = C (fromULiftInt B r) := by
  simp [mulHom, Stacks.AlgebraicGeometry.RelativeProjChain.polyGradedHom,
    RingHom.algebraMap_toAlgebra]

/-- **The substitution is natural in the coefficient ring.** -/
theorem polyGradedMap_comp_mulHom {S : Type u} [CommRing S] (f : B →+* S) (p q : B) :
    (polyGradedMap (Fin (n + 1)) f).comp (mulHom n p q) = mulHom n (f p) (f q) := by
  have h : ((polyGradedMap (Fin (n + 1)) f).comp (mulHom n p q) :
      MvPolynomial (Fin (n + 2)) (ULift.{u} ℤ) →+* MvPolynomial (Fin (n + 1)) S) =
      (mulHom n (f p) (f q) :
        MvPolynomial (Fin (n + 2)) (ULift.{u} ℤ) →+* MvPolynomial (Fin (n + 1)) S) := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun k => ?_)
    · change MvPolynomial.map f (mulHom n p q (C r)) = mulHom n (f p) (f q) (C r)
      rw [mulHom_C, mulHom_C, map_C, ← RingHom.comp_apply f, comp_fromULiftInt]
    · change MvPolynomial.map f (mulHom n p q (X k)) = mulHom n (f p) (f q) (X k)
      rw [mulHom_X, mulHom_X]
      simp only [mulForm, var, map_add, map_mul, map_C]
      split_ifs <;> simp
  exact GradedRingHom.ext fun x => congrArg (fun φ => φ x) h

private theorem mulForm_succ (p q : B) (m : ℕ) (h : m + 1 < n + 2) :
    mulForm n p q ⟨m + 1, h⟩ = C p * var n (m + 1) + C q * var n m := by
  simp [mulForm]

variable {n} in
/-- The variables lie in any ideal containing the forms `a_k + t a_{k-1}`. -/
theorem var_mem_of_mulForm_one_left (t : B) {J : Ideal (MvPolynomial (Fin (n + 1)) B)}
    (hJ : ∀ k, mulForm n 1 t k ∈ J) (m : ℕ) : var n m ∈ J := by
  induction m with
  | zero => simpa [mulForm] using hJ ⟨0, by omega⟩
  | succ m ih =>
    by_cases hm : m + 1 < n + 1
    · have h := hJ ⟨m + 1, by omega⟩
      rw [mulForm_succ, map_one, one_mul] at h
      simpa using J.sub_mem h (J.mul_mem_left (C t) ih)
    · simp [var, hm]

variable {n} in
/-- The variables lie in any ideal containing the forms `σ a_k + a_{k-1}`. -/
theorem var_mem_of_mulForm_one_right (σ : B) {J : Ideal (MvPolynomial (Fin (n + 1)) B)}
    (hJ : ∀ k, mulForm n σ 1 k ∈ J) : ∀ (j m : ℕ), m + j = n + 1 → var n m ∈ J := by
  intro j
  induction j with
  | zero => intro m hm; simp [var, show ¬ m < n + 1 by omega]
  | succ j ih =>
    intro m hm
    have h := hJ ⟨m + 1, by omega⟩
    rw [mulForm_succ, map_one] at h
    simpa using J.sub_mem h (J.mul_mem_left (C σ) (ih (m + 1) (by omega)))

/-- The ideal of `B[a₀, …, aₙ]` spanned by the images under `mulHom n p q` of the
positive-degree elements of `ℤ[c₀, …, c_{n+1}]`. -/
private abbrev imageSpan (p q : B) : Ideal (MvPolynomial (Fin (n + 1)) B) :=
  Ideal.span ((mulHom n p q) '' ⋃ d > 0,
    (polyGrading (ULift.{u} ℤ) (n + 1) d : Set (MvPolynomial (Fin (n + 2)) (ULift.{u} ℤ))))

private theorem mulForm_mem_imageSpan (p q : B) (k : Fin (n + 2)) :
    mulForm n p q k ∈ imageSpan n p q := by
  refine Ideal.subset_span ⟨X k, Set.mem_iUnion₂.2 ⟨1, Nat.one_pos, ?_⟩, mulHom_X n p q k⟩
  exact (mem_homogeneousSubmodule _ _).2 (isHomogeneous_X _ _)

private theorem irrelevant_le_of_var_mem (p q : B) (h : ∀ m, var n m ∈ imageSpan n p q) :
    HomogeneousIdeal.irrelevant (polyGrading B n) ≤
      HomogeneousIdeal.map (mulHom n p q) (HomogeneousIdeal.irrelevant _) := by
  refine Stacks.AlgebraicGeometry.ProjShared.irrelevant_le_map_of_mem_span _ _ _ ?_
  intro d hd g hg
  have hspan := Stacks.AlgebraicGeometry.ProjPolyChart.homogeneous_mem_span_X B n hd hg
  refine (Ideal.span_le.2 ?_) hspan
  rintro _ ⟨i, rfl⟩
  simpa [var, i.2] using h i

/-- On the chart `x ≠ 0`: the images of the `c_k` generate the irrelevant ideal. -/
theorem irrelevant_le_map_mulHom_one_left (t : B) :
    HomogeneousIdeal.irrelevant (polyGrading B n) ≤
      HomogeneousIdeal.map (mulHom n 1 t) (HomogeneousIdeal.irrelevant _) :=
  irrelevant_le_of_var_mem n 1 t
    (var_mem_of_mulForm_one_left t (mulForm_mem_imageSpan n 1 t))

/-- On the chart `y ≠ 0`: the images of the `c_k` generate the irrelevant ideal. -/
theorem irrelevant_le_map_mulHom_one_right (σ : B) :
    HomogeneousIdeal.irrelevant (polyGrading B n) ≤
      HomogeneousIdeal.map (mulHom n σ 1) (HomogeneousIdeal.irrelevant _) :=
  irrelevant_le_of_var_mem n σ 1 fun m => by
    by_cases hm : m < n + 1
    · exact var_mem_of_mulForm_one_right σ (mulForm_mem_imageSpan n σ 1) (n + 1 - m) m
        (by omega)
    · simp [var, hm]

/-- **Multiplication by `T + t`**: the morphism `ℙⁿ_B ⟶ ℙⁿ⁺¹_ℤ` sending a binary form `A` to
`(T + t) A`. -/
def mulMapX (t : B) :
    AlgebraicGeometry.Proj (polyGrading B n) ⟶
      AlgebraicGeometry.Proj (polyGrading (ULift.{u} ℤ) (n + 1)) :=
  Proj.map (mulHom n 1 t) (irrelevant_le_map_mulHom_one_left n t)

/-- **Multiplication by `σ T + 1`**: the morphism `ℙⁿ_B ⟶ ℙⁿ⁺¹_ℤ` sending a binary form `A` to
`(σ T + 1) A`. -/
def mulMapY (σ : B) :
    AlgebraicGeometry.Proj (polyGrading B n) ⟶
      AlgebraicGeometry.Proj (polyGrading (ULift.{u} ℤ) (n + 1)) :=
  Proj.map (mulHom n σ 1) (irrelevant_le_map_mulHom_one_right n σ)

/-- **The two charts agree on the overlap.** Over a ring `D` receiving `t` and `σ` with
`t σ = 1`, the forms `σ a_k + a_{k-1}` are `σ` times the forms `a_k + t a_{k-1}`, so the two
substitutions induce the same morphism to `ℙⁿ⁺¹_ℤ`. -/
theorem projModelMap_comp_mulMapX_eq {Bx By D : Type u} [CommRing Bx] [CommRing By] [CommRing D]
    (t : Bx) (σ : By) (ix : Bx →+* D) (iy : By →+* D) (h : ix t * iy σ = 1) :
    projModelMap n ix ≫ mulMapX n t = projModelMap n iy ≫ mulMapY n σ := by
  rw [projModelMap, projModelMap, mulMapX, mulMapY, ← Proj.map_comp, ← Proj.map_comp]
  rw [Proj_map_congr _ _ _ (by rw [map_one]; exact irrelevant_le_map_mulHom_one_left n (ix t))
      (polyGradedMap_comp_mulHom n ix 1 t),
    Proj_map_congr _ _ _ (by rw [map_one]; exact irrelevant_le_map_mulHom_one_right n (iy σ))
      (polyGradedMap_comp_mulHom n iy σ 1)]
  refine Proj.map_eq_of_eq_mul_pow _ _ _ _ (C (iy σ))
    (C_mem_homogeneousSubmodule_zero _) fun d a ha => ?_
  have hform : mulForm n (iy σ) (iy 1) = fun k => C (iy σ) * mulForm n (ix 1) (ix t) k := by
    funext k
    simp only [mulForm, map_one, mul_add, ← mul_assoc, ← map_mul, mul_comm (iy σ) (ix t), h,
      map_one, one_mul]
  have key := ((mem_homogeneousSubmodule d a).1 ha).eval₂Hom_const_mul
    ((C : D →+* MvPolynomial (Fin (n + 1)) D).comp (fromULiftInt D)) (mulForm n (ix 1) (ix t))
    (C (iy σ))
  have hφ (p q : D) (b : MvPolynomial (Fin (n + 2)) (ULift.{u} ℤ)) : mulHom n p q b =
      MvPolynomial.eval₂Hom ((C : D →+* MvPolynomial (Fin (n + 1)) D).comp (fromULiftInt D))
        (mulForm n p q) b := rfl
  rw [hφ, hφ, hform, key, mul_comm]

end Stacks.ProjectiveLineCover
