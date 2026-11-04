module

public import Mathlib.Algebra.DirectSum.Decomposition
public import Mathlib.Algebra.DirectSum.Internal
public import Mathlib.LinearAlgebra.Pi
public import StacksFrontier.Algebra.GradedModule.ExternallyGradedAlgebraRing

/-!
# Computing in the total algebra of an externally graded algebra; finite products of gradings

Let `A` be an externally graded algebra over `R` and `⨁_n A^n` its total algebra
(`ExternallyGradedAlgebra.Total`, graded by `ExternallyGradedAlgebra.grade`). This file records
how homogeneous elements multiply and decompose in `⨁_n A^n` — products of summands, components
of homogeneous elements, transport of degrees — and shows that a finite product of graded
algebras is graded by the products of the pieces.

## Main definitions

* `GradedAlgebra.piGrade`: the grading `n ↦ ∏_c 𝒜_c^n` of a finite product of graded algebras;
  it is a grading (`GradedAlgebra.pi`).

## Main results

* `ExternallyGradedAlgebra.component_mul_of_mem`: the degree-`n` component of a product of
  homogeneous elements of degrees `i + j = n`.
* `ExternallyGradedAlgebra.mul_heq_mul`: the multiplication respects transport of degrees.
-/

@[expose] public noncomputable section

open DirectSum

universe u v w

namespace ExternallyGraded

variable {R : Type u} [CommRing R] {X : ℤ → Type v} [∀ n, AddCommGroup (X n)]
  [∀ n, Module R (X n)]

/-- Transporting along `i = j` and then along `j = l` is transporting along `i = l`. -/
@[simp]
theorem degreeCast_degreeCast {i j l : ℤ} (h : i = j) (h' : j = l) (x : X i) :
    degreeCast (R := R) (X := X) h' (degreeCast (R := R) (X := X) h x) =
      degreeCast (R := R) (X := X) (h.trans h') x := by
  subst h h'
  rfl

/-- Transporting along `i = i` is the identity. -/
@[simp]
theorem degreeCast_rfl {i : ℤ} (x : X i) : degreeCast (R := R) (X := X) (rfl : i = i) x = x :=
  rfl

end ExternallyGraded

namespace ExternallyGradedAlgebra

variable {R : Type u} [CommRing R] (A : ExternallyGradedAlgebra.{u, v} R)

/-- If `i = i'`, `j = j'`, `a ≍ a'` and `b ≍ b'`, then `a * b ≍ a' * b'`. -/
theorem mul_heq_mul {i i' j j' : ℤ} (hi : i = i') (hj : j = j') {a : A.piece i} {a' : A.piece i'}
    {b : A.piece j} {b' : A.piece j'} (ha : a ≍ a') (hb : b ≍ b') :
    A.mul i j a b ≍ A.mul i' j' a' b' := by
  subst hi hj
  cases ha
  cases hb
  rfl

/-- Transporting the right factor of a product to an equal degree does not change the product,
up to transport of its degree. -/
theorem mul_degreeCast_right_heq {i j j' : ℤ} (h : j = j') (x : A.piece i) (y : A.piece j) :
    A.mul i j' x (ExternallyGraded.degreeCast (R := R) (X := A.piece) h y) ≍ A.mul i j x y := by
  subst h
  rfl

/-- Transporting the left factor of a product to an equal degree does not change the product,
up to transport of its degree. -/
theorem mul_degreeCast_left_heq {i i' j : ℤ} (h : i = i') (x : A.piece i) (y : A.piece j) :
    A.mul i' j (ExternallyGraded.degreeCast (R := R) (X := A.piece) h x) y ≍ A.mul i j x y := by
  subst h
  rfl

/-- In `⨁_n A^n`, the product of `a ∈ A^i` and `b ∈ A^j` is `A.mul i j a b ∈ A^(i + j)`. -/
theorem lof_mul_lof (i j : ℤ) (a : A.piece i) (b : A.piece j) :
    lof R ℤ A.piece i a * lof R ℤ A.piece j b = lof R ℤ A.piece (i + j) (A.mul i j a b) := by
  simp only [lof_eq_of]
  exact A.of_mul_of a b

/-- Transporting `a ∈ A^i` to an equal degree `j` gives the same element of `⨁_n A^n`. -/
theorem lof_degreeCast {i j : ℤ} (h : i = j) (a : A.piece i) :
    lof R ℤ A.piece j (ExternallyGraded.degreeCast (R := R) (X := A.piece) h a) =
      lof R ℤ A.piece i a := by
  subst h
  rfl

/-- For `i = n`, the degree-`n` component of `a ∈ A^i` is `a` transported to degree `n`. -/
theorem component_lof_of_eq {i n : ℤ} (h : i = n) (a : A.piece i) :
    component R ℤ A.piece n (lof R ℤ A.piece i a) =
      ExternallyGraded.degreeCast (R := R) (X := A.piece) h a := by
  subst h
  exact component.lof_self R _ a

/-- For `i ≠ n`, the degree-`n` component of `a ∈ A^i` is zero. -/
theorem component_lof_of_ne {i n : ℤ} (h : i ≠ n) (a : A.piece i) :
    component R ℤ A.piece n (lof R ℤ A.piece i a) = 0 := by
  rw [component.of, dif_neg h]

/-- A homogeneous element of degree `n` of `⨁_n A^n` is its degree-`n` component. -/
theorem lof_component_of_mem {n : ℤ} {x : ⨁ n, A.piece n} (hx : x ∈ A.grade n) :
    lof R ℤ A.piece n (component R ℤ A.piece n x) = x := by
  obtain ⟨a, rfl⟩ := hx
  rw [component.lof_self]

/-- If `x` and `y` are homogeneous of degrees `i` and `j` with `i + j = n`, the degree-`n`
component of `x * y` is the product of the degree-`i` component of `x` and the degree-`j`
component of `y`, transported to degree `n`. -/
theorem component_mul_of_mem {i j n : ℤ} (h : i + j = n) {x y : ⨁ n, A.piece n}
    (hx : x ∈ A.grade i) (hy : y ∈ A.grade j) :
    component R ℤ A.piece n (x * y) = ExternallyGraded.degreeCast (R := R) (X := A.piece) h
      (A.mul i j (component R ℤ A.piece i x) (component R ℤ A.piece j y)) := by
  rw [← A.lof_component_of_mem hx, ← A.lof_component_of_mem hy, lof_mul_lof,
    component_lof_of_eq _ h, component.lof_self, component.lof_self]

end ExternallyGradedAlgebra

/-! ### Finite products of graded algebras -/

namespace GradedAlgebra

variable {R : Type u} [CommRing R] {ι : Type w} [Fintype ι] [DecidableEq ι]
  {S : ι → Type v} [∀ c, Ring (S c)] [∀ c, Algebra R (S c)]
  (𝒜 : ∀ c, ℤ → Submodule R (S c)) [∀ c, GradedAlgebra (𝒜 c)]

/-- The grading `n ↦ ∏_c 𝒜_c^n` of a finite product of graded algebras. -/
def piGrade (n : ℤ) : Submodule R (∀ c, S c) :=
  Submodule.pi Set.univ fun c ↦ 𝒜 c n

omit [Fintype ι] [DecidableEq ι] [(c : ι) → GradedAlgebra (𝒜 c)] in
/-- An element lies in `∏_c 𝒜_c^n` if and only if each of its coordinates `x c` lies in
`𝒜_c^n`. -/
theorem mem_piGrade {n : ℤ} {x : ∀ c, S c} : x ∈ piGrade 𝒜 n ↔ ∀ c, x c ∈ 𝒜 c n :=
  ⟨fun h c ↦ h c trivial, fun h c _ ↦ h c⟩

/-- `x ↦ Pi.single c x`, from `𝒜_c^n` to `∏_c 𝒜_c^n`. -/
def piGradeSingle (c : ι) (n : ℤ) : 𝒜 c n →ₗ[R] piGrade 𝒜 n :=
  ((LinearMap.single R S c).comp (𝒜 c n).subtype).codRestrict _ fun x ↦
    (mem_piGrade 𝒜).2 fun c' ↦ by
      by_cases h : c' = c
      · subst h; simp
      · simp [Pi.single_eq_of_ne h]

/-- The decomposition of a finite product of graded algebras into its pieces `∏_c 𝒜_c^n`. -/
def piDecompose : (∀ c, S c) →ₗ[R] ⨁ n, piGrade 𝒜 n :=
  ∑ c, (toModule R ℤ _ fun n ↦ lof R ℤ (fun n ↦ piGrade 𝒜 n) n ∘ₗ piGradeSingle 𝒜 c n) ∘ₗ
    (decomposeLinearEquiv (𝒜 c)).toLinearMap ∘ₗ LinearMap.proj c

omit [Fintype ι] [(c : ι) → GradedAlgebra (𝒜 c)] in
/-- Including `⨁_n 𝒜_c^n` into `⨁_n ∏_c 𝒜_c^n` through `piGradeSingle` and then summing
gives `Pi.single c` of the sum of `y`. -/
theorem coeLinearMap_toModule_piGradeSingle (c : ι) (y : ⨁ n, 𝒜 c n) :
    coeLinearMap (fun n ↦ piGrade 𝒜 n)
        (toModule R ℤ _ (fun n ↦ lof R ℤ (fun n ↦ piGrade 𝒜 n) n ∘ₗ piGradeSingle 𝒜 c n) y) =
      Pi.single c (coeLinearMap (𝒜 c) y) := by
  have h : (coeLinearMap fun n ↦ piGrade 𝒜 n) ∘ₗ
      (toModule R ℤ _ fun n ↦ lof R ℤ (fun n ↦ piGrade 𝒜 n) n ∘ₗ piGradeSingle 𝒜 c n) =
      LinearMap.single R S c ∘ₗ coeLinearMap (𝒜 c) := by
    refine linearMap_ext R fun n ↦ LinearMap.ext fun a ↦ ?_
    simp only [LinearMap.comp_apply, toModule_lof]
    simp only [lof_eq_of, coeLinearMap_of]
    rfl
  exact LinearMap.congr_fun h y

/-- The sum of the components of `piDecompose 𝒜 x` is `x`. -/
theorem coeLinearMap_piDecompose (x : ∀ c, S c) :
    coeLinearMap (fun n ↦ piGrade 𝒜 n) (piDecompose 𝒜 x) = x := by
  simp only [piDecompose, LinearMap.sum_apply, LinearMap.comp_apply, map_sum,
    coeLinearMap_toModule_piGradeSingle]
  conv_rhs => rw [← Finset.univ_sum_single x]
  refine Finset.sum_congr rfl fun c _ ↦ ?_
  congr 1
  exact Decomposition.left_inv (x c)

/-- The decomposition of an element `x ∈ ∏_c 𝒜_c^n` is `x` itself, placed in degree `n`. -/
theorem piDecompose_of_mem {n : ℤ} {x : ∀ c, S c} (hx : x ∈ piGrade 𝒜 n) :
    piDecompose 𝒜 x = lof R ℤ (fun n ↦ piGrade 𝒜 n) n ⟨x, hx⟩ := by
  have hc : ∀ c, decomposeLinearEquiv (𝒜 c) (x c) =
      lof R ℤ (fun n ↦ 𝒜 c n) n ⟨x c, (mem_piGrade 𝒜).1 hx c⟩ :=
    fun c ↦ by rw [decomposeLinearEquiv_apply, lof_eq_of]; exact decompose_of_mem _ _
  simp only [piDecompose, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.coe_proj,
    Function.eval, LinearEquiv.coe_coe, hc, toModule_lof, ← map_sum]
  congr 1
  refine Subtype.ext ?_
  simp only [piGradeSingle, Submodule.coe_sum, LinearMap.codRestrict_apply, LinearMap.comp_apply,
    Submodule.coe_subtype, LinearMap.coe_single]
  exact Finset.univ_sum_single x

/-- **A finite product of graded algebras is graded by the products of the pieces.** -/
instance pi : GradedRing (piGrade 𝒜) where
  one_mem := (mem_piGrade 𝒜).2 fun c ↦ SetLike.GradedOne.one_mem
  mul_mem := fun _ _ _ _ ha hb ↦ (mem_piGrade 𝒜).2 fun c ↦
    SetLike.GradedMul.mul_mem ((mem_piGrade 𝒜).1 ha c) ((mem_piGrade 𝒜).1 hb c)
  __ := Decomposition.ofLinearMap (piGrade 𝒜) (piDecompose 𝒜)
    (LinearMap.ext (coeLinearMap_piDecompose 𝒜))
    (linearMap_ext R fun n ↦ LinearMap.ext fun x ↦ by
      rw [LinearMap.comp_apply, LinearMap.comp_apply, lof_eq_of R ℤ (fun n ↦ piGrade 𝒜 n),
        coeLinearMap_of, piDecompose_of_mem 𝒜 x.2]
      rfl)

end GradedAlgebra

end
