module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.LinearAlgebra.Matrix.Adjugate

/-!
# The determinant kills the two-term complex of a square matrix

Let `R` be a commutative ring and `A` a square matrix over `R`, with rows and columns indexed by
a finite type `m` with decidable equality. Let `K` be the two-term cochain complex
`R^m --A--> R^m` placed in cohomological degrees `-1` and `0`. Multiplication
by `det(A)` on `K` is null-homotopic, with homotopy given by the adjugate of `A`, by the
identities `adj(A) A = A adj(A) = det(A) • 1`. Hence `det(A) : K → K` is the zero morphism in
the derived category `D(R)`.

## Main definitions

* `Matrix.twoTermComplex`: The complex `K = (R^m --A--> R^m)` in degrees `-1` and `0`.
* `Matrix.detSmul`: Multiplication by `det(A)` as an endomorphism of `K`.
* `Matrix.detSmulHomotopy`: The null-homotopy of `det(A) • id : K → K` given by the adjugate
  of `A`.

## Main results

* `Matrix.Q_map_detSmul_eq_zero`: The morphism `det(A) : K → K` is zero in `D(R)`.

## References

* [Stacks, Tag 0G9L]
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory Matrix

noncomputable section

universe u

namespace Matrix

variable {R : Type u} [CommRing R] {m : Type u}

/-- The underlying object in cohomological degree `i` of the complex `K`: it is the free module
`R^m` in degrees `-1` and `0`, and the zero object elsewhere. Here `R^m` is the module of
functions `m → R`. -/
def twoTermX (i : ℤ) : ModuleCat R :=
  if i = -1 ∨ i = 0 then ModuleCat.of R (m → R) else ModuleCat.of R PUnit

/-- In cohomological degree `-1` the complex `K` is the free module `R^m`. -/
@[simp] lemma twoTermX_neg_one :
    twoTermX (R := R) (m := m) (-1) = ModuleCat.of R (m → R) := by
  simp [twoTermX]

/-- In cohomological degree `0` the complex `K` is the free module `R^m`. -/
@[simp] lemma twoTermX_zero :
    twoTermX (R := R) (m := m) 0 = ModuleCat.of R (m → R) := by
  simp [twoTermX]

/-- Outside cohomological degrees `-1` and `0` the complex `K` is the zero module. -/
lemma twoTermX_of_ne {i : ℤ} (hi1 : i ≠ -1) (hi0 : i ≠ 0) :
    twoTermX (R := R) (m := m) i = ModuleCat.of R PUnit := by
  simp [twoTermX, hi1, hi0]

variable [Fintype m] (A : Matrix m m R)

/-- The differential `K^i → K^{i+1}`: it is the matrix `A` (acting on column vectors via
`Matrix.mulVecLin`) for the single nonzero differential `d^{-1} : K^{-1} → K^0`, and zero in all
other degrees. -/
def twoTermD (i : ℤ) : twoTermX (R := R) (m := m) i ⟶ twoTermX (R := R) (m := m) (i + 1) :=
  if h : i = -1 then by
    subst h
    simp only [twoTermX, ite_eq_left,
      show (((-1 : ℤ) + 1) = -1 ∨ ((-1 : ℤ) + 1) = 0) from Or.inr (by ring)]
    exact ModuleCat.ofHom A.mulVecLin
  else 0

/-- The differential `K^i → K^{i+1}` vanishes for `i ≠ -1`. -/
lemma twoTermD_eq_zero {i : ℤ} (h : i ≠ -1) : twoTermD A i = 0 := by simp [twoTermD, h]

/-- Consecutive differentials of `K` compose to zero. -/
lemma twoTermD_comp_twoTermD (i : ℤ) : twoTermD A i ≫ twoTermD A (i + 1) = 0 := by
  by_cases h : i = -1
  · subst h
    rw [twoTermD_eq_zero A (by decide : (-1 : ℤ) + 1 ≠ -1), Limits.comp_zero]
  · rw [twoTermD_eq_zero A h, Limits.zero_comp]

/-- The object `K`: the two-term cochain complex `R^m --A--> R^m` placed in cohomological degrees
`-1` and `0`, viewed as a complex of `R`-modules. -/
def twoTermComplex : CochainComplex (ModuleCat R) ℤ :=
  CochainComplex.of (twoTermX (R := R) (m := m)) (twoTermD A) (twoTermD_comp_twoTermD A)

/-- The object of `K` in cohomological degree `i` is `twoTermX i`. -/
lemma twoTermComplex_X (i : ℤ) : (twoTermComplex A).X i = twoTermX (R := R) (m := m) i := rfl

/-- The single nonzero differential `d^{-1} : K^{-1} → K^0` is the matrix `A`. -/
lemma twoTermComplex_d_neg_one :
    (twoTermComplex A).d (-1) 0 = ModuleCat.ofHom A.mulVecLin := by
  change (twoTermComplex A).d (-1) (-1 + 1) = _
  simp only [twoTermComplex, CochainComplex.of_d]
  rfl

/-- The differential of `K` out of degree `i ≠ -1` is zero. -/
lemma twoTermComplex_d_eq_zero {i : ℤ} (h : i ≠ -1) (j : ℤ) : (twoTermComplex A).d i j = 0 := by
  by_cases hj : (ComplexShape.up ℤ).Rel i j
  · obtain rfl : i + 1 = j := hj
    simp only [twoTermComplex, CochainComplex.of_d]
    rw [twoTermD_eq_zero A h]
  · exact (twoTermComplex A).shape i j hj

variable [DecidableEq m]

/-- If `N * M` is the scalar matrix `c • 1`, the composite of the maps of `R`-modules induced by
`M` and then by `N` is `c • 𝟙`. -/
lemma ofHom_mulVecLin_comp_of_mul_eq_smul_one {M N : Matrix m m R} {c : R} (h : N * M = c • 1) :
    ModuleCat.ofHom M.mulVecLin ≫ ModuleCat.ofHom N.mulVecLin
      = c • 𝟙 (ModuleCat.of R (m → R)) := by
  have hlin : (c • (1 : Matrix m m R)).mulVecLin
      = c • (LinearMap.id : (m → R) →ₗ[R] (m → R)) := by
    apply LinearMap.ext
    intro v
    funext i
    simp
  rw [← ModuleCat.ofHom_comp, ← Matrix.mulVecLin_mul, h, hlin]
  ext v
  simp

/-- Multiplication by the scalar `det(A)` as a morphism `K → K`: this is the chain map that is
`det(A) • id` in every degree, using the `R`-linear structure on the category of cochain complexes
of `R`-modules. -/
def detSmul : twoTermComplex A ⟶ twoTermComplex A := A.det • 𝟙 (twoTermComplex A)

/-- In each degree `i`, the component of `detSmul A` is `det(A) • 𝟙`. -/
lemma detSmul_f (i : ℤ) : (detSmul A).f i = A.det • 𝟙 ((twoTermComplex A).X i) := by
  simp [detSmul]

/-- The family of maps `K^i → K^j` equal to the adjugate of `A` for `(i, j) = (0, -1)` and
zero otherwise. -/
def adjugateHom (i j : ℤ) : (twoTermComplex A).X i ⟶ (twoTermComplex A).X j :=
  if hi : i = 0 then
    if hj : j = -1 then by
      subst hi hj
      exact ModuleCat.ofHom (adjugate A).mulVecLin
    else 0
  else 0

/-- The map `adjugateHom A i j` vanishes unless `(i, j) = (0, -1)`. -/
lemma adjugateHom_eq_zero {i j : ℤ} (h : ¬(i = 0 ∧ j = -1)) : adjugateHom A i j = 0 := by
  unfold adjugateHom
  by_cases hi : i = 0
  · by_cases hj : j = -1
    · exact absurd ⟨hi, hj⟩ h
    · simp [hi, hj]
  · simp [hi]

/-- The map `adjugateHom A 0 (-1)` is the adjugate of `A`. -/
lemma adjugateHom_zero_neg_one :
    adjugateHom A 0 (-1) = ModuleCat.ofHom (adjugate A).mulVecLin := by
  unfold adjugateHom
  rfl

/-- The null-homotopy of the chain map `det(A) • id : K → K` given by the adjugate of `A`. -/
def detSmulHomotopy : Homotopy (detSmul A) 0 where
  hom := adjugateHom A
  zero i j h := adjugateHom_eq_zero A (by rintro ⟨rfl, rfl⟩; exact h rfl)
  comm i := by
    rw [detSmul_f,
      show HomologicalComplex.Hom.f (0 : twoTermComplex A ⟶ twoTermComplex A) i = 0 from rfl,
      add_zero, dNext_eq (adjugateHom A) (show (ComplexShape.up ℤ).Rel i (i+1) from rfl),
      prevD_eq (adjugateHom A) (show (ComplexShape.up ℤ).Rel (i-1) i from sub_add_cancel i 1)]
    by_cases hi1 : i = -1
    · subst hi1
      rw [adjugateHom_eq_zero A (i := -1) (by rintro ⟨h, _⟩; exact absurd h (by decide)),
        Limits.zero_comp, add_zero,
        show adjugateHom A (-1 + 1) (-1) = adjugateHom A 0 (-1) from rfl,
        adjugateHom_zero_neg_one,
        show (twoTermComplex A).d (-1) (-1 + 1) = (twoTermComplex A).d (-1) 0 from rfl,
        twoTermComplex_d_neg_one A,
        ofHom_mulVecLin_comp_of_mul_eq_smul_one (adjugate_mul A)]
      rfl
    by_cases hi0 : i = 0
    · subst hi0
      rw [adjugateHom_eq_zero A (by rintro ⟨h, _⟩; exact absurd h (by decide)), Limits.comp_zero,
        zero_add, show adjugateHom A 0 (0 - 1) = adjugateHom A 0 (-1) from rfl,
        adjugateHom_zero_neg_one,
        show (twoTermComplex A).d (0 - 1) 0 = (twoTermComplex A).d (-1) 0 from rfl,
        twoTermComplex_d_neg_one A,
        ofHom_mulVecLin_comp_of_mul_eq_smul_one (mul_adjugate A)]
      rfl
    rw [twoTermComplex_d_eq_zero A hi1, Limits.zero_comp, zero_add,
      adjugateHom_eq_zero A (by rintro ⟨h, _⟩; exact hi0 h), Limits.zero_comp]
    have hX : ((twoTermComplex A).X i : Type u) = PUnit := by
      rw [twoTermComplex_X, twoTermX_of_ne hi1 hi0]
    have : Subsingleton ((twoTermComplex A).X i : Type u) := hX ▸ inferInstance
    ext x
    exact Subsingleton.elim _ _

attribute [local instance] HasDerivedCategory.standard

/-- **Stacks 0G9L**.
The morphism `det(A) : K → K` is the zero morphism in the derived category `D(R)`. -/
@[stacks 0G9L]
theorem Q_map_detSmul_eq_zero :
    (DerivedCategory.Q (C := ModuleCat R)).map (detSmul A) = 0 := by
  rw [DerivedCategory.Q_map_eq_of_homotopy _ (detSmulHomotopy A)]
  simp

end Matrix

end
