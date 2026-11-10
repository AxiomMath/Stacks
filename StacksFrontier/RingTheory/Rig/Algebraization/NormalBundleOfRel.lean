module

public import StacksFrontier.RingTheory.Rig.Algebraization.NormalBundle

/-!
# Normal bundle data from a relation `σ ∘ d = aᶜ`

Let `B = A⟨x₁, …, x_N⟩ / J` be an object of the category of Stacks 0AL4 over `(A, (a))`, with
generators `f₁, …, f_m` of `J` and Jacobian matrix `Jac = (∂fₗ/∂xᵢ)`. Given a matrix `S` with

  `∑ₗ (S · Jac − aᶜ)ₗⱼ fₗ ∈ J²` for every `j`,

this file builds the data `Rig.NormalBundle.Data` of a completed normal bundle, with no further
input. Differentiating the relation (a derivation carries `J²` into `J`) shows that
`Jac · (S · Jac − aᶜ)` has entries in `J`, so `E₀ = (Jac · S)ᵀ` is a quasi-idempotent modulo `J`:
`Δ = E₀² − aᶜ E₀ ≡ 0`. The improved lift `Ẽ = a^{2c} E₀ − 2 E₀ Δ + aᶜ Δ` then satisfies
`Ẽ² − a^{3c} Ẽ ≡ 0` modulo `J²`.

The lift `Ẽ` is an explicit polynomial expression in `E₀` with coefficients powers of `aᶜ`
(`Rig.NormalBundle.improvedLift`), so if `f`, `S` and the Jacobian are images of polynomials, so is
`Ẽ` (`Rig.NormalBundle.improvedLift_map`).

## Main definitions

* `Rig.NormalBundle.improvedLift`: the matrix `u² E − 2 E (E² − u E) + u (E² − u E)`.
* `Rig.NormalBundle.Data.ofRel`: normal bundle data from generators and a relation
  `σ ∘ d = aᶜ` on `J / J²`.
-/

@[expose] public noncomputable section

open scoped Matrix

universe u v

namespace Rig

namespace NormalBundle

section ImprovedLift

variable {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n]

/-- The defect `E² − u E` of a matrix `E` from being a quasi-idempotent for `u`. -/
def quasiDefect (u : R) (E : Matrix n n R) : Matrix n n R := E * E - u • E

/-- **The improved lift** `u² E − 2 E Δ + u Δ` of a quasi-idempotent modulo an ideal, where
`Δ = E² − u E` is the defect. If `Δ ≡ 0` modulo `J`, then the improved lift is congruent to
`u² E` modulo `J` and is a quasi-idempotent for `u³` modulo `J²`. -/
def improvedLift (u : R) (E : Matrix n n R) : Matrix n n R :=
  u ^ 2 • E - 2 • (E * quasiDefect u E) + u • quasiDefect u E

omit [DecidableEq n] in
/-- The improved lift `improvedLift u E`, with the defect `quasiDefect u E = E² − u E` unfolded. -/
theorem improvedLift_eq (u : R) (E : Matrix n n R) :
    improvedLift u E = u ^ 2 • E - 2 • (E * (E * E - u • E)) + u • (E * E - u • E) := rfl

omit [DecidableEq n] in
/-- The improved lift commutes with ring homomorphisms applied entrywise. -/
theorem improvedLift_map {R' : Type*} [CommRing R'] (φ : R →+* R') (u : R) (E : Matrix n n R) :
    (improvedLift u E).map φ = improvedLift (φ u) (E.map φ) := by
  classical
  have hsmul : ∀ (r : R) (M : Matrix n n R), φ.mapMatrix (r • M) = φ r • φ.mapMatrix M :=
    fun r M ↦ Matrix.map_smul' _ _ _ (map_mul φ)
  change φ.mapMatrix (improvedLift u E) = improvedLift (φ u) (φ.mapMatrix E)
  simp only [improvedLift, quasiDefect, map_add, map_sub, map_nsmul, map_mul, hsmul, map_pow]

/-- The polynomial `X² − u X`, whose value at `E` is the defect `quasiDefect u E`. -/
def quasiDefectPoly (u : R) : Polynomial R := Polynomial.X ^ 2 - Polynomial.C u * Polynomial.X

/-- The polynomial `u² X − 2 X D + u D` with `D = X² − u X`, whose value at `E` is the improved
lift. -/
def improvedLiftPoly (u : R) : Polynomial R :=
  Polynomial.C u ^ 2 * Polynomial.X - 2 • (Polynomial.X * quasiDefectPoly u) +
    Polynomial.C u * quasiDefectPoly u

/-- Evaluating `C u * p` at a matrix `E` gives `u` times the value of `p` at `E`. -/
theorem aeval_C_mul (u : R) (E : Matrix n n R) (p : Polynomial R) :
    Polynomial.aeval E (Polynomial.C u * p) = u • Polynomial.aeval E p := by
  rw [map_mul, Polynomial.aeval_C, ← Algebra.smul_def]

/-- The value of `quasiDefectPoly u` at `E` is the defect `quasiDefect u E`. -/
theorem aeval_quasiDefectPoly (u : R) (E : Matrix n n R) :
    Polynomial.aeval E (quasiDefectPoly u) = quasiDefect u E := by
  rw [quasiDefectPoly, map_sub, map_pow, aeval_C_mul, Polynomial.aeval_X, pow_two, quasiDefect]

/-- The value of `improvedLiftPoly u` at `E` is the improved lift `improvedLift u E`. -/
theorem aeval_improvedLiftPoly (u : R) (E : Matrix n n R) :
    Polynomial.aeval E (improvedLiftPoly u) = improvedLift u E := by
  rw [improvedLiftPoly, map_add, map_sub, ← Polynomial.C_pow, aeval_C_mul, aeval_C_mul, map_nsmul,
    map_mul, Polynomial.aeval_X, aeval_quasiDefectPoly, improvedLift]

/-- The lift differs from `u² X` by a multiple of the defect polynomial. -/
theorem improvedLiftPoly_sub (u : R) :
    improvedLiftPoly u - Polynomial.C u ^ 2 * Polynomial.X =
      quasiDefectPoly u * (Polynomial.C u - 2 * Polynomial.X) := by
  simp only [improvedLiftPoly]; ring

/-- The defect of the lift for `u³` is divisible by the square of the defect polynomial:
`Ẽ² − u³ Ẽ = D² ((2X − u)² − 4u²)`. -/
theorem improvedLiftPoly_sq_sub (u : R) :
    improvedLiftPoly u ^ 2 - Polynomial.C u ^ 3 * improvedLiftPoly u =
      quasiDefectPoly u * (quasiDefectPoly u *
        ((2 * Polynomial.X - Polynomial.C u) ^ 2 - 4 * Polynomial.C u ^ 2)) := by
  simp only [improvedLiftPoly, quasiDefectPoly]; ring

/-- A product `M * N` has entries in `I` if `M` does. -/
private theorem mul_apply_mem {R : Type*} [CommRing R] {l m p : Type*} [Fintype m] {I : Ideal R}
    {M : Matrix l m R} (hM : ∀ i j, M i j ∈ I) (N : Matrix m p R) (i : l) (j : p) :
    (M * N) i j ∈ I :=
  Ideal.sum_mem _ fun k _ ↦ Ideal.mul_mem_right _ _ (hM i k)

omit [DecidableEq n] in
/-- If the defect of `E` has entries in `J`, then `improvedLift u E − u² E` has entries in
`J`. -/
theorem improvedLift_sub_mem {J : Ideal R} {E : Matrix n n R} {u : R}
    (hΔ : ∀ i j, quasiDefect u E i j ∈ J) (i j : n) :
    (improvedLift u E - u ^ 2 • E) i j ∈ J := by
  classical
  have hE : improvedLift u E - u ^ 2 • E =
      quasiDefect u E * Polynomial.aeval E (Polynomial.C u - 2 * Polynomial.X) := by
    rw [← aeval_quasiDefectPoly, ← map_mul, ← improvedLiftPoly_sub, map_sub,
      ← aeval_improvedLiftPoly, ← Polynomial.C_pow, aeval_C_mul, Polynomial.aeval_X]
  rw [hE]
  exact mul_apply_mem hΔ _ i j

omit [DecidableEq n] in
/-- If the defect of `E` for `u` has entries in `J`, then the defect of the improved lift for
`u³` has entries in `J²`. -/
theorem quasiDefect_improvedLift_mem {J : Ideal R} {E : Matrix n n R} {u : R}
    (hΔ : ∀ i j, quasiDefect u E i j ∈ J) (i j : n) :
    quasiDefect (u ^ 3) (improvedLift u E) i j ∈ J ^ 2 := by
  classical
  set ev := Polynomial.aeval (R := R) E
  have hE : quasiDefect (u ^ 3) (improvedLift u E) = quasiDefect u E * (quasiDefect u E *
      ev ((2 * Polynomial.X - Polynomial.C u) ^ 2 - 4 * Polynomial.C u ^ 2)) := by
    calc quasiDefect (u ^ 3) (improvedLift u E) =
          ev (improvedLiftPoly u ^ 2 - Polynomial.C (u ^ 3) * improvedLiftPoly u) := by
          rw [map_sub, aeval_C_mul, pow_two, map_mul, aeval_improvedLiftPoly, quasiDefect]
      _ = _ := by
          rw [Polynomial.C_pow, improvedLiftPoly_sq_sub, map_mul, map_mul, aeval_quasiDefectPoly]
  rw [hE, pow_two]
  exact Ideal.sum_mem _ fun k _ ↦ Ideal.mul_mem_mul (hΔ i k) (mul_apply_mem hΔ _ k j)

end ImprovedLift

variable {A : Type u} [CommRing A] [IsNoetherianRing A] {a : A}

section OfRel

variable (B : AdicFiniteTypeAlgebra.{u, v} A (Ideal.span {a}))
  (Pres : CompletedPolynomialPresentation (Ideal.span {a}) B)

/-- **Differentiating a relation.** If `∑ₗ rₗ fₗ ∈ J²` with all `fₗ ∈ J`, then
`∑ₗ rₗ ∂ₖfₗ ∈ J` for every formal partial derivative `∂ₖ`. -/
theorem sum_mul_jacobian_mem {m : ℕ} (f : Fin m → Pres.completedPolynomialRing)
    (hf : ∀ l, f l ∈ Pres.ideal) (r : Fin m → Pres.completedPolynomialRing)
    (hr : ∑ l, r l * f l ∈ Pres.ideal ^ 2) (k : Fin Pres.variableCount) :
    ∑ l, jacobian B Pres f k l * r l ∈ Pres.ideal := by
  set δ := (completedNaiveCotangentComplex B Pres).partialDeriv k
  have h := derivation_mem_of_mem_sq δ hr
  have hδ : δ (∑ l, r l * f l) = ∑ l, jacobian B Pres f k l * r l + ∑ l, f l * δ (r l) := by
    rw [map_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun l _ ↦ ?_
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, mul_comm (r l)]
    rfl
  rw [hδ] at h
  exact (Ideal.add_mem_iff_left _ (Ideal.sum_mem _ fun l _ ↦ Ideal.mul_mem_right _ _ (hf l))).1 h

variable {B Pres}

/-- **The quasi-idempotent modulo `J`.** If `∑ₗ (S · Jac − aᶜ)ₗⱼ fₗ ∈ J²` for every `j`, then
`E₀ = (Jac · S)ᵀ` satisfies `E₀² − aᶜ E₀ ≡ 0` modulo `J`. -/
theorem quasiDefect_jacobian_mul_mem {m : ℕ} {f : Fin m → Pres.completedPolynomialRing}
    (hf : Ideal.span (Set.range f) = Pres.ideal) {c : ℕ}
    {S : Matrix (Fin m) (Fin Pres.variableCount) Pres.completedPolynomialRing}
    (rel : ∀ j, ∑ l, ((S * jacobian B Pres f) l j -
      (1 : Matrix (Fin m) (Fin m) Pres.completedPolynomialRing) l j *
        algebraMap A Pres.completedPolynomialRing (a ^ c)) * f l ∈ Pres.ideal ^ 2)
    (i k : Fin Pres.variableCount) :
    quasiDefect (algebraMap A Pres.completedPolynomialRing (a ^ c))
      (jacobian B Pres f * S)ᵀ i k ∈ Pres.ideal := by
  set u := algebraMap A Pres.completedPolynomialRing (a ^ c)
  set Jac := jacobian B Pres f
  have hfJ : ∀ l, f l ∈ Pres.ideal := fun l ↦ hf ▸ Ideal.subset_span (Set.mem_range_self l)
  have hM : ∀ k j, (Jac * (S * Jac - u • (1 : Matrix (Fin m) (Fin m) _)) :
      Matrix (Fin Pres.variableCount) (Fin m) _) k j ∈ Pres.ideal := by
    intro k j
    have h := sum_mul_jacobian_mem B Pres f hfJ _ (rel j) k
    rw [Matrix.mul_apply]
    convert h using 3 with l
    rw [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, mul_comm u]
  have hE : quasiDefect u (Jac * S)ᵀ =
      ((Jac * (S * Jac - u • (1 : Matrix (Fin m) (Fin m) _))) * S)ᵀ := by
    rw [quasiDefect, ← Matrix.transpose_mul, ← Matrix.transpose_smul, ← Matrix.transpose_sub,
      Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, Matrix.sub_mul, Matrix.smul_mul,
      Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc]
  rw [hE, Matrix.transpose_apply]
  exact mul_apply_mem hM _ k i

variable (B Pres)

/-- **Normal bundle data from a relation.** Given generators `f` of `J`, an exponent `c` and a
matrix `S` with `∑ₗ (S · Jac − aᶜ)ₗⱼ fₗ ∈ J²` for every `j`, the data of a completed normal
bundle with exponent `3c`, matrix `a^{2c} S` and lift `Ẽ` the improved lift of
`E₀ = (Jac · S)ᵀ`. -/
def Data.ofRel {m : ℕ} (f : Fin m → Pres.completedPolynomialRing)
    (hf : Ideal.span (Set.range f) = Pres.ideal) (c : ℕ)
    (S : Matrix (Fin m) (Fin Pres.variableCount) Pres.completedPolynomialRing)
    (rel : ∀ j, ∑ l, ((S * jacobian B Pres f) l j -
      (1 : Matrix (Fin m) (Fin m) Pres.completedPolynomialRing) l j *
        algebraMap A Pres.completedPolynomialRing (a ^ c)) * f l ∈ Pres.ideal ^ 2) :
    Data B Pres where
  m := m
  f := f
  span_eq := hf
  c := 3 * c
  S := algebraMap A Pres.completedPolynomialRing (a ^ (2 * c)) • S
  Et := improvedLift (algebraMap A Pres.completedPolynomialRing (a ^ c)) (jacobian B Pres f * S)ᵀ
  rel j := by
    have hu2 : algebraMap A Pres.completedPolynomialRing (a ^ (2 * c)) =
        algebraMap A Pres.completedPolynomialRing (a ^ c) ^ 2 := by
      rw [pow_mul', map_pow]
    have hu3 : algebraMap A Pres.completedPolynomialRing (a ^ (3 * c)) =
        algebraMap A Pres.completedPolynomialRing (a ^ c) ^ 3 := by
      rw [pow_mul', map_pow]
    rw [hu2, hu3]
    convert Ideal.mul_mem_left _ (algebraMap A Pres.completedPolynomialRing (a ^ c) ^ 2)
      (rel j) using 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ ↦ ?_
    rw [Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul]
    ring
  lift i j := by
    have h := improvedLift_sub_mem (quasiDefect_jacobian_mul_mem hf rel) i j
    have hu2 : algebraMap A Pres.completedPolynomialRing (a ^ (2 * c)) =
        algebraMap A Pres.completedPolynomialRing (a ^ c) ^ 2 := by
      rw [pow_mul', map_pow]
    rwa [Matrix.sub_apply, Matrix.smul_apply, Matrix.transpose_apply, ← Matrix.smul_apply,
      ← Matrix.mul_smul, ← hu2] at h
  quasi i j := by
    have h := quasiDefect_improvedLift_mem (quasiDefect_jacobian_mul_mem hf rel) i j
    have hu3 : algebraMap A Pres.completedPolynomialRing (a ^ (3 * c)) =
        algebraMap A Pres.completedPolynomialRing (a ^ c) ^ 3 := by
      rw [pow_mul', map_pow]
    rwa [quasiDefect, ← hu3] at h

namespace Data

variable {m : ℕ} (f : Fin m → Pres.completedPolynomialRing)
  (hf : Ideal.span (Set.range f) = Pres.ideal) (c : ℕ)
  (S : Matrix (Fin m) (Fin Pres.variableCount) Pres.completedPolynomialRing)
  (rel : ∀ j, ∑ l, ((S * jacobian B Pres f) l j -
    (1 : Matrix (Fin m) (Fin m) Pres.completedPolynomialRing) l j *
      algebraMap A Pres.completedPolynomialRing (a ^ c)) * f l ∈ Pres.ideal ^ 2)

/-- The number of generators of the data `ofRel` is `m`. -/
@[simp] theorem ofRel_m : (ofRel B Pres f hf c S rel).m = m := rfl

/-- The generators of the data `ofRel` are `f`. -/
@[simp] theorem ofRel_f : (ofRel B Pres f hf c S rel).f = f := rfl

/-- The exponent of the data `ofRel` is `3c`. -/
@[simp] theorem ofRel_c : (ofRel B Pres f hf c S rel).c = 3 * c := rfl

/-- The matrix of the data `ofRel` is `a^{2c} S`. -/
@[simp] theorem ofRel_S :
    (ofRel B Pres f hf c S rel).S = algebraMap A Pres.completedPolynomialRing (a ^ (2 * c)) • S :=
  rfl

/-- The lift of the data `ofRel` is the improved lift of `E₀ = (Jac · S)ᵀ`. -/
theorem ofRel_Et :
    (ofRel B Pres f hf c S rel).Et =
      improvedLift (algebraMap A Pres.completedPolynomialRing (a ^ c)) (jacobian B Pres f * S)ᵀ :=
  rfl

/-- The lift of the data `ofRel`, as an explicit polynomial in `E₀ = (Jac · S)ᵀ` with
coefficients powers of `u = aᶜ`: `Ẽ = u² E₀ − 2 E₀ (E₀² − u E₀) + u (E₀² − u E₀)`. -/
theorem ofRel_Et_eq :
    (ofRel B Pres f hf c S rel).Et =
      let u := algebraMap A Pres.completedPolynomialRing (a ^ c)
      let E0 := (jacobian B Pres f * S)ᵀ
      u ^ 2 • E0 - 2 • (E0 * (E0 * E0 - u • E0)) + u • (E0 * E0 - u • E0) :=
  rfl

end Data

end OfRel

end NormalBundle

end Rig

end
