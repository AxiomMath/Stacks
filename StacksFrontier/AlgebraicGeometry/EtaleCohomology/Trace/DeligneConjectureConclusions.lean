module

public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Analysis.Complex.Basic

/-!
# The conclusions of Deligne's conjecture, and the contragredient

Let `X` be a normal variety over a finite field of characteristic `p` and let
`ρ : π₁(X, x̄) → GL_r(ℚ_ℓ)` be a continuous representation.  The conjecture of Deligne stated
just before [Tag 03VH](https://stacks.math.columbia.edu/tag/03VH) concludes:

1. there is a number field `E` such that for every closed point `x` the characteristic
   polynomial of `ρ(F_x)` has coefficients in `E`;
2. for every closed point `x` the eigenvalues of `ρ(F_x)` have complex absolute value `1`;
3. for every finite place `λ` of `E` not dividing `p` (maybe after enlarging `E`) there is a
   continuous `ρ_λ : π₁(X, x̄) → GL_r(E_λ)` compatible with `ρ`: the characteristic polynomials
   of the Frobenii agree.

The theorem of Deligne is about representations `ρ` satisfying these conclusions.  Its final
assertion, purity for smooth projective `X`, is proved by applying the weight bound to the
contragredient representation `ρ^∨ = (ρᵀ)⁻¹`, which carries the dual sheaf; this file records
the conclusions as a predicate and proves that they pass to `ρ^∨`.

## Main definitions

* `Stacks.EtaleCohomology.dualCharpoly`: for a polynomial `P` with nonzero constant term, the
  polynomial `P(0)⁻¹ · Xⁿ P(1 / X)`, which is the characteristic polynomial of `A⁻¹` when `P`
  is that of `A`.
* `Stacks.EtaleCohomology.contragredient`: the contragredient `g ↦ ((ρ g)⁻¹)ᵀ` of a matrix
  representation.
* `Stacks.EtaleCohomology.HasDeligneConclusions`: the three conclusions of the conjecture, for
  a representation `ρ` of a group `G` with Frobenius elements `Fr : P → G` indexed by the closed
  points, the eigenvalues read in `ℂ` along `ι`.

## Main results

* `Stacks.EtaleCohomology.charpoly_contragredient`: the characteristic polynomial of `ρ^∨(g)` is
  `dualCharpoly` of that of `ρ(g)`.
* `Stacks.EtaleCohomology.dualCharpoly_map`: `dualCharpoly` commutes with field homomorphisms.
* `Stacks.EtaleCohomology.HasDeligneConclusions.contragredient`: the conclusions of the
  conjecture pass from `ρ` to `ρ^∨`.

## Implementation notes

The closed points and their Frobenius elements are a family `Fr : P → G`; in the source
`G = π₁(X, x̄)` and `Fr x` is a Frobenius element at `x`, well defined up to conjugacy, which
changes no characteristic polynomial.  The number field `E` is a subfield of the coefficient
field `K` (in the source `ℚ_ℓ`); the eigenvalues, algebraic over `E`, are read in `ℂ` through a
ring homomorphism `ι : K →+* ℂ`, as the eigenvalues of `π_X^*` are in
`Stacks.EtaleCohomology.IsWeilNumber`: an eigenvalue of `ρ(F_x)` along `ι` is a complex root of
the characteristic polynomial mapped along `ι`.  A finite place of `E` is a height-one prime
`v` of its ring of integers and `E_λ` the completion `v.adicCompletion E`; "maybe after enlarging
`E`" is the existential over the field carrying the companions.
-/

@[expose] public noncomputable section

open Polynomial NumberField IsDedekindDomain Matrix

namespace Stacks.EtaleCohomology

/-! ### The dual characteristic polynomial -/

/-- The dual characteristic polynomial `P(0)⁻¹ · Xⁿ P(1 / X)` of `P`: when `P` is the
characteristic polynomial of an invertible matrix `A`, it is that of `A⁻¹` (and of `(A⁻¹)ᵀ`),
by `Stacks.EtaleCohomology.charpoly_contragredient`. -/
public def dualCharpoly {F : Type*} [Field F] (P : F[X]) : F[X] :=
  C (P.coeff 0)⁻¹ * P.reverse

/-- `dualCharpoly` commutes with homomorphisms of fields. -/
public theorem dualCharpoly_map {F F' : Type*} [Field F] [Field F'] (φ : F →+* F') (P : F[X]) :
    dualCharpoly (P.map φ) = (dualCharpoly P).map φ := by
  simp only [dualCharpoly, reverse, Polynomial.map_mul, map_C, natDegree_map, coeff_map,
    map_inv₀, reflect_map]

/-- The coefficients of `dualCharpoly P` lie in any subfield containing those of `P`. -/
public theorem coeff_dualCharpoly_mem {F : Type*} [Field F] {S : Type*} [SetLike S F]
    [SubfieldClass S F] {E : S} {P : F[X]} (hP : ∀ n, P.coeff n ∈ E) (n : ℕ) :
    (dualCharpoly P).coeff n ∈ E := by
  rw [dualCharpoly, coeff_C_mul, coeff_reverse]
  exact mul_mem (inv_mem (hP 0)) (hP _)

/-- A root of `dualCharpoly P`, for `P` monic with nonzero constant term, is the inverse of a
root of `P`. -/
public theorem isRoot_inv_of_isRoot_dualCharpoly {F : Type*} [Field F] {P : F[X]}
    (hP : P.Monic) (h0 : P.coeff 0 ≠ 0) {z : F} (hz : (dualCharpoly P).IsRoot z) :
    z ≠ 0 ∧ P.IsRoot z⁻¹ := by
  rw [dualCharpoly, IsRoot, eval_mul, eval_C, mul_eq_zero] at hz
  have hrev : P.reverse.eval z = 0 := hz.resolve_left (inv_ne_zero h0)
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [← coeff_zero_eq_eval_zero, coeff_zero_reverse, hP.leadingCoeff] at hrev
    exact one_ne_zero hrev
  refine ⟨hz0, ?_⟩
  let : Invertible z⁻¹ := invertibleOfNonzero (inv_ne_zero hz0)
  have h := (eval₂_reverse_eq_zero_iff (RingHom.id F) z⁻¹ P).1
    (by rwa [eval₂_id, invOf_eq_inv, inv_inv])
  rwa [eval₂_id] at h

/-! ### The contragredient representation -/

section Contragredient

variable {G : Type*} [Group G] {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]

/-- The contragredient `g ↦ ((ρ g)⁻¹)ᵀ` of a matrix representation `ρ : G →* GL_n(R)`. -/
public def contragredient (ρ : G →* GL n R) : G →* GL n R where
  toFun g :=
    ⟨(((ρ g)⁻¹ : GL n R) : Matrix n n R)ᵀ, ((ρ g : GL n R) : Matrix n n R)ᵀ,
      by rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one],
      by rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one]⟩
  map_one' := by ext1; simp
  map_mul' g h := by ext1; simp [Matrix.transpose_mul]

/-- The matrix of `contragredient ρ g` is the transpose of the matrix of `(ρ g)⁻¹`. -/
@[simp]
public theorem contragredient_val (ρ : G →* GL n R) (g : G) :
    ((contragredient ρ g : GL n R) : Matrix n n R) =
      (((ρ g)⁻¹ : GL n R) : Matrix n n R)ᵀ :=
  rfl

/-- The contragredient of a continuous representation is continuous. -/
public theorem continuous_contragredient [TopologicalSpace G] [TopologicalSpace R]
    {ρ : G →* GL n R} (hρ : Continuous ρ) : Continuous (contragredient ρ) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact ((Units.continuous_coe_inv).comp hρ).matrix_transpose
  · exact ((Units.continuous_val).comp hρ).matrix_transpose

end Contragredient

/-- The characteristic polynomial of `ρ^∨(g)` over a field is `dualCharpoly` of that of
`ρ(g)`. -/
public theorem charpoly_contragredient {G : Type*} [Group G] {F : Type*} [Field F] {r : ℕ}
    (ρ : G →* GL (Fin r) F) (g : G) :
    ((contragredient ρ g : GL (Fin r) F) : Matrix (Fin r) (Fin r) F).charpoly =
      dualCharpoly ((ρ g : GL (Fin r) F) : Matrix (Fin r) (Fin r) F).charpoly := by
  set A : Matrix (Fin r) (Fin r) F := (ρ g).val
  have hA : IsUnit A := (ρ g).isUnit
  rw [contragredient_val, Matrix.charpoly_transpose, Matrix.coe_units_inv,
    Matrix.charpoly_inv A hA, ← Matrix.reverse_charpoly, Ring.inverse_eq_inv',
    Matrix.det_eq_sign_charpoly_coeff, Fintype.card_fin, dualCharpoly]
  have hs : ((-1 : F) ^ r) * ((-1 : F) ^ r) = 1 := by
    rw [← mul_pow, neg_one_mul, neg_neg, one_pow]
  have hs' : ((-1 : F[X]) ^ r) = C ((-1 : F) ^ r) := by simp
  rw [hs', ← C_mul, mul_inv, ← mul_assoc, ← inv_pow, inv_neg, inv_one, hs, one_mul]

/-- The characteristic polynomial of an invertible matrix over a field has nonzero constant
term. -/
public theorem charpoly_coeff_zero_ne_zero {F : Type*} [Field F] {r : ℕ}
    (A : GL (Fin r) F) : ((A : Matrix (Fin r) (Fin r) F)).charpoly.coeff 0 ≠ 0 := by
  intro h
  have hdet := Matrix.det_eq_sign_charpoly_coeff (A : Matrix (Fin r) (Fin r) F)
  rw [h, mul_zero] at hdet
  exact (Matrix.isUnit_iff_isUnit_det _).1 A.isUnit |>.ne_zero hdet

/-! ### The conclusions of the conjecture -/

variable {G : Type*} [Group G] [TopologicalSpace G] {P : Type*} {K : Type*} [Field K]
  [CharZero K]

/-- **The conclusions of Deligne's conjecture**, the hypotheses of
[Stacks, Tag 03VH], for a representation `ρ : G →* GL_r(K)` with Frobenius elements
`Fr : P → G` indexed by the closed points, in residue characteristic `p`, with eigenvalues read
in `ℂ` along `ι`:

1. the characteristic polynomials of the `ρ(Fr x)` have coefficients in one number field
   `E ⊆ K`;
2. every eigenvalue of every `ρ(Fr x)` has complex absolute value `1`;
3. after enlarging `E`, for every finite place `v` of `E` not dividing `p` there is a continuous
   `ρ_v : G →* GL_r(E_v)` whose Frobenius characteristic polynomials are those of `ρ`. -/
public structure HasDeligneConclusions (Fr : P → G) (p : ℕ) (ι : K →+* ℂ) {r : ℕ}
    (ρ : G →* GL (Fin r) K) : Prop where
  /-- Conclusion (1): the Frobenius characteristic polynomials have coefficients in a number
  field. -/
  exists_numberField : ∃ E : IntermediateField ℚ K, FiniteDimensional ℚ E ∧
    ∀ x n, ((ρ (Fr x) : GL (Fin r) K) : Matrix (Fin r) (Fin r) K).charpoly.coeff n ∈ E
  /-- Conclusion (2): the Frobenius eigenvalues have complex absolute value `1`. -/
  norm_eq_one : ∀ x (z : ℂ),
    (((ρ (Fr x) : GL (Fin r) K) : Matrix (Fin r) (Fin r) K).charpoly.map ι).IsRoot z → ‖z‖ = 1
  /-- Conclusion (3): companions at every finite place not dividing `p`, after enlarging the
  number field. -/
  exists_companions : ∃ (E : IntermediateField ℚ K) (_ : NumberField E) (Q : P → E[X]),
    (∀ x, (Q x).map (algebraMap E K) =
      ((ρ (Fr x) : GL (Fin r) K) : Matrix (Fin r) (Fin r) K).charpoly) ∧
    ∀ v : HeightOneSpectrum (𝓞 E), (p : 𝓞 E) ∉ v.asIdeal →
      ∃ ρv : G →* GL (Fin r) (v.adicCompletion E), Continuous ρv ∧
        ∀ x, ((ρv (Fr x) : GL (Fin r) (v.adicCompletion E)) :
          Matrix (Fin r) (Fin r) (v.adicCompletion E)).charpoly =
            (Q x).map (algebraMap E (v.adicCompletion E))

/-- **The conclusions of Deligne's conjecture pass to the contragredient.**  The Frobenius
characteristic polynomials of `ρ^∨` are the dual characteristic polynomials of those of `ρ`,
whose coefficients lie in the same number field; the eigenvalues of `ρ^∨(F_x)` are the inverses
of those of `ρ(F_x)`, again of absolute value `1`; and the contragredients of the companions of
`ρ` are companions of `ρ^∨`. -/
public theorem HasDeligneConclusions.contragredient {Fr : P → G} {p : ℕ} {ι : K →+* ℂ} {r : ℕ}
    {ρ : G →* GL (Fin r) K} (h : HasDeligneConclusions Fr p ι ρ) :
    HasDeligneConclusions Fr p ι (contragredient ρ) where
  exists_numberField := by
    obtain ⟨E, hE, hcoeff⟩ := h.exists_numberField
    refine ⟨E, hE, fun x n => ?_⟩
    rw [charpoly_contragredient]
    exact coeff_dualCharpoly_mem (hcoeff x) n
  norm_eq_one := by
    intro x z hz
    rw [charpoly_contragredient, ← dualCharpoly_map] at hz
    have hmonic := (Matrix.charpoly_monic
      ((ρ (Fr x) : GL (Fin r) K) : Matrix (Fin r) (Fin r) K)).map ι
    have h0 : ((((ρ (Fr x) : GL (Fin r) K) : Matrix (Fin r) (Fin r) K)).charpoly.map ι).coeff 0
        ≠ 0 := by
      rw [coeff_map]
      exact (map_ne_zero ι).2 (charpoly_coeff_zero_ne_zero _)
    obtain ⟨hz0, hinv⟩ := isRoot_inv_of_isRoot_dualCharpoly hmonic h0 hz
    have h1 := h.norm_eq_one x z⁻¹ hinv
    rwa [norm_inv, inv_eq_one] at h1
  exists_companions := by
    obtain ⟨E, hE, Q, hQ, hcomp⟩ := h.exists_companions
    refine ⟨E, hE, fun x => dualCharpoly (Q x), fun x => ?_, fun v hv => ?_⟩
    · rw [← dualCharpoly_map, hQ x, charpoly_contragredient]
    · obtain ⟨ρv, hρv, hρvQ⟩ := hcomp v hv
      refine ⟨Stacks.EtaleCohomology.contragredient ρv, continuous_contragredient hρv,
        fun x => ?_⟩
      rw [charpoly_contragredient, hρvQ x, dualCharpoly_map]

end Stacks.EtaleCohomology

end
