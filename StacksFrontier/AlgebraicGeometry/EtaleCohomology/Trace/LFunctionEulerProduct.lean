module

public import StacksCore.Tactic.StacksAttribute
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.Topology.JacobsonSpace
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ClosedPointDegree

/-!
# Euler products and the L-function of a sheaf over a finite field

Let `X` be a scheme over a field `k` and let `Λ` be a commutative ring.  The L-function of a
sheaf `ℱ` on the étale site of `X` whose geometric Frobenius `π_x^*` acts on the stalk `ℱ_x̄` at
a closed point `x` by a square matrix `A x` over `Λ` is the Euler product

`L(X, ℱ) = ∏_{x ∈ |X|} det(1 - A x ⬝ T ^ (deg x)) ⁻¹`,

an element of the formal power series ring `Λ⟦T⟧`, the product running over the closed points
of `X` and `deg x = [κ(x) : k]` being the degree of the residue field extension.  This module
constructs that product and proves that it is well defined.

The local factor `det(1 - A ⬝ T ^ d)` is the determinant of the matrix `1 - T ^ d • A` over
`Λ⟦T⟧`.  Applying a ring homomorphism that kills `T ^ d` to this determinant gives
`det 1 = 1`, which yields at once that the local factor has constant coefficient `1` when
`d ≠ 0` — so it is a unit of `Λ⟦T⟧` and its inverse is again a power series — and that both it
and its inverse are congruent to `1` modulo `T ^ d`.

The last congruence is what makes the infinite product meaningful.  An Euler system is a family
of power series each congruent to `1` modulo `T` raised to the index's degree, with only
finitely many indices of degree at most `n` for every `n`.  Its Euler product is defined
coefficientwise, the coefficient of `T ^ n` being read off the finite product over the indices
of degree at most `n`; `EulerSystem.coeff_eulerProduct_eq` shows that *any* finite subproduct
containing those indices computes the same coefficient, which is the precise sense in which the
product converges.  The construction is insensitive to `Λ`, so it serves both a finite
coefficient ring and a field such as `ℚ_ℓ`.

## Main definitions

* `Stacks.EtaleCohomology.localCharSeries`: the local factor `det(1 - A ⬝ T ^ d)` of a square
  matrix `A` over `Λ`, as an element of `Λ⟦T⟧`.
* `Stacks.EtaleCohomology.localEulerFactor`: its inverse `det(1 - A ⬝ T ^ d) ⁻¹`.
* `Stacks.EtaleCohomology.EulerSystem`: a family of local factors with degrees, finitely many
  of each bounded degree, each factor congruent to `1` modulo `T` raised to its degree.
* `Stacks.EtaleCohomology.EulerSystem.eulerProduct`: the Euler product of such a family.
* `Stacks.EtaleCohomology.residueDegree`: the degree `deg x = [κ(x) : k]` over `k` of a point of
  a scheme.  The closed points `|X|` are Mathlib's `closedPoints X`.
* `Stacks.EtaleCohomology.FrobeniusMatrices.lFunction`: the Euler product over the closed
  points of `X` of the local Euler factors of a family of Frobenius matrices.  For the matrices
  of an actual sheaf see `Stacks.EtaleCohomology.lFunctionOfSheaf`.

## Main results

* `Stacks.EtaleCohomology.constantCoeff_localCharSeries` and
  `Stacks.EtaleCohomology.X_pow_dvd_localCharSeries_sub_one`: the local factor is `1` modulo
  `T ^ d`, hence a unit of `Λ⟦T⟧` for `d ≠ 0`.
* `Stacks.EtaleCohomology.localCharSeries_conj`: the local factor is unchanged by conjugating
  the matrix, so it depends only on the conjugacy class of the Frobenius action.
* `Stacks.EtaleCohomology.EulerSystem.coeff_eulerProduct_eq`: every coefficient of the Euler
  product is computed by any finite subproduct containing the indices of small enough degree.
* `Stacks.EtaleCohomology.EulerSystem.isUnit_eulerProduct`: an Euler product of factors at
  indices of positive degree is a unit of `Λ⟦T⟧`.
* `Stacks.EtaleCohomology.FrobeniusMatrices.coeff_lFunction_eq` and
  `Stacks.EtaleCohomology.FrobeniusMatrices.isUnit_lFunction`: the corresponding statements for
  the L-function.
* `Stacks.EtaleCohomology.FrobeniusMatrices.lFunction_congr`: the L-function depends on the
  matrices only through their local Euler factors.

## Implementation notes

The ring `Λ⟦T⟧` carries no infinite products, so the Euler product is built coefficientwise
from finite subproducts rather than as a limit; `EulerSystem.coeff_eulerProduct_eq` is the
statement that this is independent of the truncation and is the replacement for a convergence
assertion.

A `FrobeniusMatrices` records the matrices of the geometric Frobenius actions.  The two
finiteness properties the Euler product needs are not recorded with it: for `X` of finite type
over a finite field they are theorems, `residueDegree_pos` and
`finite_setOf_closedPoints_residueDegree_le`, and the Euler system is built from those.  The
matrices themselves are constructed from a sheaf by
`Stacks.EtaleCohomology.frobeniusMatricesOfSheaf`, which reads the rank and the matrix at a
closed point off the geometric stalk there;
`Stacks.EtaleCohomology.charPowerSeries_frobeniusStalkEnd` records that the matrix has the same
local factor as the stalk endomorphism, so the choice of basis is immaterial.

## References

* [Stacks Project, Tag 03UV](https://stacks.math.columbia.edu/tag/03UV)
* [Stacks Project, Tag 03UX](https://stacks.math.columbia.edu/tag/03UX)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory PowerSeries

universe u v w

namespace Stacks.EtaleCohomology

/-! ### The local factor of a matrix -/

section LocalFactor

variable {Λ : Type v} [CommRing Λ] {n : Type w} [Fintype n] [DecidableEq n]

/-- The matrix `1 - T ^ d • A` over the power series ring `Λ⟦T⟧`, whose determinant is the
local factor of `A` at a point of degree `d`. -/
public def localCharMatrix (A : Matrix n n Λ) (d : ℕ) : Matrix n n (PowerSeries Λ) :=
  1 - (PowerSeries.X : PowerSeries Λ) ^ d • A.map (PowerSeries.C)

/-- The local factor `det(1 - A ⬝ T ^ d)` of a square matrix `A` over `Λ` at a point of degree
`d`, as a formal power series over `Λ`. -/
public def localCharSeries (A : Matrix n n Λ) (d : ℕ) : PowerSeries Λ :=
  (localCharMatrix A d).det

/-- The local Euler factor `det(1 - A ⬝ T ^ d) ⁻¹` of a square matrix `A` over `Λ` at a point
of degree `d`.  By `localCharSeries_mul_localEulerFactor` it inverts the local factor whenever
`d ≠ 0`. -/
public def localEulerFactor (A : Matrix n n Λ) (d : ℕ) : PowerSeries Λ :=
  PowerSeries.invOfUnit (localCharSeries A d) 1

/-- A ring homomorphism out of `Λ⟦T⟧` that kills `T ^ d` sends `1 - T ^ d • A` to the identity
matrix. -/
public theorem mapMatrix_localCharMatrix {S : Type*} [CommRing S] (g : PowerSeries Λ →+* S)
    (A : Matrix n n Λ) (d : ℕ) (hg : g ((PowerSeries.X : PowerSeries Λ) ^ d) = 0) :
    g.mapMatrix (localCharMatrix A d) = 1 := by
  ext i j
  simp [localCharMatrix, Matrix.one_apply, hg]

/-- A ring homomorphism out of `Λ⟦T⟧` that kills `T ^ d` sends the local factor
`det(1 - A ⬝ T ^ d)` to `1`. -/
public theorem map_localCharSeries {S : Type*} [CommRing S] (g : PowerSeries Λ →+* S)
    (A : Matrix n n Λ) (d : ℕ) (hg : g ((PowerSeries.X : PowerSeries Λ) ^ d) = 0) :
    g (localCharSeries A d) = 1 := by
  rw [localCharSeries, g.map_det, mapMatrix_localCharMatrix g A d hg, Matrix.det_one]

/-- At a point of nonzero degree the local factor `det(1 - A ⬝ T ^ d)` has constant
coefficient `1`. -/
public theorem constantCoeff_localCharSeries (A : Matrix n n Λ) {d : ℕ} (hd : d ≠ 0) :
    PowerSeries.constantCoeff (localCharSeries A d) = 1 :=
  map_localCharSeries _ A d (by simp [hd])

/-- The local factor `det(1 - A ⬝ T ^ d)` is congruent to `1` modulo `T ^ d`. -/
public theorem X_pow_dvd_localCharSeries_sub_one (A : Matrix n n Λ) (d : ℕ) :
    (PowerSeries.X : PowerSeries Λ) ^ d ∣ localCharSeries A d - 1 := by
  have h := map_localCharSeries
    (Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries Λ) ^ d})) A d
    (by rw [Ideal.Quotient.eq_zero_iff_mem]; exact Ideal.mem_span_singleton_self _)
  rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem, map_sub, h, map_one, sub_self]

/-- At a point of nonzero degree the local factor `det(1 - A ⬝ T ^ d)` is a unit of `Λ⟦T⟧`
inverted by the local Euler factor. -/
public theorem localCharSeries_mul_localEulerFactor (A : Matrix n n Λ) {d : ℕ} (hd : d ≠ 0) :
    localCharSeries A d * localEulerFactor A d = 1 :=
  PowerSeries.mul_invOfUnit _ _ (by simpa using constantCoeff_localCharSeries A hd)

/-- The local Euler factor has constant coefficient `1`. -/
public theorem constantCoeff_localEulerFactor (A : Matrix n n Λ) (d : ℕ) :
    PowerSeries.constantCoeff (localEulerFactor A d) = 1 := by
  simp [localEulerFactor]

/-- At a point of nonzero degree the local Euler factor `det(1 - A ⬝ T ^ d) ⁻¹` is congruent to
`1` modulo `T ^ d`.  This is what makes the Euler product over the closed points converge. -/
public theorem X_pow_dvd_localEulerFactor_sub_one (A : Matrix n n Λ) {d : ℕ} (hd : d ≠ 0) :
    (PowerSeries.X : PowerSeries Λ) ^ d ∣ localEulerFactor A d - 1 := by
  have h : localEulerFactor A d - 1 =
      -((localCharSeries A d - 1) * localEulerFactor A d) := by
    linear_combination localCharSeries_mul_localEulerFactor A hd
  rw [h]
  exact ((X_pow_dvd_localCharSeries_sub_one A d).mul_right _).neg_right

/-- The local factor depends only on the conjugacy class of the matrix: it is unchanged on
replacing `A` by `P * A * Q` for any `P`, `Q` with `P * Q = 1`.  Hence it depends on the
Frobenius action on a stalk and not on the basis in which that action is written. -/
public theorem localCharSeries_conj (A : Matrix n n Λ) (d : ℕ) {P Q : Matrix n n Λ}
    (hPQ : P * Q = 1) : localCharSeries (P * A * Q) d = localCharSeries A d := by
  have hPQ' : P.map (PowerSeries.C (R := Λ)) * Q.map (PowerSeries.C (R := Λ)) = 1 := by
    rw [← Matrix.map_mul, hPQ, Matrix.map_one _ (map_zero _) (map_one _)]
  have key : localCharMatrix (P * A * Q) d =
      P.map (PowerSeries.C) * localCharMatrix A d * Q.map (PowerSeries.C) := by
    simp only [localCharMatrix, Matrix.map_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
      hPQ', Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
  rw [localCharSeries, localCharSeries, key, Matrix.det_mul, Matrix.det_mul, mul_right_comm,
    ← Matrix.det_mul, hPQ', Matrix.det_one, one_mul]

/-- The local Euler factor depends only on the conjugacy class of the matrix. -/
public theorem localEulerFactor_conj (A : Matrix n n Λ) (d : ℕ) {P Q : Matrix n n Λ}
    (hPQ : P * Q = 1) : localEulerFactor (P * A * Q) d = localEulerFactor A d := by
  rw [localEulerFactor, localEulerFactor, localCharSeries_conj A d hPQ]

end LocalFactor

/-! ### Euler products -/

/-- A finite product of elements congruent to `1` modulo `c` is congruent to `1` modulo `c`. -/
public theorem dvd_finsetProd_sub_one {R : Type*} [CommRing R] {ι : Type*} (c : R)
    {s : Finset ι} {g : ι → R} (h : ∀ i ∈ s, c ∣ g i - 1) : c ∣ (∏ i ∈ s, g i) - 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
      rw [Finset.prod_insert hi]
      have h1 : c ∣ g i - 1 := h i (Finset.mem_insert_self i s)
      have h2 : c ∣ (∏ j ∈ s, g j) - 1 := ih fun j hj => h j (Finset.mem_insert_of_mem hj)
      have hrw : g i * (∏ j ∈ s, g j) - 1 =
          g i * ((∏ j ∈ s, g j) - 1) + (g i - 1) := by ring
      rw [hrw]
      exact dvd_add (h2.mul_left _) h1

/-- A family of local factors in `Λ⟦T⟧` indexed by `ι`, each index carrying a degree, with the
factor at an index congruent to `1` modulo `T` raised to that degree and only finitely many
indices of degree at most `n` for each `n`.  These are exactly the hypotheses under which the
infinite product of the factors is determined coefficientwise. -/
public structure EulerSystem (Λ : Type v) [CommRing Λ] (ι : Type w) where
  /-- The local factor at an index. -/
  factor : ι → PowerSeries Λ
  /-- The degree of an index. -/
  deg : ι → ℕ
  /-- The factor at an index is congruent to `1` modulo `T` raised to the index's degree. -/
  dvd_factor_sub_one : ∀ i, (PowerSeries.X : PowerSeries Λ) ^ deg i ∣ factor i - 1
  /-- Only finitely many indices have degree at most `n`. -/
  finite_degLE : ∀ n : ℕ, {i | deg i ≤ n}.Finite

namespace EulerSystem

variable {Λ : Type v} [CommRing Λ] {ι : Type w} (E : EulerSystem Λ ι)

/-- The finite set of indices of degree at most `n`. -/
public def support (n : ℕ) : Finset ι := (E.finite_degLE n).toFinset

public theorem mem_support {n : ℕ} {i : ι} : i ∈ E.support n ↔ E.deg i ≤ n := by simp [support]

public theorem support_subset {j n : ℕ} (h : j ≤ n) : E.support j ⊆ E.support n := fun _ hi =>
  E.mem_support.2 ((E.mem_support.1 hi).trans h)

/-- The product of the local factors at the indices of degree at most `n`. -/
public def partialProduct (n : ℕ) : PowerSeries Λ := ∏ i ∈ E.support n, E.factor i

/-- The Euler product of a family of local factors: the power series whose coefficient of
`T ^ n` is that of the product of the factors at the indices of degree at most `n`. -/
public def eulerProduct : PowerSeries Λ :=
  PowerSeries.mk fun n => PowerSeries.coeff n (E.partialProduct n)

public theorem coeff_eulerProduct (n : ℕ) :
    PowerSeries.coeff n E.eulerProduct = PowerSeries.coeff n (E.partialProduct n) :=
  PowerSeries.coeff_mk n _

/-- Enlarging a finite set of indices beyond those of degree at most `j` does not change the
coefficient of `T ^ j` of the product over it: the extra factors are `1` modulo `T ^ (j + 1)`. -/
public theorem coeff_finsetProd_eq {j : ℕ} {t : Finset ι} (ht : E.support j ⊆ t) :
    PowerSeries.coeff j (∏ i ∈ t, E.factor i) = PowerSeries.coeff j (E.partialProduct j) := by
  classical
  obtain ⟨h, hh⟩ : (PowerSeries.X : PowerSeries Λ) ^ (j + 1) ∣
      (∏ i ∈ t \ E.support j, E.factor i) - 1 := by
    refine dvd_finsetProd_sub_one ((PowerSeries.X : PowerSeries Λ) ^ (j + 1)) fun i hi => ?_
    have hni : ¬ E.deg i ≤ j := fun hc => (Finset.mem_sdiff.1 hi).2 (E.mem_support.2 hc)
    exact dvd_trans (pow_dvd_pow _ (by omega)) (E.dvd_factor_sub_one i)
  have hsplit : (∏ i ∈ t \ E.support j, E.factor i) * E.partialProduct j =
      ∏ i ∈ t, E.factor i := Finset.prod_sdiff ht
  have key : (∏ i ∈ t, E.factor i) - E.partialProduct j =
      (PowerSeries.X : PowerSeries Λ) ^ (j + 1) * (h * E.partialProduct j) := by
    rw [← hsplit]
    have hfac : (∏ i ∈ t \ E.support j, E.factor i) = 1 + PowerSeries.X ^ (j + 1) * h := by
      rw [← hh]; ring
    rw [hfac]; ring
  have hz : PowerSeries.coeff j ((∏ i ∈ t, E.factor i) - E.partialProduct j) = 0 := by
    rw [key]
    exact PowerSeries.X_pow_dvd_iff.1 ⟨h * E.partialProduct j, rfl⟩ j (Nat.lt_succ_self j)
  rw [map_sub, sub_eq_zero] at hz
  exact hz

public theorem coeff_partialProduct_of_le {j n : ℕ} (h : j ≤ n) :
    PowerSeries.coeff j (E.partialProduct n) = PowerSeries.coeff j (E.partialProduct j) :=
  E.coeff_finsetProd_eq (E.support_subset h)

/-- The Euler product converges: the coefficient of `T ^ j` of the Euler product is the
coefficient of `T ^ j` of the product over any finite set of indices that contains all the
indices of degree at most `j`. -/
@[stacks 03UX "the convergence of the Euler product: it is stated for an arbitrary \
coefficient ring, so it specializes to the Q_ell case of this tag"]
public theorem coeff_eulerProduct_eq {j : ℕ} {t : Finset ι} (ht : E.support j ⊆ t) :
    PowerSeries.coeff j E.eulerProduct = PowerSeries.coeff j (∏ i ∈ t, E.factor i) := by
  rw [E.coeff_eulerProduct, E.coeff_finsetProd_eq ht]

/-- If every index has positive degree then the Euler product has constant coefficient `1`. -/
public theorem constantCoeff_eulerProduct (hdeg : ∀ i, 0 < E.deg i) :
    PowerSeries.constantCoeff E.eulerProduct = 1 := by
  have h0 : E.support 0 = ∅ := by
    ext i
    simp only [Finset.notMem_empty, iff_false, E.mem_support]
    exact Nat.not_le.2 (hdeg i)
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, E.coeff_eulerProduct, partialProduct, h0,
    Finset.prod_empty]
  simp

/-- If every index has positive degree then the Euler product is a unit of `Λ⟦T⟧`. -/
public theorem isUnit_eulerProduct (hdeg : ∀ i, 0 < E.deg i) : IsUnit E.eulerProduct :=
  PowerSeries.isUnit_iff_constantCoeff.2
    (by rw [E.constantCoeff_eulerProduct hdeg]; exact isUnit_one)

end EulerSystem

/-! ### Closed points and their degrees -/

/-! ### The L-function -/

/-- The matrices of the geometric Frobenius actions on the stalks of a sheaf of `Λ`-modules at
the closed points of a scheme `X` over `k`.  For a constructible flat `Λ`-module the matrix at
`x` is that of `π_x^*` acting on the geometric stalk at `x`. -/
public structure FrobeniusMatrices {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (Λ : Type v) [CommRing Λ] where
  /-- The rank of the stalk at a closed point. -/
  rank : closedPoints X → ℕ
  /-- The matrix of `π_x^*` on the stalk at a closed point. -/
  matrix : ∀ x : closedPoints X, Matrix (Fin (rank x)) (Fin (rank x)) Λ

namespace FrobeniusMatrices

variable {k : Type u} [Field k] {X : Scheme.{u}} {f : X ⟶ Spec (.of k)} {Λ : Type v}
  [CommRing Λ] (D : FrobeniusMatrices f Λ)

/-- The local Euler factor `det(1 - π_x^* T ^ (deg x)) ⁻¹` at a closed point. -/
public def localFactor (x : closedPoints X) : PowerSeries Λ :=
  localEulerFactor (D.matrix x) (residueDegree f x.1)

/-- The local Euler factors at the closed points of `X`, as an Euler system indexed by `|X|`
and graded by the residue degree. -/
public def eulerSystem [Finite k] [LocallyOfFiniteType f] [QuasiCompact f] :
    EulerSystem Λ (closedPoints X) where
  factor := D.localFactor
  deg := fun x => residueDegree f x.1
  dvd_factor_sub_one := fun x =>
    X_pow_dvd_localEulerFactor_sub_one (D.matrix x) (residueDegree_pos f x.1 x.2).ne'
  finite_degLE := finite_setOf_closedPoints_residueDegree_le f

/-- The L-function `∏_{x ∈ |X|} det(1 - π_x^* T ^ (deg x)) ⁻¹` of a family of Frobenius
matrices on a scheme `X` over `k`, as an element of `Λ⟦T⟧`. -/
@[sga "4½ Rapport 1.6" "Euler product"]
public def lFunction [Finite k] [LocallyOfFiniteType f] [QuasiCompact f] : PowerSeries Λ :=
  D.eulerSystem.eulerProduct

public theorem coeff_lFunction [Finite k] [LocallyOfFiniteType f] [QuasiCompact f] (n : ℕ) :
    PowerSeries.coeff n D.lFunction =
      PowerSeries.coeff n (∏ x ∈ D.eulerSystem.support n, D.localFactor x) :=
  D.eulerSystem.coeff_eulerProduct n

/-- Two families of Frobenius matrices with the same local Euler factors have the same
L-function: the Euler product depends on the matrices only through those factors. -/
public theorem lFunction_congr [Finite k] [LocallyOfFiniteType f] [QuasiCompact f]
    {D' : FrobeniusMatrices f Λ} (h : ∀ x, D.localFactor x = D'.localFactor x) :
    D.lFunction = D'.lFunction := by
  ext n
  rw [D.coeff_lFunction, D'.coeff_lFunction]
  exact congrArg _ (Finset.prod_congr rfl fun x _ => h x)

/-- The defining product converges: the coefficient of `T ^ j` of the L-function is computed by
the product of the local Euler factors over any finite set of closed points containing all
those of degree at most `j`. -/
@[sga "7 XXII 3.0" "special case"]
public theorem coeff_lFunction_eq [Finite k] [LocallyOfFiniteType f] [QuasiCompact f]
    {j : ℕ} {t : Finset (closedPoints X)}
    (ht : D.eulerSystem.support j ⊆ t) :
    PowerSeries.coeff j D.lFunction = PowerSeries.coeff j (∏ x ∈ t, D.localFactor x) :=
  D.eulerSystem.coeff_eulerProduct_eq ht

/-- The L-function has constant coefficient `1`. -/
public theorem constantCoeff_lFunction [Finite k] [LocallyOfFiniteType f] [QuasiCompact f] :
    PowerSeries.constantCoeff D.lFunction = 1 :=
  D.eulerSystem.constantCoeff_eulerProduct fun x => residueDegree_pos f x.1 x.2

/-- The L-function is a unit of `Λ⟦T⟧`. -/
public theorem isUnit_lFunction [Finite k] [LocallyOfFiniteType f] [QuasiCompact f] :
    IsUnit D.lFunction :=
  D.eulerSystem.isUnit_eulerProduct fun x => residueDegree_pos f x.1 x.2

end FrobeniusMatrices

end Stacks.EtaleCohomology

end
