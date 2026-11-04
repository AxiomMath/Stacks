module

public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.FieldTheory.RatFunc.Degree
public import Mathlib.FieldTheory.KummerPolynomial
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
public import StacksFrontier.AlgebraicGeometry.HomogeneousQuotient.Defs

/-!
# A regular model with an inseparable component: the data

Let `k = 𝔽₂(t)`, `κ = k(√t)` (purely inseparable of degree two over `k`), `R = k⟦π⟧` and
`K = Frac R`. Inside `ℙ¹_R × ℙ¹_R`, with coordinates `[X₀ : X₁]` and `[U : V]`, the divisor
`π X₀² V = (X₁² - t X₀²) U` is the blow-up of `ℙ¹_R` at the closed point `X₁² = t X₀²` of its
special fibre. Under the Segre embedding `z₀₀ = X₀U`, `z₀₁ = X₀V`, `z₁₀ = X₁U`, `z₁₁ = X₁V` it is
the closed subscheme of `ℙ³_R` cut out by the three quadrics

* `q₀ = z₀₀ z₁₁ - z₀₁ z₁₀`,
* `q₁ = π z₀₀ z₀₁ + t z₀₀² - z₁₀²`,
* `q₂ = π z₀₁² + t z₀₀ z₀₁ - z₁₀ z₁₁`,

the `2 × 2` minors of `[[z₀₀, z₀₁, z₁₀], [z₁₀, z₁₁, π z₀₁ + t z₀₀]]`. This file fixes that data:
the fields, the ring `R`, the homogeneous ideal `J = (q₀, q₁, q₂)` of `R[z₀₀, z₀₁, z₁₀, z₁₁]`
(variables indexed by `Fin 4` in this order), the graded quotient `A = R[z] ⧸ J`, the scheme
`X = Proj A` and its structure morphism to `Spec R`.

## Main definitions

* `Stacks.Models.InseparableModel.k`, `t`, `κ`, `θ` — the residue field, `t`, `κ = k(θ)`, `θ² = t`.
* `Stacks.Models.InseparableModel.R`, `π`, `K` — the discrete valuation ring, its uniformizer and
  fraction field.
* `Stacks.Models.InseparableModel.J` — the homogeneous ideal of the model.
* `Stacks.Models.InseparableModel.grading` — the grading of `R[z] ⧸ J`.
* `Stacks.Models.InseparableModel.XR` — the model `X`.

## Main results

* `Stacks.Models.InseparableModel.not_isSeparable` — `κ / k` is not separable.
* `Stacks.Models.InseparableModel.finrank_κ` — `[κ : k] = 2`.
-/

@[expose] public noncomputable section

namespace Stacks.Models.InseparableModel

/-! ### The fields -/

/-- The residue field `k = 𝔽₂(t)`. -/
abbrev k : Type := RatFunc (ZMod 2)

/-- The transcendental `t ∈ k`. -/
def t : k := RatFunc.X

/-- `t` is not a square in `k`: its degree is odd. -/
theorem pow_two_ne_t (b : k) : b ^ 2 ≠ t := by
  intro h
  have hb : b ≠ 0 := by
    rintro rfl
    exact RatFunc.X_ne_zero (by simpa [t] using h.symm)
  have h1 := congrArg RatFunc.intDegree h
  rw [pow_two, RatFunc.intDegree_mul hb hb, t, RatFunc.intDegree_X] at h1
  omega

/-- The minimal polynomial `X² - t` of `√t` over `k`. -/
def κpoly : Polynomial k := Polynomial.X ^ 2 - Polynomial.C t

/-- `X² - t` is irreducible over `k`, since `t` is not a square. -/
theorem irreducible_κpoly : Irreducible κpoly :=
  X_pow_sub_C_irreducible_of_prime Nat.prime_two pow_two_ne_t

/-- The irreducibility of `X² - t`, as an instance, so that `AdjoinRoot κpoly` is a field. -/
instance fact_irreducible_κpoly : Fact (Irreducible κpoly) := ⟨irreducible_κpoly⟩

/-- The purely inseparable quadratic extension `κ = k(√t)`. -/
abbrev κ : Type := AdjoinRoot κpoly

/-- The square root `θ = √t ∈ κ`. -/
def θ : κ := AdjoinRoot.root κpoly

/-- `θ² = t` in `κ`. -/
theorem θ_sq : θ ^ 2 = algebraMap k κ t := by
  have h := AdjoinRoot.eval₂_root κpoly
  rw [κpoly, Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C] at h
  rw [θ, ← sub_eq_zero]
  exact h

/-- The minimal polynomial of `θ` over `k` is `X² - t`. -/
theorem minpoly_θ : minpoly k θ = κpoly := by
  have hmonic : κpoly.Monic := by
    unfold κpoly
    exact Polynomial.monic_X_pow_sub_C t two_ne_zero
  exact (minpoly.eq_of_irreducible_of_monic irreducible_κpoly (AdjoinRoot.eval₂_root κpoly)
    hmonic).symm

/-- **`κ / k` is not separable**: the minimal polynomial `X² - t` of `√t` has derivative
`2X = 0`. -/
theorem not_isSeparable : ¬ Algebra.IsSeparable k κ := by
  intro h
  have hs : (minpoly k θ).Separable := Algebra.IsSeparable.isSeparable k θ
  rw [minpoly_θ] at hs
  have h2 : (2 : k) = 0 := by
    have : algebraMap (ZMod 2) k 2 = 0 := by
      rw [show (2 : ZMod 2) = 0 from rfl, map_zero]
    rwa [map_ofNat] at this
  have hd : Polynomial.derivative κpoly = 0 := by
    unfold κpoly
    rw [Polynomial.derivative_sub, Polynomial.derivative_C, sub_zero,
      Polynomial.derivative_X_pow]
    simp [h2]
  rw [Polynomial.Separable, hd] at hs
  exact irreducible_κpoly.not_isUnit (isCoprime_zero_right.mp hs)

/-- **`[κ : k] = 2`.** -/
theorem finrank_κ : Module.finrank k κ = 2 := by
  rw [(AdjoinRoot.powerBasis irreducible_κpoly.ne_zero).finrank]
  show κpoly.natDegree = 2
  unfold κpoly
  rw [Polynomial.natDegree_X_pow_sub_C]

/-! ### The discrete valuation ring -/

/-- The discrete valuation ring `R = k⟦π⟧`. -/
abbrev R : Type := PowerSeries k

/-- The uniformizer `π ∈ R`. -/
def π : R := PowerSeries.X

/-- `π` is irreducible in `R`. -/
theorem irreducible_π : Irreducible π := PowerSeries.X_irreducible

/-- The fraction field `K` of `R`. -/
abbrev K : Type := FractionRing R

/-- `R` is a `k`-algebra through the constant coefficient, i.e. reduction modulo `π`. -/
instance algebraRk : Algebra R k := (PowerSeries.constantCoeff (R := k)).toAlgebra

/-- Reduction modulo `π` is surjective onto `k`. -/
theorem algebraMap_Rk_surjective : Function.Surjective (algebraMap R k) := fun a =>
  ⟨PowerSeries.C a, by simp [RingHom.algebraMap_toAlgebra]⟩

/-- `π` reduces to `0` in `k`. -/
theorem algebraMap_Rk_π : algebraMap R k π = 0 := by
  simp [RingHom.algebraMap_toAlgebra, π]

/-- The canonical residue field of `R` is `k`, as an `R`-algebra. -/
def residueEquiv : IsLocalRing.ResidueField R ≃ₐ[R] k :=
  (Ideal.quotientEquivAlgOfEq R
      (IsLocalRing.ker_eq_maximalIdeal (algebraMap R k) algebraMap_Rk_surjective).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId R k) algebraMap_Rk_surjective)

/-- `t`, as an element of `R`. -/
def tR : R := PowerSeries.C t

/-! ### The homogeneous ideal and the model -/

/-- The polynomial ring `R[z₀₀, z₀₁, z₁₀, z₁₁]`, the variables indexed by `Fin 4` in this order. -/
abbrev P : Type := MvPolynomial (Fin 4) R

/-- The grading of `R[z]` by total degree. -/
abbrev polyGrading : ℕ → Submodule R P := MvPolynomial.homogeneousSubmodule (Fin 4) R

open MvPolynomial in
/-- `q₀ = z₀₀ z₁₁ - z₀₁ z₁₀`. -/
def q₀ : P := X 0 * X 3 - X 1 * X 2

open MvPolynomial in
/-- `q₁ = π z₀₀ z₀₁ + t z₀₀² - z₁₀²`. -/
def q₁ : P := C π * X 0 * X 1 + C tR * X 0 ^ 2 - X 2 ^ 2

open MvPolynomial in
/-- `q₂ = π z₀₁² + t z₀₀ z₀₁ - z₁₀ z₁₁`. -/
def q₂ : P := C π * X 1 ^ 2 + C tR * X 0 * X 1 - X 2 * X 3

/-- The three generators. -/
def gens : Set P := {q₀, q₁, q₂}

open MvPolynomial in
/-- The generators `q₀`, `q₁`, `q₂` are homogeneous of degree two. -/
theorem isHomogeneous_gens : ∀ q ∈ gens, q.IsHomogeneous 2 := by
  have hX : ∀ i : Fin 4, (X i : P).IsHomogeneous 1 := fun i => isHomogeneous_X R i
  have hC : ∀ r : R, (C r : P).IsHomogeneous 0 := fun r => isHomogeneous_C _ r
  rintro q (rfl | rfl | rfl)
  · exact ((hX 0).mul (hX 3)).sub ((hX 1).mul (hX 2))
  · have h := ((((hC π).mul (hX 0)).mul (hX 1)).add ((hC tR).mul ((hX 0).pow 2))).sub
      ((hX 2).pow 2)
    simpa [q₁] using h
  · have h := (((hC π).mul ((hX 1).pow 2)).add (((hC tR).mul (hX 0)).mul (hX 1))).sub
      ((hX 2).mul (hX 3))
    simpa [q₂] using h

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The homogeneous ideal `J = (q₀, q₁, q₂)`. -/
def J : HomogeneousIdeal polyGrading :=
  ⟨Ideal.span gens, Ideal.homogeneous_span _ _ fun q hq =>
    ⟨2, (MvPolynomial.mem_homogeneousSubmodule _ _).2 (isHomogeneous_gens q hq)⟩⟩

/-- The homogeneous coordinate ring `A = R[z] ⧸ J`. -/
abbrev A : Type := P ⧸ J.toIdeal

/-- The grading of `A`. -/
abbrev grading : ℕ → Submodule R A :=
  Stacks.RingTheory.HomogeneousQuotient.quotientGrading polyGrading J

/-- **The model** `X = Proj (R[z] ⧸ J)`. -/
abbrev XR : AlgebraicGeometry.Scheme := AlgebraicGeometry.Proj grading

end Stacks.Models.InseparableModel
