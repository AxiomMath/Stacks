module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.ProjAmple.DegreeOneCover
public import StacksFrontier.RingTheory.GradedAlgebra.WeightedQuotient
public import Mathlib.Data.Finsupp.Interval
public import StacksFrontier.RingTheory.DualNumber.TangentVectors
public import StacksFrontier.AlgebraicGeometry.ProjectiveCohomology.WeightSplittingNaturality
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjStandardOpenScalars
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjChartGradedThetaBuild
public import StacksFrontier.AlgebraicGeometry.VeryAmpleAffineBase.FiniteGlobalSections
public import StacksFrontier.AlgebraicGeometry.RelativeAmpleAffineBase.Basic
public import StacksFrontier.AlgebraicGeometry.AmpleBridge.Basic

/-!
# A `Proj` with an ample `𝒪(1)` no power of which is relatively very ample

Over a field `k` let

`A = k[U, V, Z₁, Z₂, Z₃, …] / (U² - Z₁², U⁴ - Z₂², U⁶ - Z₃², …)`,
`deg U = deg V = deg Z₁ = 1`,  `deg Z_d = d`,

so that `Z_d` is a degree-`d` square root of `U^{2d}`, and let `f : X = Proj A ⟶ Spec k` be the
structure morphism. Since `D₊(Z_d) = D₊(Z_d²) = D₊(U^{2d}) = D₊(U)`, the scheme `X` is covered by
the two standard opens `D₊(U)` and `D₊(V)`. Hence every twist `𝒪_X(n)` is invertible and
isomorphic to `𝒪_X(1)^{⊗ n}`, and `𝒪_X(1)` is ample and `f`-ample.

Nevertheless no power of `𝒪_X(1)` is `f`-relatively very ample. The global sections
`Γ(X, 𝒪_X(n))` are finite-dimensional over `k`: a global section is a fraction `a / U^m` on
`D₊(U)` and `b / V^l` on `D₊(V)`, the two agree on `D₊(UV)`, so `V^l a = U^m b` in `A`, and this
forces `V^l ∣ b` with a quotient of degree `n`. A relatively very ample sheaf with
finite-dimensional global sections over an affine base forces the morphism to be locally of finite
type. But `D₊(V)` is the spectrum of `k[t, t₁, t₂, …] / (t² - t₁², t⁴ - t₂², …)`, which is not
even Noetherian: the tangent vectors `t = t_d = 0`, `t_j ↦ ε` at the origin are independent, so
its maximal ideal there is not finitely generated.

## Main definitions

* `Stacks.ProjEvenPowerRoots.Vars` and `Stacks.ProjEvenPowerRoots.weight`: the variables
  `U, V, Z₁, Z₂, …` and their degrees.
* `Stacks.ProjEvenPowerRoots.relation`: the relation `U^{2d} - Z_d²`.
* `Stacks.ProjEvenPowerRoots.ring` and `Stacks.ProjEvenPowerRoots.grading`: the algebra `A` and
  its grading by weighted degree.
* `Stacks.ProjEvenPowerRoots.instGradedAlgebra`: the graded-algebra structure on `A`.
* `Stacks.ProjEvenPowerRoots.uGen`, `Stacks.ProjEvenPowerRoots.vGen` and
  `Stacks.ProjEvenPowerRoots.zGen`: the classes of the variables.
* `Stacks.ProjEvenPowerRoots.normalForm`: the `k`-linear normal form for the relations, which
  reduces the exponent of every `Z_d` to `0` or `1`.
* `Stacks.ProjEvenPowerRoots.structureMorphism`: the structure morphism `f : X ⟶ Spec k`.
* `Stacks.ProjEvenPowerRoots.chartValue`: the value of a global section of `𝒪_X(n)` on a standard
  open `D₊(g)`, as a fraction in `A_g`.
* `Stacks.ProjEvenPowerRoots.tensorPowTwistIso`: `𝒪_X(1)^{⊗ (n+1)} ≅ 𝒪_X(n + 1)`.

## Main results

* `Stacks.ProjEvenPowerRoots.uGen_pow_eq_zGen_sq`: the defining relation, `U^{2d} = Z_d²`.
* `Stacks.ProjEvenPowerRoots.sup_basicOpen_eq_top`: **`X` is covered by `D₊(U)` and `D₊(V)`.**
* `Stacks.ProjEvenPowerRoots.isInvertible_twistingSheaf`: **every `𝒪_X(n)` is invertible**, and
  `Stacks.ProjEvenPowerRoots.isIso_twistMultiplicationMap` identifies `𝒪_X(n) ⊗ 𝒪_X(m)` with
  `𝒪_X(n + m)`.
* `Stacks.ProjEvenPowerRoots.isAmple_twistingModule_one` and
  `Stacks.ProjEvenPowerRoots.isRelativelyAmple_twistingModule_one`: **`𝒪_X(1)` is ample and
  `f`-ample.**
* `Stacks.ProjEvenPowerRoots.exists_eq_vGen_pow_mul`: in `A`, `U^m b = V^l a` forces `V^l ∣ b`.
* `Stacks.ProjEvenPowerRoots.exists_finset_globalSections`: **`Γ(X, 𝒪_X(n))` is
  finite-dimensional over `k`.**
* `Stacks.ProjEvenPowerRoots.not_isNoetherianRing_away` and
  `Stacks.ProjEvenPowerRoots.not_locallyOfFiniteType`: `A_{(V)}` is not Noetherian, so `X` is not
  locally of finite type over `k`.
* `Stacks.ProjEvenPowerRoots.not_isRelativelyVeryAmple_twistingModule` and
  `Stacks.ProjEvenPowerRoots.not_isRelativelyVeryAmple_tensorPowModule`: **no `𝒪_X(n)`, and no
  power `𝒪_X(1)^{⊗ n}` with `n ≥ 1`, is `f`-relatively very ample.**

## Implementation notes

The variable `Z_d` of the source for `d ≥ 1` is `Vars.z j` with `j = d - 1`, so its weight is
`j + 1` and the `j`-th relation is `U^{2(j+1)} - Z_{j+1}²`. The grading, the homogeneity of the
relation ideal and the generation of `A` over `A₀` by the variables come from
`Stacks.WeightedQuotient`.

Every point of `X` lies in `D₊(g)` for some `g` of degree one, which is the hypothesis of
`Stacks.ProjDegreeOneCover`; this is strictly weaker than generation in degree one, which `A`
fails.

Relative very ampleness is that of [Stacks, Tag 01VM]: an immersion `X ⟶ 𝐏(E)` over `Spec k` for
some quasi-coherent `E`, pulling `𝒪(1)` back to the sheaf. Of the identification
`Γ(X, 𝒪_X(n)) = A_n` of the source only the inclusion into `A_n`, read on `D₊(V)`, is proved.

## References

* [Stacks Project, Tag 01VO](https://stacks.math.columbia.edu/tag/01VO)
* [Stacks Project, Tag 01VM](https://stacks.math.columbia.edu/tag/01VM)
* [Stacks Project, Tag 01VK](https://stacks.math.columbia.edu/tag/01VK)
* [Stacks Project, Tag 01MU](https://stacks.math.columbia.edu/tag/01MU)
* [Stacks Project, Tag 01MN](https://stacks.math.columbia.edu/tag/01MN)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory MvPolynomial TopologicalSpace Opposite
open AlgebraicGeometry.ProjectiveSpectrum.Proj (twistingSheaf)
open Stacks.AlgebraicGeometry.ProjInvertibleLocus (twistMultiplicationMap)

namespace Stacks.ProjEvenPowerRoots

/-- The variables of the example: `U`, `V`, and one variable `Z_{j+1}` for every `j : ℕ`. -/
public inductive Vars : Type
  | u : Vars
  | v : Vars
  | z (j : ℕ) : Vars
  deriving DecidableEq

/-- The degrees of the variables: `U` and `V` have degree one, and `Z_{j+1}` has degree
`j + 1`. -/
public def weight : Vars → ℕ
  | .u => 1
  | .v => 1
  | .z j => j + 1

noncomputable section

universe u

variable (k : Type u) [Field k]

/-- The `j`-th relation `U^{2(j+1)} - Z_{j+1}²` of the example. -/
public def relation (j : ℕ) : MvPolynomial Vars k :=
  X Vars.u ^ (2 * (j + 1)) - X (Vars.z j) ^ 2

/-- The weighted degree of the `j`-th relation, namely `2(j + 1)`. -/
public def relationDegree (j : ℕ) : ℕ := 2 * (j + 1)

/-- Each relation is weighted homogeneous: both `U^{2d}` and `Z_d²` have weighted degree
`2d`. -/
public theorem isWeightedHomogeneous_relation (j : ℕ) :
    (relation k j).IsWeightedHomogeneous weight (relationDegree j) := by
  have hu : (X Vars.u ^ (2 * (j + 1)) : MvPolynomial Vars k).IsWeightedHomogeneous weight
      (relationDegree j) := by
    simpa [weight, relationDegree] using
      (isWeightedHomogeneous_X k weight Vars.u).pow (2 * (j + 1))
  have hz : (X (Vars.z j) ^ 2 : MvPolynomial Vars k).IsWeightedHomogeneous weight
      (relationDegree j) := by
    simpa [weight, relationDegree, two_mul] using
      (isWeightedHomogeneous_X k weight (Vars.z j)).pow 2
  exact hu.sub hz

/-- The graded algebra `A = k[U, V, Z₁, Z₂, …] / (U^{2d} - Z_d²)` of the example. -/
public abbrev ring : Type u := Stacks.WeightedQuotient.ring (relation k)

/-- The grading of `A` by weighted degree. -/
public abbrev grading : ℕ → Submodule k (ring k) :=
  Stacks.WeightedQuotient.grading weight (relation k)

/-- **The graded-algebra structure on `A`**, the decomposition of the quotient by the homogeneous
relation ideal. -/
@[stacks 01VO "the graded algebra of the example"]
public instance instGradedAlgebra : _root_.GradedAlgebra (grading k) :=
  Stacks.WeightedQuotient.gradedAlgebra weight relationDegree (relation k)
    (isWeightedHomogeneous_relation k)

/-- The class of `U` in `A`. -/
public def uGen : ring k := Stacks.WeightedQuotient.gen (relation k) Vars.u

/-- The class of `V` in `A`. -/
public def vGen : ring k := Stacks.WeightedQuotient.gen (relation k) Vars.v

/-- The class of `Z_{j+1}` in `A`. -/
public def zGen (j : ℕ) : ring k := Stacks.WeightedQuotient.gen (relation k) (Vars.z j)

/-- `U` has degree one. -/
public theorem uGen_mem : uGen k ∈ grading k 1 :=
  Stacks.WeightedQuotient.gen_mem_grading weight (relation k) Vars.u

/-- `V` has degree one. -/
public theorem vGen_mem : vGen k ∈ grading k 1 :=
  Stacks.WeightedQuotient.gen_mem_grading weight (relation k) Vars.v

/-- `Z_{j+1}` has degree `j + 1`. -/
public theorem zGen_mem (j : ℕ) : zGen k j ∈ grading k (j + 1) :=
  Stacks.WeightedQuotient.gen_mem_grading weight (relation k) (Vars.z j)

/-- The defining relation in `A`: the degree-`d` element `Z_d` is a square root of `U^{2d}`. -/
public theorem uGen_pow_eq_zGen_sq (j : ℕ) : uGen k ^ (2 * (j + 1)) = zGen k j ^ 2 := by
  have h0 : Ideal.Quotient.mk (Stacks.WeightedQuotient.relationIdeal (relation k))
      (relation k j) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨j, rfl⟩)
  rw [relation, map_sub, map_pow, map_pow, sub_eq_zero] at h0
  exact h0

/-! ### A normal form for the relations -/

section NormalForm

/-- The contribution of the exponent `e` of the variable `i` to the reduced exponent: an even
power `Z_d^{2q}` of a variable `Z_d` is traded for `U^{2dq}`, and every other exponent is kept. -/
def reducedPiece : Vars → ℕ → (Vars →₀ ℕ)
  | .z j, e => Finsupp.single (Vars.z j) (e % 2) + Finsupp.single Vars.u (2 * (j + 1) * (e / 2))
  | i, e => Finsupp.single i e

/-- The exponent `0` contributes nothing to the reduced exponent. -/
theorem reducedPiece_zero (i : Vars) : reducedPiece i 0 = 0 := by
  cases i <;> simp [reducedPiece]

/-- **The reduced exponent** of a monomial: every `Z_d` occurs to the power `0` or `1`, the even
part of its exponent having been converted to a power of `U` by `Z_d² = U^{2d}`. -/
def reducedExp (m : Vars →₀ ℕ) : Vars →₀ ℕ := m.sum reducedPiece

/-- The reduced exponent is the sum of the pieces over any finite set containing the support. -/
theorem reducedExp_eq_sum {m : Vars →₀ ℕ} {s : Finset Vars} (hs : m.support ⊆ s) :
    reducedExp m = ∑ x ∈ s, reducedPiece x (m x) :=
  Finsupp.sum_of_support_subset m hs _ fun i _ => reducedPiece_zero i

/-- Adding to the exponent of one variable changes the reduced exponent by the change of that
variable's piece. -/
theorem reducedExp_add_single (m : Vars →₀ ℕ) (i : Vars) (e : ℕ) (Δ : Vars →₀ ℕ)
    (h : reducedPiece i (m i + e) = reducedPiece i (m i) + Δ) :
    reducedExp (m + Finsupp.single i e) = reducedExp m + Δ := by
  classical
  set s := insert i m.support
  have hs : m.support ⊆ s := Finset.subset_insert _ _
  have hs' : (m + Finsupp.single i e).support ⊆ s := by
    refine (Finsupp.support_add).trans (Finset.union_subset hs ?_)
    exact (Finsupp.support_single_subset).trans (by simp [s])
  rw [reducedExp_eq_sum hs, reducedExp_eq_sum hs',
    ← Finset.add_sum_erase s _ (Finset.mem_insert_self _ _),
    ← Finset.add_sum_erase s _ (Finset.mem_insert_self _ _)]
  have hrest : ∑ x ∈ s.erase i, reducedPiece x ((m + Finsupp.single i e) x) =
      ∑ x ∈ s.erase i, reducedPiece x (m x) := by
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [Finsupp.add_apply, Finsupp.single_eq_of_ne (Finset.ne_of_mem_erase hx), add_zero]
  rw [hrest, Finsupp.add_apply, Finsupp.single_eq_same, h]
  abel

/-- Multiplying a monomial by `U^e` multiplies its reduced monomial by `U^e`. -/
theorem reducedExp_add_single_u (m : Vars →₀ ℕ) (e : ℕ) :
    reducedExp (m + Finsupp.single Vars.u e) = reducedExp m + Finsupp.single Vars.u e :=
  reducedExp_add_single m _ e _ (by simp [reducedPiece])

/-- Multiplying a monomial by `V^e` multiplies its reduced monomial by `V^e`. -/
theorem reducedExp_add_single_v (m : Vars →₀ ℕ) (e : ℕ) :
    reducedExp (m + Finsupp.single Vars.v e) = reducedExp m + Finsupp.single Vars.v e :=
  reducedExp_add_single m _ e _ (by simp [reducedPiece])

/-- Multiplying a monomial by `Z_{j+1}²` multiplies its reduced monomial by `U^{2(j+1)}`. -/
theorem reducedExp_add_single_z (m : Vars →₀ ℕ) (j : ℕ) :
    reducedExp (m + Finsupp.single (Vars.z j) 2) =
      reducedExp m + Finsupp.single Vars.u (2 * (j + 1)) := by
  refine reducedExp_add_single m _ 2 _ ?_
  simp only [reducedPiece]
  rw [Nat.add_mod_right, show (m (Vars.z j) + 2) / 2 = m (Vars.z j) / 2 + 1 by omega, mul_add,
    mul_one, Finsupp.single_add, add_assoc]

/-- **The normal form**, the `k`-linear map sending a monomial to the monomial of its reduced
exponent. -/
def normalForm : MvPolynomial Vars k →ₗ[k] MvPolynomial Vars k :=
  (MvPolynomial.basisMonomials Vars k).constr k fun m => monomial (reducedExp m) 1

/-- The normal form of a monomial is the monomial of its reduced exponent. -/
theorem normalForm_monomial (m : Vars →₀ ℕ) (c : k) :
    normalForm k (monomial m c) = monomial (reducedExp m) c := by
  have h : monomial m c = c • (MvPolynomial.basisMonomials Vars k m) := by
    rw [MvPolynomial.coe_basisMonomials, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  rw [h, map_smul, normalForm, Module.Basis.constr_basis, MvPolynomial.smul_monomial,
    smul_eq_mul, mul_one]

/-- Two `k`-linear maps out of `k[U, V, Z₁, …]` agreeing on monomials agree. -/
theorem linearMap_ext {M : Type*} [AddCommGroup M] [Module k M]
    {φ ψ : MvPolynomial Vars k →ₗ[k] M} (h : ∀ m, φ (monomial m 1) = ψ (monomial m 1)) :
    φ = ψ :=
  (MvPolynomial.basisMonomials Vars k).ext fun m => by
    rw [MvPolynomial.coe_basisMonomials]; exact h m

/-- The normal form commutes with multiplication by a variable `X i` which shifts the reduced
exponent by `i`. -/
private theorem normalForm_X_mul (i : Vars)
    (h : ∀ m, reducedExp (m + Finsupp.single i 1) = reducedExp m + Finsupp.single i 1)
    (p : MvPolynomial Vars k) : normalForm k (X i * p) = X i * normalForm k p := by
  have := linearMap_ext k (φ := normalForm k ∘ₗ LinearMap.mulLeft k (X i))
    (ψ := LinearMap.mulLeft k (X i) ∘ₗ normalForm k) fun m => by
      have hX : (X i : MvPolynomial Vars k) = monomial (Finsupp.single i 1) 1 := rfl
      simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, normalForm_monomial, hX,
        monomial_mul, one_mul]
      rw [add_comm, h, add_comm]
  exact LinearMap.congr_fun this p

/-- If the normal form commutes with multiplication by `X i`, it commutes with `X i ^ n`. -/
private theorem normalForm_X_pow_mul (i : Vars)
    (h : ∀ p, normalForm k (X i * p) = X i * normalForm k p) (n : ℕ) (p : MvPolynomial Vars k) :
    normalForm k (X i ^ n * p) = X i ^ n * normalForm k p := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', mul_assoc, h, ih, ← mul_assoc]

/-- The normal form commutes with multiplication by `U`. -/
theorem normalForm_X_u_mul (p : MvPolynomial Vars k) :
    normalForm k (X Vars.u * p) = X Vars.u * normalForm k p :=
  normalForm_X_mul k _ (fun m => reducedExp_add_single_u m 1) p

/-- The normal form commutes with multiplication by `V`. -/
theorem normalForm_X_v_mul (p : MvPolynomial Vars k) :
    normalForm k (X Vars.v * p) = X Vars.v * normalForm k p :=
  normalForm_X_mul k _ (fun m => reducedExp_add_single_v m 1) p

/-- The normal form commutes with multiplication by `U^n`. -/
theorem normalForm_X_u_pow_mul (n : ℕ) (p : MvPolynomial Vars k) :
    normalForm k (X Vars.u ^ n * p) = X Vars.u ^ n * normalForm k p :=
  normalForm_X_pow_mul k _ (normalForm_X_u_mul k) n p

/-- The normal form commutes with multiplication by `V^n`. -/
theorem normalForm_X_v_pow_mul (n : ℕ) (p : MvPolynomial Vars k) :
    normalForm k (X Vars.v ^ n * p) = X Vars.v ^ n * normalForm k p :=
  normalForm_X_pow_mul k _ (normalForm_X_v_mul k) n p

/-- The normal form kills the multiples of each relation. -/
theorem normalForm_mul_relation (q : MvPolynomial Vars k) (j : ℕ) :
    normalForm k (q * relation k j) = 0 := by
  have := linearMap_ext k (φ := normalForm k ∘ₗ LinearMap.mulRight k (relation k j))
    (ψ := 0) fun m => by
      simp only [LinearMap.comp_apply, LinearMap.mulRight_apply, LinearMap.zero_apply,
        relation, mul_sub, map_sub, X_pow_eq_monomial, monomial_mul, one_mul,
        normalForm_monomial, reducedExp_add_single_u, reducedExp_add_single_z, sub_self]
  exact LinearMap.congr_fun this q

/-- **The normal form vanishes on the relation ideal.** -/
theorem normalForm_eq_zero_of_mem {p : MvPolynomial Vars k}
    (hp : p ∈ Stacks.WeightedQuotient.relationIdeal (relation k)) : normalForm k p = 0 := by
  obtain ⟨c, rfl⟩ := Finsupp.mem_ideal_span_range_iff_exists_finsupp.mp hp
  rw [Finsupp.sum, map_sum]
  exact Finset.sum_eq_zero fun j _ => normalForm_mul_relation k _ j

/-- The class of a monomial in `A` is the class of the monomial of its reduced exponent. -/
theorem mk_monomial_reducedExp (m : Vars →₀ ℕ) :
    Ideal.Quotient.mk (Stacks.WeightedQuotient.relationIdeal (relation k))
        (monomial (reducedExp m) (1 : k)) =
      Ideal.Quotient.mk (Stacks.WeightedQuotient.relationIdeal (relation k))
        (monomial m (1 : k)) := by
  classical
  have hm : monomial m (1 : k) = ∏ x ∈ m.support, monomial (Finsupp.single x (m x)) 1 := by
    rw [← MvPolynomial.monomial_sum_one, ← Finsupp.sum, Finsupp.sum_single]
  rw [reducedExp_eq_sum (subset_refl _), MvPolynomial.monomial_sum_one, hm, map_prod, map_prod]
  refine Finset.prod_congr rfl fun x _ => ?_
  cases x with
  | z j =>
    simp only [reducedPiece]
    rw [show monomial (Finsupp.single (Vars.z j) (m (Vars.z j) % 2) +
        Finsupp.single Vars.u (2 * (j + 1) * (m (Vars.z j) / 2))) (1 : k) =
        X (Vars.z j) ^ (m (Vars.z j) % 2) * X Vars.u ^ (2 * (j + 1) * (m (Vars.z j) / 2)) by
      rw [X_pow_eq_monomial, X_pow_eq_monomial, monomial_mul, one_mul],
      ← X_pow_eq_monomial, map_mul, map_pow, map_pow, map_pow]
    have hrel : Ideal.Quotient.mk (Stacks.WeightedQuotient.relationIdeal (relation k))
        (X (Vars.z j)) ^ 2 =
        Ideal.Quotient.mk (Stacks.WeightedQuotient.relationIdeal (relation k))
          (X Vars.u) ^ (2 * (j + 1)) := (uGen_pow_eq_zGen_sq k j).symm
    conv_rhs => rw [← Nat.mod_add_div (m (Vars.z j)) 2, pow_add, pow_mul, hrel, ← pow_mul]
  | u => rfl
  | v => rfl

/-- **The normal form represents the same class.** -/
theorem mk_normalForm (p : MvPolynomial Vars k) :
    Ideal.Quotient.mk (Stacks.WeightedQuotient.relationIdeal (relation k)) (normalForm k p) =
      Ideal.Quotient.mk (Stacks.WeightedQuotient.relationIdeal (relation k)) p := by
  have := linearMap_ext k
    (φ := (Ideal.Quotient.mkₐ k (Stacks.WeightedQuotient.relationIdeal (relation k))).toLinearMap
      ∘ₗ normalForm k)
    (ψ := (Ideal.Quotient.mkₐ k (Stacks.WeightedQuotient.relationIdeal (relation k))).toLinearMap)
    fun m => by
      simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk,
        normalForm_monomial]
      exact mk_monomial_reducedExp k m
  exact LinearMap.congr_fun this p

end NormalForm

/-! ### `U` and `V` in `A` -/

section Regular

/-- A variable whose multiplication commutes with the normal form is a nonzerodivisor of `A`. -/
private theorem eq_zero_of_gen_mul_eq_zero (i : Vars)
    (hi : ∀ p, normalForm k (X i * p) = X i * normalForm k p) {a : ring k}
    (h : Stacks.WeightedQuotient.gen (relation k) i * a = 0) : a = 0 := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  have hp : X i * p ∈ Stacks.WeightedQuotient.relationIdeal (relation k) :=
    Ideal.Quotient.eq_zero_iff_mem.mp (by rw [map_mul]; exact h)
  have h0 := normalForm_eq_zero_of_mem k hp
  rw [hi, mul_eq_zero, or_iff_right (X_ne_zero _)] at h0
  rw [← mk_normalForm, h0, map_zero]

/-- **`U` is a nonzerodivisor of `A`.** -/
theorem eq_zero_of_uGen_mul_eq_zero {a : ring k} (h : uGen k * a = 0) : a = 0 :=
  eq_zero_of_gen_mul_eq_zero k Vars.u (normalForm_X_u_mul k) h

/-- **`V` is a nonzerodivisor of `A`.** -/
theorem eq_zero_of_vGen_mul_eq_zero {a : ring k} (h : vGen k * a = 0) : a = 0 :=
  eq_zero_of_gen_mul_eq_zero k Vars.v (normalForm_X_v_mul k) h

/-- **`U^m b = V^l a` forces `V^l ∣ b` in `A`.** -/
theorem exists_eq_vGen_pow_mul {a b : ring k} {m l : ℕ} (h : uGen k ^ m * b = vGen k ^ l * a) :
    ∃ c, b = vGen k ^ l * c := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective b
  have hmem : X Vars.u ^ m * q - X Vars.v ^ l * p ∈
      Stacks.WeightedQuotient.relationIdeal (relation k) := by
    rw [← Ideal.Quotient.eq, map_mul, map_mul, map_pow, map_pow]
    exact h
  have h0 := normalForm_eq_zero_of_mem k hmem
  rw [map_sub, normalForm_X_u_pow_mul, normalForm_X_v_pow_mul, sub_eq_zero] at h0
  have hdvd : (X Vars.v : MvPolynomial Vars k) ^ l ∣ X Vars.u ^ m * normalForm k q :=
    ⟨_, h0⟩
  have hnd : ¬ (X Vars.v : MvPolynomial Vars k) ∣ X Vars.u ^ m := by
    rw [X_pow_eq_monomial, X_dvd_monomial]
    simp
  obtain ⟨r, hr⟩ := X_prime.pow_dvd_of_dvd_mul_left l hnd hdvd
  refine ⟨Ideal.Quotient.mk _ r, ?_⟩
  rw [← mk_normalForm, hr, map_mul, map_pow]
  rfl

end Regular

/-! ### The graded pieces are finite-dimensional -/

section FiniteGrading

/-- The finitely many variables of weight at most `n`. -/
def lowVars (n : ℕ) : Finset Vars := {Vars.u, Vars.v} ∪ (Finset.range n).image Vars.z

/-- For `n ≥ 1`, every variable of weight at most `n` is among `lowVars n`. -/
theorem mem_lowVars_of_weight_le {n : ℕ} {i : Vars} (_hn : 1 ≤ n) (h : weight i ≤ n) :
    i ∈ lowVars n := by
  cases i with
  | u => simp [lowVars]
  | v => simp [lowVars]
  | z j =>
    simp only [weight] at h
    simp only [lowVars, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
      Finset.mem_image, Finset.mem_range, reduceCtorEq, false_or, Vars.z.injEq]
    exact ⟨j, by omega, rfl⟩

/-- Every variable has positive weight. -/
theorem weight_ne_zero (i : Vars) : weight i ≠ 0 := by
  cases i <;> simp [weight]

/-- **Finitely many monomials have a given weighted degree**, although there are infinitely many
variables: only finitely many of them have weight at most `n`. -/
theorem finite_weight_eq (n : ℕ) :
    {d : Vars →₀ ℕ | Finsupp.weight weight d = n}.Finite := by
  classical
  refine (Set.finite_Iic (∑ i ∈ lowVars n, Finsupp.single i n)).subset fun d hd => ?_
  simp only [Set.mem_setOf_eq] at hd
  simp only [Set.mem_Iic, Finsupp.le_def]
  intro i
  by_cases hi : d i = 0
  · rw [hi]; exact Nat.zero_le _
  have hwi : weight i ≤ n := hd ▸ Finsupp.le_weight_of_ne_zero' weight hi
  have hdi : d i ≤ n := hd ▸ Finsupp.le_weight weight (weight_ne_zero i) d
  have hn : 1 ≤ n := le_trans (Nat.one_le_iff_ne_zero.mpr (weight_ne_zero i)) hwi
  rw [Finsupp.finset_sum_apply, Finset.sum_eq_single i]
  · simpa using hdi
  · intro b _ hb
    exact Finsupp.single_eq_of_ne hb.symm
  · intro h
    exact absurd (mem_lowVars_of_weight_le hn hwi) h

/-- **Every graded piece of `A` is finite-dimensional over `k`.** -/
instance finite_grading (n : ℕ) : Module.Finite k (grading k n) := by
  have hS := (finite_weight_eq n).to_subtype
  have hW : Module.Finite k (MvPolynomial.weightedHomogeneousSubmodule k weight n) := by
    rw [MvPolynomial.weightedHomogeneousSubmodule_eq_finsupp_supported]
    exact Module.Finite.equiv (AddMonoidAlgebra.supportedEquivFinsupp _).symm
  exact Module.Finite.map _ _

end FiniteGrading

/-! ### The chart `D₊(V)` is not Noetherian -/

section Tangent

/-- The tangent vector `U = 0`, `V = 1`, `Z_{i+1} = δ_{ij} ε` of `k[U, V, Z₁, …]`, with values in
the dual numbers `k[ε]`. -/
def tangentPoint (j : ℕ) : Vars → DualNumber k
  | .u => 0
  | .v => 1
  | .z i => if i = j then DualNumber.eps else 0

/-- Evaluation at `tangentPoint`, a ring map `k[U, V, Z₁, …] → k[ε]`. -/
def tangentPolyHom (j : ℕ) : MvPolynomial Vars k →+* DualNumber k :=
  MvPolynomial.eval₂Hom (algebraMap k (DualNumber k)) (tangentPoint k j)

/-- Every relation vanishes at `tangentPoint`. -/
theorem tangentPolyHom_relation (j i : ℕ) : tangentPolyHom k j (relation k i) = 0 := by
  simp only [tangentPolyHom, relation, map_sub, map_pow, MvPolynomial.eval₂Hom_X',
    tangentPoint]
  split_ifs <;> simp [pow_two, DualNumber.eps_mul_eps]

/-- The tangent vector, as a ring map `A → k[ε]`. -/
def tangentRingHom (j : ℕ) : ring k →+* DualNumber k :=
  Ideal.Quotient.lift _ (tangentPolyHom k j) fun a ha => by
    obtain ⟨c, rfl⟩ := Finsupp.mem_ideal_span_range_iff_exists_finsupp.mp ha
    simp [Finsupp.sum, map_sum, tangentPolyHom_relation]

/-- The tangent vector takes the value `1` on `V`. -/
theorem tangentRingHom_vGen (j : ℕ) : tangentRingHom k j (vGen k) = 1 := by
  simp [tangentRingHom, vGen, Stacks.WeightedQuotient.gen, tangentPolyHom, tangentPoint]

/-- The `j`-th tangent vector takes the value `δ_{ij} ε` on `Z_{i+1}`. -/
theorem tangentRingHom_zGen (j i : ℕ) :
    tangentRingHom k j (zGen k i) = if i = j then DualNumber.eps else 0 := by
  simp [tangentRingHom, zGen, Stacks.WeightedQuotient.gen, tangentPolyHom, tangentPoint]

/-- The tangent vectors all lie over one `k`-point of `A`. -/
theorem fst_comp_tangentRingHom (j : ℕ) :
    (TrivSqZeroExt.fstHom k k k).toRingHom.comp (tangentRingHom k j) =
      (TrivSqZeroExt.fstHom k k k).toRingHom.comp (tangentRingHom k 0) := by
  refine Ideal.Quotient.ringHom_ext (MvPolynomial.ringHom_ext (fun r => ?_) fun i => ?_)
  · simp [tangentRingHom, tangentPolyHom]
  · cases i with
    | z i => simp [tangentRingHom, tangentPolyHom, tangentPoint]; split_ifs <;> simp
    | _ => simp [tangentRingHom, tangentPolyHom, tangentPoint]

/-- The tangent vector, extended to the degree-zero localization `A_{(V)}`. -/
def tangentAway (j : ℕ) : HomogeneousLocalization.Away (grading k) (vGen k) →+* DualNumber k :=
  (IsLocalization.Away.lift (S := Localization.Away (vGen k)) (vGen k)
    (g := tangentRingHom k j) (by rw [tangentRingHom_vGen]; exact isUnit_one)).comp
    (algebraMap _ _)

/-- The tangent vectors on `A_{(V)}` all lie over one `k`-point. -/
theorem fst_tangentAway (j : ℕ) (r : HomogeneousLocalization.Away (grading k) (vGen k)) :
    (tangentAway k j r).fst = (tangentAway k 0 r).fst := by
  have h : (TrivSqZeroExt.fstHom k k k).toRingHom.comp
        (IsLocalization.Away.lift (S := Localization.Away (vGen k)) (vGen k)
          (g := tangentRingHom k j) (by rw [tangentRingHom_vGen]; exact isUnit_one)) =
      (TrivSqZeroExt.fstHom k k k).toRingHom.comp
        (IsLocalization.Away.lift (S := Localization.Away (vGen k)) (vGen k)
          (g := tangentRingHom k 0) (by rw [tangentRingHom_vGen]; exact isUnit_one)) := by
    refine IsLocalization.ringHom_ext (Submonoid.powers (vGen k)) ?_
    rw [RingHom.comp_assoc, RingHom.comp_assoc, IsLocalization.Away.lift_comp,
      IsLocalization.Away.lift_comp, fst_comp_tangentRingHom]
  exact congrArg (fun φ : Localization.Away (vGen k) →+* k => φ (algebraMap _ _ r)) h

/-- The degree-zero fraction `Z_{i+1} / V^{i+1}` of `A_{(V)}`. -/
def zFraction (i : ℕ) : HomogeneousLocalization.Away (grading k) (vGen k) :=
  HomogeneousLocalization.Away.mk (grading k) (vGen_mem k) (i + 1) (zGen k i)
    (by simpa using zGen_mem k i)

/-- The `j`-th tangent vector takes the value `δ_{ij} ε` on `Z_{i+1} / V^{i+1}`. -/
theorem tangentAway_zFraction (j i : ℕ) :
    tangentAway k j (zFraction k i) = if i = j then DualNumber.eps else 0 := by
  rw [← tangentRingHom_zGen]
  have hunit : IsUnit (tangentRingHom k j (vGen k)) := by
    rw [tangentRingHom_vGen]; exact isUnit_one
  have hspec := congrArg (IsLocalization.Away.lift (S := Localization.Away (vGen k)) (vGen k)
    (g := tangentRingHom k j) hunit)
    (IsLocalization.mk'_spec (Localization.Away (vGen k)) (zGen k i)
      (⟨vGen k ^ (i + 1), i + 1, rfl⟩ : Submonoid.powers (vGen k)))
  rw [map_mul, IsLocalization.Away.lift_eq, IsLocalization.Away.lift_eq, map_pow,
    tangentRingHom_vGen, one_pow, mul_one] at hspec
  simp only [tangentAway, RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply,
    zFraction, HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk']
  exact hspec

/-- **The degree-zero localization `A_{(V)}` is not Noetherian.** The tangent vectors
`tangentAway j` at the point `t = t_d = 0` are independent: the `j`-th one takes the value
`δ_{ij} ε` on `Z_{i+1} / V^{i+1}`. -/
theorem not_isNoetherianRing_away :
    ¬ IsNoetherianRing (HomogeneousLocalization.Away (grading k) (vGen k)) :=
  Stacks.DualNumberTangents.not_isNoetherianRing
    ((TrivSqZeroExt.fstHom k k k).toRingHom.comp (tangentAway k 0)) (tangentAway k)
    (fun j r => fst_tangentAway k j r) (zFraction k)
    (fun i => by
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        TrivSqZeroExt.fstHom_apply, tangentAway_zFraction]
      split_ifs <;> simp)
    (fun i j => by rw [tangentAway_zFraction]; split_ifs <;> simp)

end Tangent

/-- **The standard open of `Z_d` is the standard open of `U`**, because `Z_d² = U^{2d}`. -/
public theorem basicOpen_zGen_eq_basicOpen_uGen (j : ℕ) :
    Proj.basicOpen (grading k) (zGen k j) = Proj.basicOpen (grading k) (uGen k) := by
  rw [← Proj.basicOpen_pow (grading k) (zGen k j) 2 two_pos, ← uGen_pow_eq_zGen_sq k j,
    Proj.basicOpen_pow (grading k) (uGen k) (2 * (j + 1)) (by positivity)]

/-- **`X = Proj A` is covered by the two standard opens `D₊(U)` and `D₊(V)`.** -/
@[stacks 01VO "the two-chart cover of the example"]
public theorem sup_basicOpen_eq_top :
    Proj.basicOpen (grading k) (uGen k) ⊔ Proj.basicOpen (grading k) (vGen k) = ⊤ := by
  have hcover : (⨆ i : Vars, Proj.basicOpen (grading k)
      (Stacks.WeightedQuotient.gen (relation k) i)) = ⊤ :=
    Proj.iSup_basicOpen_eq_top' (grading k) (Stacks.WeightedQuotient.gen (relation k))
      (fun i => ⟨weight i, Stacks.WeightedQuotient.gen_mem_grading weight (relation k) i⟩)
      (Stacks.WeightedQuotient.adjoin_range_gen_eq_top weight (relation k))
  refine top_unique (hcover.ge.trans (iSup_le fun i => ?_))
  cases i with
  | u => exact le_sup_left
  | v => exact le_sup_right
  | z j => exact (basicOpen_zGen_eq_basicOpen_uGen k j).le.trans le_sup_left

/-- Every point of `X` lies in the standard open of a degree-one element, namely of `U` or of
`V`. -/
public theorem exists_mem_basicOpen_degreeOne (x : ProjectiveSpectrum.top (grading k)) :
    ∃ g ∈ grading k 1, x ∈ ProjectiveSpectrum.basicOpen (grading k) g := by
  have hx : x ∈ Proj.basicOpen (grading k) (uGen k) ⊔ Proj.basicOpen (grading k) (vGen k) := by
    rw [sup_basicOpen_eq_top]; trivial
  rcases hx with h | h
  · exact ⟨uGen k, uGen_mem k, h⟩
  · exact ⟨vGen k, vGen_mem k, h⟩

/-- **`X` is quasi-compact**: it is covered by the two affine opens `D₊(U)` and `D₊(V)`. The
algebra `A` is not of finite type over `k`, so this does not come from quasi-compactness of the
structure morphism to `Spec k`. -/
public theorem compactSpace_proj : CompactSpace (AlgebraicGeometry.Proj (grading k)) :=
  Stacks.ProjDegreeOneCover.compactSpace_of_iSup_basicOpen_eq_top (grading k)
    (fun b : Bool => cond b (uGen k) (vGen k))
    (fun b => by cases b with
      | false => exact vGen_mem k
      | true => exact uGen_mem k)
    (by rw [iSup_bool_eq]; exact sup_basicOpen_eq_top k)

/-- **Every twist `𝒪_X(n)` is invertible**, although `A` is not generated in degree one. -/
@[stacks 01VO "invertibility of the twists on the example"]
public theorem isInvertible_twistingSheaf (n : ℤ) :
    AlgebraicGeometry.SheafOfModules.IsInvertible
      (AlgebraicGeometry.Proj (grading k)).toRingedSpace.presheaf
      (structureSheafRing (AlgebraicGeometry.Proj (grading k)).toRingedSpace).property
      (twistingSheaf (grading k) n) :=
  Stacks.AlgebraicGeometry.ProjTwistDegreeOneCover.isInvertible_twistingSheaf (grading k)
    (Stacks.ProjDegreeOneCover.degreeOneCover_of_forall_exists (grading k)
      (exists_mem_basicOpen_degreeOne k)) n

/-- **The multiplication `𝒪_X(n) ⊗ 𝒪_X(m) → 𝒪_X(n + m)` is an isomorphism**, so each `𝒪_X(n)` is
the `n`-th tensor power of `𝒪_X(1)`. -/
@[stacks 01VO "the twists are tensor powers of the first twist"]
public theorem isIso_twistMultiplicationMap (n m : ℤ) :
    IsIso (twistMultiplicationMap (grading k) n m) :=
  Stacks.AlgebraicGeometry.ProjTwistDegreeOneCover.isIso_twistMultiplicationMap (grading k)
    (Stacks.ProjDegreeOneCover.degreeOneCover_of_forall_exists (grading k)
      (exists_mem_basicOpen_degreeOne k)) n m

/-- **`𝒪_X(1)` is an ample invertible sheaf on `X = Proj A`.** -/
@[stacks 01VO "the ample invertible sheaf on the example"]
public theorem isAmple_twistingModule_one :
    @AlgebraicGeometry.Scheme.Modules.IsAmple (AlgebraicGeometry.Proj (grading k))
      (Stacks.ProjTwistSection.twistingModule (grading k) 1)
      (isInvertible_twistingSheaf k 1) :=
  Stacks.ProjDegreeOneCover.isAmple_twistingModule_one (grading k) (compactSpace_proj k)
    (exists_mem_basicOpen_degreeOne k)

/-! ### `X` is not locally of finite type over `k` -/

/-- **The structure morphism `f : X = Proj A ⟶ Spec k`**: `Proj A ⟶ Spec A₀` followed by the
spectrum of `k → A₀`. -/
public def structureMorphism :
    AlgebraicGeometry.Proj (grading k) ⟶ AlgebraicGeometry.Spec (CommRingCat.of k) :=
  AlgebraicGeometry.Proj.toSpecZero (grading k) ≫
    AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap k (grading k 0)))

/-- **`X` is not locally of finite type over `k`**: the ring `A_{(V)}` of the affine open
`D₊(V)` is not Noetherian. -/
public theorem not_locallyOfFiniteType : ¬ LocallyOfFiniteType (structureMorphism k) := by
  intro h
  have := LocallyOfFiniteType.isLocallyNoetherian (structureMorphism k)
  have hU : IsAffineOpen (Proj.basicOpen (grading k) (vGen k)) :=
    Proj.isAffineOpen_basicOpen (grading k) (vGen k) (vGen_mem k) one_pos
  have hnoeth := IsLocallyNoetherian.component_noetherian (X := AlgebraicGeometry.Proj (grading k))
    ⟨_, hU⟩
  exact not_isNoetherianRing_away k (isNoetherianRing_of_ringEquiv _
    (Proj.basicOpenIsoAway (grading k) (vGen k) (vGen_mem k)
      one_pos).commRingCatIsoToRingEquiv.symm)

/-! ### The global sections of the twists are finite-dimensional -/

section GlobalSections

open Stacks.ProjectiveCohomology (sectionsTwistEquivAwayGrading mem_awayGrading
  coe_sectionsTwistEquivAwayGrading_map_homOfLE)
open AlgebraicGeometry.ProjectiveSpectrum.Proj (twistGrading integerGrading)
open _root_.ProjectiveSpectrum (moduleRestrictionMaps)

/-- `UV` has degree two. -/
theorem uvGen_mem : uGen k * vGen k ∈ grading k (1 + 1) :=
  SetLike.mul_mem_graded (uGen_mem k) (vGen_mem k)

/-- Every power of a nonzerodivisor `g` of `A` is a nonzerodivisor. -/
private theorem eq_zero_of_pow_mul_eq_zero {g : ring k} (hg : ∀ a, g * a = 0 → a = 0) {a : ring k}
    (N : ℕ) (h : g ^ N * a = 0) : a = 0 := by
  induction N with
  | zero => simpa using h
  | succ N ih =>
    rw [pow_succ', mul_assoc] at h
    exact ih (hg _ h)

/-- Every power of `U` is a nonzerodivisor of `A`. -/
theorem eq_zero_of_uGen_pow_mul_eq_zero {a : ring k} (N : ℕ) (h : uGen k ^ N * a = 0) :
    a = 0 :=
  eq_zero_of_pow_mul_eq_zero k (fun _ => eq_zero_of_uGen_mul_eq_zero k) N h

/-- Every power of `V` is a nonzerodivisor of `A`. -/
theorem eq_zero_of_vGen_pow_mul_eq_zero {a : ring k} (N : ℕ) (h : vGen k ^ N * a = 0) :
    a = 0 :=
  eq_zero_of_pow_mul_eq_zero k (fun _ => eq_zero_of_vGen_mul_eq_zero k) N h

/-- Every power of `UV` is a nonzerodivisor of `A`. -/
theorem eq_zero_of_uvGen_pow_mul_eq_zero {a : ring k} (N : ℕ)
    (h : (uGen k * vGen k) ^ N * a = 0) : a = 0 := by
  rw [mul_pow, mul_assoc] at h
  exact eq_zero_of_vGen_pow_mul_eq_zero k N (eq_zero_of_uGen_pow_mul_eq_zero k N h)

/-- An element of the degree-`i` part of the `ℤ`-grading of `A` lies in `A_i` with `i ≥ 0`, or
is zero. -/
theorem mem_of_mem_integerGrading {i : ℤ} {b : ring k}
    (h : b ∈ integerGrading (S := ring k) (grading k) i) :
    (0 ≤ i ∧ b ∈ grading k i.toNat) ∨ b = 0 := by
  unfold integerGrading at h
  split_ifs at h with hi
  · exact Or.inl ⟨hi, h⟩
  · exact Or.inr (by simpa using h)

/-- The action of `r ∈ A` on a fraction `a / s` of `A_g` is `(r a) / s`. -/
theorem algebraMap_smul_mk {g : ring k} (r a : ring k) (s : Submonoid.powers g) :
    algebraMap (ring k) (Localization.Away g) r • (LocalizedModule.mk a s :
      LocalizedModule (Submonoid.powers g) (ring k)) = LocalizedModule.mk (r * a) s := by
  rw [algebraMap_smul, LocalizedModule.smul'_mk, smul_eq_mul]

variable (n : ℤ)

/-- The value on the standard open `D₊(f)` of a global section of `𝒪_X(n)`, read as a fraction
in `A_f`. -/
def chartValue {f : ring k} {d : ℕ} (hf : f ∈ grading k d) (hd : 0 < d)
    (s : (twistingSheaf (grading k) n).val.obj (op ⊤)) :
    LocalizedModule (Submonoid.powers f) (ring k) :=
  (sectionsTwistEquivAwayGrading (grading k) hf hd n
    (((twistingSheaf (grading k) n).val.map
      (homOfLE (le_top : ProjectiveSpectrum.basicOpen (grading k) f ≤ ⊤)).op).hom s) :
    LocalizedModule (Submonoid.powers f) (ring k))

/-- **The values of a global section on `D₊(U)` and on `D₊(V)` agree on `D₊(UV)`.** -/
theorem localizedMap_chartValue_u_eq_v (s : (twistingSheaf (grading k) n).val.obj (op ⊤)) :
    (moduleRestrictionMaps (grading k) (twistGrading (S := ring k) (grading k) n) (uGen k)
        (uGen k * vGen k) ⟨1, one_pos, uGen_mem k⟩ ⟨1 + 1, by omega, uvGen_mem k⟩
        (ProjectiveSpectrum.basicOpen_mul_le_left _ _ _)).localizedMap
        (chartValue k n (uGen_mem k) one_pos s) =
      (moduleRestrictionMaps (grading k) (twistGrading (S := ring k) (grading k) n) (vGen k)
        (uGen k * vGen k) ⟨1, one_pos, vGen_mem k⟩ ⟨1 + 1, by omega, uvGen_mem k⟩
        (ProjectiveSpectrum.basicOpen_mul_le_right _ _ _)).localizedMap
        (chartValue k n (vGen_mem k) one_pos s) := by
  have hres : ∀ {f : ring k} (hfg : ProjectiveSpectrum.basicOpen (grading k) (uGen k * vGen k) ≤
      ProjectiveSpectrum.basicOpen (grading k) f),
      ((twistingSheaf (grading k) n).val.map (homOfLE hfg).op).hom
        (((twistingSheaf (grading k) n).val.map
          (homOfLE (le_top : ProjectiveSpectrum.basicOpen (grading k) f ≤ ⊤)).op).hom s) =
      ((twistingSheaf (grading k) n).val.map
          (homOfLE
            (le_top : ProjectiveSpectrum.basicOpen (grading k) (uGen k * vGen k) ≤ ⊤)).op).hom
        s := by
    intro f hfg
    exact ((twistingSheaf (grading k) n).val.map_comp_apply (homOfLE le_top).op
      (homOfLE hfg).op s).symm.trans ((twistingSheaf (grading k) n).val.congr_map_apply rfl s)
  have h1 := coe_sectionsTwistEquivAwayGrading_map_homOfLE (grading k) (uGen_mem k) one_pos
    (uvGen_mem k) (by omega) (ProjectiveSpectrum.basicOpen_mul_le_left _ _ _) n
    (((twistingSheaf (grading k) n).val.map
      (homOfLE (le_top : ProjectiveSpectrum.basicOpen (grading k) (uGen k) ≤ ⊤)).op).hom s)
  have h2 := coe_sectionsTwistEquivAwayGrading_map_homOfLE (grading k) (vGen_mem k) one_pos
    (uvGen_mem k) (by omega) (ProjectiveSpectrum.basicOpen_mul_le_right _ _ _) n
    (((twistingSheaf (grading k) n).val.map
      (homOfLE (le_top : ProjectiveSpectrum.basicOpen (grading k) (vGen k) ≤ ⊤)).op).hom s)
  have e1 := congrArg (fun x => (sectionsTwistEquivAwayGrading (grading k) (uvGen_mem k)
    (by omega) n x : LocalizedModule (Submonoid.powers (uGen k * vGen k)) (ring k)))
    (hres (ProjectiveSpectrum.basicOpen_mul_le_left (grading k) (uGen k) (vGen k)))
  have e2 := congrArg (fun x => (sectionsTwistEquivAwayGrading (grading k) (uvGen_mem k)
    (by omega) n x : LocalizedModule (Submonoid.powers (uGen k * vGen k)) (ring k)))
    (hres (ProjectiveSpectrum.basicOpen_mul_le_right (grading k) (uGen k) (vGen k)))
  exact h1.symm.trans ((e1.trans e2.symm).trans h2)

/-- **A global section of `𝒪_X(n)` written as `a / U^m` on `D₊(U)` and as `b / V^l` on `D₊(V)`
satisfies `V^l a = U^m b` in `A`.** -/
theorem vGen_pow_mul_eq_uGen_pow_mul (s : (twistingSheaf (grading k) n).val.obj (op ⊤))
    {m l : ℕ} {a b : ring k}
    (hx : chartValue k n (uGen_mem k) one_pos s =
      LocalizedModule.mk a (⟨uGen k ^ m, m, rfl⟩ : Submonoid.powers (uGen k)))
    (hy : chartValue k n (vGen_mem k) one_pos s =
      LocalizedModule.mk b (⟨vGen k ^ l, l, rfl⟩ : Submonoid.powers (vGen k))) :
    vGen k ^ l * a = uGen k ^ m * b := by
  have hc1 := Stacks.AlgebraicGeometry.ProjChartGradedThetaBuild.localizedMap_mk_cancel
    (grading k) one_pos (by omega) (uGen_mem k) (uvGen_mem k)
    (ProjectiveSpectrum.basicOpen_mul_le_left _ _ _) n m a
  have hc2 := Stacks.AlgebraicGeometry.ProjChartGradedThetaBuild.localizedMap_mk_cancel
    (grading k) one_pos (by omega) (vGen_mem k) (uvGen_mem k)
    (ProjectiveSpectrum.basicOpen_mul_le_right _ _ _) n l b
  have hK := localizedMap_chartValue_u_eq_v k n s
  rw [hx, hy] at hK
  have hmk : (LocalizedModule.mk (vGen k ^ l * a) 1 :
      LocalizedModule (Submonoid.powers (uGen k * vGen k)) (ring k)) =
      LocalizedModule.mk (uGen k ^ m * b) 1 := by
    rw [← algebraMap_smul_mk, ← algebraMap_smul_mk, ← hc1, ← hc2, hK, smul_smul, smul_smul,
      mul_comm ((algebraMap (ring k) (Localization.Away (uGen k * vGen k))) (vGen k ^ l))]
  obtain ⟨c, hc⟩ := LocalizedModule.mk_eq.mp hmk
  obtain ⟨N, hN⟩ := c.2
  have h0 : (uGen k * vGen k) ^ N * (vGen k ^ l * a - uGen k ^ m * b) = 0 := by
    simp only [one_smul, Submonoid.smul_def, smul_eq_mul, ← hN] at hc
    rw [mul_sub, hc, sub_self]
  exact sub_eq_zero.mp (eq_zero_of_uvGen_pow_mul_eq_zero k N h0)

/-- The value of a global section of `𝒪_X(n)` on the standard open `D₊(f)` of a degree-one
element `f` is a fraction `a / f^m` with `a` homogeneous of degree `m + n`. -/
theorem exists_chartValue_eq (s : (twistingSheaf (grading k) n).val.obj (op ⊤)) {f : ring k}
    (hf : f ∈ grading k 1) :
    ∃ (m : ℕ) (a : ring k), a ∈ integerGrading (S := ring k) (grading k) ((m * 1 : ℕ) + n) ∧
      chartValue k n hf one_pos s =
        LocalizedModule.mk a (⟨f ^ m, m, rfl⟩ : Submonoid.powers f) :=
  (Stacks.ProjectiveCohomology.mem_awayGrading (grading k)).mp
    (sectionsTwistEquivAwayGrading (grading k) hf one_pos n
      (((twistingSheaf (grading k) n).val.map
        (homOfLE (le_top : ProjectiveSpectrum.basicOpen (grading k) f ≤ ⊤)).op).hom s)).2

/-- **The value of a global section of `𝒪_X(n)` on `D₊(V)` is a homogeneous element of `A` of
degree `n`, read as the fraction `c / 1`.** For `n < 0` the value is `0`. -/
theorem exists_chartValue_v_eq_mk_one (s : (twistingSheaf (grading k) n).val.obj (op ⊤)) :
    ∃ c ∈ grading k n.toNat, chartValue k n (vGen_mem k) one_pos s = LocalizedModule.mk c 1 := by
  classical
  obtain ⟨m, a, -, hx⟩ := exists_chartValue_eq k n s (uGen_mem k)
  obtain ⟨l, b, hb, hy⟩ := exists_chartValue_eq k n s (vGen_mem k)
  have key := vGen_pow_mul_eq_uGen_pow_mul k n s hx hy
  obtain ⟨c, hc⟩ := exists_eq_vGen_pow_mul k key.symm
  have hy' : chartValue k n (vGen_mem k) one_pos s = LocalizedModule.mk c 1 := by
    rw [hy, hc, LocalizedModule.mk_eq]
    exact ⟨1, by simp [Submonoid.smul_def, mul_comm]⟩
  have hvl : vGen k ^ l ∈ grading k l := by simpa using SetLike.pow_mem_graded l (vGen_mem k)
  have hzero : b = 0 → ∃ c ∈ grading k n.toNat,
      chartValue k n (vGen_mem k) one_pos s = LocalizedModule.mk c 1 := by
    intro hb0
    have hc0 : c = 0 := eq_zero_of_vGen_pow_mul_eq_zero k l (hc ▸ hb0)
    exact ⟨0, zero_mem _, by rw [hy', hc0]⟩
  rcases mem_of_mem_integerGrading k hb with ⟨hnn, hb'⟩ | hb0
  · have hbdec : b = (DirectSum.decompose (grading k) (vGen k ^ l * c)
        ((((l * 1 : ℕ) : ℤ) + n).toNat) : ring k) := by
      rw [← hc, DirectSum.decompose_of_mem_same _ hb']
    by_cases hn : 0 ≤ n
    · have hidx : (((l * 1 : ℕ) : ℤ) + n).toNat = l + n.toNat := by omega
      rw [hidx, DirectSum.coe_decompose_mul_add_of_left_mem _ hvl] at hbdec
      have hcc : c = (DirectSum.decompose (grading k) c n.toNat : ring k) := by
        refine sub_eq_zero.mp (eq_zero_of_vGen_pow_mul_eq_zero k l ?_)
        rw [mul_sub, ← hc, ← hbdec, sub_self]
      exact ⟨c, hcc ▸ SetLike.coe_mem _, hy'⟩
    · have hidx : ¬ l ≤ (((l * 1 : ℕ) : ℤ) + n).toNat := by omega
      rw [DirectSum.coe_decompose_mul_of_left_mem_of_not_le _ hvl hidx] at hbdec
      exact hzero hbdec
  · exact hzero hb0

/-- **A global section of `𝒪_X(n)` vanishing on `D₊(V)` vanishes.** -/
theorem eq_zero_of_chartValue_v_eq_zero
    (s : Γ(Stacks.ProjTwistSection.twistingModule (grading k) n, ⊤))
    (h : chartValue k n (vGen_mem k) one_pos s = 0) : s = 0 := by
  obtain ⟨m, a, -, hx⟩ := exists_chartValue_eq k n s (uGen_mem k)
  obtain ⟨l, b, -, hy⟩ := exists_chartValue_eq k n s (vGen_mem k)
  have hb : b = 0 := by
    rw [hy, ← LocalizedModule.zero_mk 1, LocalizedModule.mk_eq] at h
    obtain ⟨c, hc⟩ := h
    obtain ⟨N, hN⟩ := c.2
    simp only [one_smul, smul_zero, Submonoid.smul_def, smul_eq_mul, ← hN] at hc
    exact eq_zero_of_vGen_pow_mul_eq_zero k N hc
  have ha : a = 0 := by
    have key := vGen_pow_mul_eq_uGen_pow_mul k n s hx hy
    rw [hb, mul_zero] at key
    exact eq_zero_of_vGen_pow_mul_eq_zero k l key
  have hu : chartValue k n (uGen_mem k) one_pos s = 0 := by
    rw [hx, ha, LocalizedModule.zero_mk]
  have hres : ∀ {f : ring k} (hf : f ∈ grading k 1), chartValue k n hf one_pos s = 0 →
      ((twistingSheaf (grading k) n).val.map
        (homOfLE (le_top : ProjectiveSpectrum.basicOpen (grading k) f ≤ ⊤)).op).hom s = 0 := by
    intro f hf h0
    have h1 : sectionsTwistEquivAwayGrading (grading k) hf one_pos n
        (((twistingSheaf (grading k) n).val.map
          (homOfLE (le_top : ProjectiveSpectrum.basicOpen (grading k) f ≤ ⊤)).op).hom s) = 0 :=
      Subtype.ext h0
    exact (map_eq_zero_iff _
      (sectionsTwistEquivAwayGrading (grading k) hf one_pos n).injective).mp h1
  let W : Bool → (AlgebraicGeometry.Proj (grading k)).Opens := fun b =>
    cond b (Proj.basicOpen (grading k) (uGen k)) (Proj.basicOpen (grading k) (vGen k))
  have hcov : (⊤ : (AlgebraicGeometry.Proj (grading k)).Opens) ≤ ⨆ b, W b := by
    rw [iSup_bool_eq]
    exact (sup_basicOpen_eq_top k).ge
  refine TopCat.Sheaf.eq_of_locally_eq'
    (⟨(Stacks.ProjTwistSection.twistingModule (grading k) n).presheaf,
      (Stacks.ProjTwistSection.twistingModule (grading k) n).isSheaf⟩ :
      TopCat.Sheaf Ab (AlgebraicGeometry.Proj (grading k))) W ⊤ (fun b => homOfLE le_top) hcov
    s 0 fun b => ?_
  rw [map_zero]
  cases b with
  | true => exact hres (uGen_mem k) hu
  | false => exact hres (vGen_mem k) h

/-- The ring map `k → Γ(X, 𝒪_X)` of the structure morphism. -/
def structureScalar : k →+* Γ(AlgebraicGeometry.Proj (grading k), ⊤) :=
  ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ (structureMorphism k).appTop).hom

/-- **The structure morphism on the sections of `D₊(V)`**: a scalar `c ∈ k` restricts to the
constant fraction `c / 1` of `A_{(V)}`. -/
theorem res_structureScalar (c : k) :
    (AlgebraicGeometry.Proj (grading k)).presheaf.map
        (homOfLE (le_top : Proj.basicOpen (grading k) (vGen k) ≤ ⊤)).op (structureScalar k c) =
      (Proj.awayToSection (grading k) (vGen k)).hom
        (HomogeneousLocalization.fromZeroRingHom (grading k) (Submonoid.powers (vGen k))
          (algebraMap k (grading k 0) c)) := by
  have e : Proj.basicOpen (grading k) (vGen k) ≤ structureMorphism k ⁻¹ᵁ ⊤ := le_top
  have e' : Proj.basicOpen (grading k) (vGen k) ≤ Proj.toSpecZero (grading k) ⁻¹ᵁ ⊤ := le_top
  have h1 : (structureMorphism k).appTop ≫ (AlgebraicGeometry.Proj (grading k)).presheaf.map
      (homOfLE (le_top : Proj.basicOpen (grading k) (vGen k) ≤ ⊤)).op =
      (structureMorphism k).appLE ⊤ _ e := rfl
  have h2 := Stacks.BaseSectionDictionary.toSpecZero_appLE_basicOpen (grading k) (vGen_mem k)
    one_pos e'
  have h3 : (structureMorphism k).appLE ⊤ _ e =
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap k (grading k 0)))).appTop ≫
        (Proj.toSpecZero (grading k)).appLE ⊤ _ e' :=
    Scheme.Hom.comp_appLE _ _ ⊤ _ e
  have h4 := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap k (grading k 0)))
  have key : (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ (structureMorphism k).appTop ≫
      (AlgebraicGeometry.Proj (grading k)).presheaf.map
        (homOfLE (le_top : Proj.basicOpen (grading k) (vGen k) ≤ ⊤)).op =
      CommRingCat.ofHom (algebraMap k (grading k 0)) ≫
        CommRingCat.ofHom (HomogeneousLocalization.fromZeroRingHom (grading k)
          (Submonoid.powers (vGen k))) ≫ Proj.awayToSection (grading k) (vGen k) := by
    rw [h1, h3, h2, reassoc_of% h4, Iso.inv_hom_id_assoc]
  exact congrArg (fun φ => φ.hom c) key

/-- **The value on `D₊(V)` is `k`-linear** for the action of `k` on global sections through the
structure morphism. -/
theorem chartValue_smul (c : k) (s : Γ(Stacks.ProjTwistSection.twistingModule (grading k) n, ⊤)) :
    chartValue k n (vGen_mem k) one_pos (structureScalar k c • s) =
      c • chartValue k n (vGen_mem k) one_pos s := by
  have hmap := (twistingSheaf (grading k) n).val.map_smul
    (homOfLE (le_top : ProjectiveSpectrum.basicOpen (grading k) (vGen k) ≤ ⊤)).op
    (structureScalar k c) s
  have hres := res_structureScalar k c
  have hsmul := Stacks.ProjectiveCohomology.coe_sectionsTwistEquivAwayGrading_smul (grading k)
    (vGen_mem k) one_pos n (HomogeneousLocalization.fromZeroRingHom (grading k)
      (Submonoid.powers (vGen k)) (algebraMap k (grading k 0) c))
    (((twistingSheaf (grading k) n).val.map
      (homOfLE (le_top : ProjectiveSpectrum.basicOpen (grading k) (vGen k) ≤ ⊤)).op).hom s)
  have hval : HomogeneousLocalization.val (HomogeneousLocalization.fromZeroRingHom (grading k)
      (Submonoid.powers (vGen k)) (algebraMap k (grading k 0) c)) =
      algebraMap (ring k) (Localization.Away (vGen k)) (algebraMap k (ring k) c) := by
    rw [← SetLike.GradeZero.coe_algebraMap (grading k) c]
    rfl
  obtain ⟨t, ht⟩ : ∃ t : (twistingSheaf (grading k) n).val.obj
      (op (ProjectiveSpectrum.basicOpen (grading k) (vGen k))), t =
    ((twistingSheaf (grading k) n).val.map
      (homOfLE (le_top : ProjectiveSpectrum.basicOpen (grading k) (vGen k) ≤ ⊤)).op).hom s :=
    ⟨_, rfl⟩
  have e1 : ((twistingSheaf (grading k) n).val.map
      (homOfLE (le_top : ProjectiveSpectrum.basicOpen (grading k) (vGen k) ≤ ⊤)).op).hom
        (structureScalar k c • s) =
      (ProjectiveSpectrum.Proj.awayToSection (grading k) (vGen k)).hom
        (HomogeneousLocalization.fromZeroRingHom (grading k) (Submonoid.powers (vGen k))
          (algebraMap k (grading k 0) c)) • t := by
    rw [ht]
    refine hmap.trans ?_
    exact congrArg (fun r => r • _) hres
  subst ht
  refine ((congrArg (fun x => (sectionsTwistEquivAwayGrading (grading k) (vGen_mem k) one_pos n x :
    LocalizedModule (Submonoid.powers (vGen k)) (ring k))) e1).trans hsmul).trans ?_
  refine (congrArg (fun z => z • (sectionsTwistEquivAwayGrading (grading k) (vGen_mem k)
    one_pos n (((twistingSheaf (grading k) n).val.map
      (homOfLE (le_top : ProjectiveSpectrum.basicOpen (grading k) (vGen k) ≤ ⊤)).op).hom s) :
        LocalizedModule (Submonoid.powers (vGen k)) (ring k))) hval).trans ?_
  exact (algebraMap_smul (Localization.Away (vGen k)) (algebraMap k (ring k) c) _).trans
    (algebraMap_smul (ring k) c _)

/-- The value on `D₊(V)` is additive. -/
theorem chartValue_add (s s' : Γ(Stacks.ProjTwistSection.twistingModule (grading k) n, ⊤)) :
    chartValue k n (vGen_mem k) one_pos (s + s') =
      chartValue k n (vGen_mem k) one_pos s + chartValue k n (vGen_mem k) one_pos s' := by
  have h1 := map_add ((twistingSheaf (grading k) n).val.map
      (homOfLE (le_top : ProjectiveSpectrum.basicOpen (grading k) (vGen k) ≤ ⊤)).op).hom s s'
  have h2 := map_add (sectionsTwistEquivAwayGrading (grading k) (vGen_mem k) one_pos n)
    (((twistingSheaf (grading k) n).val.map
      (homOfLE (le_top : ProjectiveSpectrum.basicOpen (grading k) (vGen k) ≤ ⊤)).op).hom s)
    (((twistingSheaf (grading k) n).val.map
      (homOfLE (le_top : ProjectiveSpectrum.basicOpen (grading k) (vGen k) ≤ ⊤)).op).hom s')
  exact (congrArg (fun x => (sectionsTwistEquivAwayGrading (grading k) (vGen_mem k) one_pos n x :
    LocalizedModule (Submonoid.powers (vGen k)) (ring k))) h1).trans (congrArg Subtype.val h2)

/-- **`Γ(X, 𝒪_X(n))` is finite-dimensional over `k`**: there is a finite family of global sections
of which every global section is a combination with coefficients from `k`, pulled back along the
structure morphism. -/
theorem exists_finset_globalSections :
    ∃ T : Finset Γ(Stacks.ProjTwistSection.twistingModule (grading k) n, ⊤),
      ∀ s : Γ(Stacks.ProjTwistSection.twistingModule (grading k) n, ⊤),
        ∃ c : Γ(Stacks.ProjTwistSection.twistingModule (grading k) n, ⊤) →
            Γ(AlgebraicGeometry.Spec (CommRingCat.of k), ⊤),
          s = ∑ t ∈ T, (structureMorphism k).appTop (c t) • t := by
  classical
  let : Module k Γ(Stacks.ProjTwistSection.twistingModule (grading k) n, ⊤) :=
    Module.compHom _ (structureScalar k)
  let ρ : Γ(Stacks.ProjTwistSection.twistingModule (grading k) n, ⊤) →ₗ[k]
      LocalizedModule (Submonoid.powers (vGen k)) (ring k) :=
    { toFun := chartValue k n (vGen_mem k) one_pos
      map_add' := chartValue_add k n
      map_smul' := fun c s => chartValue_smul k n c s }
  let Mk : ring k →ₗ[k] LocalizedModule (Submonoid.powers (vGen k)) (ring k) :=
    (LocalizedModule.mkLinearMap (Submonoid.powers (vGen k)) (ring k)).restrictScalars k
  let F : Submodule k (LocalizedModule (Submonoid.powers (vGen k)) (ring k)) :=
    (grading k n.toNat).map Mk
  have hF : ∀ s, ρ s ∈ F := by
    intro s
    obtain ⟨c, hc, hcs⟩ := exists_chartValue_v_eq_mk_one k n s
    exact ⟨c, hc, hcs.symm⟩
  let ρ' := ρ.codRestrict F hF
  have hinj : Function.Injective ρ' := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro s hs
    exact eq_zero_of_chartValue_v_eq_zero k n s (congrArg Subtype.val hs)
  have : Module.Finite k F := Module.Finite.map _ _
  have : Module.Finite k Γ(Stacks.ProjTwistSection.twistingModule (grading k) n, ⊤) :=
    Module.Finite.of_injective ρ' hinj
  obtain ⟨T, hT⟩ := (Module.Finite.fg_top :
    (⊤ : Submodule k Γ(Stacks.ProjTwistSection.twistingModule (grading k) n, ⊤)).FG)
  refine ⟨T, fun s => ?_⟩
  have hs : s ∈ Submodule.span k (T : Set _) := hT ▸ Submodule.mem_top
  obtain ⟨f, -, hf⟩ := Submodule.mem_span_finset.mp hs
  exact ⟨fun t => (Scheme.ΓSpecIso (CommRingCat.of k)).inv (f t), hf.symm⟩

end GlobalSections


/-- **The positive tensor powers of `𝒪_X(1)` are the twists**: `𝒪_X(1)^{⊗ (n+1)} ≅ 𝒪_X(n+1)`,
by induction from the multiplication isomorphisms `𝒪_X(n) ⊗ 𝒪_X(1) ≅ 𝒪_X(n + 1)` of
`isIso_twistMultiplicationMap`. -/
noncomputable def tensorPowTwistIso : (n : ℕ) →
    @Stacks.Ample.tensorPowModule (AlgebraicGeometry.Proj (grading k))
      (Stacks.ProjTwistSection.twistingModule (grading k) 1) (isInvertible_twistingSheaf k 1)
      ((n + 1 : ℕ) : ℤ) ≅ Stacks.ProjTwistSection.twistingModule (grading k) ((n + 1 : ℕ) : ℤ)
  | 0 => @Stacks.Ample.tensorPowModuleOneIso _ _ (isInvertible_twistingSheaf k 1)
  | n + 1 =>
    letI := isInvertible_twistingSheaf k 1
    eqToIso (congrArg (Stacks.Ample.tensorPowModule _ _) (by push_cast; ring)) ≪≫
      (Stacks.Ample.tensorPowModuleAddIso _ _ ((n + 1 : ℕ) : ℤ) 1).symm ≪≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor _).mapIso (tensorPowTwistIso n)).app _ ≪≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor _).obj _).mapIso
        (Stacks.Ample.tensorPowModuleOneIso _ _) ≪≫
      @asIso _ _ _ _ (twistMultiplicationMap (grading k) ((n + 1 : ℕ) : ℤ) 1)
        (isIso_twistMultiplicationMap k _ 1) ≪≫
      eqToIso (congrArg (twistingSheaf (grading k)) (by push_cast; ring))

/-! ### No power of `𝒪_X(1)` is relatively very ample -/

/-- **No twist `𝒪_X(n)` is `f`-relatively very ample for `f : X ⟶ Spec k`**, and in particular no
power `𝒪_X(1)^{⊗ n} ≅ 𝒪_X(n)` of the ample sheaf `𝒪_X(1)` is. -/
public theorem not_isRelativelyVeryAmple_twistingModule (n : ℤ) :
    ¬ @Stacks.Tag01VMVeryAmple.IsRelativelyVeryAmple _ _ (structureMorphism k)
      (Stacks.ProjTwistSection.twistingModule (grading k) n) (isInvertible_twistingSheaf k n) := by
  intro h
  obtain ⟨T, hT⟩ := exists_finset_globalSections k n
  exact not_locallyOfFiniteType k
    (@Stacks.VeryAmpleFiniteSections.locallyOfFiniteType_of_isRelativelyVeryAmple _ _
      (isAffineOpen_top _) (structureMorphism k) _ (isInvertible_twistingSheaf k n) h T hT)


/-- **No power `𝒪_X(1)^{⊗ n}` with `n ≥ 1` is `f`-relatively very ample**, for `f : X ⟶ Spec k`
the structure morphism. -/
@[stacks 01VO "no power of `𝒪_X(1)` is `f`-relatively very ample"]
public theorem not_isRelativelyVeryAmple_tensorPowModule (n : ℕ) (hn : 1 ≤ n) :
    letI := isInvertible_twistingSheaf k 1
    ¬ Stacks.Tag01VMVeryAmple.IsRelativelyVeryAmple (structureMorphism k)
      (Stacks.Ample.tensorPowModule (AlgebraicGeometry.Proj (grading k))
        (Stacks.ProjTwistSection.twistingModule (grading k) 1) (n : ℤ)) := by
  let := isInvertible_twistingSheaf k 1
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  intro h
  exact not_isRelativelyVeryAmple_twistingModule k ((m + 1 : ℕ) : ℤ)
    (@Stacks.Tag01VMVeryAmple.IsRelativelyVeryAmple.of_iso _ _ _ _ _ _
      (isInvertible_twistingSheaf k _) (tensorPowTwistIso k m) h)

/-- **`𝒪_X(1)` is `f`-ample** for the structure morphism `f : X ⟶ Spec k`. -/
@[stacks 01VO "`𝒪_X(1)` is `f`-ample"]
public theorem isRelativelyAmple_twistingModule_one :
    @Stacks.RelativeAmple.IsRelativelyAmple _ _ (structureMorphism k)
      (Stacks.ProjTwistSection.twistingModule (grading k) 1) (isInvertible_twistingSheaf k 1) :=
  (@Stacks.RelativeAmpleAffineBase.isRelativelyAmple_iff_isAmple _ _ _ (structureMorphism k) _
    (isInvertible_twistingSheaf k 1)).mpr
    ((@Stacks.AmpleBridge.isAmple_iff_isAmple _ _ (isInvertible_twistingSheaf k 1)).mpr
      (isAmple_twistingModule_one k))

end

end Stacks.ProjEvenPowerRoots

end
