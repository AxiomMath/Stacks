module

public import StacksFrontier.AlgebraicGeometry.Crystalline.CompletedDeRhamPerturbation
public import StacksFrontier.AlgebraicGeometry.Crystalline.Differentials.BidegreeFiltration
public import StacksFrontier.AlgebraicGeometry.Crystalline.Differentials.RelativePoincareSpecial
public import
  StacksFrontier.AlgebraicGeometry.Crystalline.ModuleDifferentials.CompletionLevelTransition
public import
  StacksFrontier.AlgebraicGeometry.Crystalline.Differentials.RelativeSplitDifferential.Completion

/-!
# Base-linearity and the relative contraction identity

Part of `StacksFrontier.AlgebraicGeometry.Crystalline.Differentials.RelativeSplitDifferential`,
whose module docstring explains the construction. This file contains the `B`-linearity of the
relative homotopy and of the coefficient retraction, their behaviour on coefficient degrees, the
fact that wedging with a coefficient one-form raises the coefficient degree, the relative
contraction identity `d_rel h + h d_rel + ψ ε = id`, and the `D`-module structure on the completed
forms of `D'` (`Crystalline.DividedPowerPolynomial.moduleCompletedPolynomialForms`).
-/

@[expose] public noncomputable section

open DividedPowers
open scoped TensorProduct

universe uA uB uW uM

namespace Crystalline

namespace DividedPowerPolynomial

/-! ### The relative homotopy and the coefficient retraction are linear over the base -/

section BaseLinear

variable (A : Type uA) [CommRing A] (B : DividedPowerRing.{uB}) [Algebra A B] (W : Type uW)
  [LinearOrder W]

/-- **The relative homotopy of a generator carrying a variable differential** is the Koszul
contraction of the generator's own sector `K = L + 1_J`.  This is
`Crystalline.DividedPowerPolynomial.relativeFormsHomotopy_relativeSectorMapDeg` read on the
generator, and it is the companion of
`Crystalline.DividedPowerPolynomial.relativeFormsHomotopy_decompositionGenerator_zero`, which
covers the generators carrying none. -/
theorem relativeFormsHomotopy_decompositionGenerator_succ (i j n : ℕ)
    (hij : i + (j + 1) = n + 1) (L : W →₀ ℕ) (J : Set.powersetCard W (j + 1))
    (omega : dividedPowerDifferentialForms (A := A) B.dividedPowers i) :
    relativeFormsHomotopy A B W n
        (decompositionGenerator A B W i (j + 1) (n + 1) hij L J omega) =
      relativeSectorMapDeg A B W (L + finsetMultiIndex J.val) i j n (by omega)
        (relativeSectorHomotopy A B W (L + finsetMultiIndex J.val) i j
          (sectorExteriorBasis B W (L + finsetMultiIndex J.val) (j + 1)
              (sectorLiftSubset W (L + finsetMultiIndex J.val) (j + 1) J
                (subset_support_add_finsetMultiIndex J.val L)) ⊗ₜ[(B : Type uB)] omega)) := by
  obtain rfl : i + j = n := by omega
  rw [← relativeSectorMapDeg_sectorExteriorBasis A B W i (j + 1) (i + j + 1) hij L J omega,
    relativeFormsHomotopy_relativeSectorMapDeg A B W (L + finsetMultiIndex J.val) i j (i + j) rfl]

/-- An `A`-linear map out of the forms of `P` is `B`-linear once it is on each generator of the
decomposition, whose coefficient form `B` scales. -/
private theorem map_smul_of_decompositionGenerator {N : Type*} [AddCommGroup N] [Module A N]
    [Module B N] [IsScalarTower A B N] (n : ℕ) (f : dividedPowerPolynomialForms A B W n →ₗ[A] N)
    (b : (B : Type uB))
    (h : ∀ (i j : ℕ) (hij : i + j = n) (L : W →₀ ℕ) (J : Set.powersetCard W j)
      (omega : dividedPowerDifferentialForms (A := A) B.dividedPowers i),
      f (decompositionGenerator A B W i j n hij L J (b • omega)) =
        b • f (decompositionGenerator A B W i j n hij L J omega))
    (x : dividedPowerPolynomialForms A B W n) : f (b • x) = b • f x := by
  have key : f ∘ₗ ((LinearMap.lsmul (setIndexedDividedPowerPolynomialAlgebra B W)
        (dividedPowerPolynomialForms A B W n)
        (algebraMap (B : Type uB) (setIndexedDividedPowerPolynomialAlgebra B W) b)).restrictScalars
          A) = ((LinearMap.lsmul (B : Type uB) N b).restrictScalars A) ∘ₗ f := by
    refine dividedPowerPolynomialForms_linearMap_ext A B W n ?_
    intro i j hij L J omega
    simpa only [LinearMap.comp_apply, LinearMap.coe_restrictScalars, LinearMap.lsmul_apply,
      algebraMap_smul, smul_decompositionGenerator] using h i j hij L J omega
  simpa only [LinearMap.comp_apply, LinearMap.coe_restrictScalars, LinearMap.lsmul_apply,
    algebraMap_smul] using DFunLike.congr_fun key x

/-- **The relative homotopy `h` is linear over the base ring `B`.**

On a generator carrying a variable differential the homotopy is the Koszul contraction of the
generator's own sector, and both the sector map and the sector contraction are `B`-linear in the
coefficient form; on a generator carrying none the homotopy is zero.  As for the relative
differential of `Crystalline.DividedPowerPolynomial.formsRelDifferentialAux_smul`, the linearity
is over `B` and not over `P`: the contraction of `d x_w` is a unit of `P` and does not commute
with multiplication by a variable. -/
theorem relativeFormsHomotopy_smul (n : ℕ) (b : (B : Type uB))
    (x : dividedPowerPolynomialForms A B W (n + 1)) :
    relativeFormsHomotopy A B W n (b • x) = b • relativeFormsHomotopy A B W n x := by
  refine map_smul_of_decompositionGenerator A B W (n + 1) (relativeFormsHomotopy A B W n) b ?_ x
  intro i j hij L J omega
  cases j with
  | zero =>
    obtain rfl : i = n + 1 := by omega
    rw [relativeFormsHomotopy_decompositionGenerator_zero A B W n hij L J (b • omega),
      relativeFormsHomotopy_decompositionGenerator_zero A B W n hij L J omega, smul_zero]
  | succ j =>
    rw [relativeFormsHomotopy_decompositionGenerator_succ A B W i j n hij L J (b • omega),
      TensorProduct.tmul_smul, map_smul, map_smul,
      relativeFormsHomotopy_decompositionGenerator_succ A B W i j n hij L J omega]

/-- **The coefficient retraction `ε` is linear over the base ring `B`.**

The retraction reads the single slot of the decomposition with no variable differential and the
trivial monomial, and that slot carries the coefficient form itself, on which `B` acts; every
other generator is killed. -/
theorem relativeFormsRetraction_smul (n : ℕ) (b : (B : Type uB))
    (x : dividedPowerPolynomialForms A B W n) :
    relativeFormsRetraction A B W n (b • x) = b • relativeFormsRetraction A B W n x := by
  refine map_smul_of_decompositionGenerator A B W n (relativeFormsRetraction A B W n) b ?_ x
  intro i j hij L J omega
  cases j with
  | zero =>
    obtain rfl : i = n := by omega
    by_cases hL : L = 0
    · subst hL
      rw [relativeFormsRetraction_decompositionGenerator_zero A B W i hij J (b • omega),
        relativeFormsRetraction_decompositionGenerator_zero A B W i hij J omega]
    · rw [relativeFormsRetraction_decompositionGenerator_monomial A B W i hij L hL J (b • omega),
        relativeFormsRetraction_decompositionGenerator_monomial A B W i hij L hL J omega,
        smul_zero]
  | succ j =>
    rw [relativeFormsRetraction_decompositionGenerator_succ A B W i j n hij L J (b • omega),
      relativeFormsRetraction_decompositionGenerator_succ A B W i j n hij L J omega, smul_zero]

/-! ### The coefficient degree of the comparison and of the retraction -/

/-- **The comparison `ψ` lands in the top coefficient degree.**  `ψ ω` is the generator of the
decomposition with no variable differential and the trivial monomial, which sits in bidegree
`(n, 0)`; so the coefficient-degree-`n` projection fixes it and every other one kills it. -/
theorem formsBidegreeProjection_coefficientFormsMap (n l : ℕ)
    (omega : dividedPowerDifferentialForms (A := A) B.dividedPowers n) :
    formsBidegreeProjection A B W n l (coefficientFormsMap A B W n omega) =
      if l = n then coefficientFormsMap A B W n omega else 0 := by
  classical
  have h := formsBidegreeProjection_decompositionGenerator A B W n l n 0 rfl (0 : W →₀ ℕ)
    (emptyPowersetCard W) omega
  rw [decompositionGenerator_zero_zero A B W n rfl (emptyPowersetCard W) omega] at h
  exact h

/-- **The bidegree-`(1, 0)` generator of the degree-one decomposition is a `P`-multiple of
`ψ (ω₀)`**: the sector generator carries no variable differential, so its variable factor is the
empty wedge and what is left is the monomial times the comparison of the coefficient form. -/
theorem decompositionGenerator_one_zero (L : W →₀ ℕ) (hn : 1 + 0 = 1)
    (J : Set.powersetCard W 0)
    (omega : dividedPowerDifferentialForms (A := A) B.dividedPowers 1) :
    decompositionGenerator A B W 1 0 1 hn L J omega =
      dividedPowerPolynomialMonomial (B : Type uB) L • coefficientFormsMap A B W 1 omega :=
  (decompositionGenerator_self A B W 1 0 L J omega).trans
    (congrArg (fun z : dividedPowerPolynomialForms A B W 1 ↦
        dividedPowerPolynomialMonomial (B : Type uB) L • z)
      (wedgeMul_variableWedge_zero A B W 1 (coefficientFormsMap A B W 1 omega) _))

/-- **The retraction `ε` reads only the top coefficient degree**: it kills every other bidegree
projection.  The slot it reads is the bidegree `(n, 0)` with the trivial monomial, and a
generator of coefficient degree `i ≠ n` carries a variable differential. -/
theorem relativeFormsRetraction_formsBidegreeProjection_of_ne (n i : ℕ) (hi : i ≠ n)
    (x : dividedPowerPolynomialForms A B W n) :
    relativeFormsRetraction A B W n (formsBidegreeProjection A B W n i x) = 0 := by
  classical
  have key : (relativeFormsRetraction A B W n) ∘ₗ
      ((formsBidegreeProjection A B W n i).restrictScalars A) = 0 := by
    refine dividedPowerPolynomialForms_linearMap_ext A B W n ?_
    intro i' j hij L J omega
    simp only [LinearMap.comp_apply, LinearMap.coe_restrictScalars, LinearMap.zero_apply]
    rw [formsBidegreeProjection_decompositionGenerator A B W n i i' j hij L J omega]
    by_cases hii : i = i'
    · rw [ite_eq_left hii]
      cases j with
      | zero => exact absurd (by omega : i = n) hi
      | succ j =>
        exact relativeFormsRetraction_decompositionGenerator_succ A B W i' j n hij L J omega
    · rw [ite_eq_right hii, map_zero]
  simpa only [LinearMap.comp_apply, LinearMap.coe_restrictScalars, LinearMap.zero_apply] using
    DFunLike.congr_fun key x

/-- **The retraction is unchanged by the top coefficient-degree projection**, the other
projections being killed by it. -/
theorem relativeFormsRetraction_formsBidegreeProjection_self (n : ℕ)
    (x : dividedPowerPolynomialForms A B W n) :
    relativeFormsRetraction A B W n (formsBidegreeProjection A B W n n x) =
      relativeFormsRetraction A B W n x := by
  have hsum : relativeFormsRetraction A B W n x =
      ∑ i ∈ Finset.range (n + 1),
        relativeFormsRetraction A B W n (formsBidegreeProjection A B W n i x) :=
    (congrArg (fun z : dividedPowerPolynomialForms A B W n ↦ relativeFormsRetraction A B W n z)
        (formsBidegreeProjection_sum A B W n x)).symm.trans
      (map_sum (relativeFormsRetraction A B W n) _ _)
  exact (hsum.trans (Finset.sum_eq_single_of_mem n (Finset.mem_range.2 (Nat.lt_succ_self n))
    (fun m _ hm ↦ relativeFormsRetraction_formsBidegreeProjection_of_ne A B W n m hm x))).symm

/-! ### An operator split by coefficient degree -/

/-- **An operator of `Ωⁿ_{P/A,δ'}` which preserves the coefficient degree, and whose complement
to the identity strictly raises it, is the identity.**

This is the bookkeeping behind the relative contraction identity below, and it is the whole of
the source's bigraded argument: the coefficient-degree projections sum to the identity in each
exterior degree, so an operator is determined by its components, and an operator that preserves
the degree can only be compared with the degree-preserving part of the identity.

The two hypotheses are: `S` has no off-diagonal component, and the diagonal component of `T`
vanishes. -/
theorem eq_self_of_formsBidegreeProjection_split (n : ℕ)
    (S T : dividedPowerPolynomialForms A B W n →ₗ[A] dividedPowerPolynomialForms A B W n)
    (hST : ∀ y : dividedPowerPolynomialForms A B W n, S y + T y = y)
    (hT : ∀ (i : ℕ) (y : dividedPowerPolynomialForms A B W n),
      formsBidegreeProjection A B W n i (T (formsBidegreeProjection A B W n i y)) = 0)
    (hS : ∀ (l i : ℕ), l ≠ i → ∀ y : dividedPowerPolynomialForms A B W n,
      formsBidegreeProjection A B W n l (S (formsBidegreeProjection A B W n i y)) = 0)
    (x : dividedPowerPolynomialForms A B W n) : S x = x := by
  have hstep : ∀ i : ℕ,
      formsBidegreeProjection A B W n i (S (formsBidegreeProjection A B W n i x)) =
        formsBidegreeProjection A B W n i x := by
    intro i
    have h2 : formsBidegreeProjection A B W n i (S (formsBidegreeProjection A B W n i x)) +
          formsBidegreeProjection A B W n i (T (formsBidegreeProjection A B W n i x)) =
        formsBidegreeProjection A B W n i (formsBidegreeProjection A B W n i x) :=
      (map_add (formsBidegreeProjection A B W n i) _ _).symm.trans
        (congrArg (fun z : dividedPowerPolynomialForms A B W n ↦
          formsBidegreeProjection A B W n i z) (hST (formsBidegreeProjection A B W n i x)))
    rw [hT i x, add_zero, formsBidegreeProjection_idem] at h2
    exact h2
  refine Eq.trans (congrArg (fun z : dividedPowerPolynomialForms A B W n ↦ S z)
    (formsBidegreeProjection_sum A B W n x).symm) ?_
  refine Eq.trans (map_sum S _ _) ?_
  refine Eq.trans (Finset.sum_congr rfl fun i hi ↦ ?_) (formsBidegreeProjection_sum A B W n x)
  exact (formsBidegreeProjection_sum A B W n (S (formsBidegreeProjection A B W n i x))).symm.trans
    ((Finset.sum_eq_single_of_mem i hi (fun l _ hl ↦ hS l i hl x)).trans (hstep i))

/-! ### Wedging with a coefficient one-form raises the coefficient degree -/

omit [LinearOrder W] in
/-- The bidegree projection is linear over the base ring `B`, being linear over `P`. -/
theorem formsBidegreeProjection_smul (n i : ℕ) (b : (B : Type uB))
    (x : dividedPowerPolynomialForms A B W n) :
    formsBidegreeProjection A B W n i (b • x) = b • formsBidegreeProjection A B W n i x := by
  rw [← algebraMap_smul (setIndexedDividedPowerPolynomialAlgebra B W) b x,
    map_smul (formsBidegreeProjection A B W n i)
      (algebraMap (B : Type uB) (setIndexedDividedPowerPolynomialAlgebra B W) b) x,
    algebraMap_smul (setIndexedDividedPowerPolynomialAlgebra B W) b
      (formsBidegreeProjection A B W n i x)]

/-- Moving the first summand of a sum to the other side, in an abstract abelian group; stated
abstractly for the reason given at
`Crystalline.DividedPowerPolynomial.relContraction_rearrange`. -/
private theorem eq_sub_of_eq_add_left {G : Type*} [AddCommGroup G] (a b c : G) (h : c = a + b) :
    b = c - a := by
  rw [h]
  abel

/-- `u - b · v = 0` when `u` and `v` vanish, in an abstract module; stated abstractly so that
nothing in its proof unfolds a concrete scalar action. -/
private theorem sub_smul_eq_zero_of_eq_zero {R G : Type*} [Semiring R] [AddCommGroup G]
    [Module R G] (b : R) (u v : G) (hu : u = 0) (hv : v = 0) : u - b • v = 0 := by
  rw [hu, hv, smul_zero, sub_zero]

/-- **The one-forms `d b` span `Ω¹_{B/A,δ}` over `B`**, the differentials `d b` spanning
`Ω_{B/A,δ}` by `Crystalline.dividedPowerDifferentials_span` and
`exteriorPower.oneEquiv` being an isomorphism. -/
theorem dividedPowerOneForm_span :
    Submodule.span (B : Type uB)
      (Set.range (dividedPowerOneForm A B.dividedPowers)) = ⊤ := by
  have hrange : Set.range (dividedPowerOneForm A B.dividedPowers) =
      (exteriorPower.oneEquiv (B : Type uB)
          (dividedPowerDifferentials (A := A) B.dividedPowers)).symm.toLinearMap ''
        Set.range (dividedPowerDifferential (A := A) B.dividedPowers) := by
    rw [← Set.range_comp]
    rfl
  rw [hrange, ← Submodule.map_span, dividedPowerDifferentials_span, Submodule.map_top,
    LinearEquiv.range]

omit [LinearOrder W] in
/-- **The comparison `ψ` carries the one-form of a base scalar to the one-form of its image**:
`ψ (d b) = d (b)` read in `Ω¹_{P/A,δ'}`.  It is
`Crystalline.mapDifferentialFormsOfDPMorphism_oneEquiv` together with
`Crystalline.mapDifferentialsOfDPMorphism_d`. -/
theorem coefficientFormsMap_dividedPowerOneForm (b : (B : Type uB)) :
    coefficientFormsMap A B W 1 (dividedPowerOneForm A B.dividedPowers b) =
      dividedPowerOneForm A (setIndexedDividedPowerPolynomialDividedPowers B W)
        (algebraMap (B : Type uB) (setIndexedDividedPowerPolynomialAlgebra B W) b) := by
  refine (exteriorPower.oneEquiv (setIndexedDividedPowerPolynomialAlgebra B W)
    (dividedPowerDifferentials (A := A)
      (setIndexedDividedPowerPolynomialDividedPowers B W))).injective ?_
  rw [coefficientFormsMap_apply, mapDifferentialFormsOfDPMorphism_oneEquiv,
    dividedPowerOneForm_apply, LinearEquiv.apply_symm_apply, dividedPowerOneForm_apply,
    LinearEquiv.apply_symm_apply, mapDifferentialsOfDPMorphism_d]
  rfl

/-- **On the diagonal, scaling by a base element commutes with the projected differential**: the
coefficient-degree-`i` component of `d` on forms of coefficient degree `i` is the relative
differential, which is `B`-linear. -/
private theorem formsBidegreeProjection_deRham_smul_of_eq (n l i : ℕ) (hl : l = i)
    (b : (B : Type uB)) (x : dividedPowerPolynomialForms A B W n) :
    formsBidegreeProjection A B W (n + 1) l
        (dividedPowerDeRham (setIndexedDividedPowerPolynomialDividedPowers B W) n
          (formsBidegreeProjection A B W n i (b • x))) =
      b • formsBidegreeProjection A B W (n + 1) l
        (dividedPowerDeRham (setIndexedDividedPowerPolynomialDividedPowers B W) n
          (formsBidegreeProjection A B W n i x)) := by
  subst hl
  refine Eq.trans (formsRelDifferentialAux_formsBidegreeProjection A B W n l (b • x)).symm ?_
  refine Eq.trans (congrArg (fun z : dividedPowerPolynomialForms A B W n ↦
      formsRelDifferentialAux A B W n z) (formsBidegreeProjection_smul A B W n l b x)) ?_
  refine Eq.trans (formsRelDifferentialAux_smul A B W n b
    (formsBidegreeProjection A B W n l x)) ?_
  exact congrArg (fun z : dividedPowerPolynomialForms A B W (n + 1) ↦ b • z)
    (formsRelDifferentialAux_formsBidegreeProjection A B W n l x)

/-- **Wedging with the exact one-form of a base scalar raises the coefficient degree.**

`ω ∧ d b = d (b ω) - b d ω` by the Leibniz rule, and for `ω` of coefficient degree `i` and
`l ≤ i` the two coefficient-degree-`l` components cancel: they are `0` for `l < i`, since the
differential of a form of coefficient degree `i` has components only in degrees `i` and `i + 1`,
and for `l = i` they are both `b · d_rel ω` because the relative differential is `B`-linear. -/
theorem formsBidegreeProjection_wedge_dividedPowerOneForm_eq_zero (n l i : ℕ) (hli : l ≤ i)
    (b : (B : Type uB)) (x : dividedPowerPolynomialForms A B W n) :
    formsBidegreeProjection A B W (n + 1) l
        (dividedPowerWedge (setIndexedDividedPowerPolynomialDividedPowers B W) n
          (formsBidegreeProjection A B W n i x)
          (dividedPowerOneForm A (setIndexedDividedPowerPolynomialDividedPowers B W)
            (algebraMap (B : Type uB) (setIndexedDividedPowerPolynomialAlgebra B W) b))) = 0 := by
  have hwedge : dividedPowerWedge (setIndexedDividedPowerPolynomialDividedPowers B W) n
        (formsBidegreeProjection A B W n i x)
        (dividedPowerOneForm A (setIndexedDividedPowerPolynomialDividedPowers B W)
          (algebraMap (B : Type uB) (setIndexedDividedPowerPolynomialAlgebra B W) b)) =
      dividedPowerDeRham (setIndexedDividedPowerPolynomialDividedPowers B W) n
          ((algebraMap (B : Type uB) (setIndexedDividedPowerPolynomialAlgebra B W) b) •
            formsBidegreeProjection A B W n i x) -
        (algebraMap (B : Type uB) (setIndexedDividedPowerPolynomialAlgebra B W) b) •
          dividedPowerDeRham (setIndexedDividedPowerPolynomialDividedPowers B W) n
            (formsBidegreeProjection A B W n i x) :=
    (congrArg (fun z : dividedPowerDifferentials (A := A)
          (setIndexedDividedPowerPolynomialDividedPowers B W) ↦
        leftWedge n z (formsBidegreeProjection A B W n i x))
      ((exteriorPower.oneEquiv (setIndexedDividedPowerPolynomialAlgebra B W)
        (dividedPowerDifferentials (A := A)
          (setIndexedDividedPowerPolynomialDividedPowers B W))).apply_symm_apply _)).trans
      (eq_sub_of_eq_add_left _ _ _
        (dividedPowerDeRham_smul (A := A) (setIndexedDividedPowerPolynomialDividedPowers B W) n
          (algebraMap (B : Type uB) (setIndexedDividedPowerPolynomialAlgebra B W) b)
          (formsBidegreeProjection A B W n i x)))
  rw [hwedge, map_sub (formsBidegreeProjection A B W (n + 1) l),
    map_smul (formsBidegreeProjection A B W (n + 1) l)
      (algebraMap (B : Type uB) (setIndexedDividedPowerPolynomialAlgebra B W) b)
      (dividedPowerDeRham (setIndexedDividedPowerPolynomialDividedPowers B W) n
        (formsBidegreeProjection A B W n i x)),
    algebraMap_smul (setIndexedDividedPowerPolynomialAlgebra B W) b
      (formsBidegreeProjection A B W n i x),
    algebraMap_smul (setIndexedDividedPowerPolynomialAlgebra B W) b
      (formsBidegreeProjection A B W (n + 1) l
        (dividedPowerDeRham (setIndexedDividedPowerPolynomialDividedPowers B W) n
          (formsBidegreeProjection A B W n i x))),
    ← formsBidegreeProjection_smul A B W n i b x]
  rcases Nat.lt_or_ge l i with hlt | hge
  · exact sub_smul_eq_zero_of_eq_zero b _ _
      (formsBidegreeProjection_dividedPowerDeRham_eq_zero A B W n (show l ≠ i by omega)
        (show l ≠ i + 1 by omega) (b • x))
      (formsBidegreeProjection_dividedPowerDeRham_eq_zero A B W n (show l ≠ i by omega)
        (show l ≠ i + 1 by omega) x)
  · exact sub_eq_zero_of_eq
      (formsBidegreeProjection_deRham_smul_of_eq A B W n l i (le_antisymm hli hge) b x)

/-- **Wedging with a coefficient one-form raises the coefficient degree** — the `hprojwedge`
hypothesis of `Crystalline.CompletedDeRham.exists_twistedHomotopyEquiv`, uncompleted.

The coefficient one-forms of degree one are the `P`-multiples of the images `ψ (ω₀)` of the
one-forms of `B` — that is what the bidegree-`(1, 0)` generators of the decomposition are — and
the one-forms of `B` are spanned by the exact ones, where the previous statement applies. -/
theorem formsBidegreeProjection_wedge_formsBidegreeProjection_eq_zero (n l i : ℕ) (hli : l ≤ i)
    (x : dividedPowerPolynomialForms A B W n) (y : dividedPowerPolynomialForms A B W 1) :
    formsBidegreeProjection A B W (n + 1) l
        (dividedPowerWedge (setIndexedDividedPowerPolynomialDividedPowers B W) n
          (formsBidegreeProjection A B W n i x)
          (formsBidegreeProjection A B W 1 1 y)) = 0 := by
  classical
  have hPhi : ∀ {z z' : dividedPowerPolynomialForms A B W 1}, z = z' →
      formsBidegreeProjection A B W (n + 1) l
          (dividedPowerWedge (setIndexedDividedPowerPolynomialDividedPowers B W) n
            (formsBidegreeProjection A B W n i x) z) =
        formsBidegreeProjection A B W (n + 1) l
          (dividedPowerWedge (setIndexedDividedPowerPolynomialDividedPowers B W) n
            (formsBidegreeProjection A B W n i x) z') :=
    fun h ↦ congrArg _ (congrArg _ h)
  have hcoeff : ∀ omega : dividedPowerDifferentialForms (A := A) B.dividedPowers 1,
      formsBidegreeProjection A B W (n + 1) l
        (dividedPowerWedge (setIndexedDividedPowerPolynomialDividedPowers B W) n
          (formsBidegreeProjection A B W n i x)
          (coefficientFormsMap A B W 1 omega)) = 0 := by
    have hzero : ((formsBidegreeProjection A B W (n + 1) l).restrictScalars
            (B : Type uB)) ∘ₗ
          (((dividedPowerWedge (setIndexedDividedPowerPolynomialDividedPowers B W) n
              (formsBidegreeProjection A B W n i x)).restrictScalars (B : Type uB)) ∘ₗ
            coefficientFormsMap A B W 1) =
        0 :=
      LinearMap.ext_on_range (dividedPowerOneForm_span A B) fun b ↦ by
        simp only [LinearMap.comp_apply, LinearMap.coe_restrictScalars, LinearMap.zero_apply]
        exact (hPhi (coefficientFormsMap_dividedPowerOneForm A B W b)).trans
          (formsBidegreeProjection_wedge_dividedPowerOneForm_eq_zero A B W n l i hli b x)
    intro omega
    simpa only [LinearMap.comp_apply, LinearMap.coe_restrictScalars, LinearMap.zero_apply] using
      DFunLike.congr_fun hzero omega
  have key : ((formsBidegreeProjection A B W (n + 1) l).restrictScalars A) ∘ₗ
        (((dividedPowerWedge (setIndexedDividedPowerPolynomialDividedPowers B W) n
            (formsBidegreeProjection A B W n i x)).restrictScalars A) ∘ₗ
          ((formsBidegreeProjection A B W 1 1).restrictScalars A)) =
      0 := by
    refine dividedPowerPolynomialForms_linearMap_ext A B W 1 ?_
    intro i' j' hij L J omega
    simp only [LinearMap.comp_apply, LinearMap.coe_restrictScalars, LinearMap.zero_apply]
    by_cases hi' : 1 = i'
    · subst hi'
      obtain rfl : j' = 0 := by omega
      refine Eq.trans (hPhi
        (((formsBidegreeProjection_decompositionGenerator A B W 1 1 1 0 hij L J omega).trans
            (ite_eq_left rfl)).trans
          (decompositionGenerator_one_zero A B W L hij J omega))) ?_
      refine Eq.trans (congrArg (fun z : dividedPowerPolynomialForms A B W (n + 1) ↦
          formsBidegreeProjection A B W (n + 1) l z)
        (map_smul (dividedPowerWedge (setIndexedDividedPowerPolynomialDividedPowers B W) n
            (formsBidegreeProjection A B W n i x))
          (dividedPowerPolynomialMonomial (B : Type uB) L)
          (coefficientFormsMap A B W 1 omega))) ?_
      refine Eq.trans (map_smul (formsBidegreeProjection A B W (n + 1) l)
        (dividedPowerPolynomialMonomial (B : Type uB) L) _) ?_
      refine Eq.trans (congrArg (fun z : dividedPowerPolynomialForms A B W (n + 1) ↦
        dividedPowerPolynomialMonomial (B : Type uB) L • z) (hcoeff omega)) ?_
      exact smul_zero _
    · refine Eq.trans (hPhi
        ((formsBidegreeProjection_decompositionGenerator A B W 1 1 i' j' hij L J omega).trans
          (ite_eq_right hi'))) ?_
      exact Eq.trans (congrArg (fun z : dividedPowerPolynomialForms A B W (n + 1) ↦
          formsBidegreeProjection A B W (n + 1) l z)
          (map_zero (dividedPowerWedge (setIndexedDividedPowerPolynomialDividedPowers B W) n
            (formsBidegreeProjection A B W n i x))))
        (map_zero (formsBidegreeProjection A B W (n + 1) l))
  simpa only [LinearMap.comp_apply, LinearMap.coe_restrictScalars, LinearMap.zero_apply] using
    DFunLike.congr_fun key y

/-! ### The off-diagonal components of the relative contraction vanish -/

/-- **`d_rel ∘ h` has no off-diagonal coefficient-degree component**: `h` preserves the
coefficient degree and `d_rel` preserves it, so the composite does. -/
theorem formsBidegreeProjection_relDifferential_homotopy_eq_zero (n l i : ℕ) (hl : l ≠ i)
    (y : dividedPowerPolynomialForms A B W (n + 1)) :
    formsBidegreeProjection A B W (n + 1) l
        (formsRelDifferentialAux A B W n
          (relativeFormsHomotopy A B W n (formsBidegreeProjection A B W (n + 1) i y))) = 0 :=
  ((congrArg (fun z : dividedPowerPolynomialForms A B W n ↦
        formsBidegreeProjection A B W (n + 1) l (formsRelDifferentialAux A B W n z))
      (relativeFormsHomotopy_formsBidegreeProjection A B W n i y)).trans
    (congrArg (fun z : dividedPowerPolynomialForms A B W (n + 1) ↦
        formsBidegreeProjection A B W (n + 1) l z)
      (formsRelDifferentialAux_formsBidegreeProjection A B W n i
        (relativeFormsHomotopy A B W n y)))).trans
    (formsBidegreeProjection_comp_eq_zero A B W (n + 1) hl _)

/-- **`h ∘ d_rel` has no off-diagonal coefficient-degree component.** -/
theorem formsBidegreeProjection_homotopy_relDifferential_eq_zero (n l i : ℕ) (hl : l ≠ i)
    (y : dividedPowerPolynomialForms A B W (n + 1)) :
    formsBidegreeProjection A B W (n + 1) l
        (relativeFormsHomotopy A B W (n + 1)
          (formsRelDifferentialAux A B W (n + 1)
            (formsBidegreeProjection A B W (n + 1) i y))) = 0 :=
  ((relativeFormsHomotopy_formsBidegreeProjection A B W (n + 1) l
        (formsRelDifferentialAux A B W (n + 1)
          (formsBidegreeProjection A B W (n + 1) i y))).symm.trans
    (congrArg (fun z : dividedPowerPolynomialForms A B W (n + 1 + 1) ↦
        relativeFormsHomotopy A B W (n + 1) z)
      ((congrArg (fun z : dividedPowerPolynomialForms A B W (n + 1 + 1) ↦
            formsBidegreeProjection A B W (n + 1 + 1) l z)
          (formsRelDifferentialAux_formsBidegreeProjection A B W (n + 1) i y)).trans
        (formsBidegreeProjection_comp_eq_zero A B W (n + 1 + 1) hl _)))).trans
    (map_zero (relativeFormsHomotopy A B W (n + 1)))

/-- **`ψ ∘ ε` has no off-diagonal coefficient-degree component**: the retraction reads only the
top coefficient degree and the comparison lands only there. -/
theorem formsBidegreeProjection_coefficient_retraction_eq_zero (n l i : ℕ) (hl : l ≠ i)
    (y : dividedPowerPolynomialForms A B W n) :
    formsBidegreeProjection A B W n l
        (coefficientFormsMap A B W n
          (relativeFormsRetraction A B W n (formsBidegreeProjection A B W n i y))) = 0 := by
  classical
  by_cases hin : i = n
  · refine (formsBidegreeProjection_coefficientFormsMap A B W n l
      (relativeFormsRetraction A B W n (formsBidegreeProjection A B W n i y))).trans ?_
    exact ite_eq_right (hin ▸ hl)
  · exact (congrArg (fun w : dividedPowerDifferentialForms (A := A) B.dividedPowers n ↦
          formsBidegreeProjection A B W n l (coefficientFormsMap A B W n w))
        (relativeFormsRetraction_formsBidegreeProjection_of_ne A B W n i hin y)).trans
      ((congrArg (fun w : dividedPowerPolynomialForms A B W n ↦
            formsBidegreeProjection A B W n l w)
          (map_zero (coefficientFormsMap A B W n))).trans
        (map_zero (formsBidegreeProjection A B W n l)))

/-! ### The relative contraction identity -/

/-- The rearrangement of the contraction identity, in an abstract abelian group.

It is stated abstractly because the terms it rearranges are forms of a divided power polynomial
algebra, where `abel` on the concrete terms runs past the recursion limit while here every atom
is a variable. -/
private theorem relContraction_rearrange {G : Type*} [AddCommGroup G]
    (dh hd y pj a b c d e : G) (hid : dh + hd = y - pj) (h1 : dh = a + b) (h2 : hd = c + d)
    (h3 : pj = e) : a + c + e + (b + d) = y := by
  subst h3
  rw [h1, h2, eq_sub_iff_add_eq] at hid
  rw [← hid]
  abel

/-- The degree-zero rearrangement of the contraction identity, in an abstract abelian group; see
`Crystalline.DividedPowerPolynomial.relContraction_rearrange`. -/
private theorem relContraction_rearrange_zero {G : Type*} [AddCommGroup G]
    (hd y pj c d e : G) (hid : hd = y - pj) (h2 : hd = c + d) (h3 : pj = e) :
    c + e + d = y := by
  subst h3
  rw [h2, eq_sub_iff_add_eq] at hid
  rw [← hid]
  abel

/-- A linear map kills a sum of three terms it kills, in abstract modules.  Stated abstractly for
the same reason as `Crystalline.DividedPowerPolynomial.relContraction_rearrange`. -/
private theorem map_add_three_eq_zero {R G H : Type*} [Semiring R] [AddCommGroup G] [Module R G]
    [AddCommGroup H] [Module R H] (f : G →ₗ[R] H) (a b c : G) (ha : f a = 0) (hb : f b = 0)
    (hc : f c = 0) : f (a + b + c) = 0 := by
  rw [map_add, map_add, ha, hb, hc, add_zero, add_zero]

/-- A linear map kills a sum of two terms it kills, in abstract modules. -/
private theorem map_add_two_eq_zero {R G H : Type*} [Semiring R] [AddCommGroup G] [Module R G]
    [AddCommGroup H] [Module R H] (f : G →ₗ[R] H) (a b : G) (ha : f a = 0) (hb : f b = 0) :
    f (a + b) = 0 := by
  rw [map_add, ha, hb, add_zero]

/-- **The relative contraction identity in a positive degree**:
`d_rel (h x) + h (d_rel x) + ψ (ε x) = x` on `Ωⁿ⁺¹_{P/A,δ'}`.

This is the `hconform` hypothesis of
`Crystalline.CompletedDeRham.exists_twistedHomotopyEquiv`, and it is *not* the contraction
identity `Crystalline.DividedPowerPolynomial.relativeFormsHomotopy_identity` of the full
differential: it is its coefficient-degree-preserving part.  The complementary part,
`d_base h + h d_base = 0`, is not stated separately; what the proof uses is that it strictly
raises the coefficient degree while `d_rel h`, `h d_rel` and `ψ ε` preserve it, so that
`Crystalline.DividedPowerPolynomial.eq_self_of_formsBidegreeProjection_split` separates the two.

That `d_rel` and `h` preserve the coefficient degree is
`Crystalline.DividedPowerPolynomial.formsRelDifferentialAux_formsBidegreeProjection` and
`..._relativeFormsHomotopy_formsBidegreeProjection`; that `ψ ε` does is
`..._formsBidegreeProjection_coefficientFormsMap` together with
`..._relativeFormsRetraction_formsBidegreeProjection_of_ne`; and that `d_base` raises it is
`..._formsBidegreeProjection_formsBaseDifferential_eq_zero`. -/
theorem relativeFormsHomotopy_relContraction (n : ℕ)
    (x : dividedPowerPolynomialForms A B W (n + 1)) :
    formsRelDifferentialAux A B W n (relativeFormsHomotopy A B W n x) +
        relativeFormsHomotopy A B W (n + 1) (formsRelDifferentialAux A B W (n + 1) x) +
      coefficientFormsMap A B W (n + 1) (relativeFormsRetraction A B W (n + 1) x) = x := by
  classical
  refine eq_self_of_formsBidegreeProjection_split A B W (n + 1)
    ((formsRelDifferentialAux A B W n) ∘ₗ (relativeFormsHomotopy A B W n) +
      (relativeFormsHomotopy A B W (n + 1)) ∘ₗ (formsRelDifferentialAux A B W (n + 1)) +
      ((coefficientFormsMap A B W (n + 1)).restrictScalars A) ∘ₗ
        (relativeFormsRetraction A B W (n + 1)))
    ((formsBaseDifferential A B W n) ∘ₗ (relativeFormsHomotopy A B W n) +
      (relativeFormsHomotopy A B W (n + 1)) ∘ₗ (formsBaseDifferential A B W (n + 1)))
    (fun y ↦ ?_) (fun i y ↦ ?_) (fun l i hl y ↦ ?_) x
  · simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.coe_restrictScalars]
    refine relContraction_rearrange _ _ _ _ _ _ _ _ _
      (relativeFormsHomotopy_identity A B W n y)
      (dividedPowerDeRham_eq_formsRelDifferential_add A B W n
        (relativeFormsHomotopy A B W n y))
      ((congrArg (fun z : dividedPowerPolynomialForms A B W (n + 1 + 1) ↦
            relativeFormsHomotopy A B W (n + 1) z)
          (dividedPowerDeRham_eq_formsRelDifferential_add A B W (n + 1) y)).trans
        (map_add (relativeFormsHomotopy A B W (n + 1)) _ _))
      (relativeFormsProjection_apply A B W (n + 1) y)
  · simp only [LinearMap.add_apply, LinearMap.comp_apply]
    rw [map_add, relativeFormsHomotopy_formsBidegreeProjection A B W n i y,
      formsBidegreeProjection_formsBaseDifferential_eq_zero A B W n (le_refl i)
        (relativeFormsHomotopy A B W n y),
      ← relativeFormsHomotopy_formsBidegreeProjection A B W (n + 1) i
        (formsBaseDifferential A B W (n + 1) (formsBidegreeProjection A B W (n + 1) i y)),
      formsBidegreeProjection_formsBaseDifferential_eq_zero A B W (n + 1) (le_refl i) y,
      map_zero, zero_add]
  · simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.coe_restrictScalars]
    exact map_add_three_eq_zero (formsBidegreeProjection A B W (n + 1) l) _ _ _
      (formsBidegreeProjection_relDifferential_homotopy_eq_zero A B W n l i hl y)
      (formsBidegreeProjection_homotopy_relDifferential_eq_zero A B W n l i hl y)
      (formsBidegreeProjection_coefficient_retraction_eq_zero A B W (n + 1) l i hl y)

/-- **The degree-zero relative contraction identity**: `h (d_rel x) + ψ (ε x) = x` on
`Ω⁰_{P/A,δ'}`.  This is the `hcon0form` hypothesis of
`Crystalline.CompletedDeRham.exists_twistedHomotopyEquiv`; see
`Crystalline.DividedPowerPolynomial.relativeFormsHomotopy_relContraction` for the argument. -/
theorem relativeFormsHomotopy_relContraction_zero (x : dividedPowerPolynomialForms A B W 0) :
    relativeFormsHomotopy A B W 0 (formsRelDifferentialAux A B W 0 x) +
      coefficientFormsMap A B W 0 (relativeFormsRetraction A B W 0 x) = x := by
  classical
  refine eq_self_of_formsBidegreeProjection_split A B W 0
    ((relativeFormsHomotopy A B W 0) ∘ₗ (formsRelDifferentialAux A B W 0) +
      ((coefficientFormsMap A B W 0).restrictScalars A) ∘ₗ (relativeFormsRetraction A B W 0))
    ((relativeFormsHomotopy A B W 0) ∘ₗ (formsBaseDifferential A B W 0))
    (fun y ↦ ?_) (fun i y ↦ ?_) (fun l i hl y ↦ ?_) x
  · simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.coe_restrictScalars]
    refine relContraction_rearrange_zero _ _ _ _ _ _
      (relativeFormsHomotopy_identity_zero A B W y)
      ((congrArg (fun z : dividedPowerPolynomialForms A B W 1 ↦
            relativeFormsHomotopy A B W 0 z)
          (dividedPowerDeRham_eq_formsRelDifferential_add A B W 0 y)).trans
        (map_add (relativeFormsHomotopy A B W 0) _ _))
      (relativeFormsProjection_apply A B W 0 y)
  · simp only [LinearMap.comp_apply]
    rw [← relativeFormsHomotopy_formsBidegreeProjection A B W 0 i
        (formsBaseDifferential A B W 0 (formsBidegreeProjection A B W 0 i y)),
      formsBidegreeProjection_formsBaseDifferential_eq_zero A B W 0 (le_refl i) y, map_zero]
  · simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.coe_restrictScalars]
    refine map_add_two_eq_zero (formsBidegreeProjection A B W 0 l) _ _ ?_
      (formsBidegreeProjection_coefficient_retraction_eq_zero A B W 0 l i hl y)
    exact ((relativeFormsHomotopy_formsBidegreeProjection A B W 0 l
          (formsRelDifferentialAux A B W 0 (formsBidegreeProjection A B W 0 i y))).symm.trans
        (congrArg (fun z : dividedPowerPolynomialForms A B W 1 ↦
            relativeFormsHomotopy A B W 0 z)
          ((congrArg (fun z : dividedPowerPolynomialForms A B W 1 ↦
                formsBidegreeProjection A B W 1 l z)
              (formsRelDifferentialAux_formsBidegreeProjection A B W 0 i y)).trans
            (formsBidegreeProjection_comp_eq_zero A B W 1 hl _)))).trans
      (map_zero (relativeFormsHomotopy A B W 0))

end BaseLinear

/-! ### The `D`-module structure on the completed forms of `D'` -/

section CompletedScalars

variable (A : Type uA) [CommRing A] (B : DividedPowerRing.{uB}) [Algebra A B] (W : Type uW)
  (p : ℕ)

/-- **The ring map `D → D'`**, the `p`-adic completion of the coefficient inclusion
`B → P = B⟨x_w : w ∈ W⟩`.

This is `Crystalline.completedRingHom` of
`StacksFrontier/AlgebraicGeometry/Crystalline/ModuleDifferentials/CompletionLevelTransition.lean`
at the coefficient inclusion, spelled through
`Crystalline.PAdicCompletion.mapRingHom` — the construction specialised to the ideal `(p)`, whose
levels are cut out by the integer `pⁿ` — because that is the spelling whose scalar compatibility
`Crystalline.PAdicCompletion.mapAddHom_smul` is stated for. -/
def completedCoefficientRingHom :
    completedDividedPowerRing p (B := (B : Type uB)) →+*
      completedDividedPowerPolynomialRing B W p :=
  completedRingHom p (coefficientAlgHom A B W)

/-- **The ring map `D → D'` is `Crystalline.PAdicCompletion.mapRingHom` of the coefficient
inclusion.**  `Crystalline.completedRingHom` is built from `Crystalline.adicCompletionRingMap`
and the other from the levels being cut out by the integer `pⁿ`; they are the same map, by
`Crystalline.completedRingHom_apply_eq_mapRingHom`.  This is the spelling whose scalar
compatibility `Crystalline.PAdicCompletion.mapAddHom_smul` is stated for. -/
theorem completedCoefficientRingHom_apply
    (c : completedDividedPowerRing p (B := (B : Type uB))) :
    completedCoefficientRingHom A B W p c =
      PAdicCompletion.mapRingHom p (B : Type uB)
        (setIndexedDividedPowerPolynomialAlgebra B W)
        (algebraMap (B : Type uB) (setIndexedDividedPowerPolynomialAlgebra B W)) c :=
  completedRingHom_apply_eq_mapRingHom p (coefficientAlgHom A B W) c

/-- The ring map `D → D'` on the image of `B`. -/
@[simp] theorem completedCoefficientRingHom_of (b : (B : Type uB)) :
    completedCoefficientRingHom A B W p (AdicCompletion.of _ _ b) =
      AdicCompletion.of _ _ (algebraMap (B : Type uB)
        (setIndexedDividedPowerPolynomialAlgebra B W) b) :=
  completedRingHom_of p (coefficientAlgHom A B W) b

/-- **`Ω̂ⁿ_{D'}` is a `D`-module**, by restriction of scalars along the completed coefficient
inclusion `D → D'`.

This is the structure the perturbation argument of [Stacks, Lemma 60.21.2, Tag 07LD] asks for and
that the library did not carry: `Ω̂ⁿ_{D'}` is an `AdicCompletion` along `(p) ⊆ P`, hence a
`D'`-module, while `Crystalline.CompletedDeRham.exists_twistedHomotopyEquiv` tensors the forms
with a `D`-module `M` and therefore needs them to be `D`-modules.  The scalar action is
`c • x = (D → D') c • x`, by `Crystalline.DividedPowerPolynomial.completedPolynomialForms_smul`;
nothing is asserted about `Ω̂ⁿ_{D'}` as a `D`-module beyond that. -/
instance moduleCompletedPolynomialForms (n : ℕ) :
    Module (completedDividedPowerRing p (B := (B : Type uB)))
      (completedPolynomialForms A B W p n) :=
  Module.compHom _ (completedCoefficientRingHom A B W p)

/-- **The `D`-action on `Ω̂ⁿ_{D'}` is the `D'`-action through `D → D'`.** -/
theorem completedPolynomialForms_smul (n : ℕ)
    (c : completedDividedPowerRing p (B := (B : Type uB)))
    (x : completedPolynomialForms A B W p n) :
    c • x = completedCoefficientRingHom A B W p c • x :=
  rfl

/-- The `D`-action on `Ω̂ⁿ_{D'}`, read through
`Crystalline.PAdicCompletion.mapRingHom`, which is the shape the scalar compatibility
`Crystalline.PAdicCompletion.mapAddHom_smul` consumes. -/
theorem completedPolynomialForms_smul_mapRingHom (n : ℕ)
    (c : completedDividedPowerRing p (B := (B : Type uB)))
    (x : completedPolynomialForms A B W p n) :
    c • x =
      PAdicCompletion.mapRingHom p (B : Type uB)
          (setIndexedDividedPowerPolynomialAlgebra B W)
          (algebraMap (B : Type uB) (setIndexedDividedPowerPolynomialAlgebra B W)) c • x :=
  (completedPolynomialForms_smul A B W p n c x).trans
    (congrArg (fun y : completedDividedPowerPolynomialRing B W p ↦ y • x)
      (completedCoefficientRingHom_apply A B W p c))

end CompletedScalars

end DividedPowerPolynomial

end Crystalline

end
