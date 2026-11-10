module

public import StacksFrontier.AlgebraicGeometry.Crystalline.Differentials
public import StacksFrontier.LinearAlgebra.ExteriorPower.BaseChange
public import StacksFrontier.LinearAlgebra.ExteriorPower.Prod

/-!
# The divided power polynomial decomposition of differential forms in every degree

Let `A` be a ring, let `(B, I, δ)` be a divided power ring which is an `A`-algebra, let `W` index
a family of divided power variables and let `P = B⟨x_w : w ∈ W⟩` carry the divided power ideal
`IP + P₊` of [Stacks, Tag 07H6].  [Stacks, Tag 07HS] computes the divided power differentials
of `P` in degree one:

`Ω¹_{P/A,δ'} = (P ⊗_B Ω¹_{B/A,δ}) ⊕ (W →₀ P)`,

the second summand being the free `P`-module on the symbols `d x_w`.  This module takes the
`n`-th exterior power of that decomposition over `P` and splits it by the Künneth isomorphism
`exteriorPower.prodEquivDirectSum`, giving, `P`-linearly,

`Ωⁿ_{P/A,δ'} = ⨁_{i + j = n} ((⋀ⁱ_P (P ⊗_B Ω¹_{B/A,δ})) ⊗_P (⋀ʲ_P (W →₀ P)))`.

The divided power ideal `I` of the base is arbitrary: nothing here asks for `I = ⊥`, and in
particular `Ω¹_{B/A,δ}` is not assumed free.  That is the whole point of stating the
decomposition in this shape rather than as a basis — with `I = ⊥` the coefficient factor
collapses and `Ωⁿ_{P/A,δ'}` becomes free over `P` on the `n`-element subsets of `W`, which is
the form [Stacks, Tag 07LC] is proved in, but for a nontrivial `I` only the direct sum
decomposition survives.

The family `W` is arbitrary; the direct sum runs over the antidiagonal of `n`, which is finite
whatever `W` is.

## What is deliberately not claimed

The names below are chosen so as not to suggest two identifications that are absent.

1. **The `W`-side factor is not called `Ωʲ_{P/B,δ}`.**  Nothing in this library proves
   `Ω¹_{P/B,δ} ≅ (W →₀ P)`; there is no divided power differentials object of `P` over `B` here
   at all.  So `polynomialVariableForms` is named for what it is, the `j`-th exterior power of
   the free `P`-module on the symbols `d x_w`.
2. **The coefficient-side factor is the exterior power over `P` of a base change.**  Its
   identification with the base change of the exterior power over `B`, i.e. with
   `P ⊗_B Ωⁱ_{B/A,δ}`, is `polynomialCoefficientFormsBaseChangeEquiv`, which is
   `ExteriorAlgebra.exteriorPowerBaseChange` and needs neither flatness nor a Noetherian
   hypothesis.  It is stated separately because the two are different modules.

## Main definitions

* `Crystalline.DividedPowerPolynomial.polynomialCoefficientForms` — `⋀ⁱ_P (P ⊗_B Ω¹_{B/A,δ})`.
* `Crystalline.DividedPowerPolynomial.polynomialVariableForms` — `⋀ʲ_P (W →₀ P)`.
* `Crystalline.DividedPowerPolynomial.polynomialBidegreeForms` — the tensor product over `P` of
  the two above, the bidegree-`(i, j)` summand.
* `Crystalline.DividedPowerPolynomial.dividedPowerPolynomialFormsEquiv` — **the decomposition in
  degree `n`.**
* `Crystalline.DividedPowerPolynomial.polynomialCoefficientFormsBaseChangeEquiv` — the
  coefficient factor is `P ⊗_B Ωⁱ_{B/A,δ}`.
* `Crystalline.DividedPowerPolynomial.polynomialVariableFormsBasis` — the variable factor is
  free over `P` on the `j`-element subsets of `W`.
* `Crystalline.DividedPowerPolynomial.polynomialBidegreeFormsFreeEquiv` — the bidegree-`(i, j)`
  summand is the free module on those subsets with coefficients in `P ⊗_B Ωⁱ_{B/A,δ}`.
* `Crystalline.DividedPowerPolynomial.polynomialCoefficientMonomialEquiv` — and that coefficient
  module is, `B`-linearly, the free module on the exponent vectors `L : W →₀ ℕ` with
  coefficients in `Ωⁱ_{B/A,δ}`.

Together the last three put `Ωⁿ_{P/A,δ'}` in the shape the sector argument of [Stacks, Tag 07LC]
needs: indexed by a divided power monomial `x^{[L]}` and a `j`-element subset `I` of `W`, with
coefficients in `Ωⁱ_{B/A,δ}` rather than in the base ring.  For `I = ⊥` the coefficients are the
base ring and the three compose to the basis that proof uses.

## Main results

* `Crystalline.DividedPowerPolynomial.dividedPowerPolynomialFormsEquiv_wedge` — the
  decomposition carries the wedge `d b₁ ∧ ⋯ ∧ d bᵢ ∧ d x_{w₁} ∧ ⋯ ∧ d x_{wⱼ}` of `i` coefficient
  differentials followed by `j` variable differentials into the single summand indexed by
  `(i, j)`, as the generator `((1 ⊗ d b₁) ∧ ⋯) ⊗ (d x_{w₁} ∧ ⋯)`.  Such wedges span
  `Ωⁿ_{P/A,δ'}` over `P`, so this pins the decomposition down.
* `..._polynomialVariableFormsBasis_apply`, `..._polynomialBidegreeFormsFreeEquiv_tmul_basis`
  and `..._polynomialCoefficientMonomialEquiv_monomial_tmul` — the values of the three
  freeness statements on the generators, which is what pins each of them down.

## References

* [Stacks Project, Tag 07HS](https://stacks.math.columbia.edu/tag/07HS)
* [Stacks Project, Tag 07H6](https://stacks.math.columbia.edu/tag/07H6)
* [Stacks Project, Lemma 60.19.2, Tag 07LD](https://stacks.math.columbia.edu/tag/07LD)
-/

@[expose] public noncomputable section

open DividedPowers
open scoped TensorProduct

universe uA uB uW

namespace Crystalline

namespace DividedPowerPolynomial

/-! ### Two generic facts about exterior powers -/

/-- The equivalence of exterior powers induced by a linear equivalence takes a wedge of vectors
to the wedge of their images.

This is a generic fact about `exteriorPowerCongr`, repeated here: the only other copy in the
library sits in the sheaf-theoretic
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerProdSheaf`, whose import closure has
no business in this chapter. -/
public theorem exteriorPowerCongr_ιMulti {R : Type*} [CommRing R] {M N : Type*}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (n : ℕ) (e : M ≃ₗ[R] N)
    (v : Fin n → M) :
    exteriorPowerCongr n e (exteriorPower.ιMulti R n v) =
      exteriorPower.ιMulti R n fun k ↦ e (v k) := by
  refine Subtype.ext ?_
  rw [exteriorPowerCongr_coe, exteriorPower.ιMulti_apply_coe, exteriorPower.ιMulti_apply_coe,
    ExteriorAlgebra.map_apply_ιMulti]
  rfl

/-- The Künneth decomposition of `⋀^{i+j} (M × N)` carries the wedge of `i` vectors pushed in
from the first factor followed by `j` vectors pushed in from the second to the bidegree-`(i, j)`
block generator.  Stated here for the same reason as the previous one; it is
`exteriorPower.prodEquivDirectSum_symm_lof_tmul_coe` read on wedges and inverted. -/
public theorem prodEquivDirectSum_ιMulti_append {R : Type*} [CommRing R] {M N : Type*}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (i j : ℕ) (a : Fin i → M)
    (b : Fin j → N) :
    exteriorPower.prodEquivDirectSum (R := R) (M := M) (N := N) (i + j)
        (exteriorPower.ιMulti R (i + j)
          (Fin.append (fun k ↦ LinearMap.inl R M N (a k))
            fun k ↦ LinearMap.inr R M N (b k))) =
      DirectSum.lof R {pq : ℕ × ℕ // pq.1 + pq.2 = i + j}
        (fun pq ↦ TensorProduct R (⋀[R]^pq.1.1 M) (⋀[R]^pq.1.2 N)) ⟨(i, j), rfl⟩
        (exteriorPower.ιMulti R i a ⊗ₜ[R] exteriorPower.ιMulti R j b) := by
  have hsymm : (exteriorPower.prodEquivDirectSum (R := R) (M := M) (N := N) (i + j)).symm
      (DirectSum.lof R {pq : ℕ × ℕ // pq.1 + pq.2 = i + j}
        (fun pq ↦ TensorProduct R (⋀[R]^pq.1.1 M) (⋀[R]^pq.1.2 N)) ⟨(i, j), rfl⟩
        (exteriorPower.ιMulti R i a ⊗ₜ[R] exteriorPower.ιMulti R j b)) =
      exteriorPower.ιMulti R (i + j)
        (Fin.append (fun k ↦ LinearMap.inl R M N (a k))
          fun k ↦ LinearMap.inr R M N (b k)) := by
    refine Subtype.ext ?_
    rw [exteriorPower.prodEquivDirectSum_symm_lof_tmul_coe, exteriorPower.ιMulti_apply_coe,
      exteriorPower.ιMulti_apply_coe, exteriorPower.ιMulti_apply_coe,
      ExteriorAlgebra.map_apply_ιMulti, ExteriorAlgebra.map_apply_ιMulti,
      ExteriorAlgebra.ιMulti_mul_ιMulti]
    rfl
  rw [← hsymm, LinearEquiv.apply_symm_apply]

/-! ### The decomposition in degree `n` -/

section Uncompleted

variable (A : Type uA) [CommRing A] (B : DividedPowerRing.{uB}) [Algebra A B] (W : Type uW)

/-- The coefficient factor in bidegree `i`: `⋀ⁱ_P (P ⊗_B Ω¹_{B/A,δ})`, the exterior power over
`P` of the base change of the divided power differentials of `B`.  The divided power ideal of
`B` is arbitrary, so this factor is in general not free. -/
public abbrev polynomialCoefficientForms (i : ℕ) : Type (max uB uW) :=
  ⋀[setIndexedDividedPowerPolynomialAlgebra B W]^i
    (setIndexedDividedPowerPolynomialAlgebra B W ⊗[B]
      dividedPowerDifferentials (A := A) B.dividedPowers)

/-- The variable factor in bidegree `j`: `⋀ʲ_P (W →₀ P)`, the `j`-th exterior power of the free
`P`-module on the symbols `d x_w`.

This is **not** called `Ωʲ_{P/B,δ}`, and is not claimed to be it: the library contains no proof
that `Ω¹_{P/B,δ} ≅ (W →₀ P)`, indeed no divided power differentials of `P` over `B` at all. -/
public abbrev polynomialVariableForms (j : ℕ) : Type (max uB uW) :=
  ⋀[setIndexedDividedPowerPolynomialAlgebra B W]^j
    (W →₀ setIndexedDividedPowerPolynomialAlgebra B W)

/-- The bidegree-`(i, j)` summand of the degree-`n` decomposition:
`(⋀ⁱ_P (P ⊗_B Ω¹_{B/A,δ})) ⊗_P (⋀ʲ_P (W →₀ P))`. -/
public abbrev polynomialBidegreeForms (i j : ℕ) : Type (max uB uW) :=
  TensorProduct (setIndexedDividedPowerPolynomialAlgebra B W)
    (polynomialCoefficientForms A B W i) (polynomialVariableForms B W j)

/-- **The coefficient factor is `P ⊗_B Ωⁱ_{B/A,δ}`.**  The exterior power may be taken over `B`
and then base changed, instead of over `P` after base changing, by
`ExteriorAlgebra.exteriorPowerBaseChange`, which is a base-change statement for the universal
property of alternating maps and needs neither flatness nor a Noetherian hypothesis. -/
public def polynomialCoefficientFormsBaseChangeEquiv (i : ℕ) :
    setIndexedDividedPowerPolynomialAlgebra B W ⊗[B]
        dividedPowerDifferentialForms (A := A) B.dividedPowers i ≃ₗ[
      setIndexedDividedPowerPolynomialAlgebra B W]
      polynomialCoefficientForms A B W i :=
  ExteriorAlgebra.exteriorPowerBaseChange (B : Type uB)
    (setIndexedDividedPowerPolynomialAlgebra B W)
    (dividedPowerDifferentials (A := A) B.dividedPowers) i

/-- **The divided power polynomial decomposition of differential forms in degree `n`:**

`Ωⁿ_{P/A,δ'} ≅ ⨁_{i + j = n} ((⋀ⁱ_P (P ⊗_B Ω¹_{B/A,δ})) ⊗_P (⋀ʲ_P (W →₀ P)))`,

linearly over `P`.  It is the `n`-th exterior power of the degree-one decomposition of
[Stacks, Tag 07HS], split by the Künneth isomorphism `exteriorPower.prodEquivDirectSum`.  The
divided power ideal of `B` is arbitrary and `W` is arbitrary. -/
public def dividedPowerPolynomialFormsEquiv (n : ℕ) :
    dividedPowerDifferentialForms (A := A)
        (setIndexedDividedPowerPolynomialDividedPowers B W) n ≃ₗ[
      setIndexedDividedPowerPolynomialAlgebra B W]
      DirectSum {ij : ℕ × ℕ // ij.1 + ij.2 = n}
        (fun ij ↦ polynomialBidegreeForms A B W ij.1.1 ij.1.2) :=
  exteriorPowerCongr n (dividedPowerDifferentialsDividedPowerPolynomialEquiv (A := A) B W).1 ≪≫ₗ
    exteriorPower.prodEquivDirectSum n

/-- **The decomposition on a split wedge.**  The wedge of the differentials of `i` coefficients
`b₁, …, bᵢ ∈ B` followed by the differentials of `j` variables `x_{w₁}, …, x_{wⱼ}` lands in the
single summand indexed by `(i, j)`, as the generator
`((1 ⊗ d b₁) ∧ ⋯ ∧ (1 ⊗ d bᵢ)) ⊗ (d x_{w₁} ∧ ⋯ ∧ d x_{wⱼ})`.

Such wedges span `Ωⁿ_{P/A,δ'}` over `P`, because the differentials of coefficients and of
variables span `Ω¹_{P/A,δ'}`; so this pins the decomposition down.  The spanning statement
itself is not needed here and is not proved. -/
public theorem dividedPowerPolynomialFormsEquiv_wedge (i j : ℕ) (b : Fin i → B)
    (w : Fin j → W) :
    dividedPowerPolynomialFormsEquiv A B W (i + j)
        (exteriorPower.ιMulti (setIndexedDividedPowerPolynomialAlgebra B W) (i + j)
          (Fin.append
            (fun k ↦ dividedPowerDifferential (A := A)
              (setIndexedDividedPowerPolynomialDividedPowers B W)
              (algebraMap (B : Type uB) (setIndexedDividedPowerPolynomialAlgebra B W) (b k)))
            fun k ↦ dividedPowerDifferential (A := A)
              (setIndexedDividedPowerPolynomialDividedPowers B W)
              (dividedPowerPolynomialVariable (B : Type uB) (w k)))) =
      DirectSum.lof (setIndexedDividedPowerPolynomialAlgebra B W)
        {ij : ℕ × ℕ // ij.1 + ij.2 = i + j}
        (fun ij ↦ polynomialBidegreeForms A B W ij.1.1 ij.1.2) ⟨(i, j), rfl⟩
        (exteriorPower.ιMulti (setIndexedDividedPowerPolynomialAlgebra B W) i
            (fun k ↦ (1 : setIndexedDividedPowerPolynomialAlgebra B W) ⊗ₜ[B]
              dividedPowerDifferential (A := A) B.dividedPowers (b k)) ⊗ₜ[
          setIndexedDividedPowerPolynomialAlgebra B W]
          exteriorPower.ιMulti (setIndexedDividedPowerPolynomialAlgebra B W) j
            fun k ↦ Finsupp.single (w k)
              (1 : setIndexedDividedPowerPolynomialAlgebra B W)) := by
  have hsplit : (fun m ↦ (dividedPowerDifferentialsDividedPowerPolynomialEquiv (A := A) B W).1
        (Fin.append
          (fun k ↦ dividedPowerDifferential (A := A)
            (setIndexedDividedPowerPolynomialDividedPowers B W)
            (algebraMap (B : Type uB) (setIndexedDividedPowerPolynomialAlgebra B W) (b k)))
          (fun k ↦ dividedPowerDifferential (A := A)
            (setIndexedDividedPowerPolynomialDividedPowers B W)
            (dividedPowerPolynomialVariable (B : Type uB) (w k))) m)) =
      Fin.append
        (fun k ↦ LinearMap.inl (setIndexedDividedPowerPolynomialAlgebra B W) _ _
          ((1 : setIndexedDividedPowerPolynomialAlgebra B W) ⊗ₜ[B]
            dividedPowerDifferential (A := A) B.dividedPowers (b k)))
        fun k ↦ LinearMap.inr (setIndexedDividedPowerPolynomialAlgebra B W) _ _
          (Finsupp.single (w k) (1 : setIndexedDividedPowerPolynomialAlgebra B W)) := by
    funext m
    refine Fin.addCases (fun k ↦ ?_) (fun k ↦ ?_) m
    · rw [Fin.append_left, Fin.append_left]
      exact (dividedPowerDifferentialsDividedPowerPolynomialEquiv (A := A) B W).2.1 (b k)
    · rw [Fin.append_right, Fin.append_right]
      exact (dividedPowerDifferentialsDividedPowerPolynomialEquiv (A := A) B W).2.2 (w k)
  refine Eq.trans (DFunLike.congr_arg (exteriorPower.prodEquivDirectSum (i + j))
    ((exteriorPowerCongr_ιMulti (i + j) _ _).trans
      (DFunLike.congr_arg
        (exteriorPower.ιMulti (setIndexedDividedPowerPolynomialAlgebra B W) (i + j))
        hsplit))) ?_
  exact prodEquivDirectSum_ιMulti_append i j
    (fun k ↦ (1 : setIndexedDividedPowerPolynomialAlgebra B W) ⊗ₜ[B]
      dividedPowerDifferential (A := A) B.dividedPowers (b k))
    fun k ↦ Finsupp.single (w k) (1 : setIndexedDividedPowerPolynomialAlgebra B W)

/-! ### Freeness of the two factors over the coefficients -/

/-- **`⋀ʲ_P (W →₀ P)` is free over `P` on the `j`-element subsets of `W`.**  The basis vector
indexed by `I` is the wedge `d x_{w₁} ∧ ⋯ ∧ d x_{wⱼ}` of the standard generators indexed by the
elements of `I`, taken in the order of `W`.

This is the only freeness in the relative decomposition: the coefficient factor
`⋀ⁱ_P (P ⊗_B Ω¹_{B/A,δ})` is not free, because `Ω¹_{B/A,δ}` need not be.  With `I = ⊥` the
coefficient factor collapses in positive degree and this basis becomes the whole basis of
`Ωⁿ_{P/A,δ'}`, which is the shape [Stacks, Tag 07LC] is proved in. -/
public def polynomialVariableFormsBasis [LinearOrder W] (j : ℕ) :
    Module.Basis (Set.powersetCard W j) (setIndexedDividedPowerPolynomialAlgebra B W)
      (polynomialVariableForms B W j) :=
  Module.Basis.exteriorPower j
    (Finsupp.basisSingleOne (R := setIndexedDividedPowerPolynomialAlgebra B W) (ι := W))

/-- The basis vector of `⋀ʲ_P (W →₀ P)` indexed by a `j`-element subset `I` of `W` is the wedge
of the standard generators `d x_w` for `w ∈ I`. -/
public theorem polynomialVariableFormsBasis_apply [LinearOrder W] (j : ℕ)
    (I : Set.powersetCard W j) :
    polynomialVariableFormsBasis B W j I =
      exteriorPower.ιMulti_family (setIndexedDividedPowerPolynomialAlgebra B W) j
        (fun w : W ↦ Finsupp.single w (1 : setIndexedDividedPowerPolynomialAlgebra B W)) I :=
  exteriorPower.basis_apply _ j _ I

/-- **The bidegree-`(i, j)` summand is free over its coefficient module.**  It is the free module
on the `j`-element subsets of `W` with coefficients in `P ⊗_B Ωⁱ_{B/A,δ}`: the variable factor
is free on those subsets by `polynomialVariableFormsBasis`, and the coefficient factor is
`P ⊗_B Ωⁱ_{B/A,δ}` by `polynomialCoefficientFormsBaseChangeEquiv`.

Nothing is claimed to be free over `P`, and nothing could be: `Ωⁱ_{B/A,δ}` is an arbitrary
`B`-module here. -/
public def polynomialBidegreeFormsFreeEquiv [LinearOrder W] (i j : ℕ) :
    polynomialBidegreeForms A B W i j ≃ₗ[setIndexedDividedPowerPolynomialAlgebra B W]
      (Set.powersetCard W j →₀
        (setIndexedDividedPowerPolynomialAlgebra B W ⊗[B]
          dividedPowerDifferentialForms (A := A) B.dividedPowers i)) := by
  classical
  exact (TensorProduct.congr (polynomialCoefficientFormsBaseChangeEquiv A B W i).symm
      (polynomialVariableFormsBasis B W j).repr).trans
    (TensorProduct.finsuppScalarRight (setIndexedDividedPowerPolynomialAlgebra B W)
      (setIndexedDividedPowerPolynomialAlgebra B W) _ _)

/-- The free decomposition of the bidegree-`(i, j)` summand on a pure tensor whose second factor
is a basis wedge: the coefficient is placed in the single slot indexed by that subset. -/
public theorem polynomialBidegreeFormsFreeEquiv_tmul_basis [LinearOrder W] (i j : ℕ)
    (c : polynomialCoefficientForms A B W i) (I : Set.powersetCard W j) :
    polynomialBidegreeFormsFreeEquiv A B W i j
        (c ⊗ₜ[setIndexedDividedPowerPolynomialAlgebra B W]
          polynomialVariableFormsBasis B W j I) =
      Finsupp.single I ((polynomialCoefficientFormsBaseChangeEquiv A B W i).symm c) := by
  classical
  have hrepr : (polynomialVariableFormsBasis B W j).repr
      (polynomialVariableFormsBasis B W j I) =
      Finsupp.single I (1 : setIndexedDividedPowerPolynomialAlgebra B W) :=
    (polynomialVariableFormsBasis B W j).repr_self I
  change TensorProduct.finsuppScalarRight _ _ _ _
    (TensorProduct.congr (polynomialCoefficientFormsBaseChangeEquiv A B W i).symm
      (polynomialVariableFormsBasis B W j).repr
      (c ⊗ₜ[setIndexedDividedPowerPolynomialAlgebra B W]
        polynomialVariableFormsBasis B W j I)) = _
  rw [TensorProduct.congr_tmul, hrepr, ← LinearEquiv.eq_symm_apply]
  simp

/-- **`P ⊗_B Ωⁱ_{B/A,δ}` is free over `Ωⁱ_{B/A,δ}` on the divided power monomials.**  The
coefficient module of the bidegree-`(i, j)` summand is, `B`-linearly, the free module on the
exponent vectors `L : W →₀ ℕ` with coefficients in `Ωⁱ_{B/A,δ}`, because `P` is free over `B` on
the divided power monomials `x^{[L]}`.

Only `B`-linearity is asserted: the right-hand side carries no `P`-action. -/
public def polynomialCoefficientMonomialEquiv (i : ℕ) :
    setIndexedDividedPowerPolynomialAlgebra B W ⊗[B]
        dividedPowerDifferentialForms (A := A) B.dividedPowers i ≃ₗ[(B : Type uB)]
      ((W →₀ ℕ) →₀ dividedPowerDifferentialForms (A := A) B.dividedPowers i) := by
  classical
  exact (TensorProduct.congr (dividedPowerPolynomialMonomialBasis (B : Type uB) W).repr
      (LinearEquiv.refl (B : Type uB)
        (dividedPowerDifferentialForms (A := A) B.dividedPowers i))).trans
    (TensorProduct.finsuppScalarLeft (B : Type uB)
      (dividedPowerDifferentialForms (A := A) B.dividedPowers i) (W →₀ ℕ))

/-- The monomial decomposition on a pure tensor `x^{[L]} ⊗ ω`: it is placed in the single slot
indexed by the exponent vector `L`. -/
public theorem polynomialCoefficientMonomialEquiv_monomial_tmul (i : ℕ) (L : W →₀ ℕ)
    (omega : dividedPowerDifferentialForms (A := A) B.dividedPowers i) :
    polynomialCoefficientMonomialEquiv A B W i
        (dividedPowerPolynomialMonomial (B : Type uB) L ⊗ₜ[(B : Type uB)] omega) =
      Finsupp.single L omega := by
  classical
  have hrepr : (dividedPowerPolynomialMonomialBasis (B : Type uB) W).repr
      (dividedPowerPolynomialMonomial (B : Type uB) L) =
      Finsupp.single L (1 : (B : Type uB)) := by
    rw [← dividedPowerPolynomialMonomialBasis_apply (B : Type uB) L]
    exact (dividedPowerPolynomialMonomialBasis (B : Type uB) W).repr_self L
  change TensorProduct.finsuppScalarLeft _ _ _
    (TensorProduct.congr (dividedPowerPolynomialMonomialBasis (B : Type uB) W).repr
      (LinearEquiv.refl _ _)
      (dividedPowerPolynomialMonomial (B : Type uB) L ⊗ₜ[(B : Type uB)] omega)) = _
  rw [TensorProduct.congr_tmul, hrepr, ← LinearEquiv.eq_symm_apply]
  simp

end Uncompleted

end DividedPowerPolynomial

end Crystalline

end
