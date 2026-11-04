module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.QuasiIso
public import StacksFrontier.AlgebraicGeometry.Crystalline.Differentials
public import StacksFrontier.AlgebraicGeometry.Crystalline.Differentials.BaseChangeHomotopyInverse
public import StacksFrontier.RingTheory.DividedPowers.Polynomial.Basic

/-!
# The crystalline Poincaré lemma for one divided power variable

Let `A` be a ring, let `(B, I, δ)` be a divided power ring which is an `A`-algebra, and let
`P = B⟨z⟩` be the divided power polynomial ring on one variable over `B`, with divided power
ideal `IP + P₊`.  The divided power differentials of `P` over `A` decompose as

`Ω¹_{P/A,δ'} = (P ⊗_B Ω¹_{B/A,δ}) ⊕ P · d z`,

the one-variable case of the divided power polynomial formula.  Read through that splitting,
`P` over `B` is an instance of the situation of Section 60.25: the comparison
`ψ : Ω¹_{B/A,δ} → Ω¹_{P/A,δ'}` on one-forms is the inclusion of the first summand, and the
second summand is free of rank one on `d z`.

The divided powers `z^[n]` of the variable form a basis of `P` over `B`, and the operator
`θ : z^[n] ↦ z^[n+1]` together with `a = 1` verifies the seven standing assumptions of that
section: the coefficient of `dz` in `d(θ f)` is `f`, the difference `f - θ(∂_z f)` is the
constant term of `f`, and `θ ⊗ 1` commutes with the base-change component of the differential
on the nose.  Feeding this into the homotopy inverse of Tag 07Q7 at `a = 1` makes the canonical
map of de Rham complexes

`M ⊗_B Ω^*_{B/A,δ} ⟶ M ⊗_B Ω^*_{P/A,δ'}`

attached to a `B`-module `M` with an integrable connection a homotopy equivalence, hence a
quasi-isomorphism: the crystalline Poincaré lemma in one variable.

## Main definitions

* `Crystalline.dividedPowerPolynomialOneFormComparison` — the comparison `ψ` of one-forms,
  semilinear over `B → P`.
* `Crystalline.dividedPowerPolynomialDzDecomposition` — the decomposition of `Ω¹_{P/A,δ'}` into
  the base change of `Ω¹_{B/A,δ}` and the free rank-one piece spanned by `d z`.
* `Crystalline.oneVariableDifferentialsEquiv` — that decomposition with the free summand written
  as `P` rather than as `Unit →₀ P`.
* `Crystalline.sourceDeRhamOfKaehler` — the de Rham complex of a ring over a base, as the data
  that divided power differential descent takes as input.
* `Crystalline.oneVariableMonomialBasis` — the basis `z^[n]` of `P` over `B`.
* `Crystalline.oneVariablePartialZ` and `Crystalline.oneVariableTheta` — the coefficient `∂_z`
  of `dz` in the differential, and the operator raising the divided power degree of `z` by one.
* `Crystalline.connectionDeRhamComplex` — the de Rham complex of a connection, as a cochain
  complex of modules over the base ring.
* `Crystalline.oneVariableDeRhamComparison` — the map of de Rham complexes of Tag 07LD.

## Main results

* `Crystalline.oneVariableCoefficient_universallyInjective` — `B → B⟨z⟩` is universally
  injective.
* `Crystalline.oneVariablePartialZ_comp_oneVariableTheta`,
  `Crystalline.oneVariableConstantTerm_mem_range`,
  `Crystalline.oneVariableDOne_oneVariableTheta` — the three remaining standing assumptions of
  Section 60.25 for `θ` at `a = 1`.
* `Crystalline.quasiIso_oneVariableDeRhamComparison` — the crystalline Poincaré lemma for one
  divided power variable.
* `Crystalline.oneVariableTheta_apply`, `Crystalline.oneVariable_sub_theta_partialZ`,
  `Crystalline.oneVariableDividedPowerPolynomial_standingAssumptions` — Example 07Q8: the
  operator `θ` on divided power monomials, the identity `f - θ(∂_z(f)) = f(0)`, and all seven
  standing assumptions of Section 60.25 for `B⟨z⟩` at `a = 1`.
* `Crystalline.exists_homotopyEquiv_oneVariableDeRhamComparison` — at `a = 1` the comparison
  map is a homotopy equivalence, not merely a quasi-isomorphism.

## Implementation notes

The map of de Rham complexes is not constructed here but taken as a hypothesis `c`, pinned down
by the two properties — its value on pure wedges and its commuting with the differentials — that
`Crystalline.existsUnique_baseChangeDeRhamMap` shows determine it uniquely.  This is not a
weakening: by that uniqueness there is exactly one such family, so the statement quantifies over
a single map, the canonical one.

A term of the two complexes is a module over the coefficient ring read through
`RestrictScalars`, and the module structure of such an object of `ModuleCat` is pinned to
`RestrictScalars.module` by `Crystalline.restrictScalarsModuleCat`: the instance that typeclass
search finds for the synonym carries a different, though definitionally equal, additive
structure, which `ModuleCat.of` will not accept.

Tag 07LD is stated in the source for a divided power polynomial ring on an arbitrary family of
variables, and has a second clause about `p`-adic completions.  What is proved here is the case
of a single variable, which Example 07Q8 derives from Tag 07Q7.  The first clause for an arbitrary
family of variables is `Crystalline.DividedPowerPolynomial.quasiIso_polyDeRhamComparison`, and
the clause over the completions is
`Crystalline.DividedPowerPolynomial.quasiIso_completedDeRhamComparison`.

## References

* [Stacks Project, Tag 07HS](https://stacks.math.columbia.edu/tag/07HS)
* [Stacks Project, Tag 07Q7](https://stacks.math.columbia.edu/tag/07Q7)
* [Stacks Project, Tag 07Q8](https://stacks.math.columbia.edu/tag/07Q8)
* [Stacks Project, Tag 07LD](https://stacks.math.columbia.edu/tag/07LD)
-/

@[expose] public section

open DividedPowers
open scoped TensorProduct

universe u v w

namespace Crystalline

section RelativePoincare

variable (A : Type u) [CommRing A] (B : DividedPowerRing.{u}) [Algebra A B]

/-- The divided power polynomial ring `B⟨z⟩` on one variable over a divided power ring. -/
public noncomputable abbrev oneVariableDividedPowerPolynomial : Type u :=
  setIndexedDividedPowerPolynomialAlgebra B Unit

/-- The divided powers of `B⟨z⟩` on its divided power ideal `IB⟨z⟩ + B⟨z⟩₊`. -/
public noncomputable abbrev oneVariableDividedPowers :
    DividedPowers (dividedPowerPolynomialIdeal B.ideal Unit) :=
  setIndexedDividedPowerPolynomialDividedPowers B Unit

/-- The divided power variable `z` of `B⟨z⟩`. -/
public noncomputable abbrev oneVariableVariable : oneVariableDividedPowerPolynomial B :=
  dividedPowerPolynomialVariable (B : Type u) ()

/-- The decomposition of `Ω¹_{B⟨z⟩/A,δ'}` supplied by the divided power polynomial formula,
with the free summand written as `B⟨z⟩` rather than as `Unit →₀ B⟨z⟩`. -/
public noncomputable def oneVariableDifferentialsEquiv :
    dividedPowerDifferentials (A := A) (oneVariableDividedPowers B) ≃ₗ[
      oneVariableDividedPowerPolynomial B]
      ((oneVariableDividedPowerPolynomial B ⊗[B]
          dividedPowerDifferentials (A := A) B.dividedPowers) ×
        oneVariableDividedPowerPolynomial B) :=
  (dividedPowerDifferentialsDividedPowerPolynomialEquiv (A := A) B Unit).1.trans
    (LinearEquiv.prodCongr (LinearEquiv.refl _ _)
      (Finsupp.uniqueLinearEquiv (oneVariableDividedPowerPolynomial B)
        (oneVariableDividedPowerPolynomial B) ()))

/-- The decomposition carries the differential of a coefficient into the first summand. -/
public theorem oneVariableDifferentialsEquiv_coefficient (b : B) :
    oneVariableDifferentialsEquiv A B (dividedPowerDifferential (A := A)
        (oneVariableDividedPowers B)
        (algebraMap (B : Type u) (oneVariableDividedPowerPolynomial B) b)) =
      (1 ⊗ₜ[B] dividedPowerDifferential (A := A) B.dividedPowers b, 0) := by
  have h := (dividedPowerDifferentialsDividedPowerPolynomialEquiv (A := A) B Unit).2.1 b
  show (LinearEquiv.prodCongr (LinearEquiv.refl _ _) _)
    ((dividedPowerDifferentialsDividedPowerPolynomialEquiv (A := A) B Unit).1 _) = _
  rw [h]
  refine Prod.ext rfl ?_
  show Finsupp.uniqueLinearEquiv (oneVariableDividedPowerPolynomial B)
    (oneVariableDividedPowerPolynomial B) () 0 = 0
  rw [map_zero]

/-- The decomposition carries the differential of the variable to the generator of the free
summand. -/
public theorem oneVariableDifferentialsEquiv_variable :
    oneVariableDifferentialsEquiv A B (dividedPowerDifferential (A := A)
        (oneVariableDividedPowers B) (oneVariableVariable B)) = (0, 1) := by
  have h := (dividedPowerDifferentialsDividedPowerPolynomialEquiv (A := A) B Unit).2.2 ()
  show (LinearEquiv.prodCongr (LinearEquiv.refl _ _) _)
    ((dividedPowerDifferentialsDividedPowerPolynomialEquiv (A := A) B Unit).1 _) = _
  rw [h]
  refine Prod.ext rfl ?_
  show Finsupp.uniqueLinearEquiv (oneVariableDividedPowerPolynomial B)
    (oneVariableDividedPowerPolynomial B) () (Finsupp.single () 1) = 1
  simp

/-- The comparison `ψ : Ω¹_{B/A,δ} → Ω¹_{B⟨z⟩/A,δ'}` of one-forms, the inclusion of the base
change summand of the divided power polynomial decomposition. -/
public noncomputable def dividedPowerPolynomialOneFormComparison :
    dividedPowerDifferentials (A := A) B.dividedPowers →ₛₗ[algebraMap (B : Type u)
        (oneVariableDividedPowerPolynomial B)]
      dividedPowerDifferentials (A := A) (oneVariableDividedPowers B) where
  toFun om := (oneVariableDifferentialsEquiv A B).symm (1 ⊗ₜ[B] om, 0)
  map_add' om om' := by
    have h : ((1 : oneVariableDividedPowerPolynomial B) ⊗ₜ[B] (om + om'),
          (0 : oneVariableDividedPowerPolynomial B)) =
        ((1 : oneVariableDividedPowerPolynomial B) ⊗ₜ[B] om,
            (0 : oneVariableDividedPowerPolynomial B)) +
          ((1 : oneVariableDividedPowerPolynomial B) ⊗ₜ[B] om',
            (0 : oneVariableDividedPowerPolynomial B)) := by
      refine Prod.ext ?_ ?_
      · change (1 : oneVariableDividedPowerPolynomial B) ⊗ₜ[B] (om + om') =
          (1 : oneVariableDividedPowerPolynomial B) ⊗ₜ[B] om +
            (1 : oneVariableDividedPowerPolynomial B) ⊗ₜ[B] om'
        rw [TensorProduct.tmul_add]
      · change (0 : oneVariableDividedPowerPolynomial B) = 0 + 0
        rw [add_zero]
    change (oneVariableDifferentialsEquiv A B).symm
      ((1 : oneVariableDividedPowerPolynomial B) ⊗ₜ[B] (om + om'), 0) = _
    rw [h, map_add]
  map_smul' b om := by
    have h : ((1 : oneVariableDividedPowerPolynomial B) ⊗ₜ[B] (b • om),
          (0 : oneVariableDividedPowerPolynomial B)) =
        algebraMap (B : Type u) (oneVariableDividedPowerPolynomial B) b •
          ((1 : oneVariableDividedPowerPolynomial B) ⊗ₜ[B] om,
            (0 : oneVariableDividedPowerPolynomial B)) := by
      refine Prod.ext ?_ ?_
      · change (1 : oneVariableDividedPowerPolynomial B) ⊗ₜ[B] (b • om) =
          algebraMap (B : Type u) (oneVariableDividedPowerPolynomial B) b •
            ((1 : oneVariableDividedPowerPolynomial B) ⊗ₜ[B] om)
        rw [TensorProduct.tmul_smul, IsScalarTower.algebraMap_smul]
      · change (0 : oneVariableDividedPowerPolynomial B) =
          algebraMap (B : Type u) (oneVariableDividedPowerPolynomial B) b • 0
        rw [smul_zero]
    change (oneVariableDifferentialsEquiv A B).symm
      ((1 : oneVariableDividedPowerPolynomial B) ⊗ₜ[B] (b • om), 0) = _
    rw [h, map_smul]

/-- The comparison of one-forms is compatible with the two universal differentials. -/
public theorem dividedPowerPolynomialOneFormComparison_dividedPowerDifferential (b : B) :
    dividedPowerPolynomialOneFormComparison A B
        (dividedPowerDifferential (A := A) B.dividedPowers b) =
      dividedPowerDifferential (A := A) (oneVariableDividedPowers B)
        (algebraMap (B : Type u) (oneVariableDividedPowerPolynomial B) b) := by
  show (oneVariableDifferentialsEquiv A B).symm _ = _
  rw [← oneVariableDifferentialsEquiv_coefficient A B b, LinearEquiv.symm_apply_apply]

/-- **The divided power polynomial extension is `dz`-decomposed.**  Assumption (2) of
Section 60.25 holds for `B → B⟨z⟩`: the one-forms of `B⟨z⟩` are the base change of those of `B`
together with a free rank-one piece spanned by `d z`. -/
public noncomputable def dividedPowerPolynomialDzDecomposition :
    DzDecomposition
      (dividedPowerDifferentialRelations (A := A) (oneVariableDividedPowers B)).mkQ
      (dividedPowerPolynomialOneFormComparison A B) (oneVariableVariable B) where
  equiv := (oneVariableDifferentialsEquiv A B).symm
  equiv_tmul b' om := by
    have h : (b' ⊗ₜ[B] om, (0 : oneVariableDividedPowerPolynomial B)) =
        b' • ((1 : oneVariableDividedPowerPolynomial B) ⊗ₜ[B] om,
          (0 : oneVariableDividedPowerPolynomial B)) := by
      refine Prod.ext ?_ ?_
      · change b' ⊗ₜ[B] om =
          b' • ((1 : oneVariableDividedPowerPolynomial B) ⊗ₜ[B] om)
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      · change (0 : oneVariableDividedPowerPolynomial B) = b' • 0
        rw [smul_zero]
    change (oneVariableDifferentialsEquiv A B).symm (b' ⊗ₜ[B] om, 0) =
      b' • (oneVariableDifferentialsEquiv A B).symm
        ((1 : oneVariableDividedPowerPolynomial B) ⊗ₜ[B] om, 0)
    rw [h, map_smul]
  equiv_dz b' := by
    have hz : (oneVariableDifferentialsEquiv A B).symm
          ((0 : oneVariableDividedPowerPolynomial B ⊗[B]
            dividedPowerDifferentials (A := A) B.dividedPowers),
            (1 : oneVariableDividedPowerPolynomial B)) =
        dividedPowerDifferential (A := A) (oneVariableDividedPowers B)
          (oneVariableVariable B) := by
      rw [← oneVariableDifferentialsEquiv_variable A B, LinearEquiv.symm_apply_apply]
    have h : ((0 : oneVariableDividedPowerPolynomial B ⊗[B]
            dividedPowerDifferentials (A := A) B.dividedPowers), b') =
        b' • ((0 : oneVariableDividedPowerPolynomial B ⊗[B]
            dividedPowerDifferentials (A := A) B.dividedPowers),
          (1 : oneVariableDividedPowerPolynomial B)) := by
      refine Prod.ext ?_ ?_
      · change (0 : oneVariableDividedPowerPolynomial B ⊗[B]
          dividedPowerDifferentials (A := A) B.dividedPowers) = b' • 0
        rw [smul_zero]
      · change b' = b' • (1 : oneVariableDividedPowerPolynomial B)
        rw [smul_eq_mul, mul_one]
    change (oneVariableDifferentialsEquiv A B).symm
      ((0 : oneVariableDividedPowerPolynomial B ⊗[B]
        dividedPowerDifferentials (A := A) B.dividedPowers), b') = _
    rw [h, map_smul, hz]
    rfl

/-- The coefficient inclusion `B → B⟨z⟩` is universally injective. -/
public theorem oneVariableCoefficient_universallyInjective :
    Stacks.UniversalInjectivity.LocalizationCriteria.UniversallyInjective.{v}
      (Algebra.linearMap (B : Type u) (oneVariableDividedPowerPolynomial B)) := by
  have hr : (dividedPowerPolynomialAugmentation (B : Type u) Unit).toLinearMap ∘ₗ
      Algebra.linearMap (B : Type u) (oneVariableDividedPowerPolynomial B) =
      LinearMap.id := by
    refine LinearMap.ext fun b => ?_
    show dividedPowerPolynomialAugmentation (B : Type u) Unit
      (algebraMap (B : Type u) (oneVariableDividedPowerPolynomial B) b) = b
    rw [AlgHom.commutes]
    rfl
  intro Q _ _
  have h := congrArg
    (fun f : (B : Type u) →ₗ[B] (B : Type u) => LinearMap.rTensor Q f) hr
  rw [LinearMap.rTensor_comp, LinearMap.rTensor_id] at h
  have hid : ∀ t,
      LinearMap.rTensor Q (dividedPowerPolynomialAugmentation (B : Type u) Unit).toLinearMap
        (LinearMap.rTensor Q
          (Algebra.linearMap (B : Type u) (oneVariableDividedPowerPolynomial B)) t) = t :=
    fun t => LinearMap.congr_fun h t
  intro x y hxy
  have h1 := congrArg
    (LinearMap.rTensor Q (dividedPowerPolynomialAugmentation (B : Type u) Unit).toLinearMap) hxy
  rwa [hid, hid] at h1

/-- The de Rham complex of a commutative ring over a base, as the data required for divided
power differential descent: the Kähler de Rham differentials with their defining rule on
generators.  This is `Stacks.DeRham.DifferentialDescent.sourceDeRham`, the construction of
[Stacks, Tag 0FKF]. -/
public noncomputable abbrev sourceDeRhamOfKaehler (R S : Type u) [CommRing R] [CommRing S]
    [Algebra R S] : Stacks.DeRham.DifferentialDescent.SourceDeRham R S :=
  Stacks.DeRham.DifferentialDescent.sourceDeRham R S

/-! ### The divided power monomial basis of `B⟨z⟩` and the operator `θ` -/

/-- An exponent vector in one variable is determined by the exponent of that variable. -/
public noncomputable def oneVariableExponentEquiv : (Unit →₀ ℕ) ≃ ℕ where
  toFun n := n ()
  invFun m := Finsupp.single () m
  left_inv n := Finsupp.unique_ext (by simp)
  right_inv m := by simp

/-- The divided powers `z^[n]` of the variable form a basis of `B⟨z⟩` over `B`. -/
public noncomputable def oneVariableMonomialBasis :
    Module.Basis ℕ (B : Type u) (oneVariableDividedPowerPolynomial B) :=
  (dividedPowerPolynomialMonomialBasis (B : Type u) Unit).reindex oneVariableExponentEquiv

/-- The `n`-th vector of the monomial basis is the `n`-th divided power of the variable. -/
public theorem oneVariableMonomialBasis_apply (n : ℕ) :
    oneVariableMonomialBasis B n =
      (oneVariableDividedPowers B).dpow n (oneVariableVariable B) := by
  have hmon : dividedPowerPolynomialMonomial (B : Type u) (Finsupp.single () n) =
      dividedPowerPolynomialVariableMonomial (B : Type u) () n :=
    Finsupp.prod_single_index DividedPowerAlgebra.dp_zero
  rw [setIndexedDividedPowerPolynomialDividedPowers_dpow_variable, oneVariableMonomialBasis,
    Module.Basis.reindex_apply, dividedPowerPolynomialMonomialBasis_apply]
  exact hmon

/-- The zeroth divided power of the variable is `1`. -/
public theorem oneVariableDpow_zero :
    (oneVariableDividedPowers B).dpow 0 (oneVariableVariable B) = 1 :=
  (oneVariableDividedPowers B).dpow_zero (variable_mem_polynomialIdeal B ())

/-- The universal divided power differential is additive. -/
private theorem oneVariableDifferential_add (f g : oneVariableDividedPowerPolynomial B) :
    dividedPowerDifferential (A := A) (oneVariableDividedPowers B) (f + g) =
      dividedPowerDifferential (A := A) (oneVariableDividedPowers B) f +
        dividedPowerDifferential (A := A) (oneVariableDividedPowers B) g := by
  simp only [dividedPowerDifferential, map_add]

/-- The universal divided power differential obeys the Leibniz rule. -/
private theorem oneVariableDifferential_mul (f g : oneVariableDividedPowerPolynomial B) :
    dividedPowerDifferential (A := A) (oneVariableDividedPowers B) (f * g) =
      f • dividedPowerDifferential (A := A) (oneVariableDividedPowers B) g +
        g • dividedPowerDifferential (A := A) (oneVariableDividedPowers B) f := by
  simp only [dividedPowerDifferential, Derivation.leibniz, map_add, map_smul]

/-- The universal divided power differential of `1` vanishes. -/
private theorem oneVariableDifferential_one :
    dividedPowerDifferential (A := A) (oneVariableDividedPowers B) 1 = 0 := by
  simp only [dividedPowerDifferential, Derivation.map_one_eq_zero, map_zero]

/-- The component of `d f` in the base-change summand, read through the splitting. -/
private theorem oneVariableDOne_eq (f : oneVariableDividedPowerPolynomial B) :
    (dividedPowerPolynomialDzDecomposition A B).dOne f =
      (oneVariableDifferentialsEquiv A B
        (dividedPowerDifferential (A := A) (oneVariableDividedPowers B) f)).1 :=
  rfl

/-- The coefficient of `dz` in `d f`, read through the splitting. -/
private theorem oneVariablePartialZ_eq (f : oneVariableDividedPowerPolynomial B) :
    (dividedPowerPolynomialDzDecomposition A B).partialZ f =
      (oneVariableDifferentialsEquiv A B
        (dividedPowerDifferential (A := A) (oneVariableDividedPowers B) f)).2 :=
  rfl

/-- The differential of `z^[n+1]` is `z^[n] d z`, so it is carried to the free summand. -/
public theorem oneVariableDifferentialsEquiv_dpow_succ (n : ℕ) :
    oneVariableDifferentialsEquiv A B (dividedPowerDifferential (A := A)
        (oneVariableDividedPowers B)
        ((oneVariableDividedPowers B).dpow (n + 1) (oneVariableVariable B))) =
      (0, (oneVariableDividedPowers B).dpow n (oneVariableVariable B)) := by
  have h : dividedPowerDifferential (A := A) (oneVariableDividedPowers B)
        ((oneVariableDividedPowers B).dpow (n + 1) (oneVariableVariable B)) =
      (oneVariableDividedPowers B).dpow n (oneVariableVariable B) •
        dividedPowerDifferential (A := A) (oneVariableDividedPowers B)
          (oneVariableVariable B) :=
    dividedPowerDifferential_dpow (A := A) (oneVariableDividedPowers B)
      ⟨oneVariableVariable B, variable_mem_polynomialIdeal B ()⟩ n
  rw [h, map_smul, oneVariableDifferentialsEquiv_variable]
  exact Prod.ext (smul_zero _) (smul_eq_mul _ _ |>.trans (mul_one _))

/-- The differential of `z^[0] = 1` vanishes. -/
public theorem oneVariableDifferentialsEquiv_dpow_zero :
    oneVariableDifferentialsEquiv A B (dividedPowerDifferential (A := A)
        (oneVariableDividedPowers B)
        ((oneVariableDividedPowers B).dpow 0 (oneVariableVariable B))) = 0 := by
  rw [oneVariableDpow_zero, oneVariableDifferential_one, map_zero]

/-- The divided powers of the variable have no component in the base-change summand. -/
public theorem oneVariableDOne_dpow (n : ℕ) :
    (dividedPowerPolynomialDzDecomposition A B).dOne
        ((oneVariableDividedPowers B).dpow n (oneVariableVariable B)) = 0 := by
  cases n with
  | zero => rw [oneVariableDOne_eq, oneVariableDifferentialsEquiv_dpow_zero]; rfl
  | succ n => rw [oneVariableDOne_eq, oneVariableDifferentialsEquiv_dpow_succ]

/-- The base-change component of the differential obeys the Leibniz rule, the correction term
being the differential of the scalar. -/
private theorem oneVariableDOne_smul (b : (B : Type u))
    (f : oneVariableDividedPowerPolynomial B) :
    (dividedPowerPolynomialDzDecomposition A B).dOne (b • f) =
      b • (dividedPowerPolynomialDzDecomposition A B).dOne f +
        f ⊗ₜ[(B : Type u)] dividedPowerDifferential (A := A) B.dividedPowers b := by
  rw [oneVariableDOne_eq, oneVariableDOne_eq, Algebra.smul_def, oneVariableDifferential_mul,
    map_add, map_smul, map_smul, oneVariableDifferentialsEquiv_coefficient, Prod.fst_add,
    Prod.smul_fst, Prod.smul_fst, IsScalarTower.algebraMap_smul, TensorProduct.smul_tmul',
    smul_eq_mul, mul_one]

/-- `∂_z : B⟨z⟩ → B⟨z⟩`, the coefficient of `dz` in the differential, as a `B`-linear map. -/
public noncomputable def oneVariablePartialZ :
    oneVariableDividedPowerPolynomial B →ₗ[(B : Type u)]
      oneVariableDividedPowerPolynomial B where
  toFun := (dividedPowerPolynomialDzDecomposition A B).partialZ
  map_add' f g := by
    rw [oneVariablePartialZ_eq, oneVariablePartialZ_eq, oneVariablePartialZ_eq,
      oneVariableDifferential_add, map_add, Prod.snd_add]
  map_smul' b f := by
    rw [RingHom.id_apply, oneVariablePartialZ_eq, oneVariablePartialZ_eq, Algebra.smul_def,
      oneVariableDifferential_mul, map_add, map_smul, map_smul,
      oneVariableDifferentialsEquiv_coefficient, Prod.snd_add, Prod.smul_snd, Prod.smul_snd,
      smul_zero, add_zero, IsScalarTower.algebraMap_smul]

/-- `θ : B⟨z⟩ → B⟨z⟩`, the `B`-linear operator `z^[n] ↦ z^[n+1]` raising the divided power
degree of the variable by one. -/
public noncomputable def oneVariableTheta :
    oneVariableDividedPowerPolynomial B →ₗ[(B : Type u)]
      oneVariableDividedPowerPolynomial B :=
  (oneVariableMonomialBasis B).constr ℕ fun n => oneVariableMonomialBasis B (n + 1)

/-- `θ` raises the divided power degree of the variable by one. -/
public theorem oneVariableTheta_dpow (n : ℕ) :
    oneVariableTheta B ((oneVariableDividedPowers B).dpow n (oneVariableVariable B)) =
      (oneVariableDividedPowers B).dpow (n + 1) (oneVariableVariable B) := by
  rw [← oneVariableMonomialBasis_apply B n, ← oneVariableMonomialBasis_apply B (n + 1),
    oneVariableTheta, Module.Basis.constr_basis]

/-- `∂_z(z^[n+1]) = z^[n]`. -/
public theorem oneVariablePartialZ_dpow_succ (n : ℕ) :
    oneVariablePartialZ A B
        ((oneVariableDividedPowers B).dpow (n + 1) (oneVariableVariable B)) =
      (oneVariableDividedPowers B).dpow n (oneVariableVariable B) := by
  show (dividedPowerPolynomialDzDecomposition A B).partialZ _ = _
  rw [oneVariablePartialZ_eq, oneVariableDifferentialsEquiv_dpow_succ]

/-- `∂_z(1) = 0`. -/
public theorem oneVariablePartialZ_dpow_zero :
    oneVariablePartialZ A B
      ((oneVariableDividedPowers B).dpow 0 (oneVariableVariable B)) = 0 := by
  show (dividedPowerPolynomialDzDecomposition A B).partialZ _ = _
  rw [oneVariablePartialZ_eq, oneVariableDifferentialsEquiv_dpow_zero]
  rfl

/-- **Assumption (4) of Section 60.25 at `a = 1`.**  Differentiating in `z` undoes `θ`. -/
public theorem oneVariablePartialZ_comp_oneVariableTheta :
    (oneVariablePartialZ A B).comp (oneVariableTheta B) = LinearMap.id := by
  refine (oneVariableMonomialBasis B).ext fun n => ?_
  rw [LinearMap.comp_apply, oneVariableMonomialBasis_apply, oneVariableTheta_dpow,
    oneVariablePartialZ_dpow_succ, LinearMap.id_apply]

/-- **Assumption (6) of Section 60.25 at `a = 1`.**  The difference `f - θ(∂_z f)` is the
constant term of `f`, hence a scalar. -/
public theorem oneVariableConstantTerm_mem_range (f : oneVariableDividedPowerPolynomial B) :
    (1 : (B : Type u)) • f -
        oneVariableTheta B ((dividedPowerPolynomialDzDecomposition A B).partialZ f) ∈
      Set.range (algebraMap (B : Type u) (oneVariableDividedPowerPolynomial B)) := by
  set N := LinearMap.range
    (Algebra.linearMap (B : Type u) (oneVariableDividedPowerPolynomial B)) with hN
  set eps := LinearMap.id (R := (B : Type u))
      (M := oneVariableDividedPowerPolynomial B) -
    (oneVariableTheta B).comp (oneVariablePartialZ A B) with heps
  have hbasis : ∀ n : ℕ, eps (oneVariableMonomialBasis B n) ∈ N := by
    intro n
    rw [heps, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply,
      oneVariableMonomialBasis_apply]
    cases n with
    | zero =>
      rw [oneVariablePartialZ_dpow_zero, map_zero, sub_zero, oneVariableDpow_zero]
      exact ⟨1, by simp⟩
    | succ n =>
      rw [oneVariablePartialZ_dpow_succ, oneVariableTheta_dpow, sub_self]
      exact Submodule.zero_mem N
  have hall : ∀ g : oneVariableDividedPowerPolynomial B, eps g ∈ N := by
    intro g
    have hle : (⊤ : Submodule (B : Type u) (oneVariableDividedPowerPolynomial B)) ≤
        N.comap eps := by
      rw [← (oneVariableMonomialBasis B).span_eq]
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨n, rfl⟩
      exact hbasis n
    exact hle Submodule.mem_top
  obtain ⟨y, hy⟩ := hall f
  refine ⟨y, hy.trans ?_⟩
  rw [heps, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, one_smul]
  rfl

/-- The failure `(θ ⊗ 1) ∘ d₁ - d₁ ∘ θ` of `θ ⊗ 1` to commute with the base-change component
`d₁` of the differential, as a `B`-linear map. -/
private noncomputable def oneVariableDOneDefect :
    oneVariableDividedPowerPolynomial B →ₗ[(B : Type u)]
      (oneVariableDividedPowerPolynomial B ⊗[(B : Type u)]
        dividedPowerDifferentials (A := A) B.dividedPowers) where
  toFun f :=
    TensorProduct.map (oneVariableTheta B)
        (LinearMap.id (R := (B : Type u))
          (M := dividedPowerDifferentials (A := A) B.dividedPowers))
        ((dividedPowerPolynomialDzDecomposition A B).dOne f) -
      (dividedPowerPolynomialDzDecomposition A B).dOne (oneVariableTheta B f)
  map_add' f g := by
    have hd : (dividedPowerPolynomialDzDecomposition A B).dOne (f + g) =
        (dividedPowerPolynomialDzDecomposition A B).dOne f +
          (dividedPowerPolynomialDzDecomposition A B).dOne g := by
      rw [oneVariableDOne_eq, oneVariableDOne_eq, oneVariableDOne_eq,
        oneVariableDifferential_add, map_add, Prod.fst_add]
    have hdt : (dividedPowerPolynomialDzDecomposition A B).dOne
          (oneVariableTheta B (f + g)) =
        (dividedPowerPolynomialDzDecomposition A B).dOne (oneVariableTheta B f) +
          (dividedPowerPolynomialDzDecomposition A B).dOne (oneVariableTheta B g) := by
      rw [map_add, oneVariableDOne_eq, oneVariableDOne_eq, oneVariableDOne_eq,
        oneVariableDifferential_add, map_add, Prod.fst_add]
    rw [hd, hdt, map_add]
    abel
  map_smul' b f := by
    rw [RingHom.id_apply, oneVariableDOne_smul, map_smul, map_add, TensorProduct.map_tmul,
      LinearMap.map_smul, oneVariableDOne_smul, LinearMap.id_apply, smul_sub]
    abel

/-- The defect vanishes: `θ ⊗ 1` commutes with the base-change component of the differential. -/
private theorem oneVariableDOneDefect_eq_zero : oneVariableDOneDefect A B = 0 := by
  refine (oneVariableMonomialBasis B).ext fun n => ?_
  rw [oneVariableMonomialBasis_apply, LinearMap.zero_apply]
  show TensorProduct.map (oneVariableTheta B) _
      ((dividedPowerPolynomialDzDecomposition A B).dOne _) -
    (dividedPowerPolynomialDzDecomposition A B).dOne (oneVariableTheta B _) = 0
  rw [oneVariableDOne_dpow, map_zero, oneVariableTheta_dpow, oneVariableDOne_dpow, sub_zero]

/-- **Assumption (7) of Section 60.25.**  `θ ⊗ 1` commutes with the base-change component `d₁`
of the differential. -/
public theorem oneVariableDOne_oneVariableTheta
    (f : oneVariableDividedPowerPolynomial B) :
    TensorProduct.map (oneVariableTheta B)
        (LinearMap.id (R := (B : Type u))
          (M := dividedPowerDifferentials (A := A) B.dividedPowers))
        ((dividedPowerPolynomialDzDecomposition A B).dOne f) -
      (dividedPowerPolynomialDzDecomposition A B).dOne (oneVariableTheta B f) = 0 :=
  congrFun (congrArg DFunLike.coe (oneVariableDOneDefect_eq_zero A B)) f

end RelativePoincare

/-! ### Restriction of scalars as an object of the category of modules -/

section ModuleCategory

open CategoryTheory

/-- An `S`-module `X`, read as an object of the category of `R`-modules along an algebra map
`R → S`.  The module structure is pinned to `RestrictScalars.module`, so that an `R`-linear map
between two such synonyms is a morphism of the category. -/
public noncomputable abbrev restrictScalarsModuleCat (R S : Type*) [CommRing R] [Ring S]
    [Algebra R S] (X : Type v) [AddCommGroup X] [Module S X] : ModuleCat.{v} R :=
  @ModuleCat.of R _ (RestrictScalars R S X) inferInstance (RestrictScalars.module R S X)

/-- Multiplication by `1` through the restricted scalars is the identity. -/
public theorem restrictScalars_lsmul_one {R S X : Type*} [CommSemiring R] [Semiring S]
    [Algebra R S] [AddCommMonoid X] [Module S X] (x : RestrictScalars R S X) :
    RestrictScalars.lsmul R S X 1 x = x := by
  rw [map_one]
  rfl

/-- Multiplication by the image of `1` under an algebra map, through the restricted scalars, is
the identity. -/
public theorem restrictScalars_lsmul_algebraMap_one (S : Type*) {R T X : Type*} [CommSemiring R]
    [CommSemiring S] [Semiring T] [Algebra R T] [Algebra S T] [AddCommMonoid X] [Module T X]
    (x : RestrictScalars R T X) :
    RestrictScalars.lsmul R T X (algebraMap S T 1) x = x := by
  rw [map_one]
  exact restrictScalars_lsmul_one x

end ModuleCategory

/-! ### Homotopies of cochain complexes from degreewise data -/

section Homotopies

open CategoryTheory

/-- A homotopy between two maps of `ℕ`-indexed cochain complexes, assembled from a degreewise
family of maps lowering the degree by one together with the two homotopy identities. -/
public noncomputable def cochainHomotopyOfDegreewise
    {V : Type*} [Category V] [Preadditive V] {K L : CochainComplex V ℕ} {f g : K ⟶ L}
    (hh : ∀ p : ℕ, K.X (p + 1) ⟶ L.X p)
    (hzero : f.f 0 = K.d 0 (0 + 1) ≫ hh 0 + g.f 0)
    (hsucc : ∀ p : ℕ, f.f (p + 1) =
      K.d (p + 1) (p + 1 + 1) ≫ hh (p + 1) + hh p ≫ L.d p (p + 1) + g.f (p + 1)) :
    Homotopy f g where
  hom i j := if hij : j + 1 = i then eqToHom (congrArg K.X hij.symm) ≫ hh j else 0
  zero _ _ hji := dite_eq_right hji
  comm i := by
    have hdite : ∀ p : ℕ, (if hij : p + 1 = p + 1 then
        eqToHom (congrArg K.X hij.symm) ≫ hh p else 0) = hh p := fun p => by
      rw [dite_eq_left rfl, eqToHom_refl, Category.id_comp]
    cases i with
    | zero =>
      rw [dNext_eq _ (show (ComplexShape.up ℕ).Rel 0 (0 + 1) from rfl),
        prevD_eq_zero _ 0 (by simp), hdite, add_zero]
      exact hzero
    | succ p =>
      rw [dNext_eq _ (show (ComplexShape.up ℕ).Rel (p + 1) (p + 1 + 1) from rfl),
        prevD_eq _ (show (ComplexShape.up ℕ).Rel p (p + 1) from rfl), hdite, hdite]
      exact hsucc p

end Homotopies

/-! ### The de Rham complex of a connection as a cochain complex of `A`-modules -/

section CochainComplexes

open CategoryTheory
open Stacks.DeRham.DifferentialDescent

variable {A B Omega : Type u} {M : Type w}
  [CommRing A] [CommRing B] [Algebra A B]
  [AddCommGroup Omega] [Module B Omega]
  [AddCommGroup M] [Module B M]

/-- The de Rham complex `M ⊗_B Ω^*` of an integrable connection, as a cochain complex of
`A`-modules: in degree `p` the module `M ⊗_B ⋀^p Ω`, with the extended connection as
differential. -/
public noncomputable def connectionDeRhamComplex
    (S : SourceDeRham A B) (pi : Ω[B⁄A] →ₗ[B] Omega)
    (hpi : Function.Surjective pi) (hgen : S.GenerationHypothesis pi)
    (nabla : Connection A B pi M)
    (hint : Connection.IsIntegrable S pi hpi hgen nabla) :
    CochainComplex (ModuleCat.{max u w} A) ℕ :=
  CochainComplex.of (fun p => restrictScalarsModuleCat A B (M ⊗[B] (⋀[B]^p Omega)))
    (fun p => ConcreteCategory.ofHom (C := ModuleCat A)
      ((extendedConnection S pi hpi hgen nabla).toLinearMap p))
    fun p => ModuleCat.hom_ext
      (extendedConnection_comp_self_eq_zero S pi hpi hgen nabla hint p)

/-- The differential of the de Rham complex is the extended connection. -/
public theorem connectionDeRhamComplex_hom_d
    (S : SourceDeRham A B) (pi : Ω[B⁄A] →ₗ[B] Omega)
    (hpi : Function.Surjective pi) (hgen : S.GenerationHypothesis pi)
    (nabla : Connection A B pi M)
    (hint : Connection.IsIntegrable S pi hpi hgen nabla) (p : ℕ) :
    ((connectionDeRhamComplex S pi hpi hgen nabla hint).d p (p + 1)).hom =
      (extendedConnection S pi hpi hgen nabla).toLinearMap p :=
  congrArg ModuleCat.Hom.hom (CochainComplex.of_d
    (fun q => restrictScalarsModuleCat A B (M ⊗[B] (⋀[B]^q Omega)))
    (fun q => ConcreteCategory.ofHom (C := ModuleCat A)
      ((extendedConnection S pi hpi hgen nabla).toLinearMap q)) p)

/-- A homotopy from the identity of a de Rham complex to an endomorphism of it, assembled from
degreewise `A`-linear maps lowering the degree by one. -/
public noncomputable def connectionDeRhamSelfHomotopy
    (S : SourceDeRham A B) (pi : Ω[B⁄A] →ₗ[B] Omega)
    (hpi : Function.Surjective pi) (hgen : S.GenerationHypothesis pi)
    (nabla : Connection A B pi M)
    (hint : Connection.IsIntegrable S pi hpi hgen nabla)
    (phi : connectionDeRhamComplex S pi hpi hgen nabla hint ⟶
      connectionDeRhamComplex S pi hpi hgen nabla hint)
    (g : ∀ p : ℕ, RestrictScalars A B (M ⊗[B] (⋀[B]^p Omega)) →ₗ[A]
      RestrictScalars A B (M ⊗[B] (⋀[B]^p Omega)))
    (hg : ∀ p : ℕ, (phi.f p).hom = g p)
    (k : ∀ p : ℕ, RestrictScalars A B (M ⊗[B] (⋀[B]^(p + 1) Omega)) →ₗ[A]
      RestrictScalars A B (M ⊗[B] (⋀[B]^p Omega)))
    (hk0 : ∀ x : RestrictScalars A B (M ⊗[B] (⋀[B]^0 Omega)),
      k 0 ((extendedConnection S pi hpi hgen nabla).toLinearMap 0 x) + g 0 x = x)
    (hks : ∀ (p : ℕ) (x : RestrictScalars A B (M ⊗[B] (⋀[B]^(p + 1) Omega))),
      (extendedConnection S pi hpi hgen nabla).toLinearMap p (k p x) +
          k (p + 1) ((extendedConnection S pi hpi hgen nabla).toLinearMap (p + 1) x) +
          g (p + 1) x = x) :
    Homotopy (𝟙 (connectionDeRhamComplex S pi hpi hgen nabla hint)) phi :=
  cochainHomotopyOfDegreewise
    (fun p => ConcreteCategory.ofHom (C := ModuleCat A) (k p))
    (by
      rw [ModuleCat.hom_ext_iff, ModuleCat.hom_add, ModuleCat.hom_comp,
        connectionDeRhamComplex_hom_d, hg, HomologicalComplex.id_f, ModuleCat.hom_id]
      refine LinearMap.ext fun x => ?_
      change x = k 0 ((extendedConnection S pi hpi hgen nabla).toLinearMap 0 x) + g 0 x
      exact (hk0 x).symm)
    (fun p => by
      rw [ModuleCat.hom_ext_iff, ModuleCat.hom_add, ModuleCat.hom_add, ModuleCat.hom_comp,
        ModuleCat.hom_comp, connectionDeRhamComplex_hom_d, connectionDeRhamComplex_hom_d,
        hg, HomologicalComplex.id_f, ModuleCat.hom_id]
      refine LinearMap.ext fun x => ?_
      change x = k (p + 1) ((extendedConnection S pi hpi hgen nabla).toLinearMap (p + 1) x) +
          (extendedConnection S pi hpi hgen nabla).toLinearMap p (k p x) + g (p + 1) x
      exact (hks p x).symm.trans (by abel))

end CochainComplexes

/-! ### The crystalline Poincaré lemma for one divided power variable -/

section Poincare

open CategoryTheory
open Stacks.DeRham.DifferentialDescent

variable (A : Type u) [CommRing A] (B : DividedPowerRing.{u}) [Algebra A B]

/-- The quotient `π : Ω_{B/A} → Ω¹_{B/A,δ}` onto divided power differentials. -/
public noncomputable abbrev oneVariableBaseProjection :
    Ω[(B : Type u)⁄A] →ₗ[(B : Type u)]
      dividedPowerDifferentials (A := A) B.dividedPowers :=
  (dividedPowerDifferentialRelations (A := A) B.dividedPowers).mkQ

/-- The quotient `π' : Ω_{B⟨z⟩/A} → Ω¹_{B⟨z⟩/A,δ'}` onto divided power differentials. -/
public noncomputable abbrev oneVariablePolyProjection :
    Ω[oneVariableDividedPowerPolynomial B⁄A] →ₗ[oneVariableDividedPowerPolynomial B]
      dividedPowerDifferentials (A := A) (oneVariableDividedPowers B) :=
  (dividedPowerDifferentialRelations (A := A) (oneVariableDividedPowers B)).mkQ

/-- The de Rham complex of `B` over `A`, as the data that divided power descent consumes. -/
public noncomputable abbrev oneVariableBaseSource : SourceDeRham A (B : Type u) :=
  sourceDeRhamOfKaehler A (B : Type u)

/-- The de Rham complex of `B⟨z⟩` over `A`, as the data that divided power descent consumes. -/
public noncomputable abbrev oneVariablePolySource :
    SourceDeRham A (oneVariableDividedPowerPolynomial B) :=
  sourceDeRhamOfKaehler A (oneVariableDividedPowerPolynomial B)

/-- The divided power relations of `B` are spanned by good generators, so the de Rham
differential descends to `Ω^*_{B/A,δ}`. -/
public theorem oneVariableBaseGenerationHypothesis :
    (oneVariableBaseSource A B).GenerationHypothesis (oneVariableBaseProjection A B) :=
  dividedPowerDifferentials_generationHypothesis B _

/-- The divided power relations of `B⟨z⟩` are spanned by good generators, so the de Rham
differential descends to `Ω^*_{B⟨z⟩/A,δ'}`. -/
public theorem oneVariablePolyGenerationHypothesis :
    (oneVariablePolySource A B).GenerationHypothesis (oneVariablePolyProjection A B) :=
  generationHypothesis_of_ker_eq_relations (oneVariableDividedPowers B) _ _
    (Submodule.ker_mkQ _)

/-- The comparison `ψ` of one-forms is compatible with the two Kähler differentials. -/
public theorem oneVariableOneFormComparison_compatible (b : (B : Type u)) :
    dividedPowerPolynomialOneFormComparison A B
        (oneVariableBaseProjection A B (KaehlerDifferential.D A (B : Type u) b)) =
      oneVariablePolyProjection A B (KaehlerDifferential.D A
        (oneVariableDividedPowerPolynomial B)
        (algebraMap (B : Type u) (oneVariableDividedPowerPolynomial B) b)) :=
  dividedPowerPolynomialOneFormComparison_dividedPowerDifferential A B b

/-- **Assumption (1) of Section 60.25 at `a = 1`.**  The differential of `1` vanishes. -/
public theorem oneVariableBase_targetD_one :
    SourceDeRham.targetD (oneVariableBaseProjection A B) (1 : (B : Type u)) = 0 := by
  show (dividedPowerDifferentialRelations (A := A) B.dividedPowers).mkQ
    (KaehlerDifferential.D A (B : Type u) 1) = 0
  rw [Derivation.map_one_eq_zero, map_zero]

variable (M : Type w) [AddCommGroup M] [Module (B : Type u) M]

/-- The degree-`p` term `M ⊗_B Ω^p_{B/A,δ}` of the de Rham complex of a connection on `M`. -/
public noncomputable abbrev oneVariableSourceTerm (p : ℕ) : Type (max u w) :=
  RestrictScalars A (B : Type u) (M ⊗[(B : Type u)]
    (⋀[(B : Type u)]^p (dividedPowerDifferentials (A := A) B.dividedPowers)))

/-- The degree-`p` term `(B⟨z⟩ ⊗_B M) ⊗_{B⟨z⟩} Ω^p_{B⟨z⟩/A,δ'}` of the de Rham complex of the
base-changed connection. -/
public noncomputable abbrev oneVariableTargetTerm (p : ℕ) : Type (max u w) :=
  RestrictScalars A (oneVariableDividedPowerPolynomial B)
    ((oneVariableDividedPowerPolynomial B ⊗[(B : Type u)] M) ⊗[
      oneVariableDividedPowerPolynomial B]
      (⋀[oneVariableDividedPowerPolynomial B]^p
        (dividedPowerDifferentials (A := A) (oneVariableDividedPowers B))))

variable {M}

/-- The base change to `B⟨z⟩` of a connection on `M`. -/
public noncomputable def oneVariableBaseChangeConnection
    (nabla : Connection A (B : Type u) (oneVariableBaseProjection A B) M) :
    Connection A (oneVariableDividedPowerPolynomial B) (oneVariablePolyProjection A B)
      (oneVariableDividedPowerPolynomial B ⊗[(B : Type u)] M) :=
  Connection.baseChange (dividedPowerPolynomialOneFormComparison A B) nabla
    (oneVariableOneFormComparison_compatible A B)

/-- The base change to `B⟨z⟩` of an integrable connection is integrable. -/
public theorem oneVariableBaseChangeConnection_isIntegrable
    (nabla : Connection A (B : Type u) (oneVariableBaseProjection A B) M)
    (hint : Connection.IsIntegrable (oneVariableBaseSource A B) (oneVariableBaseProjection A B)
      (Submodule.mkQ_surjective _) (oneVariableBaseGenerationHypothesis A B) nabla) :
    Connection.IsIntegrable (oneVariablePolySource A B) (oneVariablePolyProjection A B)
      (Submodule.mkQ_surjective _) (oneVariablePolyGenerationHypothesis A B)
      (oneVariableBaseChangeConnection A B nabla) :=
  baseChange_isIntegrable (oneVariableBaseSource A B) (oneVariablePolySource A B)
    (oneVariableBaseProjection A B) (oneVariablePolyProjection A B)
    (Submodule.mkQ_surjective _) (oneVariableBaseGenerationHypothesis A B)
    (Submodule.mkQ_surjective _) (oneVariablePolyGenerationHypothesis A B)
    (dividedPowerPolynomialOneFormComparison A B)
    (oneVariableOneFormComparison_compatible A B) nabla hint

/-- The de Rham complex `M ⊗_B Ω^*_{B/A,δ}` of an integrable connection. -/
public noncomputable abbrev oneVariableSourceDeRhamComplex
    (nabla : Connection A (B : Type u) (oneVariableBaseProjection A B) M)
    (hint : Connection.IsIntegrable (oneVariableBaseSource A B) (oneVariableBaseProjection A B)
      (Submodule.mkQ_surjective _) (oneVariableBaseGenerationHypothesis A B) nabla) :
    CochainComplex (ModuleCat.{max u w} A) ℕ :=
  connectionDeRhamComplex (oneVariableBaseSource A B) (oneVariableBaseProjection A B)
    (Submodule.mkQ_surjective _) (oneVariableBaseGenerationHypothesis A B) nabla hint

/-- The de Rham complex `M ⊗_B Ω^*_{B⟨z⟩/A,δ'} = (B⟨z⟩ ⊗_B M) ⊗_{B⟨z⟩} Ω^*_{B⟨z⟩/A,δ'}` of the
base-changed connection. -/
public noncomputable abbrev oneVariableTargetDeRhamComplex
    (nabla : Connection A (B : Type u) (oneVariableBaseProjection A B) M)
    (hint : Connection.IsIntegrable (oneVariableBaseSource A B) (oneVariableBaseProjection A B)
      (Submodule.mkQ_surjective _) (oneVariableBaseGenerationHypothesis A B) nabla) :
    CochainComplex (ModuleCat.{max u w} A) ℕ :=
  connectionDeRhamComplex (oneVariablePolySource A B) (oneVariablePolyProjection A B)
    (Submodule.mkQ_surjective _) (oneVariablePolyGenerationHypothesis A B)
    (oneVariableBaseChangeConnection A B nabla)
    (oneVariableBaseChangeConnection_isIntegrable A B nabla hint)

/-- The differential of the de Rham complex of `∇`. -/
public theorem oneVariableSourceDeRhamComplex_hom_d
    (nabla : Connection A (B : Type u) (oneVariableBaseProjection A B) M)
    (hint : Connection.IsIntegrable (oneVariableBaseSource A B) (oneVariableBaseProjection A B)
      (Submodule.mkQ_surjective _) (oneVariableBaseGenerationHypothesis A B) nabla) (p : ℕ) :
    ((oneVariableSourceDeRhamComplex A B nabla hint).d p (p + 1)).hom =
      (extendedConnection (oneVariableBaseSource A B) (oneVariableBaseProjection A B)
        (Submodule.mkQ_surjective _) (oneVariableBaseGenerationHypothesis A B)
        nabla).toLinearMap p :=
  connectionDeRhamComplex_hom_d _ _ _ _ _ _ p

/-- The differential of the de Rham complex of the base change of `∇`. -/
public theorem oneVariableTargetDeRhamComplex_hom_d
    (nabla : Connection A (B : Type u) (oneVariableBaseProjection A B) M)
    (hint : Connection.IsIntegrable (oneVariableBaseSource A B) (oneVariableBaseProjection A B)
      (Submodule.mkQ_surjective _) (oneVariableBaseGenerationHypothesis A B) nabla) (p : ℕ) :
    ((oneVariableTargetDeRhamComplex A B nabla hint).d p (p + 1)).hom =
      (extendedConnection (oneVariablePolySource A B) (oneVariablePolyProjection A B)
        (Submodule.mkQ_surjective _) (oneVariablePolyGenerationHypothesis A B)
        (oneVariableBaseChangeConnection A B nabla)).toLinearMap p :=
  connectionDeRhamComplex_hom_d _ _ _ _ _ _ p

/-- The map of de Rham complexes `M ⊗_B Ω^*_{B/A,δ} ⟶ M ⊗_B Ω^*_{B⟨z⟩/A,δ'}` cut out by a
degreewise family commuting with the two differentials. -/
public noncomputable def oneVariableDeRhamComparison
    (nabla : Connection A (B : Type u) (oneVariableBaseProjection A B) M)
    (hint : Connection.IsIntegrable (oneVariableBaseSource A B) (oneVariableBaseProjection A B)
      (Submodule.mkQ_surjective _) (oneVariableBaseGenerationHypothesis A B) nabla)
    (c : ∀ p : ℕ, oneVariableSourceTerm A B M p →ₗ[A] oneVariableTargetTerm A B M p)
    (hc : ∀ (p : ℕ) (x : oneVariableSourceTerm A B M p),
      c (p + 1) ((extendedConnection (oneVariableBaseSource A B)
            (oneVariableBaseProjection A B) (Submodule.mkQ_surjective _)
            (oneVariableBaseGenerationHypothesis A B) nabla).toLinearMap p x) =
        (extendedConnection (oneVariablePolySource A B) (oneVariablePolyProjection A B)
          (Submodule.mkQ_surjective _) (oneVariablePolyGenerationHypothesis A B)
          (oneVariableBaseChangeConnection A B nabla)).toLinearMap p (c p x)) :
    oneVariableSourceDeRhamComplex A B nabla hint ⟶
      oneVariableTargetDeRhamComplex A B nabla hint where
  f p := ConcreteCategory.ofHom (C := ModuleCat A) (c p)
  comm' p q hpq := by
    obtain rfl : p + 1 = q := hpq
    refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    rw [ModuleCat.hom_comp, ModuleCat.hom_comp, LinearMap.comp_apply, LinearMap.comp_apply,
      oneVariableSourceDeRhamComplex_hom_d, oneVariableTargetDeRhamComplex_hom_d]
    exact (hc p x).symm

/-- The degreewise components of the comparison map. -/
public theorem oneVariableDeRhamComparison_hom_f
    (nabla : Connection A (B : Type u) (oneVariableBaseProjection A B) M)
    (hint : Connection.IsIntegrable (oneVariableBaseSource A B) (oneVariableBaseProjection A B)
      (Submodule.mkQ_surjective _) (oneVariableBaseGenerationHypothesis A B) nabla)
    (c : ∀ p : ℕ, oneVariableSourceTerm A B M p →ₗ[A] oneVariableTargetTerm A B M p)
    (hc : ∀ (p : ℕ) (x : oneVariableSourceTerm A B M p),
      c (p + 1) ((extendedConnection (oneVariableBaseSource A B)
            (oneVariableBaseProjection A B) (Submodule.mkQ_surjective _)
            (oneVariableBaseGenerationHypothesis A B) nabla).toLinearMap p x) =
        (extendedConnection (oneVariablePolySource A B) (oneVariablePolyProjection A B)
          (Submodule.mkQ_surjective _) (oneVariablePolyGenerationHypothesis A B)
          (oneVariableBaseChangeConnection A B nabla)).toLinearMap p (c p x)) (p : ℕ) :
    ((oneVariableDeRhamComparison A B nabla hint c hc).f p).hom = c p :=
  rfl

/-- A degreewise family in the opposite direction commuting with the two differentials, as a map
of de Rham complexes `M ⊗_B Ω^*_{B⟨z⟩/A,δ'} ⟶ M ⊗_B Ω^*_{B/A,δ}`. -/
public noncomputable def oneVariableDeRhamRetraction
    (nabla : Connection A (B : Type u) (oneVariableBaseProjection A B) M)
    (hint : Connection.IsIntegrable (oneVariableBaseSource A B) (oneVariableBaseProjection A B)
      (Submodule.mkQ_surjective _) (oneVariableBaseGenerationHypothesis A B) nabla)
    (e : ∀ p : ℕ, oneVariableTargetTerm A B M p →ₗ[A] oneVariableSourceTerm A B M p)
    (he : ∀ (p : ℕ) (x : oneVariableTargetTerm A B M p),
      e (p + 1) ((extendedConnection (oneVariablePolySource A B)
            (oneVariablePolyProjection A B) (Submodule.mkQ_surjective _)
            (oneVariablePolyGenerationHypothesis A B)
            (oneVariableBaseChangeConnection A B nabla)).toLinearMap p x) =
        (extendedConnection (oneVariableBaseSource A B) (oneVariableBaseProjection A B)
          (Submodule.mkQ_surjective _) (oneVariableBaseGenerationHypothesis A B)
          nabla).toLinearMap p (e p x)) :
    oneVariableTargetDeRhamComplex A B nabla hint ⟶
      oneVariableSourceDeRhamComplex A B nabla hint where
  f p := ConcreteCategory.ofHom (C := ModuleCat A) (e p)
  comm' p q hpq := by
    obtain rfl : p + 1 = q := hpq
    refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    rw [ModuleCat.hom_comp, ModuleCat.hom_comp, LinearMap.comp_apply, LinearMap.comp_apply,
      oneVariableSourceDeRhamComplex_hom_d, oneVariableTargetDeRhamComplex_hom_d]
    exact (he p x).symm

/-- The degreewise components of the retraction. -/
public theorem oneVariableDeRhamRetraction_hom_f
    (nabla : Connection A (B : Type u) (oneVariableBaseProjection A B) M)
    (hint : Connection.IsIntegrable (oneVariableBaseSource A B) (oneVariableBaseProjection A B)
      (Submodule.mkQ_surjective _) (oneVariableBaseGenerationHypothesis A B) nabla)
    (e : ∀ p : ℕ, oneVariableTargetTerm A B M p →ₗ[A] oneVariableSourceTerm A B M p)
    (he : ∀ (p : ℕ) (x : oneVariableTargetTerm A B M p),
      e (p + 1) ((extendedConnection (oneVariablePolySource A B)
            (oneVariablePolyProjection A B) (Submodule.mkQ_surjective _)
            (oneVariablePolyGenerationHypothesis A B)
            (oneVariableBaseChangeConnection A B nabla)).toLinearMap p x) =
        (extendedConnection (oneVariableBaseSource A B) (oneVariableBaseProjection A B)
          (Submodule.mkQ_surjective _) (oneVariableBaseGenerationHypothesis A B)
          nabla).toLinearMap p (e p x)) (p : ℕ) :
    ((oneVariableDeRhamRetraction A B nabla hint e he).f p).hom = e p :=
  rfl

/-- If `u = s - v` and `s = x`, then `u + v = x`. -/
private theorem add_eq_of_eq_sub {G : Type*} [AddGroup G] {u v s x : G}
    (h : u = s - v) (hs : s = x) : u + v = x := by
  rw [h, hs, sub_add_cancel]


/-- The comparison map of de Rham complexes is a homotopy equivalence at `a = 1`. -/
private theorem exists_homotopyEquiv_of_comparison
    (nabla : Connection A (B : Type u) (oneVariableBaseProjection A B) M)
    (hint : Connection.IsIntegrable (oneVariableBaseSource A B) (oneVariableBaseProjection A B)
      (Submodule.mkQ_surjective _) (oneVariableBaseGenerationHypothesis A B) nabla)
    (c : ∀ p : ℕ, oneVariableSourceTerm A B M p →ₗ[A] oneVariableTargetTerm A B M p)
    (hc_wedge : ∀ (p : ℕ) (m : M)
        (omega : Fin p → dividedPowerDifferentials (A := A) B.dividedPowers),
      c p (m ⊗ₜ[(B : Type u)] exteriorPower.ιMulti (B : Type u) p omega) =
        ((1 : oneVariableDividedPowerPolynomial B) ⊗ₜ[(B : Type u)] m) ⊗ₜ[
          oneVariableDividedPowerPolynomial B]
          exteriorPower.ιMulti (oneVariableDividedPowerPolynomial B) p
            (dividedPowerPolynomialOneFormComparison A B ∘ omega))
    (hc : ∀ (p : ℕ) (x : oneVariableSourceTerm A B M p),
      c (p + 1) ((extendedConnection (oneVariableBaseSource A B)
            (oneVariableBaseProjection A B) (Submodule.mkQ_surjective _)
            (oneVariableBaseGenerationHypothesis A B) nabla).toLinearMap p x) =
        (extendedConnection (oneVariablePolySource A B) (oneVariablePolyProjection A B)
          (Submodule.mkQ_surjective _) (oneVariablePolyGenerationHypothesis A B)
          (oneVariableBaseChangeConnection A B nabla)).toLinearMap p (c p x)) :
    ∃ E : HomotopyEquiv (oneVariableSourceDeRhamComplex A B nabla hint)
        (oneVariableTargetDeRhamComplex A B nabla hint),
      E.hom = oneVariableDeRhamComparison A B nabla hint c hc := by
  obtain ⟨e, hecomm, ⟨htp, hh0, hhs⟩, ⟨ktp, hk0, hks⟩⟩ :=
    exists_homotopyInverse_baseChangeDeRhamMap (oneVariableBaseSource A B)
      (oneVariablePolySource A B) (oneVariableBaseProjection A B)
      (oneVariablePolyProjection A B) (Submodule.mkQ_surjective _)
      (oneVariableBaseGenerationHypothesis A B) (Submodule.mkQ_surjective _)
      (oneVariablePolyGenerationHypothesis A B)
      (dividedPowerPolynomialOneFormComparison A B)
      (oneVariableOneFormComparison_compatible A B) nabla hint c hc_wedge hc
      1 (oneVariableVariable B) (oneVariableTheta B)
      (dividedPowerPolynomialDzDecomposition A B) (oneVariableBase_targetD_one A B)
      (fun f => by
        rw [one_smul]
        exact LinearMap.congr_fun (oneVariablePartialZ_comp_oneVariableTheta A B) f)
      (oneVariableCoefficient_universallyInjective B)
      (oneVariableConstantTerm_mem_range A B)
      (fun f => by
        rw [oneVariableDOne_oneVariableTheta]
        exact Submodule.zero_mem _)
  exact ⟨{ hom := oneVariableDeRhamComparison A B nabla hint c hc
           inv := oneVariableDeRhamRetraction A B nabla hint e hecomm
           homotopyHomInvId :=
             (connectionDeRhamSelfHomotopy (oneVariableBaseSource A B)
               (oneVariableBaseProjection A B) (Submodule.mkQ_surjective _)
               (oneVariableBaseGenerationHypothesis A B) nabla hint
               (oneVariableDeRhamComparison A B nabla hint c hc ≫
                 oneVariableDeRhamRetraction A B nabla hint e hecomm)
               (fun p => (e p).comp (c p))
               (fun p => by simp only [HomologicalComplex.comp_f]; rfl) ktp
               (fun x => add_eq_of_eq_sub (hk0 x) (restrictScalars_lsmul_one x))
               (fun p x => add_eq_of_eq_sub (hks p x) (restrictScalars_lsmul_one x))).symm
           homotopyInvHomId :=
             (connectionDeRhamSelfHomotopy (oneVariablePolySource A B)
               (oneVariablePolyProjection A B) (Submodule.mkQ_surjective _)
               (oneVariablePolyGenerationHypothesis A B)
               (oneVariableBaseChangeConnection A B nabla)
               (oneVariableBaseChangeConnection_isIntegrable A B nabla hint)
               (oneVariableDeRhamRetraction A B nabla hint e hecomm ≫
                 oneVariableDeRhamComparison A B nabla hint c hc)
               (fun p => (c p).comp (e p))
               (fun p => by simp only [HomologicalComplex.comp_f]; rfl) htp
               (fun x => add_eq_of_eq_sub (hh0 x)
                 (restrictScalars_lsmul_algebraMap_one (B : Type u) x))
               (fun p x => add_eq_of_eq_sub (hhs p x)
                 (restrictScalars_lsmul_algebraMap_one (B : Type u) x))).symm }, rfl⟩

/-- **The crystalline Poincaré lemma for one divided power variable.**
Let `(B, I, δ)` be a divided power ring which is an `A`-algebra, let `P = B⟨z⟩` be the divided
power polynomial ring on one variable with divided power ideal `IP + P₊`, and let `M` be a
`B`-module with an integrable connection `∇ : M → M ⊗_B Ω¹_{B/A,δ}`.  Then the canonical map of
de Rham complexes `M ⊗_B Ω^*_{B/A,δ} → M ⊗_B Ω^*_{P/A,δ'}` is a quasi-isomorphism.  The map is
the family `c` of equation 07PY, which `Crystalline.existsUnique_baseChangeDeRhamMap` shows the
two hypotheses on it determine uniquely. -/
public theorem quasiIso_oneVariableDeRhamComparison
    (nabla : Connection A (B : Type u) (oneVariableBaseProjection A B) M)
    (hint : Connection.IsIntegrable (oneVariableBaseSource A B) (oneVariableBaseProjection A B)
      (Submodule.mkQ_surjective _) (oneVariableBaseGenerationHypothesis A B) nabla)
    (c : ∀ p : ℕ, oneVariableSourceTerm A B M p →ₗ[A] oneVariableTargetTerm A B M p)
    (hc_wedge : ∀ (p : ℕ) (m : M)
        (omega : Fin p → dividedPowerDifferentials (A := A) B.dividedPowers),
      c p (m ⊗ₜ[(B : Type u)] exteriorPower.ιMulti (B : Type u) p omega) =
        ((1 : oneVariableDividedPowerPolynomial B) ⊗ₜ[(B : Type u)] m) ⊗ₜ[
          oneVariableDividedPowerPolynomial B]
          exteriorPower.ιMulti (oneVariableDividedPowerPolynomial B) p
            (dividedPowerPolynomialOneFormComparison A B ∘ omega))
    (hc : ∀ (p : ℕ) (x : oneVariableSourceTerm A B M p),
      c (p + 1) ((extendedConnection (oneVariableBaseSource A B)
            (oneVariableBaseProjection A B) (Submodule.mkQ_surjective _)
            (oneVariableBaseGenerationHypothesis A B) nabla).toLinearMap p x) =
        (extendedConnection (oneVariablePolySource A B) (oneVariablePolyProjection A B)
          (Submodule.mkQ_surjective _) (oneVariablePolyGenerationHypothesis A B)
          (oneVariableBaseChangeConnection A B nabla)).toLinearMap p (c p x)) :
    QuasiIso (oneVariableDeRhamComparison A B nabla hint c hc) := by
  obtain ⟨E, hE⟩ := exists_homotopyEquiv_of_comparison A B nabla hint c hc_wedge hc
  rw [← hE]
  exact E.quasiIso_hom


end Poincare

section DividedPowerPolynomialExample

open Stacks.DeRham.DifferentialDescent

variable (A : Type u) [CommRing A] (B : DividedPowerRing.{u}) [Algebra A B]

/-- **The operator `θ` of Example 07Q8.**  It raises the divided power degree of the variable by
one in every term of the divided power monomial expansion: `θ(∑ bₘ z^[m]) = ∑ bₘ z^[m+1]`. -/
@[stacks 07Q8 "the operator θ"]
public theorem oneVariableTheta_apply (f : oneVariableDividedPowerPolynomial B) :
    oneVariableTheta B f =
      ((oneVariableMonomialBasis B).repr f).sum fun m b =>
        b • (oneVariableDividedPowers B).dpow (m + 1) (oneVariableVariable B) := by
  rw [oneVariableTheta, Module.Basis.constr_apply]
  exact Finsupp.sum_congr fun m _ => by rw [oneVariableMonomialBasis_apply]

/-- The augmentation of `B⟨z⟩` sends `z^[0] = 1` to `1`. -/
private theorem oneVariableAugmentation_dpow_zero :
    dividedPowerPolynomialAugmentation (B : Type u) Unit
        ((oneVariableDividedPowers B).dpow 0 (oneVariableVariable B)) = 1 := by
  rw [oneVariableDpow_zero, map_one]

/-- The augmentation of `B⟨z⟩` kills every positive divided power of the variable. -/
private theorem oneVariableAugmentation_dpow_succ (n : ℕ) :
    dividedPowerPolynomialAugmentation (B : Type u) Unit
        ((oneVariableDividedPowers B).dpow (n + 1) (oneVariableVariable B)) = 0 := by
  have hmon : dividedPowerPolynomialMonomial (B : Type u) (Finsupp.single () (n + 1)) =
      dividedPowerPolynomialVariableMonomial (B : Type u) () (n + 1) :=
    Finsupp.prod_single_index DividedPowerAlgebra.dp_zero
  rw [setIndexedDividedPowerPolynomialDividedPowers_dpow_variable, ← hmon,
    augmentation_monomial]
  simp [Finsupp.single_eq_zero]

/-- **Assumption (6) of Section 60.25 at `a = 1`, in sharp form.**  The difference
`f - θ(∂_z(f))` is the constant term `f(0)` of `f`, the image under `B → B⟨z⟩` of the
augmentation of `f`. -/
@[stacks 07Q8 "f - θ(∂_z f) = f(0)"]
public theorem oneVariable_sub_theta_partialZ (f : oneVariableDividedPowerPolynomial B) :
    f - oneVariableTheta B (oneVariablePartialZ A B f) =
      algebraMap (B : Type u) (oneVariableDividedPowerPolynomial B)
        (dividedPowerPolynomialAugmentation (B : Type u) Unit f) := by
  have key : LinearMap.id (R := (B : Type u)) (M := oneVariableDividedPowerPolynomial B) -
        (oneVariableTheta B).comp (oneVariablePartialZ A B) =
      (Algebra.linearMap (B : Type u) (oneVariableDividedPowerPolynomial B)).comp
        (dividedPowerPolynomialAugmentation (B : Type u) Unit).toLinearMap := by
    refine (oneVariableMonomialBasis B).ext fun n => ?_
    simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply,
      oneVariableMonomialBasis_apply, Algebra.linearMap_apply, AlgHom.toLinearMap_apply]
    cases n with
    | zero =>
      rw [oneVariablePartialZ_dpow_zero, map_zero, sub_zero,
        oneVariableAugmentation_dpow_zero, map_one, oneVariableDpow_zero]
    | succ n =>
      rw [oneVariablePartialZ_dpow_succ, oneVariableTheta_dpow, sub_self,
        oneVariableAugmentation_dpow_succ, map_zero]
  simpa only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply,
    Algebra.linearMap_apply, AlgHom.toLinearMap_apply] using LinearMap.congr_fun key f

/-- **Example 07Q8, the verification of the standing assumptions.**  For a divided power ring
`(B, J, δ)` over `A`, the divided power polynomial ring `B' = B⟨z⟩` with its divided powers on
`J' = B'₊ + JB'`, the quotients `Ω = Ω¹_{B/A,δ}` and `Ω' = Ω¹_{B'/A,δ'}`, the element `a = 1` and
the operator `θ` of `Crystalline.oneVariableTheta` satisfy the seven standing assumptions of
Section 60.25: `d(1) = 0`, the decomposition `Ω' = (B' ⊗_B Ω) ⊕ B' dz`, `B`-linearity of `θ`,
`∂_z ∘ θ = 1`, universal injectivity of `B → B'`, `f - θ(∂_z(f)) ∈ B`, and
`(θ ⊗ 1)(d₁(f)) - d₁(θ(f)) ∈ Ω`. -/
@[stacks 07Q8 "the seven standing assumptions for B⟨z⟩ at a = 1"]
public theorem oneVariableDividedPowerPolynomial_standingAssumptions :
    ∃ dec : DzDecomposition (oneVariablePolyProjection A B)
      (dividedPowerPolynomialOneFormComparison A B) (oneVariableVariable B),
      SourceDeRham.targetD (oneVariableBaseProjection A B) (1 : (B : Type u)) = 0 ∧
      (∀ f : oneVariableDividedPowerPolynomial B,
        dec.partialZ (oneVariableTheta B f) = (1 : (B : Type u)) • f) ∧
      Stacks.UniversalInjectivity.LocalizationCriteria.UniversallyInjective.{v}
        (Algebra.linearMap (B : Type u) (oneVariableDividedPowerPolynomial B)) ∧
      (∀ f : oneVariableDividedPowerPolynomial B,
        (1 : (B : Type u)) • f - oneVariableTheta B (dec.partialZ f) ∈
          Set.range (algebraMap (B : Type u) (oneVariableDividedPowerPolynomial B))) ∧
      (∀ f : oneVariableDividedPowerPolynomial B,
        TensorProduct.map (oneVariableTheta B)
            (LinearMap.id (R := (B : Type u))
              (M := dividedPowerDifferentials (A := A) B.dividedPowers)) (dec.dOne f) -
            dec.dOne (oneVariableTheta B f) ∈
          LinearMap.range (TensorProduct.mk (B : Type u)
            (oneVariableDividedPowerPolynomial B)
            (dividedPowerDifferentials (A := A) B.dividedPowers) 1)) :=
  ⟨dividedPowerPolynomialDzDecomposition A B, oneVariableBase_targetD_one A B,
    fun f => by
      rw [one_smul]
      exact LinearMap.congr_fun (oneVariablePartialZ_comp_oneVariableTheta A B) f,
    oneVariableCoefficient_universallyInjective B,
    oneVariableConstantTerm_mem_range A B,
    fun f => by
      rw [oneVariableDOne_oneVariableTheta]
      exact Submodule.zero_mem _⟩

end DividedPowerPolynomialExample

section DividedPowerPolynomialHomotopyEquivalence

open CategoryTheory
open Stacks.DeRham.DifferentialDescent

variable (A : Type u) [CommRing A] (B : DividedPowerRing.{u}) [Algebra A B]
  {M : Type w} [AddCommGroup M] [Module (B : Type u) M]

/-- **Example 07Q8, the conclusion.**  Let `(B, J, δ)` be a divided power ring which is an
`A`-algebra, let `B⟨z⟩` be the divided power polynomial ring on one divided power variable, and
let `M` carry an integrable connection `∇ : M → M ⊗_B Ω¹_{B/A,δ}`.  Then the canonical map of de
Rham complexes `c_M^• : M ⊗_B Ω^*_{B/A,δ} ⟶ M ⊗_B Ω^*_{B⟨z⟩/A,δ'}` is a homotopy equivalence. -/
@[stacks 07Q8 "Lemma 07Q7 at a = 1 for B⟨z⟩"]
public theorem exists_homotopyEquiv_oneVariableDeRhamComparison
    (nabla : Connection A (B : Type u) (oneVariableBaseProjection A B) M)
    (hint : Connection.IsIntegrable (oneVariableBaseSource A B) (oneVariableBaseProjection A B)
      (Submodule.mkQ_surjective _) (oneVariableBaseGenerationHypothesis A B) nabla)
    (c : ∀ p : ℕ, oneVariableSourceTerm A B M p →ₗ[A] oneVariableTargetTerm A B M p)
    (hc_wedge : ∀ (p : ℕ) (m : M)
        (omega : Fin p → dividedPowerDifferentials (A := A) B.dividedPowers),
      c p (m ⊗ₜ[(B : Type u)] exteriorPower.ιMulti (B : Type u) p omega) =
        ((1 : oneVariableDividedPowerPolynomial B) ⊗ₜ[(B : Type u)] m) ⊗ₜ[
          oneVariableDividedPowerPolynomial B]
          exteriorPower.ιMulti (oneVariableDividedPowerPolynomial B) p
            (dividedPowerPolynomialOneFormComparison A B ∘ omega))
    (hc : ∀ (p : ℕ) (x : oneVariableSourceTerm A B M p),
      c (p + 1) ((extendedConnection (oneVariableBaseSource A B)
            (oneVariableBaseProjection A B) (Submodule.mkQ_surjective _)
            (oneVariableBaseGenerationHypothesis A B) nabla).toLinearMap p x) =
        (extendedConnection (oneVariablePolySource A B) (oneVariablePolyProjection A B)
          (Submodule.mkQ_surjective _) (oneVariablePolyGenerationHypothesis A B)
          (oneVariableBaseChangeConnection A B nabla)).toLinearMap p (c p x)) :
    ∃ E : HomotopyEquiv (oneVariableSourceDeRhamComplex A B nabla hint)
        (oneVariableTargetDeRhamComplex A B nabla hint),
      E.hom = oneVariableDeRhamComparison A B nabla hint c hc :=
  exists_homotopyEquiv_of_comparison A B nabla hint c hc_wedge hc

end DividedPowerPolynomialHomotopyEquivalence

end Crystalline

end
