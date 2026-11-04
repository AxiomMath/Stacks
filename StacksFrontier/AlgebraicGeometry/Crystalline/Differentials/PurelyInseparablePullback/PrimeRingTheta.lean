module

public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.AlgebraTower
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Crystalline.Differentials.BaseChangeHomotopyInverse
public import StacksFrontier.RingTheory.DividedPowers.Extend
public import StacksFrontier.RingTheory.DividedPowers.Polynomial.Basic

/-!
# Pulling back along a purely inseparable map: the ring and the operator `θ`

Let `(B, J, γ)` be a divided power ring which is an algebra over `ℤ_(p)` for a prime `p`, and let
`λ ∈ B`.  This file constructs the ring `B[z]⟨ξ⟩/(ξ - (z^p - λ)) = B⟨ξ⟩[z]/(z^p - ξ - λ)` of the
proof of Tag 07N1, its free `B`-module basis `z^i ξ^[n]` with `0 ≤ i < p` and `n ≥ 0`, and the
`B`-linear operator `θ` of the proof of Tag 07N1 on that basis.

## Main definitions

* `Crystalline.PthRootExtension.primeRing` — the ring `B[z]⟨ξ⟩/(ξ - (z^p - λ))`.
* `Crystalline.PthRootExtension.basisZXi` — its free `B`-module basis `z^i ξ^[n]`.
* `Crystalline.PthRootExtension.theta` — the `B`-linear operator `θ`.
* `Crystalline.PthRootExtension.PartialZValues` — the three values of `∂_z` on the basis.
* `Crystalline.PthRootExtension.epsilon` — the `B`-valued remainder `p f - θ(∂_z f)`.

## Main results

* `Crystalline.PthRootExtension.universallyInjective_toPrimeRing` — assumption (07Q4) of
  Lemma 07Q7: `B → B[z]⟨ξ⟩/(ξ - (z^p - λ))` is universally injective.
* `Crystalline.PthRootExtension.partialZ_theta` — assumption (07Q3): `∂_z ∘ θ` is
  multiplication by `p`.
* `Crystalline.PthRootExtension.smul_sub_theta_partialZ` — assumption (07Q5):
  `p f - θ(∂_z f)` is the image of `epsilon f ∈ B`.

## References

* [Stacks Project, Tag 07Q7](https://stacks.math.columbia.edu/tag/07Q7)
* [Stacks Project, Tag 07N1](https://stacks.math.columbia.edu/tag/07N1)
-/

@[expose] public section

noncomputable section

open DividedPowers Stacks.DeRham.DifferentialDescent

open scoped TensorProduct

universe uQ u

namespace Crystalline.PthRootExtension

variable (B : DividedPowerRing.{u})

/-- The divided power polynomial ring `B⟨ξ⟩` in one divided power variable. -/
public abbrev XiAlg : Type u := DividedPowerAlgebra (B : Type u) (Unit →₀ (B : Type u))

/-- `B⟨ξ⟩` as a divided power ring, with divided power ideal `J B⟨ξ⟩ + B⟨ξ⟩₊`. -/
public abbrev xiRing : DividedPowerRing.{u} :=
  dividedPowerPolynomialDividedPowerRing B Unit

/-- The divided power variable `ξ`. -/
public def xi : XiAlg B := dividedPowerPolynomialVariable (B : Type u) ()

/-- The divided power monomial `ξ^[n]`. -/
public def xiMonomial (n : ℕ) : XiAlg B :=
  dividedPowerPolynomialVariableMonomial (B : Type u) () n

/-- The divided powers of `ξ` are the divided power monomials `ξ^[n]`. -/
public theorem dpow_xi (n : ℕ) :
    (xiRing B).dividedPowers.dpow n (xi B) = xiMonomial B n :=
  dividedPowerPolynomialDividedPowers_dpow_variable B Unit () n

/-- The reindexing `(Unit →₀ ℕ) ≃ ℕ` of the exponents of one divided power variable. -/
public def unitFinsuppEquiv : (Unit →₀ ℕ) ≃ ℕ :=
  Finsupp.equivFunOnFinite.trans (Equiv.funUnique Unit ℕ)

/-- `B⟨ξ⟩` is free as a `B`-module on the divided power monomials `ξ^[n]`. -/
public def basisXi : Module.Basis ℕ (B : Type u) (XiAlg B) :=
  (dividedPowerPolynomialMonomialBasis (B : Type u) Unit).reindex unitFinsuppEquiv

/-- The `n`-th basis vector of `B⟨ξ⟩` over `B` is the divided power monomial `ξ^[n]`. -/
@[simp] public theorem basisXi_apply (n : ℕ) : basisXi B n = xiMonomial B n := by
  classical
  rw [basisXi, Module.Basis.reindex_apply, dividedPowerPolynomialMonomialBasis_apply]
  have h : unitFinsuppEquiv.symm n = Finsupp.single () n := by
    ext
    simp [unitFinsuppEquiv]
  rw [h, xiMonomial, dividedPowerPolynomialVariableMonomial,
    dividedPowerPolynomialMonomial, Finsupp.prod_single_index]
  exact DividedPowerAlgebra.dp_zero

/-- `B⟨ξ⟩` is nontrivial whenever `B` is, because the augmentation splits `B → B⟨ξ⟩`. -/
public theorem nontrivial_xiAlg [Nontrivial (B : Type u)] : Nontrivial (XiAlg B) := by
  refine ⟨1, 0, fun h ↦ ?_⟩
  have h1 := congrArg (dividedPowerPolynomialAugmentation (B : Type u) Unit) h
  rw [map_one, map_zero] at h1
  exact one_ne_zero h1

section Prime

variable (p : ℕ) (lam : (B : Type u))

/-- The monic polynomial `z^p - ξ - λ` over `B⟨ξ⟩`. -/
public def primePoly : Polynomial (XiAlg B) :=
  Polynomial.X ^ p - Polynomial.C (xi B) -
    Polynomial.C (algebraMap (B : Type u) (XiAlg B) lam)

/-- `z^p - ξ - λ` is `z^p - (ξ + λ)`. -/
public theorem primePoly_eq :
    primePoly B p lam =
      Polynomial.X ^ p -
        Polynomial.C (xi B + algebraMap (B : Type u) (XiAlg B) lam) := by
  rw [primePoly, map_add]
  ring

/-- `z^p - ξ - λ` is monic when `p ≠ 0`. -/
public theorem primePoly_monic (hp : p ≠ 0) : (primePoly B p lam).Monic := by
  rw [primePoly_eq]
  exact Polynomial.monic_X_pow_sub_C _ hp

/-- `z^p - ξ - λ` has degree `p`. -/
public theorem primePoly_natDegree [Nontrivial (XiAlg B)] :
    (primePoly B p lam).natDegree = p := by
  rw [primePoly_eq]
  exact Polynomial.natDegree_X_pow_sub_C

/-- The ring `B[z]⟨ξ⟩/(ξ - (z^p - λ))` of Tag 07N1, written as `B⟨ξ⟩[z]/(z^p - ξ - λ)`. -/
public abbrev primeRing : Type u := AdjoinRoot (primePoly B p lam)

/-- The class of the ordinary polynomial variable `z`. -/
public def zElt : primeRing B p lam := AdjoinRoot.root (primePoly B p lam)

private theorem eval₂_X_pow_sub_C_sub_C {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (x : S) (n : ℕ) (a b : R) :
    Polynomial.eval₂ f x (Polynomial.X ^ n - Polynomial.C a - Polynomial.C b) =
      x ^ n - f a - f b := by
  simp

/-- The defining relation `ξ = z^p - λ` of the extension. -/
public theorem xi_eq :
    AdjoinRoot.of (primePoly B p lam) (xi B) =
      zElt B p lam ^ p -
        AdjoinRoot.of (primePoly B p lam) (algebraMap (B : Type u) (XiAlg B) lam) := by
  have he := eval₂_X_pow_sub_C_sub_C (AdjoinRoot.of (primePoly B p lam))
    (zElt B p lam) p (xi B) (algebraMap (B : Type u) (XiAlg B) lam)
  have h2 : zElt B p lam ^ p - AdjoinRoot.of (primePoly B p lam) (xi B) -
      AdjoinRoot.of (primePoly B p lam) (algebraMap (B : Type u) (XiAlg B) lam) = 0 :=
    he.symm.trans (AdjoinRoot.eval₂_root (primePoly B p lam))
  linear_combination -h2

/-- `1, z, …, z^{p-1}` is a power basis of the extension over `B⟨ξ⟩`. -/
public def powerBasisZ (hp : p ≠ 0) : PowerBasis (XiAlg B) (primeRing B p lam) :=
  AdjoinRoot.powerBasis' (primePoly_monic B p lam hp)

/-- The power basis over `B⟨ξ⟩` has `p` elements. -/
public theorem powerBasisZ_dim [Nontrivial (XiAlg B)] (hp : p ≠ 0) :
    (powerBasisZ B p lam hp).dim = p := by
  rw [powerBasisZ, AdjoinRoot.powerBasis'_dim, primePoly_natDegree B p lam]

/-- The generator of the power basis over `B⟨ξ⟩` is `z`. -/
public theorem powerBasisZ_gen (hp : p ≠ 0) :
    (powerBasisZ B p lam hp).gen = zElt B p lam :=
  AdjoinRoot.powerBasis'_gen _

/-- The free `B`-module basis `z^i ξ^[n]` of the extension, with `0 ≤ i < p` and `n ≥ 0`. -/
public def basisZXi [Nontrivial (XiAlg B)] (hp : p ≠ 0) :
    Module.Basis (ℕ × Fin p) (B : Type u) (primeRing B p lam) :=
  ((basisXi B).smulTower (powerBasisZ B p lam hp).basis).reindex
    (Equiv.prodCongr (Equiv.refl ℕ) (finCongr (powerBasisZ_dim B p lam hp)))

/-- The basis vector indexed by `(n, i)` is `ξ^[n] z^i`. -/
@[simp] public theorem basisZXi_apply [Nontrivial (XiAlg B)] (hp : p ≠ 0)
    (n : ℕ) (i : Fin p) :
    basisZXi B p lam hp (n, i) =
      AdjoinRoot.of (primePoly B p lam) (xiMonomial B n) * zElt B p lam ^ (i : ℕ) := by
  rw [basisZXi, Module.Basis.reindex_apply, Module.Basis.smulTower_apply]
  simp only [PowerBasis.coe_basis, powerBasisZ_gen, basisXi_apply, finCongr_symm,
    Equiv.prodCongr_symm, Equiv.refl_symm, Equiv.prodCongr_apply, Prod.map_apply,
    finCongr_apply]
  rw [Algebra.smul_def]
  rfl

/-- The basis vector indexed by `(0, 0)` is `1`. -/
public theorem basisZXi_zero [Nontrivial (XiAlg B)] (hp : p ≠ 0) :
    basisZXi B p lam hp (0, ⟨0, Nat.pos_of_ne_zero hp⟩) = 1 := by
  rw [basisZXi_apply, xiMonomial, dividedPowerPolynomialVariableMonomial]
  simp [DividedPowerAlgebra.dp_zero]

/-- The `B`-linear coordinate of `z^0 ξ^[0] = 1`, a retraction of `B → B[z]⟨ξ⟩/(ξ - (z^p - λ))`.
-/
public def primeRetraction [Nontrivial (XiAlg B)] (hp : p ≠ 0) :
    primeRing B p lam →ₗ[(B : Type u)] (B : Type u) :=
  (basisZXi B p lam hp).coord (0, ⟨0, Nat.pos_of_ne_zero hp⟩)

/-- The coordinate of `1` is a left inverse of the structure map. -/
public theorem primeRetraction_comp [Nontrivial (XiAlg B)] (hp : p ≠ 0) :
    (primeRetraction B p lam hp).comp
        (Algebra.linearMap (B : Type u) (primeRing B p lam)) =
      LinearMap.id := by
  refine LinearMap.ext fun b ↦ ?_
  have h1 : (Algebra.linearMap (B : Type u) (primeRing B p lam)) b =
      b • basisZXi B p lam hp (0, ⟨0, Nat.pos_of_ne_zero hp⟩) := by
    rw [basisZXi_zero]
    exact Algebra.algebraMap_eq_smul_one b
  rw [LinearMap.comp_apply, h1, primeRetraction, Module.Basis.coord_apply, map_smul,
    Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul,
    mul_one, LinearMap.id_apply]

/-- **Assumption (07Q4) of Lemma 07Q7 for the extension of Tag 07N1.** The map
`B → B[z]⟨ξ⟩/(ξ - (z^p - λ))` is universally injective, being split as a map of
`B`-modules by the coordinate of the basis vector `1`. -/
public theorem universallyInjective_toPrimeRing [Nontrivial (XiAlg B)] (hp : p ≠ 0) :
    Stacks.UniversalInjectivity.LocalizationCriteria.UniversallyInjective.{uQ}
      (Algebra.linearMap (B : Type u) (primeRing B p lam)) := by
  intro Q _ _
  have h : ((primeRetraction B p lam hp).rTensor Q).comp
      ((Algebra.linearMap (B : Type u) (primeRing B p lam)).rTensor Q) = LinearMap.id := by
    rw [← LinearMap.rTensor_comp, primeRetraction_comp, LinearMap.rTensor_id]
  refine Function.LeftInverse.injective
    (g := (primeRetraction B p lam hp).rTensor Q) fun x ↦ ?_
  exact congrArg (fun f : _ →ₗ[(B : Type u)] _ ↦ f x) h

/-- The element `ξ^[n] z^i` of the extension. -/
public def xiElt (n i : ℕ) : primeRing B p lam :=
  AdjoinRoot.of (primePoly B p lam) (xiMonomial B n) * zElt B p lam ^ i

/-- The basis vector indexed by `(n, i)` is `ξ^[n] z^i`. -/
public theorem basisZXi_eq_xiElt [Nontrivial (XiAlg B)] (hp : p ≠ 0) (n : ℕ) (i : Fin p) :
    basisZXi B p lam hp (n, i) = xiElt B p lam n (i : ℕ) :=
  basisZXi_apply B p lam hp n i

/-- `ξ^[0] z^i` is the ordinary power `z^i`. -/
public theorem xiElt_zero_left (i : ℕ) : xiElt B p lam 0 i = zElt B p lam ^ i := by
  rw [xiElt, xiMonomial, dividedPowerPolynomialVariableMonomial]
  simp [DividedPowerAlgebra.dp_zero]

/-- `ξ^[n] z^0` is the image of the divided power monomial `ξ^[n]`. -/
public theorem xiElt_zero_right (n : ℕ) :
    xiElt B p lam n 0 = AdjoinRoot.of (primePoly B p lam) (xiMonomial B n) := by
  rw [xiElt, pow_zero, mul_one]

/-- `ξ^[0] z^0` is `1`. -/
public theorem xiElt_zero_zero : xiElt B p lam 0 0 = 1 := by
  rw [xiElt_zero_left, pow_zero]

/-- The image of `ξ` is the basis vector `ξ^[1] z^0`. -/
public theorem xiElt_one_zero :
    xiElt B p lam 1 0 = AdjoinRoot.of (primePoly B p lam) (xi B) := by
  rw [xiElt_zero_right]
  rfl

/-- The relation `z^p = ξ + λ` of the extension, in terms of the elements `ξ^[n] z^i`. -/
public theorem zElt_pow_prime :
    zElt B p lam ^ p = xiElt B p lam 1 0 + lam • xiElt B p lam 0 0 := by
  have hl : AdjoinRoot.of (primePoly B p lam) (algebraMap (B : Type u) (XiAlg B) lam) =
      lam • (1 : primeRing B p lam) := by
    rw [Algebra.smul_def, mul_one,
      IsScalarTower.algebraMap_apply (B : Type u) (XiAlg B) (primeRing B p lam),
      AdjoinRoot.algebraMap_eq]
  rw [xiElt_one_zero, xiElt_zero_zero, xi_eq, hl]
  ring

/-- The value of the operator `θ` of the proof of Tag 07N1 on the basis vector `ξ^[n] z^i`:
`θ(z^j) = p z^{j+1}/(j+1)` for `j < p - 1` and `θ(z^{p-1}) = z^p`, `θ(z^{p-1} ξ^[m]) = ξ^[m+1]`
for `m ≥ 1`, and `θ(z^j ξ^[m]) = (p z^{j+1} ξ^[m] - θ(p λ z^j ξ^[m-1]))/(j + 1 + pm)` for
`j < p - 1` and `m ≥ 1`, by induction on `m`. -/
public def thetaBasis : ℕ → Fin p → primeRing B p lam
  | 0, i =>
    if (i : ℕ) + 1 = p then xiElt B p lam 1 0 + lam • xiElt B p lam 0 0
    else ((p : (B : Type u)) * Ring.inverse (((i : ℕ) + 1 : ℕ) : (B : Type u))) •
      xiElt B p lam 0 ((i : ℕ) + 1)
  | n + 1, i =>
    if (i : ℕ) + 1 = p then xiElt B p lam (n + 2) 0
    else Ring.inverse (((i : ℕ) + 1 + p * (n + 1) : ℕ) : (B : Type u)) •
      ((p : (B : Type u)) • xiElt B p lam (n + 1) ((i : ℕ) + 1) -
        ((p : (B : Type u)) * lam) • thetaBasis n i)

/-- `θ(z^{p-1}) = z^p`, the value of `θ` on the top power of `z`. -/
public theorem thetaBasis_zero_top (i : Fin p) (hi : (i : ℕ) + 1 = p) :
    thetaBasis B p lam 0 i = zElt B p lam ^ p := by
  rw [thetaBasis, ite_eq_left_of_eq_true _ _ (eq_true hi), zElt_pow_prime]

/-- `θ(z^j) = p z^{j+1}/(j+1)` for `j < p - 1`. -/
public theorem thetaBasis_zero_of_ne (i : Fin p) (hi : (i : ℕ) + 1 ≠ p) :
    thetaBasis B p lam 0 i =
      ((p : (B : Type u)) * Ring.inverse (((i : ℕ) + 1 : ℕ) : (B : Type u))) •
        xiElt B p lam 0 ((i : ℕ) + 1) := by
  rw [thetaBasis, ite_eq_right_of_eq_false _ _ (eq_false hi)]

/-- `θ(z^{p-1} ξ^[m]) = ξ^[m+1]` for `m ≥ 1`. -/
public theorem thetaBasis_succ_top (n : ℕ) (i : Fin p) (hi : (i : ℕ) + 1 = p) :
    thetaBasis B p lam (n + 1) i = xiElt B p lam (n + 2) 0 := by
  rw [thetaBasis, ite_eq_left_of_eq_true _ _ (eq_true hi)]

/-- `θ(z^j ξ^[m]) = (p z^{j+1} ξ^[m] - θ(p λ z^j ξ^[m-1]))/(j + 1 + pm)` for `j < p - 1`,
`m ≥ 1`. -/
public theorem thetaBasis_succ_of_ne (n : ℕ) (i : Fin p) (hi : (i : ℕ) + 1 ≠ p) :
    thetaBasis B p lam (n + 1) i =
      Ring.inverse (((i : ℕ) + 1 + p * (n + 1) : ℕ) : (B : Type u)) •
        ((p : (B : Type u)) • xiElt B p lam (n + 1) ((i : ℕ) + 1) -
          ((p : (B : Type u)) * lam) • thetaBasis B p lam n i) := by
  rw [thetaBasis, ite_eq_right_of_eq_false _ _ (eq_false hi)]

/-- The operator `θ` of the proof of Tag 07N1: the `B`-linear map with the stated values on the
free basis `z^i ξ^[n]`.  This is assumption (07Q2) of Lemma 07Q7 by construction. -/
public def theta [Nontrivial (XiAlg B)] (hp : p ≠ 0) :
    primeRing B p lam →ₗ[(B : Type u)] primeRing B p lam :=
  (basisZXi B p lam hp).constr (B : Type u) fun ni ↦ thetaBasis B p lam ni.1 ni.2

/-- `θ` has the stated values on the basis. -/
@[simp] public theorem theta_basisZXi [Nontrivial (XiAlg B)] (hp : p ≠ 0) (n : ℕ) (i : Fin p) :
    theta B p lam hp (basisZXi B p lam hp (n, i)) = thetaBasis B p lam n i :=
  Module.Basis.constr_basis _ _ _ _

/-- The three values of `∂_z` on the basis vectors `ξ^[n] z^i` computed in the proof of
Tag 07N1 from `ξ = z^p - λ` and `ξ ξ^[n-1] = n ξ^[n]`, namely `∂_z(z^i) = i z^{i-1}`,
`∂_z(ξ^[n]) = p z^{p-1} ξ^[n-1]` and
`∂_z(z^i ξ^[n]) = (i + pn) z^{i-1} ξ^[n] + p λ z^{i-1} ξ^[n-1]`. -/
public structure PartialZValues (pz : primeRing B p lam →ₗ[(B : Type u)] primeRing B p lam) :
    Prop where
  /-- `∂_z(z^i) = i z^{i - 1}`. -/
  pow : ∀ i : ℕ, pz (xiElt B p lam 0 i) = ((i : ℕ) : (B : Type u)) • xiElt B p lam 0 (i - 1)
  /-- `∂_z(ξ^[n + 1]) = p z^{p - 1} ξ^[n]`. -/
  xiPow : ∀ n : ℕ,
    pz (xiElt B p lam (n + 1) 0) = ((p : ℕ) : (B : Type u)) • xiElt B p lam n (p - 1)
  /-- `∂_z(z^i ξ^[n + 1]) = (i + p(n+1)) z^{i - 1} ξ^[n + 1] + p λ z^{i - 1} ξ^[n]`. -/
  xiZ : ∀ (n i : ℕ), 1 ≤ i →
    pz (xiElt B p lam (n + 1) i) =
      ((i + p * (n + 1) : ℕ) : (B : Type u)) • xiElt B p lam (n + 1) (i - 1) +
        (((p : ℕ) : (B : Type u)) * lam) • xiElt B p lam n (i - 1)

/-- The `B`-valued remainder `ε(f) = p f - θ(∂_z f)` of assumption (07Q5), which by the
footnote of Tag 07N1 vanishes on every basis vector `z^i ξ^[n]` except `1 ↦ p` and
`ξ ↦ -p λ`. -/
public def epsilon [Nontrivial (XiAlg B)] (hp : p ≠ 0) :
    primeRing B p lam →ₗ[(B : Type u)] (B : Type u) :=
  (basisZXi B p lam hp).constr (B : Type u) fun ni ↦
    if ni.1 = 0 ∧ (ni.2 : ℕ) = 0 then ((p : ℕ) : (B : Type u))
    else if ni.1 = 1 ∧ (ni.2 : ℕ) = 0 then -(((p : ℕ) : (B : Type u)) * lam) else 0

/-- `ε` has the stated values on the basis. -/
@[simp] public theorem epsilon_basisZXi [Nontrivial (XiAlg B)] (hp : p ≠ 0) (n : ℕ) (i : Fin p) :
    epsilon B p lam hp (basisZXi B p lam hp (n, i)) =
      if n = 0 ∧ (i : ℕ) = 0 then ((p : ℕ) : (B : Type u))
      else if n = 1 ∧ (i : ℕ) = 0 then -(((p : ℕ) : (B : Type u)) * lam) else 0 :=
  Module.Basis.constr_basis _ _ _ _

/-- Two `B`-linear maps out of the extension which agree on all `ξ^[n] z^i` with `i < p` are
equal. -/
public theorem linearMap_ext_xiElt [Nontrivial (XiAlg B)] (hp : p ≠ 0) {N : Type*}
    [AddCommGroup N] [Module (B : Type u) N]
    {f g : primeRing B p lam →ₗ[(B : Type u)] N}
    (h : ∀ (n : ℕ) (i : Fin p), f (xiElt B p lam n (i : ℕ)) = g (xiElt B p lam n (i : ℕ))) :
    f = g := by
  refine (basisZXi B p lam hp).ext fun ni ↦ ?_
  rw [basisZXi_eq_xiElt]
  exact h ni.1 ni.2

section AtPrime

variable [Fact p.Prime] [Algebra (IntegersAtPrime p) (B : Type u)]

/-- A natural number prime to `p` is invertible in any `ℤ_(p)`-algebra. -/
public theorem isUnit_natCast_of_not_dvd {k : ℕ} (hk : ¬ p ∣ k) :
    IsUnit ((k : (B : Type u))) := by
  have hprime : (Ideal.span ({(p : ℤ)} : Set ℤ)).IsPrime :=
    (Ideal.span_singleton_prime (Int.ofNat_ne_zero.mpr (Fact.out : p.Prime).ne_zero)).mpr
      (Nat.prime_iff_prime_int.mp (Fact.out : p.Prime))
  have hmem : (k : ℤ) ∈ (Ideal.span ({(p : ℤ)} : Set ℤ)).primeCompl := by
    change (k : ℤ) ∉ Ideal.span ({(p : ℤ)} : Set ℤ)
    simpa only [Ideal.mem_span_singleton, Int.natCast_dvd_natCast] using hk
  have h1 : IsUnit (algebraMap ℤ (IntegersAtPrime p) (k : ℤ)) :=
    (IsLocalization.AtPrime.isUnit_to_map_iff (IntegersAtPrime p)
      (Ideal.span ({(p : ℤ)} : Set ℤ)) (k : ℤ)).2 hmem
  have h2 : IsUnit ((k : IntegersAtPrime p)) := by
    have hcast : algebraMap ℤ (IntegersAtPrime p) (k : ℤ) = ((k : ℕ) : IntegersAtPrime p) := by
      simp
    rwa [hcast] at h1
  simpa only [map_natCast] using h2.map (algebraMap (IntegersAtPrime p) (B : Type u))

end AtPrime

/-- A natural number of the form `i + p m` with `1 ≤ i < p` is prime to `p`. -/
public theorem not_dvd_add_mul {i m : ℕ} (hi : 1 ≤ i) (hip : i < p) : ¬ p ∣ i + p * m := by
  intro h
  have h1 : p ∣ i := by
    have h2 := Nat.dvd_sub h (dvd_mul_right p m)
    rwa [Nat.add_sub_cancel] at h2
  exact absurd (Nat.le_of_dvd hi h1) (by omega)

/-- A natural number `i` with `1 ≤ i < p` is invertible in any `ℤ_(p)`-algebra. -/
public theorem isUnit_natCast_of_lt [Fact p.Prime] [Algebra (IntegersAtPrime p) (B : Type u)]
    {i : ℕ} (hi : 1 ≤ i) (hip : i < p) : IsUnit ((i : (B : Type u))) :=
  isUnit_natCast_of_not_dvd B p (Nat.not_dvd_of_pos_of_lt hi hip)

/-- A natural number `i + p m` with `1 ≤ i < p` is invertible in any `ℤ_(p)`-algebra. -/
public theorem isUnit_natCast_add_mul [Fact p.Prime]
    [Algebra (IntegersAtPrime p) (B : Type u)] {i m : ℕ} (hi : 1 ≤ i) (hip : i < p) :
    IsUnit (((i + p * m : ℕ) : (B : Type u))) :=
  isUnit_natCast_of_not_dvd B p (not_dvd_add_mul p hi hip)

/-- The value of `θ` on `z^j ξ^[n]` with `j < p` is the value `thetaBasis` assigns to `(n, j)`. -/
public theorem theta_xiElt [Nontrivial (XiAlg B)] (hp : p ≠ 0) (n j : ℕ) (hj : j < p) :
    theta B p lam hp (xiElt B p lam n j) = thetaBasis B p lam n ⟨j, hj⟩ := by
  have h := theta_basisZXi B p lam hp n ⟨j, hj⟩
  rwa [basisZXi_eq_xiElt] at h

/-- `θ(z^j) = p z^{j+1}/(j+1)` for `j + 1 ≠ p`. -/
public theorem theta_xiElt_zero [Nontrivial (XiAlg B)] (hp : p ≠ 0) (j : ℕ) (hj : j < p)
    (hne : j + 1 ≠ p) :
    theta B p lam hp (xiElt B p lam 0 j) =
      ((p : (B : Type u)) * Ring.inverse ((j + 1 : ℕ) : (B : Type u))) •
        xiElt B p lam 0 (j + 1) := by
  rw [theta_xiElt B p lam hp 0 j hj]
  exact thetaBasis_zero_of_ne B p lam ⟨j, hj⟩ hne

/-- `θ(z^{p-1}) = z^p`. -/
public theorem theta_xiElt_zero_top [Nontrivial (XiAlg B)] (hp : p ≠ 0) (j : ℕ) (hj : j < p)
    (hne : j + 1 = p) :
    theta B p lam hp (xiElt B p lam 0 j) = zElt B p lam ^ p := by
  rw [theta_xiElt B p lam hp 0 j hj]
  exact thetaBasis_zero_top B p lam ⟨j, hj⟩ hne

/-- `θ(z^{p-1} ξ^[n+1]) = ξ^[n+2]`. -/
public theorem theta_xiElt_succ_top [Nontrivial (XiAlg B)] (hp : p ≠ 0) (n j : ℕ) (hj : j < p)
    (hne : j + 1 = p) :
    theta B p lam hp (xiElt B p lam (n + 1) j) = xiElt B p lam (n + 2) 0 := by
  rw [theta_xiElt B p lam hp (n + 1) j hj]
  exact thetaBasis_succ_top B p lam n ⟨j, hj⟩ hne

/-- `θ(z^j ξ^[n+1]) = (p z^{j+1} ξ^[n+1] - p λ θ(z^j ξ^[n]))/(j + 1 + p(n+1))` for `j + 1 ≠ p`. -/
public theorem theta_xiElt_succ [Nontrivial (XiAlg B)] (hp : p ≠ 0) (n j : ℕ) (hj : j < p)
    (hne : j + 1 ≠ p) :
    theta B p lam hp (xiElt B p lam (n + 1) j) =
      Ring.inverse ((j + 1 + p * (n + 1) : ℕ) : (B : Type u)) •
        ((p : (B : Type u)) • xiElt B p lam (n + 1) (j + 1) -
          ((p : (B : Type u)) * lam) • theta B p lam hp (xiElt B p lam n j)) := by
  rw [theta_xiElt B p lam hp (n + 1) j hj, theta_xiElt B p lam hp n j hj]
  exact thetaBasis_succ_of_ne B p lam n ⟨j, hj⟩ hne

/-- `ε` is `p` on `1`, `-p λ` on `ξ` and zero on every other basis vector `z^j ξ^[n]`. -/
public theorem epsilon_xiElt [Nontrivial (XiAlg B)] (hp : p ≠ 0) (n j : ℕ) (hj : j < p) :
    epsilon B p lam hp (xiElt B p lam n j) =
      if n = 0 ∧ j = 0 then ((p : ℕ) : (B : Type u))
      else if n = 1 ∧ j = 0 then -(((p : ℕ) : (B : Type u)) * lam) else 0 := by
  have h := epsilon_basisZXi B p lam hp n ⟨j, hj⟩
  rwa [basisZXi_eq_xiElt] at h

/-- `θ(∂_z 1) = 0`, because `∂_z 1 = 0`. -/
public theorem theta_partialZ_one [Nontrivial (XiAlg B)] (hp : p ≠ 0)
    {pz : primeRing B p lam →ₗ[(B : Type u)] primeRing B p lam}
    (hpz : PartialZValues B p lam pz) :
    theta B p lam hp (pz (xiElt B p lam 0 0)) = 0 := by
  rw [hpz.pow 0]
  simp

/-- `θ(∂_z z^j) = p z^j` for `1 ≤ j < p`, since `∂_z z^j = j z^{j-1}` and
`θ(z^{j-1}) = p z^j / j`. -/
public theorem theta_partialZ_pow [Nontrivial (XiAlg B)] [Fact p.Prime]
    [Algebra (IntegersAtPrime p) (B : Type u)] (hp : p ≠ 0)
    {pz : primeRing B p lam →ₗ[(B : Type u)] primeRing B p lam}
    (hpz : PartialZValues B p lam pz) (j : ℕ) (hj1 : 1 ≤ j) (hj : j < p) :
    theta B p lam hp (pz (xiElt B p lam 0 j)) =
      ((p : ℕ) : (B : Type u)) • xiElt B p lam 0 j := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  have hu : IsUnit (((k + 1 : ℕ) : (B : Type u))) := isUnit_natCast_of_lt B p hj1 hj
  have hc : ((k + 1 : ℕ) : (B : Type u)) *
      (((p : ℕ) : (B : Type u)) * Ring.inverse ((k + 1 : ℕ) : (B : Type u))) =
        ((p : ℕ) : (B : Type u)) := by
    rw [mul_comm, mul_assoc, Ring.inverse_mul_cancel _ hu, mul_one]
  rw [hpz.pow (k + 1), Nat.add_sub_cancel, map_smul,
    theta_xiElt_zero B p lam hp k (by omega) (by omega), smul_smul, hc]

/-- `θ(∂_z ξ) = p ξ + p λ`, since `∂_z ξ = p z^{p-1}` and `θ(z^{p-1}) = z^p = ξ + λ`. -/
public theorem theta_partialZ_xi [Nontrivial (XiAlg B)] (hp : p ≠ 0)
    {pz : primeRing B p lam →ₗ[(B : Type u)] primeRing B p lam}
    (hpz : PartialZValues B p lam pz) :
    theta B p lam hp (pz (xiElt B p lam 1 0)) =
      ((p : ℕ) : (B : Type u)) • xiElt B p lam 1 0 +
        (((p : ℕ) : (B : Type u)) * lam) • xiElt B p lam 0 0 := by
  have h : pz (xiElt B p lam 1 0) =
      ((p : ℕ) : (B : Type u)) • xiElt B p lam 0 (p - 1) := hpz.xiPow 0
  rw [h, map_smul, theta_xiElt_zero_top B p lam hp (p - 1) (by omega) (by omega),
    zElt_pow_prime, smul_add, smul_smul]

/-- `θ(∂_z ξ^[n+2]) = p ξ^[n+2]`, since `∂_z ξ^[n+2] = p z^{p-1} ξ^[n+1]` and
`θ(z^{p-1} ξ^[n+1]) = ξ^[n+2]`. -/
public theorem theta_partialZ_xiMonomial [Nontrivial (XiAlg B)] (hp : p ≠ 0)
    {pz : primeRing B p lam →ₗ[(B : Type u)] primeRing B p lam}
    (hpz : PartialZValues B p lam pz) (n : ℕ) :
    theta B p lam hp (pz (xiElt B p lam (n + 2) 0)) =
      ((p : ℕ) : (B : Type u)) • xiElt B p lam (n + 2) 0 := by
  have h : pz (xiElt B p lam (n + 2) 0) =
      ((p : ℕ) : (B : Type u)) • xiElt B p lam (n + 1) (p - 1) := hpz.xiPow (n + 1)
  rw [h, map_smul, theta_xiElt_succ_top B p lam hp n (p - 1) (by omega) (by omega)]

/-- `θ(∂_z (z^j ξ^[n+1])) = p z^j ξ^[n+1]` for `1 ≤ j < p`: the two terms of `∂_z (z^j ξ^[n+1])`
are matched exactly by the defining recursion of `θ` on `z^{j-1} ξ^[n+1]`. -/
public theorem theta_partialZ_xiElt_succ [Nontrivial (XiAlg B)] [Fact p.Prime]
    [Algebra (IntegersAtPrime p) (B : Type u)] (hp : p ≠ 0)
    {pz : primeRing B p lam →ₗ[(B : Type u)] primeRing B p lam}
    (hpz : PartialZValues B p lam pz) (n j : ℕ) (hj1 : 1 ≤ j) (hj : j < p) :
    theta B p lam hp (pz (xiElt B p lam (n + 1) j)) =
      ((p : ℕ) : (B : Type u)) • xiElt B p lam (n + 1) j := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  have hu : IsUnit (((k + 1 + p * (n + 1) : ℕ) : (B : Type u))) :=
    isUnit_natCast_add_mul B p hj1 hj
  rw [hpz.xiZ n (k + 1) hj1, Nat.add_sub_cancel, map_add, map_smul, map_smul,
    theta_xiElt_succ B p lam hp n k (by omega) (by omega), smul_smul,
    Ring.mul_inverse_cancel _ hu, one_smul, sub_add_cancel]

/-- **Assumption (07Q5) on a basis vector.** The remainder `p z^j ξ^[n] - θ(∂_z (z^j ξ^[n]))` is
the image of `ε(z^j ξ^[n]) ∈ B`. -/
public theorem smul_sub_theta_partialZ_xiElt [Nontrivial (XiAlg B)] [Fact p.Prime]
    [Algebra (IntegersAtPrime p) (B : Type u)] (hp : p ≠ 0)
    {pz : primeRing B p lam →ₗ[(B : Type u)] primeRing B p lam}
    (hpz : PartialZValues B p lam pz) (n j : ℕ) (hj : j < p) :
    ((p : ℕ) : (B : Type u)) • xiElt B p lam n j -
        theta B p lam hp (pz (xiElt B p lam n j)) =
      algebraMap (B : Type u) (primeRing B p lam)
        (epsilon B p lam hp (xiElt B p lam n j)) := by
  rw [epsilon_xiElt B p lam hp n j hj]
  split_ifs with h0 h1
  · obtain ⟨rfl, rfl⟩ := h0
    rw [theta_partialZ_one B p lam hp hpz, sub_zero, xiElt_zero_zero,
      Algebra.algebraMap_eq_smul_one]
  · obtain ⟨rfl, rfl⟩ := h1
    rw [theta_partialZ_xi B p lam hp hpz, xiElt_zero_zero, Algebra.algebraMap_eq_smul_one,
      neg_smul]
    abel
  · rw [map_zero, sub_eq_zero]
    rcases Nat.eq_zero_or_pos j with rfl | hj1
    · obtain _ | _ | k := n
      · exact absurd ⟨rfl, rfl⟩ h0
      · exact absurd ⟨rfl, rfl⟩ h1
      · exact (theta_partialZ_xiMonomial B p lam hp hpz k).symm
    · obtain _ | m := n
      · exact (theta_partialZ_pow B p lam hp hpz j hj1 hj).symm
      · exact (theta_partialZ_xiElt_succ B p lam hp hpz m j hj1 hj).symm

/-- **Assumption (07Q5) of Lemma 07Q7 for the extension of Tag 07N1**, in the sharp form of the
footnote of the source: the remainder `p f - θ(∂_z f)` is the image of the element
`epsilon f` of `B`, which is `p` on `1`, `-p λ` on `ξ` and zero on every other basis vector. -/
public theorem smul_sub_theta_partialZ [Nontrivial (XiAlg B)] [Fact p.Prime]
    [Algebra (IntegersAtPrime p) (B : Type u)] (hp : p ≠ 0)
    {pz : primeRing B p lam →ₗ[(B : Type u)] primeRing B p lam}
    (hpz : PartialZValues B p lam pz) (f : primeRing B p lam) :
    ((p : ℕ) : (B : Type u)) • f - theta B p lam hp (pz f) =
      algebraMap (B : Type u) (primeRing B p lam) (epsilon B p lam hp f) := by
  have key : (((p : ℕ) : (B : Type u)) • LinearMap.id -
        (theta B p lam hp).comp pz : primeRing B p lam →ₗ[(B : Type u)] primeRing B p lam) =
      (Algebra.linearMap (B : Type u) (primeRing B p lam)).comp (epsilon B p lam hp) := by
    refine linearMap_ext_xiElt B p lam hp fun n i ↦ ?_
    simpa using smul_sub_theta_partialZ_xiElt B p lam hp hpz n (i : ℕ) i.isLt
  have h := congrArg (fun g : primeRing B p lam →ₗ[(B : Type u)] primeRing B p lam ↦ g f) key
  simpa using h

/-- The values of `θ` on the free basis satisfy `∂_z(θ(z^i ξ^[n])) = p z^i ξ^[n]`, by induction
on `n` and case distinction on whether `i` is the top power `p - 1` of `z`. -/
public theorem partialZ_thetaBasis [Fact p.Prime]
    [Algebra (IntegersAtPrime p) (B : Type u)]
    {pz : primeRing B p lam →ₗ[(B : Type u)] primeRing B p lam}
    (hpz : PartialZValues B p lam pz) (n : ℕ) (i : Fin p) :
    pz (thetaBasis B p lam n i) = ((p : ℕ) : (B : Type u)) • xiElt B p lam n (i : ℕ) := by
  induction n with
  | zero =>
    by_cases hi : (i : ℕ) + 1 = p
    · have h1 := hpz.pow p
      have h2 : p - 1 = (i : ℕ) := by omega
      rw [h2] at h1
      rw [thetaBasis_zero_top B p lam i hi, ← xiElt_zero_left]
      exact h1
    · have hlt := i.isLt
      have hu := Ring.inverse_mul_cancel ((((i : ℕ) + 1 : ℕ)) : (B : Type u))
        (isUnit_natCast_of_lt B p (Nat.le_add_left 1 (i : ℕ)) (by omega))
      have hscal : (p : (B : Type u)) * Ring.inverse ((((i : ℕ) + 1 : ℕ)) : (B : Type u)) *
          ((((i : ℕ) + 1 : ℕ)) : (B : Type u)) = (p : (B : Type u)) := by
        linear_combination (p : (B : Type u)) * hu
      rw [thetaBasis_zero_of_ne B p lam i hi, map_smul, hpz.pow ((i : ℕ) + 1),
        Nat.add_sub_cancel, smul_smul, hscal]
  | succ m ih =>
    by_cases hi : (i : ℕ) + 1 = p
    · have h1 := hpz.xiPow (m + 1)
      have h2 : p - 1 = (i : ℕ) := by omega
      rw [h2] at h1
      rw [thetaBasis_succ_top B p lam m i hi]
      exact h1
    · have hlt := i.isLt
      have hu := Ring.inverse_mul_cancel
        ((((i : ℕ) + 1 + p * (m + 1) : ℕ)) : (B : Type u))
        (isUnit_natCast_add_mul B p (Nat.le_add_left 1 (i : ℕ)) (by omega))
      have hscal : Ring.inverse ((((i : ℕ) + 1 + p * (m + 1) : ℕ)) : (B : Type u)) *
          ((p : (B : Type u)) * ((((i : ℕ) + 1 + p * (m + 1) : ℕ)) : (B : Type u))) =
            (p : (B : Type u)) := by
        linear_combination (p : (B : Type u)) * hu
      have hinner : (p : (B : Type u)) •
            (((((i : ℕ) + 1 + p * (m + 1) : ℕ)) : (B : Type u)) •
                xiElt B p lam (m + 1) (i : ℕ) +
              ((p : (B : Type u)) * lam) • xiElt B p lam m (i : ℕ)) -
            ((p : (B : Type u)) * lam) • ((p : (B : Type u)) • xiElt B p lam m (i : ℕ)) =
          ((p : (B : Type u)) * ((((i : ℕ) + 1 + p * (m + 1) : ℕ)) : (B : Type u))) •
            xiElt B p lam (m + 1) (i : ℕ) := by
        module
      rw [thetaBasis_succ_of_ne B p lam m i hi, map_smul, map_sub, map_smul, map_smul,
        hpz.xiZ m ((i : ℕ) + 1) (Nat.le_add_left 1 (i : ℕ)), ih, Nat.add_sub_cancel, hinner,
        smul_smul, hscal]

/-- **Assumption (07Q3) of Lemma 07Q7 for the extension of Tag 07N1.**  The composite
`∂_z ∘ θ` is multiplication by `p`. -/
public theorem partialZ_theta [Nontrivial (XiAlg B)] [Fact p.Prime]
    [Algebra (IntegersAtPrime p) (B : Type u)] (hp : p ≠ 0)
    {pz : primeRing B p lam →ₗ[(B : Type u)] primeRing B p lam}
    (hpz : PartialZValues B p lam pz) (f : primeRing B p lam) :
    pz (theta B p lam hp f) = ((p : ℕ) : (B : Type u)) • f := by
  have key : pz ∘ₗ theta B p lam hp =
      ((p : ℕ) : (B : Type u)) •
        (LinearMap.id : primeRing B p lam →ₗ[(B : Type u)] primeRing B p lam) := by
    refine linearMap_ext_xiElt B p lam hp fun n i ↦ ?_
    rw [LinearMap.comp_apply, ← basisZXi_eq_xiElt B p lam hp n i, theta_basisZXi,
      partialZ_thetaBasis B p lam hpz n i, LinearMap.smul_apply, LinearMap.id_apply,
      basisZXi_eq_xiElt]
  exact congrArg (fun g : primeRing B p lam →ₗ[(B : Type u)] primeRing B p lam ↦ g f) key

end Prime

end Crystalline.PthRootExtension

end

end
