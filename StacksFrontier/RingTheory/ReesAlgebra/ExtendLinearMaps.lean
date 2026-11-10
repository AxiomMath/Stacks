module

public import Mathlib.RingTheory.ReesAlgebra
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import StacksCore.Tactic.StacksAttribute

/-!
# Extending a family of coefficient maps on an ideal to its Rees algebra

Let `A` be a commutative ring, `J ⊆ A` an ideal and `φ : Fin r → J →ₗ[A] A` a finite family of
`A`-linear maps on `J`. This file extends `φ` to a graded `A`-algebra map
`extendLinearMaps J φ : reesAlgebra J →ₐ[A] MvPolynomial (Fin r) A` which sends an element `x`
of `J`, placed in degree one, to the linear form `∑ⱼ φ j x · Xⱼ`, and shows that this is the
only algebra map with that degree-one component.

The extension exists because the degree-`n` part of the Rees algebra is `Jⁿ`, and each `φ j`
carries `J^(n+1)` into `Jⁿ`: iterating the `φ j` therefore turns an element of `Jⁿ` into a
homogeneous polynomial of degree `n`, and multiplicativity is a direct induction.

If the `φ j` split the inclusion `I^c ⊆ A` against a chosen family of generators `f` of `I`,
in the sense that `∑ⱼ f j · φ j x = x` on `I^c`, then evaluating the variables of the extension
at `f j` in degree one recovers the inclusion `reesAlgebra (I ^ c) ⊆ A[X]`.

## Main definitions

* `Stacks.ReesAlgebra.degreeOne` — an element of `J`, placed in degree one of `reesAlgebra J`.
* `Stacks.ReesAlgebra.extendLinearMaps` — the graded algebra map extending `φ`.

## Main results

* `Stacks.ReesAlgebra.extendLinearMaps_degreeOne` — the degree-one component of the extension.
* `Stacks.ReesAlgebra.extendLinearMaps_homogeneous` — the extension preserves the grading.
* `Stacks.ReesAlgebra.extendLinearMaps_unique` — the extension is the unique algebra map with
  that degree-one component.
* `Stacks.ReesAlgebra.aeval_extendLinearMaps_eq` — under the splitting identity, evaluating the
  extension at the chosen generators in degree one is the inclusion into `A[X]`.

## Implementation notes

Mathlib realizes `⨁ₙ Jⁿ` as `reesAlgebra J`, the subalgebra of `A[X]` of polynomials whose
`n`-th coefficient lies in `Jⁿ`. An element of `reesAlgebra J` supported in a single degree `n`
is therefore described by the condition that all its other coefficients vanish, which is how
`extendLinearMaps_homogeneous` is stated. The extension is built as a linear map by summing its
degreewise pieces over the coefficients of a polynomial, and only then upgraded to an algebra
map; `degreeMap_mul` is the multiplicativity of the degreewise pieces that this needs.

Uniqueness is `AlgHom.ext_of_eq_adjoin` applied to Mathlib's
`adjoin_monomial_eq_reesAlgebra`: the Rees algebra is generated over `A` by its degree-one part.

## References

* [Stacks Project, Tag 0EIB](https://stacks.math.columbia.edu/tag/0EIB)
-/

@[expose] public noncomputable section

namespace Stacks.ReesAlgebra

universe u

variable {A : Type u} [CommRing A] {r : ℕ}

/-- An `A`-linear map `J →ₗ[A] A` carries `J ^ (n + 1)` into `J ^ n`.

An element of `J ^ (n + 1) = J ^ n * J` is a sum of products `a * b` with `a ∈ J ^ n` and
`b ∈ J`, and `φ (a * b) = a * φ b`. -/
public lemma linearMap_mem_pow_pred (J : Ideal A) (φ : J →ₗ[A] A) (n : ℕ)
    {x : A} (hx : x ∈ J ^ (n + 1)) : φ ⟨x, Ideal.pow_le_self (by omega) hx⟩ ∈ J ^ n := by
  have hJ : J ^ n * J ≤ J := Ideal.mul_le_right
  have hmain : ∀ (z : A) (hz : z ∈ J ^ n * J), φ ⟨z, hJ hz⟩ ∈ J ^ n := by
    intro z hz
    refine Submodule.mul_induction_on' ?_ ?_ hz
    · intro a ha b hb
      have heq : (⟨a * b, hJ (Ideal.mul_mem_mul ha hb)⟩ : J) = a • (⟨b, hb⟩ : J) := by
        ext
        simp [smul_eq_mul]
      rw [heq, map_smul]
      exact Ideal.mul_mem_right (φ ⟨b, hb⟩) (J ^ n) ha
    · intro z hz w hw hzmem hwmem
      have heq : (⟨z + w, hJ (Ideal.add_mem (J ^ n * J) hz hw)⟩ : J) =
          (⟨z, hJ hz⟩ : J) + ⟨w, hJ hw⟩ := by
        ext
        rfl
      rw [heq, map_add]
      exact Ideal.add_mem (J ^ n) hzmem hwmem
  rw [pow_succ J n] at hx
  exact hmain x hx

/-- The map `J ^ (n + 1) →ₗ[A] J ^ n` induced by the `j`-th member of the family `φ`. -/
public noncomputable def phiOnPow (J : Ideal A) (φ : Fin r → J →ₗ[A] A)
    (j : Fin r) (n : ℕ) : ↥(J ^ (n + 1) : Ideal A) →ₗ[A] ↥(J ^ n : Ideal A) :=
  LinearMap.codRestrict (J ^ n)
    ((φ j).comp (LinearMap.codRestrict J (Submodule.subtype (J ^ (n + 1)))
      (fun x => Ideal.pow_le_self (by omega) x.property)))
    (fun x => linearMap_mem_pow_pred J (φ j) n x.property)

/-- The degree-`n` piece of the extension of `φ`: a map `J ^ n →ₗ[A] A[Xᵢ]` landing in the
homogeneous polynomials of degree `n`.

In degree `0` it is the structure map `A → A[Xᵢ]`; in degree `n + 1` it is
`x ↦ ∑ⱼ degreeMap n (φ j x) * Xⱼ`. -/
public noncomputable def degreeMap (J : Ideal A) (φ : Fin r → J →ₗ[A] A) :
    (n : ℕ) → ↥(J ^ n : Ideal A) →ₗ[A] MvPolynomial (Fin r) A :=
  Nat.rec
    ((Algebra.linearMap A (MvPolynomial (Fin r) A)).comp (Submodule.subtype (J ^ 0)))
    (fun n prev => ∑ j : Fin r,
      (LinearMap.mulRight A (MvPolynomial.X j)).comp (prev.comp (phiOnPow J φ j n)))

/-- The recursion defining `degreeMap`, in applied form. -/
public lemma degreeMap_succ (J : Ideal A) (φ : Fin r → J →ₗ[A] A) (n : ℕ)
    (x : ↥(J ^ (n + 1) : Ideal A)) :
    degreeMap J φ (n + 1) x =
      ∑ j : Fin r, degreeMap J φ n (phiOnPow J φ j n x) * MvPolynomial.X j := by
  simp [degreeMap, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.mulRight_apply]

/-- The degreewise pieces of the extension are multiplicative. -/
public lemma degreeMap_mul (J : Ideal A) (φ : Fin r → J →ₗ[A] A)
    (m n : ℕ) (x : ↥(J ^ m : Ideal A)) (y : ↥(J ^ n : Ideal A)) :
    degreeMap J φ (m + n) ⟨(x : A) * (y : A), by
      simpa only [pow_add] using Ideal.mul_mem_mul x.property y.property⟩ =
      degreeMap J φ m x * degreeMap J φ n y := by
  induction n with
  | zero =>
      have hxy : ((x : A) * (y : A) : A) = (y : A) • (x : A) := by
        simp [smul_eq_mul, mul_comm]
      have hmem : (x : A) * (y : A) ∈ J ^ m := by
        simpa [mul_comm] using Ideal.mul_mem_left (J ^ m) (y : A) x.property
      have hsub : (⟨(x : A) * (y : A), hmem⟩ : ↥(J ^ m : Ideal A)) = (y : A) • x := by
        ext
        exact hxy
      change degreeMap J φ (m + 0) _ = _
      simp only [Nat.add_zero]
      rw [hsub, (degreeMap J φ m).map_smul]
      simp [degreeMap, Algebra.smul_def, mul_comm]
  | succ n ih =>
      simp only [Nat.add_succ, degreeMap_succ]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      have hphi : phiOnPow J φ j (m + n)
          ⟨(x : A) * (y : A), by
            simpa [pow_add, pow_succ, mul_assoc] using
              Ideal.mul_mem_mul x.property y.property⟩ =
          ⟨(x : A) * (phiOnPow J φ j n y : A), by
            simpa [pow_add, mul_assoc] using
              Ideal.mul_mem_mul x.property (phiOnPow J φ j n y).property⟩ := by
        apply Subtype.ext
        have hxyM : (x : A) * (y : A) ∈ J ^ ((m + n) + 1) := by
          simpa [pow_add, pow_succ, mul_assoc] using Ideal.mul_mem_mul x.property y.property
        change φ j ⟨(x : A) * (y : A), Ideal.pow_le_self (by omega) hxyM⟩ =
          (x : A) * φ j ⟨(y : A), Ideal.pow_le_self (by omega) y.property⟩
        have hinput : (⟨(x : A) * (y : A), Ideal.pow_le_self (by omega) hxyM⟩ : J) =
            (x : A) • (⟨(y : A), Ideal.pow_le_self (by omega) y.property⟩ : J) := by
          ext
          simp [smul_eq_mul]
        rw [hinput, map_smul]
        simp [smul_eq_mul]
      rw [hphi, ih]
      ring

/-- The degreewise pieces of the extension land in the homogeneous polynomials of the
corresponding degree. -/
public lemma degreeMap_isHomogeneous (J : Ideal A) (φ : Fin r → J →ₗ[A] A) :
    ∀ (n : ℕ) (x : ↥(J ^ n : Ideal A)), (degreeMap J φ n x).IsHomogeneous n := by
  intro n
  induction n with
  | zero =>
      intro x
      exact MvPolynomial.isHomogeneous_C _ _
  | succ n ih =>
      intro x
      rw [degreeMap_succ]
      refine MvPolynomial.IsHomogeneous.sum _ _ _ fun j _ => ?_
      exact (ih (phiOnPow J φ j n x)).mul (MvPolynomial.isHomogeneous_X (R := A) j)

/-- Summing the degreewise pieces over the coefficients of an element of the Rees algebra may be
done over any range of indices past its degree. -/
private lemma sum_degreeMap_range (J : Ideal A) (φ : Fin r → J →ₗ[A] A)
    (N : ℕ) (z : reesAlgebra J) (hz : z.val.natDegree < N) :
    (∑ n ∈ Finset.range (z.val.natDegree + 1),
      degreeMap J φ n ⟨z.val.coeff n, z.property n⟩) =
    ∑ n ∈ Finset.range N, degreeMap J φ n ⟨z.val.coeff n, z.property n⟩ := by
  classical
  refine Finset.sum_subset (fun n hn => ?_) (fun n hn hnot => ?_)
  · exact Finset.mem_range.mpr (by have h := Finset.mem_range.mp hn; omega)
  · have hlt : z.val.natDegree < n := by
      have h₁ := Finset.mem_range.mp hn
      have h₂ : ¬ n < z.val.natDegree + 1 := by simpa using hnot
      omega
    have heq : (⟨z.val.coeff n, z.property n⟩ : ↥(J ^ n : Ideal A)) = 0 :=
      Subtype.ext (Polynomial.coeff_eq_zero_of_natDegree_lt hlt)
    rw [heq]
    simp

/-- The extension of `φ` as an `A`-linear map: the sum of its degreewise pieces, applied to the
coefficients of an element of the Rees algebra. -/
public noncomputable def reesLinearMap (J : Ideal A) (φ : Fin r → J →ₗ[A] A) :
    reesAlgebra J →ₗ[A] MvPolynomial (Fin r) A where
  toFun p := ∑ n ∈ Finset.range (p.val.natDegree + 1),
    degreeMap J φ n ⟨p.val.coeff n, p.property n⟩
  map_add' p q := by
    classical
    set N := max p.val.natDegree q.val.natDegree + 1 with hN
    have hpN : p.val.natDegree < N := by omega
    have hqN : q.val.natDegree < N := by omega
    have hpqN : (p.val + q.val).natDegree < N :=
      lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) (by omega)
    rw [sum_degreeMap_range J φ N p hpN, sum_degreeMap_range J φ N q hqN,
      sum_degreeMap_range J φ N (p + q) hpqN, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    have heq : (⟨(p + q).val.coeff n, (p + q).property n⟩ : ↥(J ^ n : Ideal A)) =
        (⟨p.val.coeff n, p.property n⟩ : ↥(J ^ n : Ideal A)) +
          ⟨q.val.coeff n, q.property n⟩ :=
      Subtype.ext (by simp [Polynomial.coeff_add])
    rw [heq, map_add]
  map_smul' a p := by
    classical
    set N := p.val.natDegree + 1 with hN
    have hpN : p.val.natDegree < N := by omega
    have hspN : (a • p.val).natDegree < N :=
      lt_of_le_of_lt (Polynomial.natDegree_smul_le a p.val) (Nat.lt_succ_self _)
    rw [sum_degreeMap_range J φ N p hpN, sum_degreeMap_range J φ N (a • p) hspN,
      Finset.smul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    have heq : (⟨(a • p).val.coeff n, (a • p).property n⟩ : ↥(J ^ n : Ideal A)) =
        a • (⟨p.val.coeff n, p.property n⟩ : ↥(J ^ n : Ideal A)) :=
      Subtype.ext (by simp [Polynomial.coeff_smul])
    rw [heq, map_smul]
    congr 1

/-- On an element of the Rees algebra supported in a single degree, the extension is the
degreewise piece in that degree. -/
public lemma reesLinearMap_monomial (J : Ideal A) (φ : Fin r → J →ₗ[A] A)
    (n : ℕ) (a : A) (ha : a ∈ J ^ n) :
    reesLinearMap J φ ⟨Polynomial.monomial n a, reesAlgebra.monomial_mem.mpr ha⟩ =
      degreeMap J φ n ⟨a, ha⟩ := by
  classical
  by_cases hzero : a = 0
  · subst a
    have hterm : (⟨Polynomial.monomial n (0 : A), reesAlgebra.monomial_mem.mpr ha⟩ :
        reesAlgebra J) = 0 := Subtype.ext (by simp)
    have hzero' : (⟨(0 : A), ha⟩ : ↥(J ^ n : Ideal A)) = 0 := Subtype.ext rfl
    rw [hterm, hzero']
    simp
  · have hm : Polynomial.monomial n a ∈ reesAlgebra J := reesAlgebra.monomial_mem.mpr ha
    have hcoeff : ∀ i, (Polynomial.monomial n a).coeff i ∈ J ^ i :=
      (mem_reesAlgebra_iff J (Polynomial.monomial n a)).mp hm
    change (∑ i ∈ Finset.range (((Polynomial.monomial n a).natDegree) + 1),
      degreeMap J φ i ⟨(Polynomial.monomial n a).coeff i, hcoeff i⟩) =
        degreeMap J φ n ⟨a, ha⟩
    rw [Polynomial.natDegree_monomial_eq n hzero, Finset.sum_eq_single n]
    · simp [Polynomial.coeff_monomial_same]
    · intro b _ hbn
      have h0 : (⟨(Polynomial.monomial n a).coeff b, hcoeff b⟩ : ↥(J ^ b : Ideal A)) = 0 :=
        Subtype.ext (by simp [Polynomial.coeff_monomial, Ne.symm hbn])
      rw [h0]
      simp
    · intro hn
      exact (hn (Finset.mem_range.mpr (Nat.lt_succ_self n))).elim

/-- The extension of `φ` is unital. -/
public lemma reesLinearMap_one (J : Ideal A) (φ : Fin r → J →ₗ[A] A) :
    reesLinearMap J φ 1 = 1 := by
  classical
  simp [reesLinearMap, degreeMap]

/-- The extension of `φ` is multiplicative. -/
public lemma reesLinearMap_mul (J : Ideal A) (φ : Fin r → J →ₗ[A] A) (p q : reesAlgebra J) :
    reesLinearMap J φ (p * q) = reesLinearMap J φ p * reesLinearMap J φ q := by
  classical
  let term (z : reesAlgebra J) (i : ℕ) : reesAlgebra J :=
    ⟨Polynomial.monomial i (z.val.coeff i), reesAlgebra.monomial_mem.mpr (z.property i)⟩
  have hsum : ∀ z : reesAlgebra J, z = ∑ i ∈ z.val.support, term z i := fun z => by
    apply Subtype.ext
    change z.val = (Subalgebra.val (reesAlgebra J)) (∑ i ∈ z.val.support, term z i)
    rw [map_sum]
    simpa [term] using z.val.as_sum_support
  rw [hsum p, hsum q, Finset.sum_mul_sum]
  simp only [map_sum]
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have hprod : term p i * term q j =
      ⟨Polynomial.monomial (i + j) (p.val.coeff i * q.val.coeff j),
        reesAlgebra.monomial_mem.mpr (by
          simpa only [pow_add] using Ideal.mul_mem_mul (p.property i) (q.property j))⟩ :=
    Subtype.ext (by simp [term, Polynomial.monomial_mul_monomial])
  rw [hprod, reesLinearMap_monomial, reesLinearMap_monomial, reesLinearMap_monomial]
  exact degreeMap_mul J φ i j ⟨p.val.coeff i, p.property i⟩ ⟨q.val.coeff j, q.property j⟩

/-- An element of an ideal `J`, placed in degree one of the Rees algebra of `J`. -/
public def degreeOne (J : Ideal A) (x : J) : reesAlgebra J :=
  ⟨Polynomial.monomial 1 (x : A),
    reesAlgebra.monomial_mem.mpr (by simpa only [pow_one] using x.property)⟩

/-- The graded `A`-algebra map `reesAlgebra J →ₐ[A] A[Xᵢ]` extending a finite family `φ` of
`A`-linear maps `J →ₗ[A] A`. -/
@[stacks 0EIB "the extended graded algebra map"]
public noncomputable def extendLinearMaps (J : Ideal A) (φ : Fin r → J →ₗ[A] A) :
    reesAlgebra J →ₐ[A] MvPolynomial (Fin r) A :=
  AlgHom.ofLinearMap (reesLinearMap J φ) (reesLinearMap_one J φ) (reesLinearMap_mul J φ)

/-- The extension sends an element of `J` in degree one to the linear form `∑ⱼ φ j x · Xⱼ`. -/
@[stacks 0EIB "the degree-one formula"]
public theorem extendLinearMaps_degreeOne (J : Ideal A) (φ : Fin r → J →ₗ[A] A) (x : J) :
    extendLinearMaps J φ (degreeOne J x) =
      ∑ j, MvPolynomial.C (φ j x) * MvPolynomial.X j := by
  classical
  rw [extendLinearMaps, AlgHom.ofLinearMap_apply, degreeOne,
    reesLinearMap_monomial J φ 1 (x : A) (by simp)]
  change degreeMap J φ (0 + 1) ⟨(x : A), by simp⟩ = _
  rw [degreeMap_succ]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [degreeMap, phiOnPow]
  change MvPolynomial.C (φ j (⟨(x : A), x.property⟩ : J)) * _ = _
  exact congrArg (fun t => MvPolynomial.C t * MvPolynomial.X j)
    (congrArg (φ j) (Subtype.ext rfl))

/-- The extension sends an element of the Rees algebra supported in degree `n` to a homogeneous
polynomial of total degree `n`. -/
@[stacks 0EIB "preservation of grading"]
public theorem extendLinearMaps_homogeneous (J : Ideal A) (φ : Fin r → J →ₗ[A] A) (n : ℕ)
    (p : reesAlgebra J) (hp : ∀ k : ℕ, k ≠ n → (p : Polynomial A).coeff k = 0) :
    (extendLinearMaps J φ p).IsHomogeneous n := by
  classical
  have hcoeff : p.val.coeff n ∈ J ^ n := p.property n
  have hpeq : p = ⟨Polynomial.monomial n (p.val.coeff n),
      reesAlgebra.monomial_mem.mpr hcoeff⟩ := by
    refine Subtype.ext (Polynomial.ext fun k => ?_)
    by_cases hk : k = n
    · subst k
      simp
    · simp [hp k hk, Polynomial.coeff_monomial, Ne.symm hk]
  rw [extendLinearMaps, AlgHom.ofLinearMap_apply, hpeq, reesLinearMap_monomial]
  exact degreeMap_isHomogeneous J φ n ⟨p.val.coeff n, hcoeff⟩

/-- Two algebra maps out of a Rees algebra agreeing on the degree-one part are equal: the Rees
algebra is generated over `A` by its degree-one elements. -/
public theorem reesAlgebra_hom_ext {B : Type*} [CommRing B] [Algebra A B] (J : Ideal A)
    (F G : reesAlgebra J →ₐ[A] B)
    (h : ∀ x : J, F (degreeOne J x) = G (degreeOne J x)) : F = G := by
  refine AlgHom.ext_of_eq_adjoin (adjoin_monomial_eq_reesAlgebra J).symm fun x hx => ?_
  obtain ⟨a, ha, hax⟩ := Submodule.mem_map.mp hx
  have heq : (⟨x, (adjoin_monomial_eq_reesAlgebra J).symm.ge
      (Algebra.subset_adjoin hx)⟩ : reesAlgebra J) = degreeOne J ⟨a, ha⟩ :=
    Subtype.ext hax.symm
  rw [heq]
  exact h ⟨a, ha⟩

/-- An algebra map out of the Rees algebra with the prescribed degree-one component is the
extension. -/
@[stacks 0EIB "uniqueness"]
public theorem extendLinearMaps_unique (J : Ideal A) (φ : Fin r → J →ₗ[A] A)
    (Ψ : reesAlgebra J →ₐ[A] MvPolynomial (Fin r) A)
    (hΨ : ∀ x : J, Ψ (degreeOne J x) = ∑ j, MvPolynomial.C (φ j x) * MvPolynomial.X j) :
    Ψ = extendLinearMaps J φ :=
  reesAlgebra_hom_ext J Ψ (extendLinearMaps J φ)
    (fun x => (hΨ x).trans (extendLinearMaps_degreeOne J φ x).symm)

/-- If the maps `φ` split the inclusion of `I ^ c` into `A` against the generators `f` of `I`,
then evaluating the extension at the `f j` in degree one is the inclusion
`reesAlgebra (I ^ c) ⊆ A[X]`.

Both sides are algebra maps out of `reesAlgebra (I ^ c)`, so by `reesAlgebra_hom_ext` it is
enough to compare them in degree one, where the comparison is exactly the splitting identity. -/
@[stacks 0EIB "the composite is the inclusion"]
public theorem aeval_extendLinearMaps_eq (I : Ideal A) (c : ℕ) (f : Fin r → A)
    (hf : ∀ j, f j ∈ I) (φ : Fin r → (I ^ c : Ideal A) →ₗ[A] A)
    (hφ : ∀ x : (I ^ c : Ideal A), (∑ j, f j * φ j x) = (x : A))
    (p : reesAlgebra (I ^ c)) :
    ((MvPolynomial.aeval (fun j ↦ degreeOne I ⟨f j, hf j⟩)
        (extendLinearMaps (I ^ c) φ p) : reesAlgebra I) : Polynomial A) =
      (p : Polynomial A) := by
  classical
  let E : MvPolynomial (Fin r) A →ₐ[A] Polynomial A :=
    (Subalgebra.val (reesAlgebra I)).comp
      (MvPolynomial.aeval (fun j ↦ degreeOne I ⟨f j, hf j⟩))
  let Ψ : reesAlgebra (I ^ c) →ₐ[A] Polynomial A := E.comp (extendLinearMaps (I ^ c) φ)
  have hE : E = MvPolynomial.aeval (fun j ↦ (degreeOne I ⟨f j, hf j⟩ : Polynomial A)) := by
    refine MvPolynomial.algHom_ext fun j => ?_
    simp [E, AlgHom.comp_apply, degreeOne, MvPolynomial.aeval_X]
  have hΨ : ∀ x : (I ^ c : Ideal A),
      Ψ (degreeOne (I ^ c) x) =
        (Subalgebra.val (reesAlgebra (I ^ c))) (degreeOne (I ^ c) x) := by
    intro x
    change E (extendLinearMaps (I ^ c) φ (degreeOne (I ^ c) x)) = _
    rw [hE, extendLinearMaps_degreeOne]
    simp only [MvPolynomial.aeval_sum, map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_X]
    simp only [degreeOne]
    change (∑ j : Fin r, Polynomial.C (φ j x) * Polynomial.monomial 1 (f j)) =
      Polynomial.monomial 1 (x : A)
    simp only [Polynomial.C_mul_monomial]
    have hsum : (∑ j, (φ j x : A) * f j) = (x : A) :=
      (Finset.sum_congr rfl fun j _ => mul_comm _ _).trans (hφ x)
    have hmap : (∑ j, Polynomial.monomial 1 ((φ j x : A) * f j)) =
        Polynomial.monomial 1 (∑ j, (φ j x : A) * f j) := by
      simp
    rw [hmap, hsum]
  have hEq : Ψ = Subalgebra.val (reesAlgebra (I ^ c)) :=
    reesAlgebra_hom_ext (I ^ c) Ψ (Subalgebra.val (reesAlgebra (I ^ c))) hΨ
  exact congrArg (fun F : reesAlgebra (I ^ c) →ₐ[A] Polynomial A => F p) hEq

end Stacks.ReesAlgebra

end
