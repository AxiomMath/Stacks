module

public import StacksFrontier.RingTheory.ReesAlgebra.ExtendLinearMaps

/-!
# Enlarging the exponent of a splitting

Let `A` be a commutative ring, `J ⊆ A` an ideal and `c ≤ d`. A family `ψ : Fin r → J ^ d →ₗ[A] A`
*restricts* a family `φ : Fin r → J ^ c →ₗ[A] A` when the two agree on `J ^ d ⊆ J ^ c`. This file
shows that the graded algebra map `Stacks.ReesAlgebra.extendLinearMaps` built from `ψ` agrees,
on every homogeneous element of `reesAlgebra (J ^ d)`, with the one built from `φ`.

This is what lets a splitting be enlarged more than once without changing the maps already
constructed from it: the statement of [Stacks, Tag 0EH6] enlarges `c` and adjusts the `φ_j`
accordingly, and the enlargement is produced one target at a time, each step keeping the maps
produced by the previous ones.

It also records the coefficient of the extension at a fixed monomial as an honest `A`-linear
map on the relevant power of `J`, which is the form in which the local-section formula of
[Stacks, Tag 0EH6] is applied to a sum of products.

## Main definitions

* `Stacks.ReesAlgebra.RestrictsSplitting` — `ψ` on `J ^ d` restricts `φ` on `J ^ c`.
* `Stacks.ReesAlgebra.extendCoeff` — the coefficient of the extension at a monomial, as an
  `A`-linear map on `(J ^ d) ^ n`.

## Main results

* `Stacks.ReesAlgebra.degreeMap_of_restrictsSplitting` — the degreewise pieces of the extension
  are unchanged by an enlargement of the exponent.
* `Stacks.ReesAlgebra.extendLinearMaps_monomial_of_restrictsSplitting` — hence so is the
  extension itself on a homogeneous element.
* `Stacks.ReesAlgebra.extendCoeff_apply` — the linear map is the coefficient it is meant to be.

## Implementation notes

`Stacks.ReesAlgebra.degreeMap` is defined by recursion on the degree through
`Stacks.ReesAlgebra.phiOnPow`, which applies a member of the family to an element of
`(J ^ d) ^ (n + 1)` viewed in `J ^ d`. Both the hypothesis of `RestrictsSplitting` and the
induction step therefore compare the two families at one and the same element of `A`, with
different membership proofs; the proofs are irrelevant, so each step is `Subtype.ext` on the
value.

## References

* [Stacks Project, Tag 0EIB](https://stacks.math.columbia.edu/tag/0EIB)
* [Stacks Project, Tag 0EIC](https://stacks.math.columbia.edu/tag/0EIC)
* [Stacks Project, Tag 0EH6](https://stacks.math.columbia.edu/tag/0EH6)
-/

@[expose] public noncomputable section

namespace Stacks.ReesAlgebra

universe u

variable {A : Type u} [CommRing A] {r : ℕ}

/-- The family `ψ` on `J ^ d` restricts the family `φ` on `J ^ c`, where `c ≤ d`. -/
public def RestrictsSplitting (J : Ideal A) {c d : ℕ} (hcd : c ≤ d)
    (φ : Fin r → (J ^ c : Ideal A) →ₗ[A] A) (ψ : Fin r → (J ^ d : Ideal A) →ₗ[A] A) : Prop :=
  ∀ (j : Fin r) (g : A) (hg : g ∈ J ^ d),
    ψ j ⟨g, hg⟩ = φ j ⟨g, Ideal.pow_le_pow_right hcd hg⟩

/-- Restricting a splitting is transitive. -/
public lemma RestrictsSplitting.trans {J : Ideal A} {c d e : ℕ} {hcd : c ≤ d} {hde : d ≤ e}
    {φ : Fin r → (J ^ c : Ideal A) →ₗ[A] A} {ψ : Fin r → (J ^ d : Ideal A) →ₗ[A] A}
    {χ : Fin r → (J ^ e : Ideal A) →ₗ[A] A}
    (h₁ : RestrictsSplitting J hcd φ ψ) (h₂ : RestrictsSplitting J hde ψ χ) :
    RestrictsSplitting J (hcd.trans hde) φ χ := fun j g hg =>
  (h₂ j g hg).trans (h₁ j g (Ideal.pow_le_pow_right hde hg))

/-- A power of a larger power of an ideal is contained in the same power of a smaller one. -/
public lemma pow_pow_le_pow_pow (J : Ideal A) {c d : ℕ} (hcd : c ≤ d) (n : ℕ) :
    ((J ^ d : Ideal A) ^ n) ≤ ((J ^ c : Ideal A) ^ n) := by
  rw [← pow_mul, ← pow_mul]
  exact Ideal.pow_le_pow_right (Nat.mul_le_mul hcd (le_refl n))

/-- On a monomial of the Rees algebra, the extension is the degreewise piece. -/
private lemma extendLinearMaps_monomial_eq (J : Ideal A) (φ : Fin r → J →ₗ[A] A) (n : ℕ) (x : A)
    (hx : x ∈ J ^ n) (p : Polynomial.monomial n x ∈ reesAlgebra J) :
    extendLinearMaps J φ ⟨Polynomial.monomial n x, p⟩ = degreeMap J φ n ⟨x, hx⟩ :=
  reesLinearMap_monomial J φ n x hx

/-- **The degreewise pieces of the extension are unchanged by an enlargement of the exponent.**

The recursion is the same on both sides, and at each step the two families are applied to the
same element of `A`. -/
public lemma degreeMap_of_restrictsSplitting (J : Ideal A) {c d : ℕ} (hcd : c ≤ d)
    (φ : Fin r → (J ^ c : Ideal A) →ₗ[A] A) (ψ : Fin r → (J ^ d : Ideal A) →ₗ[A] A)
    (h : RestrictsSplitting J hcd φ ψ) :
    ∀ (n : ℕ) (x : A) (hxd : x ∈ (J ^ d : Ideal A) ^ n) (hxc : x ∈ (J ^ c : Ideal A) ^ n),
      degreeMap (J ^ d) ψ n ⟨x, hxd⟩ = degreeMap (J ^ c) φ n ⟨x, hxc⟩ := by
  intro n
  induction n with
  | zero =>
      intro x hxd hxc
      simp [degreeMap]
  | succ n ih =>
      intro x hxd hxc
      rw [degreeMap_succ, degreeMap_succ]
      refine Finset.sum_congr rfl fun j _ => ?_
      have hval : ((phiOnPow (J ^ d) ψ j n ⟨x, hxd⟩ : ↥((J ^ d : Ideal A) ^ n)) : A) =
          ((phiOnPow (J ^ c) φ j n ⟨x, hxc⟩ : ↥((J ^ c : Ideal A) ^ n)) : A) :=
        h j x (Ideal.pow_le_self (by omega) hxd)
      refine congrArg (· * MvPolynomial.X j) ((ih _ (phiOnPow _ ψ j n ⟨x, hxd⟩).2
        (hval ▸ (phiOnPow _ φ j n ⟨x, hxc⟩).2)).trans (congrArg _ (Subtype.ext hval)))

/-- **The extension is unchanged by an enlargement of the exponent**, on an element of the Rees
algebra supported in a single degree. -/
public lemma extendLinearMaps_monomial_of_restrictsSplitting (J : Ideal A) {c d : ℕ}
    (hcd : c ≤ d) (φ : Fin r → (J ^ c : Ideal A) →ₗ[A] A)
    (ψ : Fin r → (J ^ d : Ideal A) →ₗ[A] A) (h : RestrictsSplitting J hcd φ ψ)
    (n : ℕ) (x : A) (hxd : x ∈ (J ^ d : Ideal A) ^ n) (hxc : x ∈ (J ^ c : Ideal A) ^ n)
    (pd : Polynomial.monomial n x ∈ reesAlgebra (J ^ d))
    (pc : Polynomial.monomial n x ∈ reesAlgebra (J ^ c)) :
    extendLinearMaps (J ^ d) ψ ⟨Polynomial.monomial n x, pd⟩ =
      extendLinearMaps (J ^ c) φ ⟨Polynomial.monomial n x, pc⟩ := by
  have h1 : reesLinearMap (J ^ d) ψ ⟨Polynomial.monomial n x, pd⟩ =
      degreeMap (J ^ d) ψ n ⟨x, hxd⟩ := reesLinearMap_monomial (J ^ d) ψ n x hxd
  have h2 : reesLinearMap (J ^ c) φ ⟨Polynomial.monomial n x, pc⟩ =
      degreeMap (J ^ c) φ n ⟨x, hxc⟩ := reesLinearMap_monomial (J ^ c) φ n x hxc
  show reesLinearMap (J ^ d) ψ ⟨Polynomial.monomial n x, pd⟩ =
    reesLinearMap (J ^ c) φ ⟨Polynomial.monomial n x, pc⟩
  rw [h1, h2, degreeMap_of_restrictsSplitting J hcd φ ψ h n x hxd hxc]

/-- The coefficient at a monomial `σ` of the extension of `φ`, as an `A`-linear map on
`(J ^ d) ^ n`. -/
public def extendCoeff (J : Ideal A) (d n : ℕ) (φ : Fin r → (J ^ d : Ideal A) →ₗ[A] A)
    (σ : Fin r →₀ ℕ) : ↥((J ^ d : Ideal A) ^ n) →ₗ[A] A where
  toFun x := (degreeMap (J ^ d) φ n x).coeff σ
  map_add' x y := by
    rw [map_add (degreeMap (J ^ d) φ n), AddMonoidAlgebra.coeff_add]
    rfl
  map_smul' a x := by
    rw [map_smul (degreeMap (J ^ d) φ n), MvPolynomial.coeff_smul]
    rfl

/-- `Stacks.ReesAlgebra.extendCoeff` is the coefficient of the extension that it is meant to
be. -/
public lemma extendCoeff_apply (J : Ideal A) (d n : ℕ)
    (φ : Fin r → (J ^ d : Ideal A) →ₗ[A] A) (σ : Fin r →₀ ℕ) (x : A)
    (hx : x ∈ (J ^ d : Ideal A) ^ n) (p : Polynomial.monomial n x ∈ reesAlgebra (J ^ d)) :
    extendCoeff J d n φ σ ⟨x, hx⟩ =
      (extendLinearMaps (J ^ d) φ ⟨Polynomial.monomial n x, p⟩).coeff σ := by
  have h1 : reesLinearMap (J ^ d) φ ⟨Polynomial.monomial n x, p⟩ =
      degreeMap (J ^ d) φ n ⟨x, hx⟩ := reesLinearMap_monomial (J ^ d) φ n x hx
  show _ = (reesLinearMap (J ^ d) φ ⟨Polynomial.monomial n x, p⟩).coeff σ
  rw [h1]
  rfl

/-- **The coefficients of the extension are unchanged by an enlargement of the exponent.** -/
public lemma extendCoeff_of_restrictsSplitting (J : Ideal A) {c d : ℕ} (hcd : c ≤ d)
    (φ : Fin r → (J ^ c : Ideal A) →ₗ[A] A) (ψ : Fin r → (J ^ d : Ideal A) →ₗ[A] A)
    (h : RestrictsSplitting J hcd φ ψ) (n : ℕ) (σ : Fin r →₀ ℕ) (x : A)
    (hxd : x ∈ (J ^ d : Ideal A) ^ n) (hxc : x ∈ (J ^ c : Ideal A) ^ n) :
    extendCoeff J d n ψ σ ⟨x, hxd⟩ = extendCoeff J c n φ σ ⟨x, hxc⟩ := by
  show (degreeMap (J ^ d) ψ n ⟨x, hxd⟩).coeff σ =
    (degreeMap (J ^ c) φ n ⟨x, hxc⟩).coeff σ
  rw [degreeMap_of_restrictsSplitting J hcd φ ψ h n x hxd hxc]

end Stacks.ReesAlgebra

end
