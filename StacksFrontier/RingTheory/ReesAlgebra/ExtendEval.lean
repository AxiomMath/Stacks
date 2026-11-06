module

public import Mathlib.Algebra.Order.Antidiag.Finsupp
public import StacksFrontier.RingTheory.ReesAlgebra.ExtendEnlarge

/-!
# Recombining the coefficients of the extension at the generators

Let `I = (f₁, …, f_r)` be an ideal of a commutative ring `A` and let
`ψ_j : I ^ d → A` split the inclusion against the generators, so that `∑ⱼ fⱼ ψⱼ(x) = x` for
`x ∈ I ^ d`. [Stacks, Tag 0EIB] extends the `ψ_j` to a graded algebra map
`Φ : reesAlgebra (I ^ d) ⟶ A[T₁, …, T_r]` and says that composing `Φ` with `T_j ↦ f_j` returns
the inclusion `reesAlgebra (I ^ d) ⊆ A[X]`; that is
`Stacks.ReesAlgebra.aeval_extendLinearMaps_eq`.

This file reads that identity off one coefficient of `A[X]` at a time. In degree `n` it says
that for `g ∈ (I ^ d) ^ n` the coefficients `Φ(g)_σ` of
`Stacks.ReesAlgebra.extendCoeff` recombine to `g`:

`∑_{|σ| = n} f^σ · Φ(g)_σ = g`.

That elementwise statement is the algebraic content of the last clause of [Stacks, Tag 0EH6] —
the composite of `Φ_F` with `T_j ↦ f_j` is the canonical inclusion
`⨁_n I ^ (n d) F ⟶ ⨁_n I ^ n F` — because the characterizing property of `Φ_F` prescribes its
value on a product `g · m` to be `Φ(g)_σ · m`, so the clause on such a product is this identity
multiplied by `m`.

## Main definitions

* `Stacks.ReesAlgebra.degreeMonomials` — the monomials of degree `n` in `r` variables, as a
  `Finset`, over which the recombination is summed.

## Main results

* `Stacks.ReesAlgebra.mem_degreeMonomials` — membership in that `Finset` is having degree `n`.
* `Stacks.ReesAlgebra.sum_pow_mul_extendCoeff` — the recombination identity.
* `Stacks.ReesAlgebra.extendCoeff_congr_degree` — the coefficient read at either of two equal
  degrees, the two spellings differing only in the membership proof.

## Implementation notes

The sum is indexed by `Finset.finsuppAntidiag Finset.univ n` rather than by the support of the
image, so that the index set does not depend on the element `g`; the terms outside the support
vanish, and the terms inside it all have degree `n` because the degreewise piece of the
extension is homogeneous (`Stacks.ReesAlgebra.degreeMap_isHomogeneous`).

## References

* [Stacks Project, Tag 0EIB](https://stacks.math.columbia.edu/tag/0EIB)
* [Stacks Project, Tag 0EH6](https://stacks.math.columbia.edu/tag/0EH6)
-/

@[expose] public noncomputable section

namespace Stacks.ReesAlgebra

universe u

variable {A : Type u} [CommRing A] {r : ℕ}

/-- The monomials of degree `n` in `r` variables. -/
public abbrev degreeMonomials (r n : ℕ) : Finset (Fin r →₀ ℕ) :=
  Finset.finsuppAntidiag (Finset.univ : Finset (Fin r)) n

/-- On a `Fintype` the degree of a finitely supported function is the sum over the whole type. -/
public lemma degree_eq_sum_univ (σ : Fin r →₀ ℕ) : Finsupp.degree σ = ∑ j, σ j :=
  Finsupp.degree_eq_sum σ

/-- A monomial lies in `Stacks.ReesAlgebra.degreeMonomials r n` exactly when its degree is
`n`. -/
public lemma mem_degreeMonomials {n : ℕ} {σ : Fin r →₀ ℕ} :
    σ ∈ degreeMonomials r n ↔ Finsupp.degree σ = n := by
  rw [Finset.mem_finsuppAntidiag, degree_eq_sum_univ]
  exact ⟨fun h => h.1, fun h => ⟨h, Finset.subset_univ _⟩⟩

/-- An element of `I ^ (n d)` as an element of `(I ^ d) ^ n`. -/
public lemma mem_pow_pow_of_mem_pow_mul (I : Ideal A) (d n : ℕ) {g : A}
    (hg : g ∈ I ^ (n * d)) : g ∈ ((I ^ d : Ideal A) ^ n) := by
  rw [← pow_mul, mul_comm]
  exact hg

/-- The coefficient of the extension at a monomial does not depend on which of two equal
degrees it is read at. The two sides are not syntactically equal because the membership proof
mentions the degree. -/
public lemma extendCoeff_congr_degree (I : Ideal A) (d : ℕ)
    (ψ : Fin r → (I ^ d : Ideal A) →ₗ[A] A) {k l : ℕ} (h : k = l) (σ : Fin r →₀ ℕ)
    (g : A) (hk : g ∈ ((I ^ d : Ideal A) ^ k)) (hl : g ∈ ((I ^ d : Ideal A) ^ l)) :
    extendCoeff I d k ψ σ ⟨g, hk⟩ = extendCoeff I d l ψ σ ⟨g, hl⟩ := by
  subst h
  rfl

/-- **The coefficients of the extension recombine at the generators.**

If the family `ψ` on `I ^ d` splits the inclusion against generators `f₁, …, f_r` of `I`, then
for `g ∈ (I ^ d) ^ n` the coefficients of the image of `g` under the graded algebra map of
[Stacks, Tag 0EIB] satisfy `∑_{|σ| = n} f^σ · Φ(g)_σ = g`.

Both sides are coefficients of polynomials in one variable: by
`Stacks.ReesAlgebra.aeval_extendLinearMaps_eq` the evaluation of `Φ(g)` at `T_j ↦ f_j`, read
inside `reesAlgebra I ⊆ A[X]`, is the monomial `g X ^ n`, and expanding the evaluation turns
each monomial `σ` of `Φ(g)` into `(f^σ · Φ(g)_σ) X ^ {|σ|}`. The degreewise piece of the
extension is homogeneous, so every monomial occurring has `|σ| = n` and comparing the
coefficients of `X ^ n` gives the identity. -/
public theorem sum_pow_mul_extendCoeff (I : Ideal A) (d n : ℕ) (f : Fin r → A)
    (hf : ∀ j, f j ∈ I) (ψ : Fin r → (I ^ d : Ideal A) →ₗ[A] A)
    (hψ : ∀ x : (I ^ d : Ideal A), (∑ j, f j * ψ j x) = (x : A))
    (g : A) (hg : g ∈ ((I ^ d : Ideal A) ^ n)) :
    (∑ σ ∈ degreeMonomials r n, (∏ j, f j ^ σ j) * extendCoeff I d n ψ σ ⟨g, hg⟩) = g := by
  classical
  set P : MvPolynomial (Fin r) A := degreeMap ((I : Ideal A) ^ d) ψ n ⟨g, hg⟩ with hPdef
  have hcoeff : ∀ σ : Fin r →₀ ℕ,
      extendCoeff I d n ψ σ ⟨g, hg⟩ = P.coeff σ := fun _ => rfl
  have hhom : P.IsHomogeneous n := degreeMap_isHomogeneous ((I : Ideal A) ^ d) ψ n ⟨g, hg⟩
  have hsupp : ∀ σ ∈ P.support, Finsupp.degree σ = n := by
    intro σ hσ
    by_contra hne
    exact (MvPolynomial.mem_support_iff.1 hσ) (hhom.coeff_eq_zero hne)
  -- the evaluation identity of [Stacks, Tag 0EIB], at the monomial `g X ^ n`
  have hmem : Polynomial.monomial n g ∈ reesAlgebra ((I : Ideal A) ^ d) :=
    reesAlgebra.monomial_mem.mpr hg
  have hext : extendLinearMaps ((I : Ideal A) ^ d) ψ ⟨Polynomial.monomial n g, hmem⟩ = P := by
    show reesLinearMap ((I : Ideal A) ^ d) ψ ⟨Polynomial.monomial n g, hmem⟩ = P
    exact reesLinearMap_monomial ((I : Ideal A) ^ d) ψ n g hg
  have hpol := aeval_extendLinearMaps_eq I d f hf ψ hψ ⟨Polynomial.monomial n g, hmem⟩
  rw [hext] at hpol
  -- evaluation into `A[X]`, with the generators read as `C (f j) * X`
  set v : Fin r → Polynomial A := fun j => Polynomial.C (f j) * Polynomial.X with hv
  have hE : (Subalgebra.val (reesAlgebra I)).comp
      (MvPolynomial.aeval fun j => degreeOne I ⟨f j, hf j⟩) = MvPolynomial.aeval v := by
    refine MvPolynomial.algHom_ext fun j => ?_
    have hgen : (Polynomial.monomial 1) (f j) = Polynomial.C (f j) * Polynomial.X := by
      rw [← Polynomial.C_mul_X_pow_eq_monomial, pow_one]
    simp [hv, degreeOne, hgen]
  have hkey : MvPolynomial.aeval v P = Polynomial.monomial n g := by
    rw [← hE]
    exact hpol
  -- expand the evaluation and collect each monomial into a monomial of `A[X]`
  have hprod : ∀ σ : Fin r →₀ ℕ,
      (∏ j, v j ^ σ j) = Polynomial.C (∏ j, f j ^ σ j) * Polynomial.X ^ Finsupp.degree σ := by
    intro σ
    rw [degree_eq_sum_univ, show (∏ j, v j ^ σ j) =
        ∏ j, (Polynomial.C (f j) ^ σ j * Polynomial.X ^ σ j) from
      Finset.prod_congr rfl fun j _ => mul_pow _ _ _,
      Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
    congr 1
    simp only [← map_pow, ← map_prod]
  have hterm : ∀ σ : Fin r →₀ ℕ,
      Polynomial.C (P.coeff σ) * (∏ j, v j ^ σ j) =
        Polynomial.monomial (Finsupp.degree σ)
          ((∏ j, f j ^ σ j) * P.coeff σ) := by
    intro σ
    rw [hprod σ, ← mul_assoc, ← map_mul,
      mul_comm (P.coeff σ) (∏ j, f j ^ σ j),
      Polynomial.C_mul_X_pow_eq_monomial]
  have hexp : MvPolynomial.aeval v P =
      Polynomial.monomial n (∑ σ ∈ P.support, (∏ j, f j ^ σ j) * P.coeff σ) := by
    rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq', map_sum]
    exact Finset.sum_congr rfl fun σ hσ => (hterm σ).trans (by rw [hsupp σ hσ])
  rw [hexp] at hkey
  have hval : (∑ σ ∈ P.support, (∏ j, f j ^ σ j) * P.coeff σ) = g := by
    have := congrArg (fun p : Polynomial A => p.coeff n) hkey
    simpa using this
  -- the sum over the degree-`n` monomials has the same value
  rw [show (∑ σ ∈ degreeMonomials r n, (∏ j, f j ^ σ j) * extendCoeff I d n ψ σ ⟨g, hg⟩) =
      ∑ σ ∈ degreeMonomials r n, (∏ j, f j ^ σ j) * P.coeff σ from
    Finset.sum_congr rfl fun σ _ => by rw [hcoeff σ]]
  rw [← hval]
  refine (Finset.sum_subset (fun σ hσ => mem_degreeMonomials.2 (hsupp σ hσ)) ?_).symm
  intro σ _ hσ
  rw [MvPolynomial.notMem_support_iff.1 hσ, mul_zero]

end Stacks.ReesAlgebra

end
