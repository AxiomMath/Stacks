module

public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.LaurentCharts
public import StacksFrontier.RingTheory.GradedAlgebra.SymmetricAway.DegreeOneChart

/-!
# The monomial chart of `𝒪(d)` over a standard affine chart of projective space

Let `R` be a commutative ring, `n : ℕ` and `i : Fin (n + 1)`. The degree-`d` Laurent monomials
`T₀^{e₀} ⋯ Tₙ^{eₙ}` of `ℙⁿ_R` which are regular away from `Tᵢ` — those with `∑ eⱼ = d` and
`eⱼ ≥ 0` for every `j ≠ i` — are exactly the products `Tᵢ^{d - deg m} · m` for an arbitrary
monomial `m` in the variables other than `Tᵢ`: the exponent at `i` is forced by the degree, and
the remaining exponents are free natural numbers.

Consequently the monomial model
`Stacks.ProjectiveSpace.Cohomology.twistChart R n d {i}` of the degree-`d` part of
`R[T₀, …, Tₙ][1/Tᵢ]` is a free `R`-module on `{j // j ≠ i} →₀ ℕ`, that is, the polynomial algebra
on the remaining variables; and that algebra is `Stacks.SymmetricAway.chartRing R i`, the ring of
functions on the standard affine chart `D₊(Tᵢ)`, by
`Stacks.SymmetricAway.chartAlgEquiv`. Multiplication by `Tᵢ^d` is what turns the chart ring into
the sections of the twist, so this is the `R`-module side of the comparison of
`Γ(D₊(Tᵢ), 𝒪(d))` with the monomial charts.

## Main definitions

* `Stacks.ProjectiveSpace.TwistSections.singletonExponents` — the exponent vector of
  `Tᵢ^{d - deg m} · m`.
* `Stacks.ProjectiveSpace.TwistSections.laurentMonomialRestrict` — the monomial in the variables
  other than `Tᵢ` carried by a Laurent monomial regular away from `Tᵢ`.

## Main results

* `Stacks.ProjectiveSpace.TwistSections.laurentMonomialsSingletonEquiv` — the two constructions
  above are mutually inverse bijections.
* `Stacks.ProjectiveSpace.TwistSections.twistChartSingletonEquiv` — the one-variable monomial
  chart is the polynomial algebra on the remaining variables, as an `R`-module.
* `Stacks.ProjectiveSpace.TwistSections.twistChartSingletonChartRingEquiv` — the same, read in
  the standard affine chart ring of projective space.

The identification of sections of a twist over a standard open with a degree-zero localization
is part of Stacks 01MN (`AlgebraicGeometry.ProjectiveSpectrum.Proj.twistingSheaf`); this file
supplies the monomial description of the module appearing there.

## References

* [Stacks Project, Tag 01MN](https://stacks.math.columbia.edu/tag/01MN)
* [Stacks Project, Tag 01XT](https://stacks.math.columbia.edu/tag/01XT)
-/

@[expose] public noncomputable section

open Finsupp Stacks.ProjectiveSpace.Cohomology Stacks.SymmetricAway

universe u

namespace Stacks.ProjectiveSpace.TwistSections

attribute [local instance] MvPolynomial.gradedAlgebra

variable {R : Type u} [CommRing R] {n : ℕ}

/-- The exponent vector of the degree-`d` Laurent monomial `Tᵢ^{d - deg m} · m`, where `m` is a
monomial in the variables other than `Tᵢ`. -/
def singletonExponents (d : ℤ) (i : Fin (n + 1)) (m : {j : Fin (n + 1) // j ≠ i} →₀ ℕ) :
    Fin (n + 1) → ℤ :=
  fun j => if h : j = i then d - ∑ k : {j : Fin (n + 1) // j ≠ i}, (m k : ℤ)
    else (m ⟨j, h⟩ : ℤ)

/-- The exponent at `i` is the degree `d` less the degree of the monomial in the other
variables. -/
theorem singletonExponents_self (d : ℤ) (i : Fin (n + 1))
    (m : {j : Fin (n + 1) // j ≠ i} →₀ ℕ) :
    singletonExponents d i m i = d - ∑ k : {j : Fin (n + 1) // j ≠ i}, (m k : ℤ) :=
  dite_eq_left rfl

/-- Away from `i` the exponents are those of the given monomial. -/
theorem singletonExponents_of_ne (d : ℤ) {i j : Fin (n + 1)} (h : j ≠ i)
    (m : {j : Fin (n + 1) // j ≠ i} →₀ ℕ) :
    singletonExponents d i m j = (m ⟨j, h⟩ : ℤ) :=
  dite_eq_right h

/-- `singletonExponents_of_ne` read at a point of the subtype of indices other than `i`. -/
theorem singletonExponents_subtype (d : ℤ) {i : Fin (n + 1)}
    (m : {j : Fin (n + 1) // j ≠ i} →₀ ℕ) (k : {j : Fin (n + 1) // j ≠ i}) :
    singletonExponents d i m k.1 = (m k : ℤ) := by
  rw [singletonExponents_of_ne d k.2 m]

/-- The total degree of `Tᵢ^{d - deg m} · m` is `d`. -/
theorem sum_singletonExponents (d : ℤ) (i : Fin (n + 1))
    (m : {j : Fin (n + 1) // j ≠ i} →₀ ℕ) : ∑ j, singletonExponents d i m j = d := by
  rw [Fintype.sum_eq_add_sum_subtype_ne _ i, singletonExponents_self,
    Finset.sum_congr rfl fun k _ => singletonExponents_subtype d m k]
  ring

/-- `Tᵢ^{d - deg m} · m` is a degree-`d` Laurent monomial regular away from `Tᵢ`. -/
theorem singletonExponents_mem (d : ℤ) (i : Fin (n + 1))
    (m : {j : Fin (n + 1) // j ≠ i} →₀ ℕ) :
    singletonExponents d i m ∈ laurentMonomials n d ({i} : Set (Fin (n + 1))) := by
  refine ⟨sum_singletonExponents d i m, fun j hj => ?_⟩
  rw [singletonExponents_of_ne d (by simpa using hj) m]
  exact Int.natCast_nonneg _

/-- The monomial in the variables other than `Tᵢ` carried by a degree-`d` Laurent monomial that
is regular away from `Tᵢ`: its exponents outside `i`, which are nonnegative. -/
def laurentMonomialRestrict (d : ℤ) (i : Fin (n + 1))
    (e : laurentMonomials n d ({i} : Set (Fin (n + 1)))) : {j : Fin (n + 1) // j ≠ i} →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun j => (e.1 j.1).toNat

/-- The restricted monomial has the expected exponents. -/
theorem laurentMonomialRestrict_apply (d : ℤ) (i : Fin (n + 1))
    (e : laurentMonomials n d ({i} : Set (Fin (n + 1)))) (j : {j : Fin (n + 1) // j ≠ i}) :
    laurentMonomialRestrict d i e j = (e.1 j.1).toNat := by
  rw [laurentMonomialRestrict, Finsupp.coe_equivFunOnFinite_symm]

/-- **The degree-`d` Laurent monomials regular away from `Tᵢ` are the monomials in the remaining
variables.** The exponent at `i` is determined by the total degree, and the other exponents are
arbitrary natural numbers. -/
def laurentMonomialsSingletonEquiv (n : ℕ) (d : ℤ) (i : Fin (n + 1)) :
    laurentMonomials n d ({i} : Set (Fin (n + 1))) ≃ ({j : Fin (n + 1) // j ≠ i} →₀ ℕ) where
  toFun := laurentMonomialRestrict d i
  invFun m := ⟨singletonExponents d i m, singletonExponents_mem d i m⟩
  left_inv e := by
    have hnn : ∀ k : Fin (n + 1), k ≠ i → 0 ≤ e.1 k := fun k hk =>
      (mem_laurentMonomials.1 e.2).2 k (by simpa using hk)
    have hres : ∀ k : {j : Fin (n + 1) // j ≠ i},
        ((laurentMonomialRestrict d i e k : ℕ) : ℤ) = e.1 k.1 := fun k => by
      rw [laurentMonomialRestrict_apply]
      exact Int.toNat_of_nonneg (hnn k.1 k.2)
    refine Subtype.ext (funext fun j => ?_)
    change singletonExponents d i (laurentMonomialRestrict d i e) j = e.1 j
    by_cases h : j = i
    · subst h
      rw [singletonExponents_self]
      have hsum := (mem_laurentMonomials.1 e.2).1
      rw [Fintype.sum_eq_add_sum_subtype_ne _ j] at hsum
      rw [Finset.sum_congr rfl fun k _ => hres k]
      omega
    · rw [singletonExponents_of_ne d h, hres ⟨j, h⟩]
  right_inv m := by
    refine Finsupp.ext fun j => ?_
    change laurentMonomialRestrict d i ⟨singletonExponents d i m, _⟩ j = m j
    rw [laurentMonomialRestrict_apply]
    change (singletonExponents d i m j.1).toNat = m j
    rw [singletonExponents_subtype]
    simp

/-- **The one-variable monomial chart of `𝒪(d)` is an affine space.** The degree-`d` part of
`R[T₀, …, Tₙ][1/Tᵢ]` is free as an `R`-module on the monomials in the variables other than `Tᵢ`,
the basis element attached to `m` being the Laurent monomial `Tᵢ^{d - deg m} · m`. -/
def twistChartSingletonEquiv (R : Type u) [CommRing R] (n : ℕ) (d : ℤ) (i : Fin (n + 1)) :
    twistChart R n d ({i} : Set (Fin (n + 1))) ≃ₗ[R]
      MvPolynomial {j : Fin (n + 1) // j ≠ i} R :=
  (Finsupp.supportedEquivFinsupp _).trans
    ((Finsupp.domLCongr (laurentMonomialsSingletonEquiv n d i)).trans
      (AddMonoidAlgebra.coeffLinearEquiv R).symm)

/-- **The one-variable monomial chart of `𝒪(d)` is free of rank one over the chart ring.** The
degree-`d` part of `R[T₀, …, Tₙ][1/Tᵢ]` is `R`-linearly isomorphic to the ring
`Stacks.SymmetricAway.chartRing R i` of functions on the standard affine chart `D₊(Tᵢ)`; the
isomorphism is division by `Tᵢ^d`. -/
def twistChartSingletonChartRingEquiv (R : Type u) [CommRing R] (n : ℕ) (d : ℤ)
    (i : Fin (n + 1)) :
    twistChart R n d ({i} : Set (Fin (n + 1))) ≃ₗ[R] chartRing R i :=
  (twistChartSingletonEquiv R n d i).trans (chartAlgEquiv i).toLinearEquiv

end Stacks.ProjectiveSpace.TwistSections

end
