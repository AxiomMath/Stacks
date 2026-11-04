module

public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.SerreComputation
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.TopDuality

/-!
# The cohomology of a twist on projective space is a finite module

Let `R` be a commutative ring, let `n = m + 1 ≥ 1` and let `d` be an integer. Each cohomology
module `H^q(ℙⁿ_R, 𝒪(d))` is a finite `R`-module, and in fact finite free:

$$ H^q(\mathbf{P}^n_R, \mathcal{O}(d)) =
  \begin{cases} (R[T_0, \ldots, T_n])_d & q = 0 \\
    0 & q \neq 0, n \\
    \operatorname{Hom}_R((R[T_0, \ldots, T_n])_{-n-1-d}, R) & q = n \end{cases} $$

and every module on the right is free of finite rank on the monomials of the relevant degree.
No hypothesis on `R` is needed: finiteness here is a statement about a module of homogeneous
polynomials in finitely many variables, not about Noetherianness of the coefficients.

This is the finiteness half of [Stacks, Tag 01XT], and it is the input that the reduction of
[Stacks, Tag 02O6] to a supply of resolving modules takes as its `hTfin` slot — the cohomology
module it speaks of is `Stacks.ProjectiveSpace.Cohomology.twistCohomology`, which is by
definition the global-sections cohomology of the twist restricted along
`Stacks.ProjectiveSpace.Cohomology.coeffScalar`.

## Main results

* `Stacks.ProjectiveSpace.Cohomology.moduleFinite_twistChart_empty`: the degree-`d` part of
  `R[T₀, …, Tₙ]` is a finite `R`-module.
* `Stacks.ProjectiveSpace.Cohomology.moduleFinite_dual_twistChart_empty`: so is its `R`-dual.
* `Stacks.ProjectiveSpace.Cohomology.moduleFinite_twistCohomology_succ`: **`H^q(ℙⁿ_R, 𝒪(d))` is a
  finite `R`-module**, for every `q` and every `d`.
* `Stacks.ProjectiveSpace.Cohomology.moduleFree_twistChart_empty` and
  `moduleFree_dual_twistChart_empty`: the two nonvanishing cases are moreover free.

## Implementation notes

**No tag attribute is attached.** [Stacks, Tag 01XT] asserts the vanishing of the middle degrees
and the identification of the two extreme ones as well as this finiteness, and those are
`Stacks.ProjectiveSpace.Cohomology.serreTwistCohomology`; by the covering-set rule the
finiteness alone is not the tag.

**`n ≥ 1` is inherited from the computation, not imposed here.**
`Stacks.ProjectiveSpace.Cohomology.serreTwistCohomology` is stated at `n = m + 1` because at
`n = 0` its first and third rows would both apply and disagree, so the finiteness read off it
carries the same shape.

**The dual is free because the index set is finite.** `Module.Basis.dualBasis` needs the index
type of the basis to be finite, which for the polynomial chart is
`Stacks.ProjectiveSpace.Cohomology.instFiniteLaurentMonomialsEmpty`: a monomial of total degree
`d` with all exponents nonnegative has every exponent in `[0, d]`. For a chart with a variable
inverted the index set is infinite and no such statement holds, which is why only the
`∅` chart appears.

## References

* [Stacks Project, Tag 01XT](https://stacks.math.columbia.edu/tag/01XT)
* [Stacks Project, Tag 01XU](https://stacks.math.columbia.edu/tag/01XU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] HasDerivedCategory.standard

namespace Stacks.ProjectiveSpace.Cohomology

/-! ### The polynomial chart and its dual -/

/-- **The degree-`d` part of `R[T₀, …, Tₙ]` is free as an `R`-module**, on the monomials of total
degree `d`. -/
theorem moduleFree_twistChart_empty (R : Type u) [CommRing R] (n : ℕ) (d : ℤ) :
    Module.Free R (twistChart R n d (∅ : Set (Fin (n + 1)))) :=
  Module.Free.of_basis (twistChartBasis R n d (∅ : Set (Fin (n + 1))))

/-- **The degree-`d` part of `R[T₀, …, Tₙ]` is a finite `R`-module**: there are finitely many
monomials of total degree `d` with all exponents nonnegative, and they are a basis. -/
theorem moduleFinite_twistChart_empty (R : Type u) [CommRing R] (n : ℕ) (d : ℤ) :
    Module.Finite R (twistChart R n d (∅ : Set (Fin (n + 1)))) :=
  Module.Finite.of_basis (twistChartBasis R n d (∅ : Set (Fin (n + 1))))

/-- **The `R`-dual of the degree-`d` part of `R[T₀, …, Tₙ]` is free**, on the dual basis of the
monomial basis, which exists because the monomials of a fixed degree are finite in number. -/
theorem moduleFree_dual_twistChart_empty (R : Type u) [CommRing R] (n : ℕ) (d : ℤ) :
    Module.Free R (twistChart R n d (∅ : Set (Fin (n + 1))) →ₗ[R] R) := by
  classical
  exact Module.Free.of_basis (twistChartBasis R n d (∅ : Set (Fin (n + 1)))).dualBasis

/-- **The `R`-dual of the degree-`d` part of `R[T₀, …, Tₙ]` is a finite `R`-module.** -/
theorem moduleFinite_dual_twistChart_empty (R : Type u) [CommRing R] (n : ℕ) (d : ℤ) :
    Module.Finite R (twistChart R n d (∅ : Set (Fin (n + 1))) →ₗ[R] R) := by
  classical
  exact Module.Finite.of_basis (twistChartBasis R n d (∅ : Set (Fin (n + 1)))).dualBasis

/-! ### Finiteness of the cohomology of a twist -/

/-- **`H^q(ℙⁿ_R, 𝒪(d))` is a finite `R`-module**, for `n = m + 1 ≥ 1`, every degree `q` and every
twist `d`. By Serre's computation the module is the degree-`d` part of `R[T₀, …, Tₙ]` for `q = 0`,
the `R`-dual of the degree-`(-n-1-d)` part for `q = n`, and zero otherwise; each of the three is
finite over `R`, with no hypothesis on `R`. -/
theorem moduleFinite_twistCohomology_succ (R : Type u) [CommRing R] (m : ℕ) (d : ℤ) (q : ℕ) :
    Module.Finite R (twistCohomology R (m + 1) d q) := by
  rcases eq_or_ne q 0 with rfl | hq0
  · have := moduleFinite_twistChart_empty R (m + 1) d
    exact Module.Finite.equiv (serreTwistCohomology R m d).degreeZero.symm.toLinearEquiv
  rcases eq_or_ne q (m + 1) with rfl | hqn
  · have := moduleFinite_dual_twistChart_empty R (m + 1) (-d - (((m + 1 : ℕ) : ℤ) + 1))
    exact Module.Finite.equiv (serreTwistCohomology R m d).degreeTop.symm.toLinearEquiv
  obtain ⟨p, rfl⟩ : ∃ p, q = p + 1 := ⟨q - 1, by omega⟩
  exact moduleFinite_of_isZero ((serreTwistCohomology R m d).vanishing p hqn)

end Stacks.ProjectiveSpace.Cohomology

end
