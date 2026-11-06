module

public import StacksFrontier.AlgebraicGeometry.ProjectiveCohomology.TwistSections
public import StacksFrontier.RingTheory.MvPolynomial.AwayMonomialBasis

/-!
# The `ℤ^{n+1}`-graded description of a Čech term of the standard cover

The proof of [Stacks, Tag 01XT] computes the cohomology of a twist `𝒪(d)` on projective
`n`-space by splitting the Čech complex of the `n + 1` standard charts according to the
`ℤ^{n+1}`-valued *Laurent weight* of a monomial. This file identifies the Čech term

`Γ(D₊(T_{i₀} ⋯ T_{i_p}), 𝒪(d)) = (R[T₀, …, Tₙ, 1/(T_{i₀} ⋯ T_{i_p})])_d`

with the free `R`-module on the Laurent monomials `Tᵉ` whose exponent vector `e : ℤ^{n+1}`
has total degree `∑ᵢ eᵢ = d` and is nonnegative on every coordinate that was not inverted.

`Stacks.ProjectiveCohomology.sectionsTwistProdXEquiv` identifies the Čech term with the
degree-`d` part `awayGrading` of the localization, the set of single fractions `a / fᵐ` with `a`
homogeneous, and `Stacks.PartialLaurent` gives the localization its Laurent monomial basis and
its `ℤ^{n+1}`-grading by weight. The total-degree-`d` part of the first is spanned by exactly the
weight vectors of total degree `d` of the second.

## Main definitions

* `Stacks.ProjectiveCohomology.TwistWeight`: the Laurent weights of total degree `d` available
  on an intersection of standard charts.
* `Stacks.ProjectiveCohomology.twistWeightMonomial`: the Laurent monomial of such a weight.
* `Stacks.ProjectiveCohomology.twistWeightSpan`: their span, i.e. the degree-`d` part of the
  Čech term.
* `Stacks.ProjectiveCohomology.awayGradingSubmodule`: the degree-`d` part of the localization
  as a submodule over the *coefficient ring*, rather than over `ℤ`.

## Main results

* `Stacks.ProjectiveCohomology.basis_eq_mk`: a Laurent monomial basis vector is a single
  fraction `Tᵘ / (T^δ)ᵐ`.
* `Stacks.ProjectiveCohomology.smul_mem_integerGrading`: the pieces of an `ℤ`-extended grading
  by `R`-submodules are `R`-submodules.
* `Stacks.ProjectiveCohomology.awayGradingSubmodule_eq_twistWeightSpan` and
  `Stacks.ProjectiveCohomology.coe_awayGrading_eq_twistWeightSpan`: **the degree-`d` part of
  `R[T₀, …, Tₙ, 1/(T_{i₀} ⋯ T_{i_p})]` is spanned by the Laurent monomials of total degree
  `d`.**
* `Stacks.ProjectiveCohomology.twistWeightBasis`,
  `Stacks.ProjectiveCohomology.free_twistWeightSpan`: **those monomials are an `R`-basis of
  it**, so the degree-`d` part is free.
* `Stacks.ProjectiveCohomology.sectionsTwistProdXEquivWeightSpan`: **the Čech term of
  [Stacks, Tag 01XT] is that free module**, as an isomorphism of additive groups.
* `Stacks.ProjectiveCohomology.finite_nonneg_weights` and
  `Stacks.ProjectiveCohomology.finite_neg_weights`: the all-nonnegative and the all-negative
  weights of a fixed total degree are **finite** in number.

## Implementation notes

No attribute for [Stacks, Tag 01XT] is attached: that tag is a statement about the cohomology
groups `H^q(ℙⁿ_R, 𝒪(d))`, and nothing here mentions cohomology.

`awayGrading` is a `Submodule ℤ`, the shape `DirectSum.Decomposition` over `ℤ` requires, and so
carries no basis over `R`. Its carrier is stable under `R` (`smul_mem_integerGrading`), and
`awayGradingSubmodule` is the same set as a `Submodule R`.

`TwistWeight` is a subtype of `Fin (n + 1) → ℤ`, matching `Stacks.PartialLaurent.basisProdX`,
while the computations run over `Fin (n + 1) →₀ ℤ`; `Stacks.PartialLaurent.prodXIndexEquiv`
mediates between the two.

## References

* [Stacks Project, Tag 01XT](https://stacks.math.columbia.edu/tag/01XT)
* [Stacks Project, Tag 01M6](https://stacks.math.columbia.edu/tag/01M6)
* [Stacks Project, Tag 0G6J](https://stacks.math.columbia.edu/tag/0G6J)
-/

@[expose] public noncomputable section

open AlgebraicGeometry AlgebraicGeometry.ProjectiveSpectrum.Proj CategoryTheory
open TopologicalSpace Opposite
open Stacks.PartialLaurent

universe u

namespace Stacks.ProjectiveCohomology

/-! ### A Laurent monomial basis vector as a single fraction -/

section Monomial

variable {ι : Type*} (R : Type u) [CommRing R] (δ : ι →₀ ℕ)

/-- `natToInt` commutes with scalar multiplication by a natural number. -/
theorem natToInt_nsmul (m : ℕ) : natToInt (m • δ) = m • natToInt (ι := ι) δ := by
  ext i; simp [natToInt_apply]

variable (M : Submonoid (MvPolynomial ι R))
  [IsLocalization.Away (MvPolynomial.monomial δ (1 : R))
    (LocalizedModule M (MvPolynomial ι R))]

/-- **A Laurent monomial basis vector is a single fraction.** If the Laurent exponent `ε`
becomes the honest exponent `μ` after adding `m` copies of the inverted monomial's exponent,
then the basis vector `Tᵋ` is the fraction `Tᵘ / (T^δ)ᵐ`. -/
theorem basis_eq_mk (ε : exponentMonoid (↑δ.support : Set ι)) (m : ℕ) (μ : ι →₀ ℕ)
    (w : M) (hw : (w : MvPolynomial ι R) = MvPolynomial.monomial δ (1 : R) ^ m)
    (h : (ε : ι →₀ ℤ) + m • natToInt δ = natToInt μ) :
    basis R δ (LocalizedModule M (MvPolynomial ι R)) ε =
      LocalizedModule.mk (MvPolynomial.monomial μ (1 : R)) w := by
  have hsum : ε + ofNat (↑δ.support : Set ι) (m • δ) = ofNat (↑δ.support : Set ι) μ :=
    Subtype.ext (by rw [AddSubmonoid.coe_add, coe_ofNat, coe_ofNat, natToInt_nsmul, h])
  have hmp : MvPolynomial.monomial (m • δ) (1 : R) = (w : MvPolynomial ι R) := by
    rw [hw, MvPolynomial.monomial_pow, one_pow]
  have key : basis R δ (LocalizedModule M (MvPolynomial ι R)) ε *
      algebraMap (MvPolynomial ι R) (LocalizedModule M (MvPolynomial ι R))
        (w : MvPolynomial ι R) =
      algebraMap (MvPolynomial ι R) (LocalizedModule M (MvPolynomial ι R))
        (MvPolynomial.monomial μ (1 : R)) := by
    rw [← hmp, ← basis_ofNat R δ (LocalizedModule M (MvPolynomial ι R)) (m • δ),
      ← basis_ofNat R δ (LocalizedModule M (MvPolynomial ι R)) μ, basis_mul_basis, hsum]
  have halg : ∀ a : MvPolynomial ι R,
      algebraMap (MvPolynomial ι R) (LocalizedModule M (MvPolynomial ι R)) a =
        LocalizedModule.mk a 1 := fun _ => rfl
  have hu : IsUnit (algebraMap (MvPolynomial ι R) (LocalizedModule M (MvPolynomial ι R))
      (w : MvPolynomial ι R)) :=
    IsLocalization.map_units (LocalizedModule M (MvPolynomial ι R)) w
  have hinj : Function.Injective
      fun t : LocalizedModule M (MvPolynomial ι R) => (w : MvPolynomial ι R) • t := by
    intro x y hxy
    simp only [Algebra.smul_def] at hxy
    exact hu.mul_left_cancel hxy
  refine hinj ?_
  simp only
  rw [LocalizedModule.smul'_mk, Algebra.smul_def, mul_comm, key, halg,
    show (w : MvPolynomial ι R) • MvPolynomial.monomial μ (1 : R) =
      w • MvPolynomial.monomial μ (1 : R) from by
        rw [Submonoid.smul_def, smul_eq_mul],
    LocalizedModule.mk_cancel]

end Monomial

/-! ### The integer-indexed grading of a graded algebra is stable under the base scalars -/

section Scalars

variable {S : Type u} [CommRing S] (R : Type*) [CommRing R] [Algebra R S]
  (𝒜 : ℕ → Submodule R S)

/-- **Each piece of an `ℤ`-extended grading by `R`-submodules is stable under `R`.** -/
theorem smul_mem_integerGrading (c : R) {j : ℤ} {a : S} (ha : a ∈ integerGrading 𝒜 j) :
    c • a ∈ integerGrading 𝒜 j := by
  by_cases hj : 0 ≤ j
  · lift j to ℕ using hj with jn
    rw [integerGrading_natCast] at ha ⊢
    exact Submodule.smul_mem (𝒜 jn) c ha
  · rw [integerGrading_neg _ _ (not_le.mp hj), Submodule.mem_bot] at ha ⊢
    rw [ha, smul_zero]

end Scalars

/-! ### The Laurent weights of a Čech term of the standard cover -/

section ProdX

variable {n r : ℕ} (R : Type u) [CommRing R] (s : Fin (r + 1) → Fin (n + 1))

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The localization `R[T₀, …, Tₙ, 1/(T_{i₀} ⋯ T_{i_p})]`. -/
abbrev chartRing : Type u :=
  LocalizedModule.Away (∏ j, MvPolynomial.X (s j) : MvPolynomial (Fin (n + 1)) R)
    (MvPolynomial (Fin (n + 1)) R)

/-- The Laurent exponent of the product of coordinates being inverted. -/
abbrev chartExponent : Fin (n + 1) →₀ ℕ := ∑ j, Finsupp.single (s j) (1 : ℕ)

/-- The product of the inverted coordinates is the monomial with exponent `chartExponent s`. -/
theorem prod_X_eq_monomial_chartExponent :
    (∏ j, MvPolynomial.X (s j) : MvPolynomial (Fin (n + 1)) R) =
      MvPolynomial.monomial (chartExponent s) (1 : R) :=
  prod_X_eq_monomial R Finset.univ s

/-- The exponent of a coordinate that is not inverted is zero. -/
theorem chartExponent_eq_zero {i : Fin (n + 1)} (hi : i ∉ Set.range s) :
    chartExponent s i = 0 := by
  have h : (↑(chartExponent s).support : Set (Fin (n + 1))) = Set.range s :=
    coe_support_sum_single s
  exact Finsupp.notMem_support_iff.mp (by rw [← Finset.mem_coe, h]; exact hi)

/-- The total degree of the product of the `r + 1` inverted coordinates is `r + 1`. -/
theorem sum_chartExponent : ∑ i, (chartExponent s i : ℤ) = (r : ℤ) + 1 := by
  simp only [chartExponent, Finsupp.finsetSum_apply, Nat.cast_sum]
  rw [Finset.sum_comm]
  simp [Finsupp.single_apply]

/-- **The Laurent weights of total degree `d` on an intersection of standard charts.**
An exponent vector `e : ℤ^{n+1}` of total degree `d` that is nonnegative on every coordinate
which was *not* inverted. -/
abbrev TwistWeight (s : Fin (r + 1) → Fin (n + 1)) (d : ℤ) : Type :=
  {e : Fin (n + 1) → ℤ // (∑ i, e i) = d ∧ ∀ i ∉ Set.range s, 0 ≤ e i}

/-- The Laurent monomial `Tᵉ` of a weight of total degree `d`. -/
def twistWeightMonomial (d : ℤ) (e : TwistWeight s d) : chartRing R s :=
  basisLocalizedModuleProdX R s ⟨e.1, e.2.2⟩

/-- **A Laurent monomial of a Čech term is a single fraction.** -/
theorem twistWeightMonomial_eq_mk (d : ℤ) (e : TwistWeight s d) (m : ℕ)
    (μ : Fin (n + 1) →₀ ℕ)
    (h : ∀ i, e.1 i + m * (chartExponent s i : ℤ) = (μ i : ℤ)) :
    twistWeightMonomial R s d e =
      LocalizedModule.mk (MvPolynomial.monomial μ (1 : R))
        (⟨(∏ j, MvPolynomial.X (s j) : MvPolynomial (Fin (n + 1)) R) ^ m,
          by exact ⟨m, rfl⟩⟩ : Submonoid.powers _) := by
  rw [twistWeightMonomial, basisLocalizedModuleProdX, basisProdX, Module.Basis.reindex_apply]
  refine basis_eq_mk R (chartExponent s) (Submonoid.powers _) _ m μ _ ?_ ?_
  · exact congrArg (fun x : MvPolynomial (Fin (n + 1)) R => x ^ m)
      (prod_X_eq_monomial_chartExponent R s)
  · ext i
    simp only [Finsupp.add_apply, Finsupp.smul_apply, natToInt_apply, nsmul_eq_mul]
    exact h i

/-- The Laurent monomials of total degree `d` of a Čech term are linearly independent. -/
theorem linearIndependent_twistWeightMonomial (d : ℤ) :
    LinearIndependent R (twistWeightMonomial R s d) :=
  (basisLocalizedModuleProdX R s).linearIndependent.comp
    (fun e : TwistWeight s d => ⟨e.1, e.2.2⟩) fun _ _ hxy => Subtype.ext (by simpa using hxy)

/-- **The degree-`d` part of the Čech term, spanned by its Laurent monomials.** -/
def twistWeightSpan (d : ℤ) : Submodule R (chartRing R s) :=
  Submodule.span R (Set.range (twistWeightMonomial R s d))

/-- The degree-`d` part `Stacks.ProjectiveCohomology.awayGrading` of the localization, as a
submodule over the coefficient ring. -/
def awayGradingSubmodule (d : ℤ) : Submodule R (chartRing R s) where
  carrier := awayGrading (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
    (prod_X_mem_degree R s) d
  zero_mem' := zero_mem (awayGrading _ (prod_X_mem_degree R s) d)
  add_mem' ha hb := add_mem ha hb
  smul_mem' := by
    rintro c z ⟨m, a, ha, rfl⟩
    refine ⟨m, c • a, smul_mem_integerGrading R _ c ha, ?_⟩
    rw [LocalizedModule.smul'_mk]

/-- Membership in `awayGradingSubmodule` is membership in `awayGrading`. -/
@[simp] theorem mem_awayGradingSubmodule {d : ℤ} {z : chartRing R s} :
    z ∈ awayGradingSubmodule R s d ↔
      z ∈ awayGrading (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
        (prod_X_mem_degree R s) d := Iff.rfl

/-- Splitting a weight `e` with `e + m • chartExponent = μ` into total degrees: `e` has total
degree `d` iff `μ` has total degree `m * (r + 1) + d`. -/
private theorem sum_eq_iff_sum_cast_eq (d : ℤ) (m : ℕ) (e : Fin (n + 1) → ℤ)
    (μ : Fin (n + 1) →₀ ℕ) (hw : ∀ i, e i + m * (chartExponent s i : ℤ) = (μ i : ℤ)) :
    (∑ i, e i) = d ↔ ((∑ i, μ i : ℕ) : ℤ) = ((m * (r + 1) : ℕ) : ℤ) + d := by
  have h : ((∑ i, μ i : ℕ) : ℤ) = ∑ i, e i + m * ((r : ℤ) + 1) := by
    rw [Nat.cast_sum, Finset.sum_congr rfl fun i _ => (hw i).symm, Finset.sum_add_distrib,
      ← Finset.mul_sum, sum_chartExponent]
  rw [h]
  push_cast
  constructor <;> intro h' <;> linarith

/-- **The ℤ^{n+1}-graded description of the Čech term of [Stacks, Tag 01XT].** -/
theorem awayGradingSubmodule_eq_twistWeightSpan (d : ℤ) :
    awayGradingSubmodule R s d = twistWeightSpan R s d := by
  classical
  refine le_antisymm ?_ ?_
  · rintro z ⟨m, a, ha, rfl⟩
    by_cases hj : 0 ≤ ((m * (r + 1) : ℕ) : ℤ) + d
    · have hahom : a.IsHomogeneous (((m * (r + 1) : ℕ) : ℤ) + d).toNat := by
        rwa [show ((m * (r + 1) : ℕ) : ℤ) + d =
          ((((m * (r + 1) : ℕ) : ℤ) + d).toNat : ℤ) from (Int.toNat_of_nonneg hj).symm,
          integerGrading_natCast] at ha
      have hdeg : ∀ μ ∈ a.support, ((∑ i, μ i : ℕ) : ℤ) = ((m * (r + 1) : ℕ) : ℤ) + d := by
        intro μ hμ
        have hw := hahom (MvPolynomial.mem_support_iff.mp hμ)
        have hw' : μ.degree = (((m * (r + 1) : ℕ) : ℤ) + d).toNat := by
          rwa [Finsupp.degree_eq_weight_one, ← Pi.one_def]
        rw [← Finsupp.degree_eq_sum, hw', Int.toNat_of_nonneg hj]
      rw [show a = ∑ μ ∈ a.support, MvPolynomial.monomial μ (a.coeff μ) from
        a.as_sum, mk_sum (S := Submonoid.powers _)]
      refine sum_mem fun μ hμ => ?_
      rw [show MvPolynomial.monomial μ (a.coeff μ) =
          a.coeff μ • MvPolynomial.monomial μ (1 : R) from by
        rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one], ← LocalizedModule.smul'_mk]
      refine Submodule.smul_mem _ _ ?_
      have hw : ∀ i, ((μ i : ℤ) - m * (chartExponent s i : ℤ)) +
          m * (chartExponent s i : ℤ) = (μ i : ℤ) := fun i => by ring
      have hmem : (∑ i, ((μ i : ℤ) - m * (chartExponent s i : ℤ))) = d ∧
          ∀ i ∉ Set.range s, (0 : ℤ) ≤ (μ i : ℤ) - m * (chartExponent s i : ℤ) := by
        refine ⟨?_, fun i hi => ?_⟩
        · exact (sum_eq_iff_sum_cast_eq s d m _ μ hw).2 (hdeg μ hμ)
        · rw [chartExponent_eq_zero s hi]
          simp
      rw [← twistWeightMonomial_eq_mk R s d
        ⟨(fun i => (μ i : ℤ) - m * (chartExponent s i : ℤ)), hmem⟩ m μ hw]
      exact Submodule.subset_span ⟨_, rfl⟩
    · rw [integerGrading_neg _ _ (not_le.mp hj), Submodule.mem_bot] at ha
      rw [ha, LocalizedModule.zero_mk]
      exact zero_mem _
  · rw [twistWeightSpan, Submodule.span_le]
    rintro x ⟨e, rfl⟩
    have hmem : (Finsupp.equivFunOnFinite.symm e.1 : Fin (n + 1) →₀ ℤ) ∈
        exponentMonoid (↑(chartExponent s).support : Set (Fin (n + 1))) := by
      intro i hi
      exact e.2.2 i (by rwa [← coe_support_sum_single s])
    obtain ⟨m, μ, hmμ⟩ := exists_nsmul_add_eq (chartExponent s) hmem
    have hw : ∀ i, e.1 i + m * (chartExponent s i : ℤ) = (μ i : ℤ) := fun i => by
      simpa [nsmul_eq_mul] using congrArg (fun t : Fin (n + 1) →₀ ℤ => t i) hmμ
    rw [twistWeightMonomial_eq_mk R s d e m μ hw]
    refine mk_mem_awayGrading _ (prod_X_mem_degree R s) ?_
    rw [← (sum_eq_iff_sum_cast_eq s d m e.1 μ hw).1 e.2.1, integerGrading_natCast]
    exact MvPolynomial.isHomogeneous_monomial 1 (Finsupp.degree_eq_sum μ)

/-- **The degree-`d` part of a Čech term is free on the Laurent monomials of total
degree `d`.** -/
def twistWeightBasis (d : ℤ) : Module.Basis (TwistWeight s d) R (twistWeightSpan R s d) :=
  Module.Basis.span (linearIndependent_twistWeightMonomial R s d)

/-- The degree-`d` part of a Čech term is a free `R`-module. -/
theorem free_twistWeightSpan (d : ℤ) : Module.Free R (twistWeightSpan R s d) :=
  Module.Free.of_basis (twistWeightBasis R s d)

/-- The degree-`d` part of the localization and the span of its Laurent monomials of total
degree `d` have the same underlying set. -/
theorem coe_awayGrading_eq_twistWeightSpan (d : ℤ) :
    (awayGrading (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
        (prod_X_mem_degree R s) d : Set (chartRing R s)) =
      (twistWeightSpan R s d : Set (chartRing R s)) :=
  congrArg (fun U : Submodule R (chartRing R s) => (U : Set (chartRing R s)))
    (awayGradingSubmodule_eq_twistWeightSpan R s d)

/-- The degree-`d` part of the localization and the span of its Laurent monomials of total
degree `d` are the same subgroup. -/
def awayGradingAddEquivTwistWeightSpan (d : ℤ) :
    awayGrading (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
        (prod_X_mem_degree R s) d ≃+ twistWeightSpan R s d where
  toFun z := ⟨z.1, by
    rw [← SetLike.mem_coe, ← coe_awayGrading_eq_twistWeightSpan R s d]; exact z.2⟩
  invFun z := ⟨z.1, by
    rw [← SetLike.mem_coe, coe_awayGrading_eq_twistWeightSpan R s d]; exact z.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- **The Čech term of [Stacks, Tag 01XT] is free over `R` on the Laurent monomials of total
degree `d`.** The sections of `𝒪(d)` over the intersection `D₊(T_{i₀} ⋯ T_{i_p})` of standard
coordinate charts of `Proj R[T₀, …, Tₙ]` form the free `R`-module on the exponent vectors
`e : ℤ^{n+1}` with `∑ᵢ eᵢ = d` that are nonnegative on every coordinate not among
`i₀, …, i_p`, as an additive group. -/
def sectionsTwistProdXEquivWeightSpan (d : ℤ) :
    ((twistingSheaf (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) d).val.obj
        (op (ProjectiveSpectrum.basicOpen _ (∏ j, MvPolynomial.X (s j))))) ≃+
      twistWeightSpan R s d :=
  (sectionsTwistProdXEquiv R s d).trans (awayGradingAddEquivTwistWeightSpan R s d)

end ProdX

/-! ### The two extreme weight ranges are finite -/

section Finiteness

variable {n : ℕ}

/-- The vectors in `ℤ^{n+1}` with every entry in `[lo, hi]` form a finite set. -/
theorem finite_setOf_forall_mem_Icc (lo hi : ℤ) :
    {e : Fin (n + 1) → ℤ | ∀ i, e i ∈ Set.Icc lo hi}.Finite :=
  Set.Finite.subset (Set.Finite.pi fun _ : Fin (n + 1) => Set.finite_Icc lo hi)
    fun _ he i _ => he i

/-- **The nonnegative weights of a fixed total degree form a finite set.** -/
theorem finite_nonneg_weights (d : ℤ) :
    {e : Fin (n + 1) → ℤ | (∑ i, e i) = d ∧ ∀ i, 0 ≤ e i}.Finite := by
  refine Set.Finite.subset (finite_setOf_forall_mem_Icc (n := n) 0 d) ?_
  rintro e ⟨hsum, hnn⟩ i
  refine ⟨hnn i, ?_⟩
  rw [← hsum]
  exact Finset.single_le_sum (f := e) (fun j _ => hnn j) (Finset.mem_univ i)

/-- **The strictly negative weights of a fixed total degree form a finite set.** -/
theorem finite_neg_weights (d : ℤ) :
    {e : Fin (n + 1) → ℤ | (∑ i, e i) = d ∧ ∀ i, e i < 0}.Finite := by
  refine Set.Finite.subset (finite_setOf_forall_mem_Icc (n := n) d (-1)) ?_
  rintro e ⟨hsum, hneg⟩ i
  have hi := hneg i
  refine ⟨?_, by omega⟩
  have hle : -(e i) ≤ ∑ j, -(e j) :=
    Finset.single_le_sum (f := fun j => -(e j)) (fun j _ => neg_nonneg.2 (hneg j).le)
      (Finset.mem_univ i)
  rw [Finset.sum_neg_distrib, hsum] at hle
  omega

/-- The nonnegative weights of a fixed total degree form a finite type. -/
instance finite_subtype_nonneg_weights (d : ℤ) :
    Finite {e : Fin (n + 1) → ℤ // (∑ i, e i) = d ∧ ∀ i, 0 ≤ e i} :=
  (finite_nonneg_weights (n := n) d).to_subtype

/-- The strictly negative weights of a fixed total degree form a finite type. -/
instance finite_subtype_neg_weights (d : ℤ) :
    Finite {e : Fin (n + 1) → ℤ // (∑ i, e i) = d ∧ ∀ i, e i < 0} :=
  (finite_neg_weights (n := n) d).to_subtype

end Finiteness

end Stacks.ProjectiveCohomology

end
