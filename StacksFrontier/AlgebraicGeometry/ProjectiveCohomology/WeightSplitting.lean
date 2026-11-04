module

public import StacksFrontier.AlgebraicGeometry.ProjectiveCohomology.TwistWeights
public import Mathlib.LinearAlgebra.DirectSum.Basis

/-!
# The weight splitting of a Čech term of a twist on projective space

Let `R` be a commutative ring and let `s` enumerate `r + 1` of the homogeneous coordinates of
`R[T₀, …, Tₙ]`. The Čech term

`Γ(D₊(T_{i₀} ⋯ T_{i_p}), 𝒪(d)) = (R[T₀, …, Tₙ, 1/(T_{i₀} ⋯ T_{i_p})])_d`

of the twist `𝒪(d)` on `Proj R[T₀, …, Tₙ]` for the cover by the `n + 1` standard coordinate charts
is the free `R`-module on the Laurent monomials of total degree `d` admissible there. This file
splits these terms, and the maps between them, along the `ℤ^{n+1}`-valued Laurent weight of a
monomial, as in the proof of [Stacks, Tag 01XT].

**The terms split.** `Stacks.PartialLaurent.weight` grades the whole localization
`R[T₀, …, Tₙ, 1/(T_{i₀} ⋯ T_{i_p})]` by Laurent weight. The degree-`d` Čech term is the sum of the
weight pieces whose weight has total degree `d` (`iSup_chartWeight_eq_twistWeightSpan`), those
pieces are independent (`iSupIndep_chartWeight`), and each one is a free `R`-module of rank at most
one — rank one exactly at an admissible weight (`free_chartWeight`, `finite_chartWeight`,
`chartWeight_eq_bot_iff`). Hence a weight summand of a Čech degree is free of finite rank over `R`
(`free_directSum_chartWeight`, `finite_directSum_chartWeight`).

**The maps split.** The map between two Čech terms is the localization map
`R[T₀, …, Tₙ, 1/(T_{i₀} ⋯ T_{i_p})] → R[T₀, …, Tₙ, 1/(T_{j₀} ⋯ T_{j_q})]`, defined whenever the
second chart intersection is contained in the first, i.e. whenever `Set.range s ⊆ Set.range t`.
It is `chartTransition`, and it carries the Laurent monomial of a weight to the Laurent monomial
of the same weight (`chartTransition_basis`, `chartTransition_twistWeightMonomial`), hence each
weight piece into the weight piece of the same weight (`chartTransition_mem_chartWeight`).

## Main definitions

* `Stacks.ProjectiveCohomology.chartWeight`: the weight-`e` piece of a Čech term.
* `Stacks.ProjectiveCohomology.DegreeWeight`: the Laurent weights of total degree `d`.
* `Stacks.ProjectiveCohomology.chartTransition`: the localization map between two Čech terms.
* `Stacks.ProjectiveCohomology.basisSpanSingleton`: the span of a single basis vector, with its
  one-element basis.

## Main results

* `Stacks.ProjectiveCohomology.basis_mul_pow` and
  `Stacks.ProjectiveCohomology.eq_basis_of_mul_pow_eq`: a Laurent monomial is the unique element
  which a power of a clearing monomial carries to the corresponding honest monomial.
* `Stacks.ProjectiveCohomology.iSup_chartWeight_eq_twistWeightSpan`: **the degree-`d` part of a
  Čech term is the sum of the weight pieces of total degree `d`.**
* `Stacks.ProjectiveCohomology.iSupIndep_chartWeight`: **those pieces are independent.**
* `Stacks.ProjectiveCohomology.free_chartWeight`,
  `Stacks.ProjectiveCohomology.finite_chartWeight`: **each weight piece is a finitely generated
  free `R`-module**, of rank one or zero by
  `Stacks.ProjectiveCohomology.chartWeight_eq_bot_iff`.
* `Stacks.ProjectiveCohomology.twistWeightEquivDegreeWeight`: the Laurent monomial basis of the
  degree-`d` Čech term at `s` is indexed by exactly the global degree-`d` weights admissible
  at `s`.
* `Stacks.ProjectiveCohomology.iSup_twistWeightSpan_eq_top`: the degree parts exhaust the
  localization.
* `Stacks.ProjectiveCohomology.chartTransition_twistWeightMonomial` and
  `Stacks.ProjectiveCohomology.chartTransition_mem_chartWeight`: **the map between Čech terms is
  weight-preserving.**
* `Stacks.ProjectiveCohomology.chartTransition_mem_twistWeightSpan`: it preserves the total
  degree as well.
* `Stacks.ProjectiveCohomology.sectionsTwistProdXEquivISupChartWeight`: **the Čech term of
  [Stacks, Tag 01XT] is the sum of its weight pieces of total degree `d`.**
* `Stacks.ProjectiveCohomology.free_directSum_chartWeight`,
  `Stacks.ProjectiveCohomology.finite_directSum_chartWeight`: **a weight summand of a Čech
  degree is free of finite rank over `R`.**

## Implementation notes

No attribute for [Stacks, Tag 01XT] is attached: that tag is a statement about the groups
`H^q(ℙⁿ_R, 𝒪(d))`, and nothing here mentions cohomology.

`chartTransition` is the localization map between the two localizations of `R[T₀, …, Tₙ]` that
`Stacks.ProjectiveCohomology.sectionsTwistProdXEquiv` identifies the two Čech terms with; every
statement here is about these localizations and their Laurent weights.

## References

* [Stacks Project, Tag 01XT](https://stacks.math.columbia.edu/tag/01XT)
* [Stacks Project, Tag 01M6](https://stacks.math.columbia.edu/tag/01M6)
-/

@[expose] public noncomputable section

open AlgebraicGeometry AlgebraicGeometry.ProjectiveSpectrum.Proj CategoryTheory
open TopologicalSpace Opposite
open Stacks.PartialLaurent

universe u

namespace Stacks.ProjectiveCohomology

/-! ### The span of a single basis vector -/

section SpanBasis

variable {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- **The span of a single basis vector, with its one-element basis.** -/
def basisSpanSingleton (b : Module.Basis ι R M) (i : ι) :
    Module.Basis Unit R (Submodule.span R {b i}) :=
  (Module.Basis.span (v := fun _ : Unit => b i)
      (b.linearIndependent.comp _ fun _ _ _ => Subsingleton.elim _ _)).map
    (LinearEquiv.ofEq _ _ (by rw [Set.range_const]))

/-- The span of a single basis vector is a free module. -/
theorem free_span_singleton_basis (b : Module.Basis ι R M) (i : ι) :
    Module.Free R (Submodule.span R {b i}) :=
  Module.Free.of_basis (basisSpanSingleton b i)

/-- The span of a single basis vector is finitely generated. -/
theorem finite_span_singleton_basis (b : Module.Basis ι R M) (i : ι) :
    Module.Finite R (Submodule.span R {b i}) :=
  Module.Finite.of_basis (basisSpanSingleton b i)

end SpanBasis

/-! ### Clearing the denominator of a Laurent monomial -/

section Clear

variable {ι : Type*} (R : Type u) [CommRing R] (δ : ι →₀ ℕ)
variable (T : Type*) [CommRing T] [Algebra (MvPolynomial ι R) T]
  [IsLocalization.Away (MvPolynomial.monomial δ (1 : R)) T]
  [Module R T] [IsScalarTower R (MvPolynomial ι R) T]

/-- **Multiplying a Laurent monomial by a power of a monomial that clears its denominator gives
the honest monomial.** The clearing monomial `T^ν` is arbitrary: it need not be the monomial
that was inverted. -/
theorem basis_mul_pow (ε : exponentMonoid (↑δ.support : Set ι)) (m : ℕ) (ν μ : ι →₀ ℕ)
    (h : (ε : ι →₀ ℤ) + m • natToInt ν = natToInt μ) :
    basis R δ T ε * algebraMap (MvPolynomial ι R) T (MvPolynomial.monomial ν (1 : R)) ^ m =
      algebraMap (MvPolynomial ι R) T (MvPolynomial.monomial μ (1 : R)) := by
  have hpow : algebraMap (MvPolynomial ι R) T (MvPolynomial.monomial ν (1 : R)) ^ m =
      basis R δ T (ofNat (↑δ.support : Set ι) (m • ν)) := by
    rw [basis_ofNat, ← map_pow, MvPolynomial.monomial_pow, one_pow]
  have hsum : ε + ofNat (↑δ.support : Set ι) (m • ν) = ofNat (↑δ.support : Set ι) μ :=
    Subtype.ext (by rw [AddSubmonoid.coe_add, coe_ofNat, coe_ofNat, natToInt_nsmul, h])
  rw [hpow, basis_mul_basis, hsum, basis_ofNat]

/-- **A Laurent monomial is the unique element with a given cleared numerator.** -/
theorem eq_basis_of_mul_pow_eq (ε : exponentMonoid (↑δ.support : Set ι)) (m : ℕ) (ν μ : ι →₀ ℕ)
    (h : (ε : ι →₀ ℤ) + m • natToInt ν = natToInt μ)
    (hu : IsUnit (algebraMap (MvPolynomial ι R) T (MvPolynomial.monomial ν (1 : R))))
    (z : T)
    (hz : z * algebraMap (MvPolynomial ι R) T (MvPolynomial.monomial ν (1 : R)) ^ m =
      algebraMap (MvPolynomial ι R) T (MvPolynomial.monomial μ (1 : R))) :
    z = basis R δ T ε := by
  refine (hu.pow m).mul_left_cancel ?_
  rw [mul_comm _ z, hz, mul_comm _ (basis R δ T ε), basis_mul_pow R δ T ε m ν μ h]

end Clear

/-! ### The weight pieces of a Čech term -/

section Weight

variable {n r : ℕ} (R : Type u) [CommRing R] (s : Fin (r + 1) → Fin (n + 1))

attribute [local instance] MvPolynomial.gradedAlgebra

/-- **The weight-`e` piece of the Čech term at `s`**, i.e. the `R`-line spanned by the Laurent
monomial `Tᵉ` inside `R[T₀, …, Tₙ, 1/(T_{i₀} ⋯ T_{i_p})]`, which is zero when `e` is negative on
a coordinate that was not inverted. -/
abbrev chartWeight (e : Fin (n + 1) →₀ ℤ) : Submodule R (chartRing R s) :=
  Stacks.PartialLaurent.weight R (chartExponent s) (chartRing R s) e

/-- **The Laurent weights of total degree `d`**, as exponent vectors, with no admissibility
condition. -/
abbrev DegreeWeight (n : ℕ) (d : ℤ) : Type := {e : Fin (n + 1) →₀ ℤ // ∑ i, e i = d}

/-- A weight is available on the chart intersection `s` exactly when it is nonnegative on every
coordinate that was not inverted. -/
theorem mem_exponentMonoid_chartExponent_iff {e : Fin (n + 1) →₀ ℤ} :
    e ∈ exponentMonoid (↑(chartExponent s).support : Set (Fin (n + 1))) ↔
      ∀ i ∉ Set.range s, 0 ≤ e i := by
  rw [mem_exponentMonoid, coe_support_sum_single]

/-- A Laurent monomial of a Čech term is a basis vector of the Laurent monomial basis. -/
theorem twistWeightMonomial_eq_basis (d : ℤ) (e : TwistWeight s d) :
    twistWeightMonomial R s d e =
      basis R (chartExponent s) (chartRing R s) ((prodXIndexEquiv s).symm ⟨e.1, e.2.2⟩) := by
  rw [twistWeightMonomial, basisLocalizedModuleProdX, basisProdX, Module.Basis.reindex_apply]

/-- A basis vector at an admissible weight of total degree `d` is a Laurent monomial of the
degree-`d` Čech term. -/
theorem basis_eq_twistWeightMonomial (d : ℤ) (e : Fin (n + 1) →₀ ℤ) (hd : ∑ i, e i = d)
    (he : e ∈ exponentMonoid (↑(chartExponent s).support : Set (Fin (n + 1)))) :
    basis R (chartExponent s) (chartRing R s) ⟨e, he⟩ =
      twistWeightMonomial R s d
        ⟨fun i => e i, hd, (mem_exponentMonoid_chartExponent_iff s).1 he⟩ := by
  have hidx : ((prodXIndexEquiv s).symm
        ⟨fun i => e i, (mem_exponentMonoid_chartExponent_iff s).1 he⟩ :
      exponentMonoid (↑(chartExponent s).support : Set (Fin (n + 1)))) = ⟨e, he⟩ :=
    Subtype.ext (by ext i; rfl)
  rw [twistWeightMonomial_eq_basis, hidx]

/-- A weight piece at an admissible weight is the span of the Laurent monomial of that weight. -/
private theorem chartWeight_eq_span (e : Fin (n + 1) →₀ ℤ)
    (he : e ∈ exponentMonoid (↑(chartExponent s).support : Set (Fin (n + 1)))) :
    chartWeight R s e = Submodule.span R {basis R (chartExponent s) (chartRing R s) ⟨e, he⟩} :=
  weight_coe R (chartExponent s) (chartRing R s) ⟨e, he⟩

/-- **A weight piece of total degree `d` sits inside the degree-`d` part of the Čech term.** -/
theorem chartWeight_le_twistWeightSpan (d : ℤ) (e : Fin (n + 1) →₀ ℤ) (hd : ∑ i, e i = d) :
    chartWeight R s e ≤ twistWeightSpan R s d := by
  by_cases he : e ∈ exponentMonoid (↑(chartExponent s).support : Set (Fin (n + 1)))
  · rw [chartWeight_eq_span R s e he, basis_eq_twistWeightMonomial R s d e hd he,
      Submodule.span_le,
      Set.singleton_subset_iff]
    exact Submodule.subset_span ⟨_, rfl⟩
  · exact (weight_eq_bot R (chartExponent s) (chartRing R s) he).trans_le bot_le

/-- **The degree-`d` part of a Čech term is the sum of its weight pieces of total degree
`d`.** -/
theorem iSup_chartWeight_eq_twistWeightSpan (d : ℤ) :
    (⨆ e : DegreeWeight n d, chartWeight R s e.1) = twistWeightSpan R s d := by
  refine le_antisymm (iSup_le fun e => chartWeight_le_twistWeightSpan R s d e.1 e.2) ?_
  rw [twistWeightSpan, Submodule.span_le]
  rintro x ⟨e, rfl⟩
  have hmem : (Finsupp.equivFunOnFinite.symm e.1 : Fin (n + 1) →₀ ℤ) ∈
      exponentMonoid (↑(chartExponent s).support : Set (Fin (n + 1))) :=
    (mem_exponentMonoid_chartExponent_iff s).2 e.2.2
  have hd : ∑ i, (Finsupp.equivFunOnFinite.symm e.1 : Fin (n + 1) →₀ ℤ) i = d := e.2.1
  refine Submodule.mem_iSup_of_mem ⟨Finsupp.equivFunOnFinite.symm e.1, hd⟩ ?_
  have hidx : ((prodXIndexEquiv s).symm ⟨e.1, e.2.2⟩ :
      exponentMonoid (↑(chartExponent s).support : Set (Fin (n + 1)))) =
      ⟨Finsupp.equivFunOnFinite.symm e.1, hmem⟩ := Subtype.ext rfl
  show twistWeightMonomial R s d e ∈ Stacks.PartialLaurent.weight R (chartExponent s)
    (chartRing R s)
    ((⟨Finsupp.equivFunOnFinite.symm e.1, hmem⟩ :
      exponentMonoid (↑(chartExponent s).support : Set (Fin (n + 1)))) : Fin (n + 1) →₀ ℤ)
  rw [weight_coe, twistWeightMonomial_eq_basis, hidx]
  exact Submodule.mem_span_singleton_self _

/-- **The weight pieces of total degree `d` of a Čech term are independent.** -/
theorem iSupIndep_chartWeight (d : ℤ) :
    iSupIndep (fun e : DegreeWeight n d => chartWeight R s e.1) :=
  (iSupIndep_weight R (chartExponent s) (chartRing R s)).comp Subtype.val_injective

/-- **Each weight piece of a Čech term is free over the coefficient ring.** -/
theorem free_chartWeight (e : Fin (n + 1) →₀ ℤ) : Module.Free R (chartWeight R s e) := by
  by_cases he : e ∈ exponentMonoid (↑(chartExponent s).support : Set (Fin (n + 1)))
  · rw [chartWeight_eq_span R s e he]
    exact free_span_singleton_basis _ _
  · rw [show chartWeight R s e = ⊥ from weight_eq_bot R (chartExponent s) (chartRing R s) he]
    infer_instance

/-- **Each weight piece of a Čech term is finitely generated over the coefficient ring.** -/
theorem finite_chartWeight (e : Fin (n + 1) →₀ ℤ) : Module.Finite R (chartWeight R s e) := by
  by_cases he : e ∈ exponentMonoid (↑(chartExponent s).support : Set (Fin (n + 1)))
  · rw [chartWeight_eq_span R s e he]
    exact finite_span_singleton_basis _ _
  · rw [show chartWeight R s e = ⊥ from weight_eq_bot R (chartExponent s) (chartRing R s) he]
    infer_instance

/-- **A weight piece of a Čech term over a nontrivial ring vanishes exactly at an inadmissible
weight**, i.e. at a weight that is negative on a coordinate which was not inverted. -/
theorem chartWeight_eq_bot_iff [Nontrivial R] (e : Fin (n + 1) →₀ ℤ) :
    chartWeight R s e = ⊥ ↔ ∃ i ∉ Set.range s, e i < 0 := by
  refine ⟨fun hbot => ?_, fun ⟨i, hi, hneg⟩ => ?_⟩
  · by_contra hc
    push Not at hc
    have he : e ∈ exponentMonoid (↑(chartExponent s).support : Set (Fin (n + 1))) :=
      (mem_exponentMonoid_chartExponent_iff s).2 hc
    rw [chartWeight_eq_span R s e he] at hbot
    exact (basis R (chartExponent s) (chartRing R s)).ne_zero ⟨e, he⟩
      (by simpa using Submodule.span_eq_bot.1 hbot _ rfl)
  · exact weight_eq_bot R (chartExponent s) (chartRing R s) fun hc =>
      absurd ((mem_exponentMonoid_chartExponent_iff s).1 hc i hi) (not_le.2 hneg)

/-- **The Laurent monomial basis of the degree-`d` Čech term at `s` is indexed by exactly the
global degree-`d` weights which are admissible at `s`.** -/
def twistWeightEquivDegreeWeight (d : ℤ) :
    TwistWeight s d ≃ {e : DegreeWeight n d // ∀ i ∉ Set.range s, 0 ≤ e.1 i} where
  toFun e := ⟨⟨Finsupp.equivFunOnFinite.symm e.1, e.2.1⟩, e.2.2⟩
  invFun e := ⟨fun i => e.1.1 i, e.1.2, e.2⟩
  left_inv _ := rfl
  right_inv e := Subtype.ext (Subtype.ext (by ext i; rfl))

/-- **The degree parts of a Čech term exhaust it.** -/
theorem iSup_twistWeightSpan_eq_top : (⨆ d : ℤ, twistWeightSpan R s d) = ⊤ := by
  rw [eq_top_iff, ← iSup_weight_eq_top R (chartExponent s) (chartRing R s)]
  exact iSup_le fun e => le_iSup_of_le (∑ i, e i) (chartWeight_le_twistWeightSpan R s _ e rfl)

/-- **The Čech term of [Stacks, Tag 01XT] is the sum of its Laurent weight pieces of total
degree `d`.** The sections of `𝒪(d)` over the intersection `D₊(T_{i₀} ⋯ T_{i_p})` of standard
coordinate charts of `Proj R[T₀, …, Tₙ]` are, as an additive group, the sum of the weight pieces
of the localization whose weight has total degree `d`. -/
def sectionsTwistProdXEquivISupChartWeight (d : ℤ) :
    ((twistingSheaf (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) d).val.obj
        (op (ProjectiveSpectrum.basicOpen _ (∏ j, MvPolynomial.X (s j))))) ≃+
      (⨆ e : DegreeWeight n d, chartWeight R s e.1 : Submodule R (chartRing R s)) :=
  (sectionsTwistProdXEquivWeightSpan R s d).trans
    (LinearEquiv.ofEq _ _ (iSup_chartWeight_eq_twistWeightSpan R s d).symm).toAddEquiv

/-! ### A weight summand of a Čech degree is free of finite rank -/

/-- **A weight summand of a Čech degree is a free `R`-module**: the direct sum, over the index
set `Fin (p + 1) → Fin (n + 1)` of a Čech degree of the covering by the `n + 1` standard charts, of
the weight pieces of weight `e`. -/
theorem free_directSum_chartWeight (e : Fin (n + 1) →₀ ℤ) (p : ℕ) :
    Module.Free R (DirectSum (Fin (p + 1) → Fin (n + 1)) fun u => chartWeight R u e) :=
  have : ∀ u : Fin (p + 1) → Fin (n + 1), Module.Free R (chartWeight R u e) :=
    fun u => free_chartWeight R u e
  inferInstance

/-- **A weight summand of a Čech degree is a finitely generated `R`-module.** -/
theorem finite_directSum_chartWeight (e : Fin (n + 1) →₀ ℤ) (p : ℕ) :
    Module.Finite R (DirectSum (Fin (p + 1) → Fin (n + 1)) fun u => chartWeight R u e) :=
  have : ∀ u : Fin (p + 1) → Fin (n + 1), Module.Finite R (chartWeight R u e) :=
    fun u => finite_chartWeight R u e
  Module.Finite.equiv
    (DirectSum.linearEquivFunOnFintype R (Fin (p + 1) → Fin (n + 1))
      (fun u => (chartWeight R u e : Type u))).symm

end Weight

/-! ### The map between two Čech terms, and its compatibility with the weights -/

section Transition

variable {n q r : ℕ} (R : Type u) [CommRing R]
  (s : Fin (r + 1) → Fin (n + 1)) (t : Fin (q + 1) → Fin (n + 1))

/-- A product of coordinates divides a power of a product of coordinates containing them all. -/
theorem prod_X_dvd_prod_X_pow (hst : Set.range s ⊆ Set.range t) :
    (∏ j, MvPolynomial.X (s j) : MvPolynomial (Fin (n + 1)) R) ∣
      (∏ j, MvPolynomial.X (t j) : MvPolynomial (Fin (n + 1)) R) ^ (r + 1) := by
  rw [show ((∏ j, MvPolynomial.X (t j) : MvPolynomial (Fin (n + 1)) R) ^ (r + 1)) =
      ∏ _j : Fin (r + 1), (∏ k, MvPolynomial.X (t k) : MvPolynomial (Fin (n + 1)) R) from by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]]
  refine Finset.prod_dvd_prod_of_dvd _ _ fun j _ => ?_
  obtain ⟨k, hk⟩ := hst (Set.mem_range_self j)
  rw [← hk]
  exact Finset.dvd_prod_of_mem _ (Finset.mem_univ k)

/-- The coordinates inverted on the larger chart intersection are units there. -/
theorem isUnit_algebraMap_prod_X (hst : Set.range s ⊆ Set.range t) :
    IsUnit (algebraMap (MvPolynomial (Fin (n + 1)) R) (chartRing R t)
      (∏ j, MvPolynomial.X (s j))) :=
  (IsLocalization.Away.algebraMap_isUnit_iff
    (∏ j, MvPolynomial.X (t j) : MvPolynomial (Fin (n + 1)) R)).2
      ⟨r + 1, prod_X_dvd_prod_X_pow R s t hst⟩

/-- The clearing monomial of the smaller chart intersection is a unit on the larger one. -/
theorem isUnit_algebraMap_monomial_chartExponent (hst : Set.range s ⊆ Set.range t) :
    IsUnit (algebraMap (MvPolynomial (Fin (n + 1)) R) (chartRing R t)
      (MvPolynomial.monomial (chartExponent s) (1 : R))) := by
  rw [← prod_X_eq_monomial_chartExponent R s]
  exact isUnit_algebraMap_prod_X R s t hst

/-- **The localization map from the Čech term at `s` to the Čech term at `t`**, available
whenever every coordinate inverted at `s` is inverted at `t`, i.e. whenever the chart
intersection at `t` is contained in the one at `s`. -/
def chartTransition (hst : Set.range s ⊆ Set.range t) :
    chartRing R s →ₐ[MvPolynomial (Fin (n + 1)) R] chartRing R t :=
  IsLocalization.Away.liftAlgHom (∏ j, MvPolynomial.X (s j))
    (f := Algebra.ofId (MvPolynomial (Fin (n + 1)) R) (chartRing R t))
    (isUnit_algebraMap_prod_X R s t hst)

/-- The map between Čech terms is the identity on polynomials. -/
theorem chartTransition_algebraMap (hst : Set.range s ⊆ Set.range t)
    (a : MvPolynomial (Fin (n + 1)) R) :
    chartTransition R s t hst (algebraMap _ (chartRing R s) a) =
      algebraMap _ (chartRing R t) a :=
  (chartTransition R s t hst).commutes a

/-- The map between Čech terms is linear over the coefficient ring. -/
theorem chartTransition_smul (hst : Set.range s ⊆ Set.range t) (c : R) (z : chartRing R s) :
    chartTransition R s t hst (c • z) = c • chartTransition R s t hst z := by
  rw [← IsScalarTower.algebraMap_smul (MvPolynomial (Fin (n + 1)) R) c z, Algebra.smul_def,
    map_mul, chartTransition_algebraMap, ← Algebra.smul_def,
    IsScalarTower.algebraMap_smul (MvPolynomial (Fin (n + 1)) R) c]

/-- A weight admissible on a chart intersection is admissible on every smaller one. -/
theorem exponentMonoid_chartExponent_le (hst : Set.range s ⊆ Set.range t) :
    exponentMonoid (↑(chartExponent s).support : Set (Fin (n + 1))) ≤
      exponentMonoid (↑(chartExponent t).support : Set (Fin (n + 1))) := by
  intro e he
  rw [mem_exponentMonoid_chartExponent_iff] at he ⊢
  exact fun i hi => he i fun h => hi (hst h)

/-- **The map between Čech terms carries the Laurent monomial of a weight to the Laurent
monomial of the same weight.** -/
theorem chartTransition_basis (hst : Set.range s ⊆ Set.range t)
    (ε : exponentMonoid (↑(chartExponent s).support : Set (Fin (n + 1))))
    (ε' : exponentMonoid (↑(chartExponent t).support : Set (Fin (n + 1))))
    (hε : (ε : Fin (n + 1) →₀ ℤ) = (ε' : Fin (n + 1) →₀ ℤ)) :
    chartTransition R s t hst (basis R (chartExponent s) (chartRing R s) ε) =
      basis R (chartExponent t) (chartRing R t) ε' := by
  obtain ⟨m, μ, hmμ⟩ := exists_nsmul_add_eq (chartExponent s) ε.2
  refine eq_basis_of_mul_pow_eq R (chartExponent t) (chartRing R t) ε' m (chartExponent s) μ
    (by rw [← hε]; exact hmμ) (isUnit_algebraMap_monomial_chartExponent R s t hst) _ ?_
  rw [← chartTransition_algebraMap R s t hst, ← map_pow, ← map_mul,
    basis_mul_pow R (chartExponent s) (chartRing R s) ε m (chartExponent s) μ hmμ]
  exact chartTransition_algebraMap R s t hst _

/-- **The map between Čech terms is weight-preserving on the Laurent monomials of total
degree `d`.** -/
theorem chartTransition_twistWeightMonomial (hst : Set.range s ⊆ Set.range t) (d : ℤ)
    (e : TwistWeight s d) :
    chartTransition R s t hst (twistWeightMonomial R s d e) =
      twistWeightMonomial R t d ⟨e.1, e.2.1, fun i hi => e.2.2 i fun h => hi (hst h)⟩ := by
  rw [twistWeightMonomial_eq_basis, twistWeightMonomial_eq_basis]
  exact chartTransition_basis R s t hst _ _ rfl

/-- **The map between Čech terms carries each weight piece into the weight piece of the same
weight.** -/
theorem chartTransition_mem_chartWeight (hst : Set.range s ⊆ Set.range t)
    (e : Fin (n + 1) →₀ ℤ) {z : chartRing R s} (hz : z ∈ chartWeight R s e) :
    chartTransition R s t hst z ∈ chartWeight R t e := by
  by_cases he : e ∈ exponentMonoid (↑(chartExponent s).support : Set (Fin (n + 1)))
  · have het : e ∈ exponentMonoid (↑(chartExponent t).support : Set (Fin (n + 1))) :=
      exponentMonoid_chartExponent_le s t hst he
    rw [chartWeight_eq_span R s e he] at hz
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hz
    rw [chartTransition_smul, chartTransition_basis R s t hst ⟨e, he⟩ ⟨e, het⟩ rfl,
      chartWeight_eq_span R t e het]
    exact Submodule.smul_mem _ c (Submodule.mem_span_singleton_self _)
  · rw [show chartWeight R s e = ⊥ from weight_eq_bot R (chartExponent s) (chartRing R s) he,
      Submodule.mem_bot] at hz
    simp [hz]

/-- **The map between Čech terms preserves the total degree.** -/
theorem chartTransition_mem_twistWeightSpan (hst : Set.range s ⊆ Set.range t) (d : ℤ)
    {z : chartRing R s} (hz : z ∈ twistWeightSpan R s d) :
    chartTransition R s t hst z ∈ twistWeightSpan R t d := by
  rw [← iSup_chartWeight_eq_twistWeightSpan] at hz ⊢
  induction hz using Submodule.iSup_induction' with
  | mem e w hw =>
    exact Submodule.mem_iSup_of_mem e (chartTransition_mem_chartWeight R s t hst e.1 hw)
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy

end Transition

end Stacks.ProjectiveCohomology

end
