module

public import Mathlib.LinearAlgebra.Finsupp.Supported
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import StacksCore.Tactic.StacksAttribute

/-!
# Monomial charts of the twists of the structure sheaf on projective space

Let `R` be a commutative ring and let `n : ℕ`. The sections of `𝒪(d)` on the standard open
`D₊(∏_{i ∈ S} Tᵢ)` of `ℙⁿ_R` are the degree-`d` elements of the localization
`R[T₀, …, Tₙ][1/∏_{i ∈ S} Tᵢ]`, and that module is free on the Laurent monomials
`T₀^{e₀} ⋯ Tₙ^{eₙ}` whose exponents sum to `d` and which are nonnegative outside `S`.

This file introduces those index sets and the corresponding submodules of the free `R`-module
on all Laurent exponent vectors, and records how they interact with unions and intersections of
the sets `S`. This is the combinatorial substrate of the Čech computation of
`H^q(ℙⁿ_R, 𝒪(d))`: the Čech complex of the standard cover splits as a direct sum over exponent
vectors, and the summand attached to a vector depends only on which of its entries are negative.

Two identifications of the extreme charts are proved here. The chart `S = ∅` — no variable
inverted — is the degree-`d` part of the polynomial ring itself, and is identified with
`MvPolynomial.homogeneousSubmodule`; in particular it is spanned by, and free on, the degree-`d`
monomials, and it vanishes for `d < 0`. The chart `S = Set.univ` — every variable inverted — is
the whole degree-`d` Laurent piece.

## Main definitions

* `Stacks.ProjectiveSpace.Cohomology.laurentMonomials` — the exponent vectors of total degree
  `d` that are nonnegative outside `S`.
* `Stacks.ProjectiveSpace.Cohomology.twistChart` — the free `R`-module on those exponent
  vectors, the monomial model of the degree-`d` part of `R[T₀, …, Tₙ][1/∏_{i ∈ S} Tᵢ]`.

## Main results

* `twistChart_sup` and `twistChart_iInf` — the charts turn unions and intersections of the
  inverted-variable sets into joins and meets of submodules.
* `iInter_laurentMonomials_singleton` — a Laurent monomial lies in every one-variable chart
  exactly when it is a polynomial monomial.
* `twistChartEmptyLinearEquiv` — the chart with no variable inverted is the module of
  degree-`d` homogeneous polynomials, for `0 ≤ d`.
* `twistChart_eq_bot_of_neg` — that chart is zero for `d < 0`.

## References

* [Stacks Project, Tag 01XT](https://stacks.math.columbia.edu/tag/01XT)
-/

@[expose] public noncomputable section

open Finsupp

universe u

namespace Stacks.ProjectiveSpace.Cohomology

variable (R : Type u) [CommRing R] {n : ℕ}

/-- The exponent vectors of a Laurent monomial in `T₀, …, Tₙ` of total degree `d` which is
regular away from the variables indexed by `S`: the entries outside `S` are nonnegative.
These index a basis of the degree-`d` part of `R[T₀, …, Tₙ][1/∏_{i ∈ S} Tᵢ]`. -/
def laurentMonomials (n : ℕ) (d : ℤ) (S : Set (Fin (n + 1))) : Set (Fin (n + 1) → ℤ) :=
  {e | (∑ i, e i) = d ∧ ∀ i ∉ S, 0 ≤ e i}

variable {R}

/-- An exponent vector is an allowed Laurent monomial when its entries sum to `d` and its entries
outside `S` are nonnegative. -/
@[simp]
theorem mem_laurentMonomials {d : ℤ} {S : Set (Fin (n + 1))} {e : Fin (n + 1) → ℤ} :
    e ∈ laurentMonomials n d S ↔ (∑ i, e i) = d ∧ ∀ i ∉ S, 0 ≤ e i :=
  Iff.rfl

/-- Inverting more variables allows more monomials. -/
theorem laurentMonomials_mono {d : ℤ} {S T : Set (Fin (n + 1))} (h : S ⊆ T) :
    laurentMonomials n d S ⊆ laurentMonomials n d T :=
  fun _ he => ⟨he.1, fun i hi => he.2 i fun hiS => hi (h hiS)⟩

/-- Every Laurent monomial of total degree `d` is allowed once all variables are inverted. -/
@[simp]
theorem laurentMonomials_univ (n : ℕ) (d : ℤ) :
    laurentMonomials n d Set.univ = {e : Fin (n + 1) → ℤ | (∑ i, e i) = d} := by
  ext e
  simp [laurentMonomials]

/-- With no variable inverted, the allowed monomials are the polynomial ones. -/
theorem laurentMonomials_empty (n : ℕ) (d : ℤ) :
    laurentMonomials n d (∅ : Set (Fin (n + 1))) =
      {e : Fin (n + 1) → ℤ | (∑ i, e i) = d ∧ ∀ i, 0 ≤ e i} := by
  ext e
  simp [laurentMonomials]

/-- A Laurent monomial allowed in the chart inverting only `Tᵢ`, for every `i`, has all its
exponents nonnegative: given two indices, the condition at one of them covers the other.
This is the combinatorial form of `H⁰(ℙⁿ, 𝒪(d)) = R[T₀, …, Tₙ]_d`. -/
theorem iInter_laurentMonomials_singleton (n : ℕ) (hn : 0 < n) (d : ℤ) :
    ⋂ i : Fin (n + 1), laurentMonomials n d {i} = laurentMonomials n d (∅ : Set (Fin (n + 1))) := by
  ext e
  simp only [Set.mem_iInter, mem_laurentMonomials, Set.mem_singleton_iff, Set.mem_empty_iff_false,
    not_false_eq_true, forall_const]
  refine ⟨fun h => ⟨(h 0).1, fun i => ?_⟩, fun h i => ⟨h.1, fun j _ => h.2 j⟩⟩
  obtain ⟨j, hj⟩ : ∃ j : Fin (n + 1), j ≠ i := by
    rcases eq_or_ne i 0 with hi | hi
    · exact ⟨⟨1, by omega⟩, by simp [hi, Fin.ext_iff]⟩
    · exact ⟨0, fun h => hi h.symm⟩
  exact (h j).2 i (Ne.symm hj)

variable (R)

/-- The degree-`d` part of `R[T₀, …, Tₙ][1/∏_{i ∈ S} Tᵢ]`, as the free `R`-module on the
Laurent monomials of total degree `d` that are nonnegative outside `S`. It is a submodule of
the free `R`-module on all Laurent exponent vectors, so the restriction maps between charts are
the inclusions. -/
def twistChart (n : ℕ) (d : ℤ) (S : Set (Fin (n + 1))) :
    Submodule R ((Fin (n + 1) → ℤ) →₀ R) :=
  Finsupp.supported R R (laurentMonomials n d S)

variable {R}

/-- An element lies in the chart exactly when its support consists of allowed monomials. -/
theorem mem_twistChart {d : ℤ} {S : Set (Fin (n + 1))} {x : (Fin (n + 1) → ℤ) →₀ R} :
    x ∈ twistChart R n d S ↔ ↑x.support ⊆ laurentMonomials n d S :=
  Iff.rfl

/-- A single Laurent monomial lies in every chart that allows it. -/
theorem single_mem_twistChart {d : ℤ} {S : Set (Fin (n + 1))} {e : Fin (n + 1) → ℤ}
    (he : e ∈ laurentMonomials n d S) (r : R) : Finsupp.single e r ∈ twistChart R n d S :=
  Finsupp.single_mem_supported R r he

/-- Restriction to a chart inverting more variables is an inclusion of submodules. -/
@[gcongr]
theorem twistChart_mono {d : ℤ} {S T : Set (Fin (n + 1))} (h : S ⊆ T) :
    twistChart R n d S ≤ twistChart R n d T :=
  Finsupp.supported_mono (laurentMonomials_mono h)

/-- The chart of a union of inverted-variable sets is the join of the two charts. -/
theorem twistChart_sup (n : ℕ) (d : ℤ) (S T : Set (Fin (n + 1))) :
    twistChart R n d S ⊔ twistChart R n d T =
      Finsupp.supported R R (laurentMonomials n d S ∪ laurentMonomials n d T) :=
  (Finsupp.supported_union _ _).symm

/-- The chart of an intersection of inverted-variable sets is the meet of the charts. -/
theorem twistChart_iInf {ι : Type*} (n : ℕ) (d : ℤ) (S : ι → Set (Fin (n + 1))) :
    ⨅ j, twistChart R n d (S j) =
      Finsupp.supported R R (⋂ j, laurentMonomials n d (S j)) :=
  (Finsupp.supported_iInter _).symm

/-- **Stacks 01XT, the degree-zero chart intersection.** A Laurent section of `𝒪(d)` that is
regular on every standard open `D₊(Tᵢ)` is a polynomial section. -/
theorem twistChart_iInf_singleton (n : ℕ) (hn : 0 < n) (d : ℤ) :
    ⨅ i : Fin (n + 1), twistChart R n d {i} = twistChart R n d (∅ : Set (Fin (n + 1))) := by
  rw [twistChart_iInf, iInter_laurentMonomials_singleton n hn d, twistChart]

/-- The chart with no variable inverted vanishes in negative degrees: a monomial with all
exponents nonnegative has nonnegative total degree. -/
theorem twistChart_eq_bot_of_neg (n : ℕ) {d : ℤ} (hd : d < 0) :
    twistChart R n d (∅ : Set (Fin (n + 1))) = ⊥ := by
  have hempty : laurentMonomials n d (∅ : Set (Fin (n + 1))) = ∅ := by
    rw [laurentMonomials_empty]
    refine Set.eq_empty_iff_forall_notMem.2 fun e he => ?_
    exact absurd (he.1 ▸ Finset.sum_nonneg fun i _ => he.2 i) (not_le.2 hd)
  rw [twistChart, hempty, Finsupp.supported_empty]

/-- The monomials of the polynomial chart in degree `d ≥ 0` are the exponent vectors of the
degree-`d.toNat` monomials of `R[T₀, …, Tₙ]`, read as functions with values in `ℤ`. -/
def laurentMonomialsEmptyEquiv (n : ℕ) {d : ℤ} (hd : 0 ≤ d) :
    laurentMonomials n d (∅ : Set (Fin (n + 1))) ≃
      {m : Fin (n + 1) →₀ ℕ | m.degree = d.toNat} where
  toFun e :=
    ⟨Finsupp.equivFunOnFinite.symm fun i => (e.1 i).toNat, by
      change (Finsupp.equivFunOnFinite.symm fun i => (e.1 i).toNat).degree = d.toNat
      rw [Finsupp.degree_eq_sum]
      change (∑ i, (e.1 i).toNat) = d.toNat
      have he := mem_laurentMonomials.1 e.2
      have key : ((∑ i, (e.1 i).toNat : ℕ) : ℤ) = d := by
        rw [Nat.cast_sum]
        exact Eq.trans
          (Finset.sum_congr rfl fun i _ => Int.toNat_of_nonneg (he.2 i (by simp))) he.1
      omega⟩
  invFun m :=
    ⟨fun i => ((m.1 i : ℕ) : ℤ), by
      refine ⟨?_, fun i _ => Int.natCast_nonneg _⟩
      change (∑ i, ((m.1 i : ℕ) : ℤ)) = d
      rw [← Nat.cast_sum]
      have hm' : m.1.degree = d.toNat := m.2
      rw [Finsupp.degree_eq_sum] at hm'
      rw [hm', Int.toNat_of_nonneg hd]⟩
  left_inv e :=
    Subtype.ext (funext fun i =>
      Int.toNat_of_nonneg ((mem_laurentMonomials.1 e.2).2 i (by simp)))
  right_inv m := Subtype.ext (Finsupp.ext fun i => by
    change (((m.1 i : ℕ) : ℤ)).toNat = m.1 i
    simp)

/-- **Stacks 01XT, the monomial basis of the polynomial chart.** For `0 ≤ d` the chart with no
variable inverted is the module of degree-`d` homogeneous polynomials in `T₀, …, Tₙ`, matched
monomial by monomial. This is the degree-zero half of the cohomology of `𝒪(d)` on `ℙⁿ_R`,
before any comparison with sheaf cohomology. -/
def twistChartEmptyLinearEquiv (n : ℕ) {d : ℤ} (hd : 0 ≤ d) :
    twistChart R n d (∅ : Set (Fin (n + 1))) ≃ₗ[R]
      MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R d.toNat :=
  (Finsupp.supportedEquivFinsupp _).trans
    ((Finsupp.domLCongr (laurentMonomialsEmptyEquiv n hd)).trans
      ((AddMonoidAlgebra.supportedEquivFinsupp (R := R) (S := R) _).symm.trans
        (LinearEquiv.ofEq _ _
          (MvPolynomial.homogeneousSubmodule_eq_finsupp_supported
            (Fin (n + 1)) R d.toNat).symm)))

end Stacks.ProjectiveSpace.Cohomology

end
