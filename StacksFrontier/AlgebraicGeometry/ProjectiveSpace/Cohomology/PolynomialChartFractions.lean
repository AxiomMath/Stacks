module

public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.ChartSectionsComparison

/-!
# The polynomial chart of a twist on projective space, as fractions over `1`

Let `R` be a commutative ring, let `P = R[T₀, …, Tₙ]` carry its grading by total degree, and let
`k ≥ 0`. The monomial model
`Stacks.ProjectiveSpace.Cohomology.twistChart R n k ∅` of the sections of `𝒪(k)` with no variable
inverted is the module of degree-`k` homogeneous polynomials; this file says what that means
inside each localization: an element of that chart, read as a section of `𝒪(k)` over any standard
open `D₊(∏_{i ∈ s} Tᵢ)`, is the fraction `a / 1` of one homogeneous polynomial `a` of degree `k`,
the *same* `a` for every `s`.

This is the algebraic half of the identification of `Γ(ℙⁿ_R, 𝒪(k))` with `(R[T₀, …, Tₙ])_k`
*through the canonical section map* of [Stacks, Tag 01MP]: the geometric half glues the charts,
and what it needs from here is that a Laurent section regular on every `D₊(Tᵢ)` is `a / 1` on
every chart at once.

## Main definitions

* `Stacks.ProjectiveSpace.Cohomology.toNatExp`: the monomial exponent vector of a nonnegative
  Laurent exponent vector.

## Main results

* `Stacks.ProjectiveSpace.Cohomology.laurentFrac_of_nonneg`: a Laurent monomial with every
  exponent nonnegative is the polynomial monomial of the same exponents, over the denominator
  `1`.
* `Stacks.ProjectiveSpace.Cohomology.monomial_toNatExp_mem_homogeneousSubmodule`: that monomial is
  homogeneous of the total degree.
* `Stacks.ProjectiveSpace.Cohomology.exists_homogeneous_coe_twistChartEquivTwistSections`:
  **an element of the polynomial chart is a homogeneous polynomial over `1`, in every chart at
  once.**
* `Stacks.ProjectiveSpace.Cohomology.iInter_laurentMonomials_singleton_of_nonneg` and
  `Stacks.ProjectiveSpace.Cohomology.twistChart_iInf_singleton_of_nonneg`: **the one-variable
  charts meet in the polynomial chart**, in nonnegative degree and for every `n ≥ 0`.

## Implementation notes

The quantifier over the chart `s` sits *inside* the existential of
`exists_homogeneous_coe_twistChartEquivTwistSections`, and that is the whole point of the
statement: the geometric argument compares the restrictions of a global section to the different
charts `D₊(Tᵢ)`, and would get a different polynomial from each of them if the existential were
on the outside. The proof is the span induction on the chart, whose generator case is a single
Laurent monomial; the witness is additive in the generators, so one witness serves every `s`.

`Stacks.ProjectiveSpace.Cohomology.iInter_laurentMonomials_singleton` already has the intersection
of the one-variable charts for `n ≥ 1`, where it holds in every degree. For `n = 0` there is only
one chart and its condition is empty, so the statement is false in negative degrees and needs
`0 ≤ d`; that is the hypothesis added here, and it is satisfied in the only case the
identification of `Γ(ℙⁿ_R, 𝒪(k))` is used, `k` a natural number.

## References

* [Stacks Project, Tag 01XT](https://stacks.math.columbia.edu/tag/01XT)
* [Stacks Project, Tag 01MP](https://stacks.math.columbia.edu/tag/01MP)
-/

@[expose] public noncomputable section

open Finsupp MvPolynomial

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace Stacks.ProjectiveSpace.Cohomology

variable {R : Type u} [CommRing R] {n : ℕ}

/-- The monomial exponent vector of a nonnegative Laurent exponent vector. -/
def toNatExp (e : Fin (n + 1) → ℤ) : Fin (n + 1) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun i => (e i).toNat

/-- With the power `N = 0` of the denominator, the numerator exponent vector `numExp s e 0` is the
truncation `toNatExp e`. -/
theorem numExp_zero (s : Finset (Fin (n + 1))) (e : Fin (n + 1) → ℤ) :
    numExp s e 0 = toNatExp e :=
  Finsupp.ext fun i => by simp [toNatExp]

/-- A Laurent monomial with every exponent nonnegative is the polynomial monomial of the same
exponents, over the denominator `1`. -/
theorem laurentFrac_of_nonneg (R : Type u) [CommRing R] (n : ℕ) (s : Finset (Fin (n + 1)))
    {e : Fin (n + 1) → ℤ} (he : ∀ i, 0 ≤ e i) :
    laurentFrac R n s e = LocalizedModule.mk (MvPolynomial.monomial (toNatExp e) (1 : R)) 1 := by
  rw [laurentFrac_eq_mk (N := 0) (fun i _ => he i) (fun i _ => by simpa using he i), numExp_zero]
  congr 1

/-- The exponent vector of a nonnegative degree-`k` Laurent monomial has degree `k`, so the
corresponding monomial is homogeneous of degree `k`. -/
theorem monomial_toNatExp_mem_homogeneousSubmodule (R : Type u) [CommRing R] (n k : ℕ) (r : R)
    {e : Fin (n + 1) → ℤ} (he : e ∈ laurentMonomials n (k : ℤ) (∅ : Set (Fin (n + 1)))) :
    MvPolynomial.monomial (toNatExp e) r ∈
      MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R k := by
  have hnn : ∀ i, 0 ≤ e i := fun i => he.2 i (Set.notMem_empty i)
  have hsum : ((∑ i, (e i).toNat : ℕ) : ℤ) = (k : ℤ) := by
    rw [Nat.cast_sum]
    exact Eq.trans (Finset.sum_congr rfl fun i _ => Int.toNat_of_nonneg (hnn i)) he.1
  have hdeg : (toNatExp e).degree = k := by
    have : (toNatExp e).degree = ∑ i, (e i).toNat := by
      rw [Finsupp.degree_eq_sum]
      rfl
    rw [this]
    omega
  exact (MvPolynomial.mem_homogeneousSubmodule _ _).2
    (MvPolynomial.isHomogeneous_monomial r hdeg)

/-! ### A polynomial chart element is the fraction of a homogeneous polynomial -/

/-- **An element of the polynomial chart is a homogeneous polynomial, in every chart at once.**
For `v` in the chart with no variable inverted there is one homogeneous polynomial `a` of degree
`k` such that, read as a section of `𝒪(k)` over any standard open `D₊(∏_{i ∈ s} Tᵢ)`, `v` is the
fraction `a / 1`. -/
theorem exists_homogeneous_coe_twistChartEquivTwistSections (R : Type u) [CommRing R] (n k : ℕ)
    {v : (Fin (n + 1) → ℤ) →₀ R}
    (hv : v ∈ twistChart R n (k : ℤ) (∅ : Set (Fin (n + 1)))) :
    ∃ a : MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R k,
      ∀ (s : Finset (Fin (n + 1))) (h : v ∈ twistChart R n (k : ℤ) (↑s : Set (Fin (n + 1)))),
        ((twistChartEquivTwistSections R n (k : ℤ) s ⟨v, h⟩ : twistSections R n (k : ℤ) s) :
          LocalizedModule.Away (chartDenom R n s) (MvPolynomial (Fin (n + 1)) R))
          = LocalizedModule.mk (a : MvPolynomial (Fin (n + 1)) R) 1 := by
  have hmono : ∀ (s : Finset (Fin (n + 1))) {x}, x ∈ Submodule.span R
      ((fun i => single i (1 : R)) '' laurentMonomials n k (∅ : Set (Fin (n + 1)))) →
      x ∈ twistChart R n k (↑s : Set (Fin (n + 1))) := fun s x hx =>
    twistChart_mono (Set.empty_subset _) (by rwa [twistChart, supported_eq_span_single])
  rw [twistChart, Finsupp.supported_eq_span_single] at hv
  induction hv using Submodule.span_induction with
  | mem w hw =>
      obtain ⟨e, he, rfl⟩ := hw
      refine ⟨⟨MvPolynomial.monomial (toNatExp e) 1,
        monomial_toNatExp_mem_homogeneousSubmodule R n k 1 he⟩, fun s h => ?_⟩
      rw [coe_twistChartEquivTwistSections_single R n (k : ℤ) s
        (laurentMonomials_mono (Set.empty_subset _) he) _ rfl]
      exact laurentFrac_of_nonneg R n s fun i => he.2 i (Set.notMem_empty i)
  | zero =>
      refine ⟨0, fun s h => ?_⟩
      have h0 : (⟨(0 : (Fin (n + 1) → ℤ) →₀ R), h⟩ :
          twistChart R n (k : ℤ) (↑s : Set (Fin (n + 1)))) = 0 := rfl
      rw [h0, map_zero]
      simp
  | add x y hx hy ihx ihy =>
      obtain ⟨a, ha⟩ := ihx
      obtain ⟨b, hb⟩ := ihy
      refine ⟨a + b, fun s h => ?_⟩
      have hxs := hmono s hx
      have hys := hmono s hy
      have hsum : (⟨x + y, h⟩ : twistChart R n (k : ℤ) (↑s : Set (Fin (n + 1))))
          = ⟨x, hxs⟩ + ⟨y, hys⟩ := rfl
      rw [hsum, map_add]
      rw [Submodule.coe_add, ha s hxs, hb s hys]
      rw [Submodule.coe_add, LocalizedModule.mk_add_mk]
      simp
  | smul c x hx ihx =>
      obtain ⟨a, ha⟩ := ihx
      refine ⟨c • a, fun s h => ?_⟩
      have hxs := hmono s hx
      have hsmul : (⟨c • x, h⟩ : twistChart R n (k : ℤ) (↑s : Set (Fin (n + 1))))
          = c • ⟨x, hxs⟩ := rfl
      rw [hsmul, map_smul, Submodule.coe_smul, ha s hxs, SetLike.val_smul,
        LocalizedModule.smul'_mk]

/-! ### The intersection of the one-variable charts in nonnegative degree -/

/-- **The one-variable charts meet in the polynomial chart, in nonnegative degree.** A Laurent
monomial of total degree `d ≥ 0` allowed in every chart `D₊(Tᵢ)` has all its exponents
nonnegative. For `n ≥ 1` this is `iInter_laurentMonomials_singleton` and does not need `d ≥ 0`;
in the one-variable case `n = 0` the single chart condition is empty and the total degree is the
only exponent, so `d ≥ 0` is what gives the conclusion. -/
theorem iInter_laurentMonomials_singleton_of_nonneg (n : ℕ) {d : ℤ} (hd : 0 ≤ d) :
    ⋂ i : Fin (n + 1), laurentMonomials n d {i} =
      laurentMonomials n d (∅ : Set (Fin (n + 1))) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · ext e
    simp only [Set.mem_iInter, mem_laurentMonomials, Set.mem_singleton_iff,
      Set.mem_empty_iff_false, not_false_eq_true, forall_const]
    refine ⟨fun h => ⟨(h 0).1, fun i => ?_⟩, fun h i => ⟨h.1, fun j _ => h.2 j⟩⟩
    have hsum : e 0 = d := by
      have h1 := (h 0).1
      rwa [Fin.sum_univ_one] at h1
    have hi : i = 0 := Fin.ext (by have := i.isLt; omega)
    rw [hi, hsum]
    exact hd
  · exact iInter_laurentMonomials_singleton n hn d

/-- **The one-variable charts meet in the polynomial chart, in nonnegative degree.** -/
theorem twistChart_iInf_singleton_of_nonneg (R : Type u) [CommRing R] (n : ℕ) {d : ℤ}
    (hd : 0 ≤ d) :
    ⨅ i : Fin (n + 1), twistChart R n d {i} = twistChart R n d (∅ : Set (Fin (n + 1))) := by
  rw [twistChart_iInf, iInter_laurentMonomials_singleton_of_nonneg n hd, twistChart]

end Stacks.ProjectiveSpace.Cohomology

end
