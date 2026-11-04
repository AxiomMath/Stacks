module

public import StacksFrontier.RingTheory.LocalCohomology.FinitenessCriterion
public import StacksFrontier.RingTheory.LocalCohomology.FinitenessDepthDimension
public import StacksFrontier.Topology.Dimension.DimensionFunction

/-!
# Finiteness of local cohomology in degrees at most one from a depth bound on immediate
specializations

Let `A` be a Noetherian ring admitting a dualizing complex, let `T ⊆ Spec(A)` be stable under
specialization and let `M` be a finite `A`-module.  Faltings' criterion
[Stacks, Tag 0EFD] makes finiteness of `H^i_T(M)` for `i ≤ s` equivalent to
`depth(M_p) + dim((A/p)_q) > s` for every pair of primes `p ⊆ q` with `p ∉ T` and `q ∈ T`.  For
`s = 1` that quantifier collapses onto the *immediate* specializations into `T`: a pair `p ⊆ q`
with `p ∉ T` and `q ∈ T` has `p ≠ q`, so the dimension of `(A/p)_q` is at least one, and it is at
least two unless `q` is an immediate specialization of `p`.  Hence `H^0_T(M)` and `H^1_T(M)` are
finite as soon as `depth(M_p) ≥ 1` at every `p ∉ T` admitting an immediate specialization into
`T`.

That is the hypothesis under which [Stacks, Tag 0EI3] constructs its depth-two extension, and
this file supplies the implication the source uses without comment: the two hypotheses of
[Stacks, Tag 0EI3] beyond coherence — that `A` has a dualizing complex and that the depth of the
module is at least one across the boundary of `T` — enter its proof only through the finiteness
of `H^1_T` of the depth-one quotient, which is what is proved here.

## Main results

* `Stacks.LocalCohomology.one_lt_depth_add_height_quotient_of_depth_immediate` — the
  depth-plus-dimension inequality of [Stacks, Tag 0EFD] at `s = 1`, in `ℕ∞`.
* `Stacks.LocalCohomology.finite_localCohomologyWithSupportIn_le_one_of_depth_immediate` —
  finiteness of `H^i_T(M)` for `i ≤ 1`.

## Implementation notes

The dimension of `(A/p)_q` is `ringKrullDim (A_q ⧸ p A_q)` in the statement of
[Stacks, Tag 0EFD]; it is rewritten to the height of the image of `q` in `A/p` by
`Stacks.LocalCohomology.ringKrullDim_localization_quotient_eq_height`, and the comparison of the
`ℕ∞`-valued depth and height with the integer bound is
`Stacks.LocalCohomology.natCast_lt_add_iff_eint`.  So the whole argument runs in `ℕ∞`: the two
lower bounds for the height come from `Ideal.height_add_one_le_of_lt_of_isPrime` applied along
`⊥ < q/p`, respectively `⊥ < r/p < q/p` for an intermediate prime `r`, and the base case is
`Ideal.height_bot`.

Immediate specialization is `TopologicalSpace.IsImmediateSpecialization`, whose unfolded form
`TopologicalSpace.isImmediateSpecialization_iff` is what the case distinction uses: the failure
of immediacy for a non-trivial specialization is exactly the existence of a strictly
intermediate point, and on `Spec(A)` specialization is inclusion of primes by
`PrimeSpectrum.le_iff_specializes`.

No `@[stacks 0EFD]` attribute is placed here: Tag 0EFD is the equivalence, which is
`Stacks.LocalCohomology.finite_localCohomologyWithSupportIn_iff_depth_add_dim`, and what is
proved below is one direction of it at one value of `s` with the quantifier rewritten.  No
`@[stacks 0EI3]` attribute is placed either: this is the ring-theoretic input of that tag's
existence half, not the existence statement.

## References

* [Stacks Project, Tag 0EFD](https://stacks.math.columbia.edu/tag/0EFD)
* [Stacks Project, Tag 0EI3](https://stacks.math.columbia.edu/tag/0EI3)
-/

@[expose] public noncomputable section

open CategoryTheory IsLocalRing TopologicalSpace
open Stacks.Algebraization (enatToEInt krullDimToEInt)

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.LocalCohomology

/-! ### Lower bounds for the height of the image of a prime in a quotient -/

section Height

variable {A : Type u} [CommRing A]

/-- Two primes containing `p` with the same image in `A/p` are equal. -/
private lemma eq_of_map_quotientMk_eq {p q r : PrimeSpectrum A} (hpq : p.asIdeal ≤ q.asIdeal)
    (hpr : p.asIdeal ≤ r.asIdeal)
    (h : q.asIdeal.map (Ideal.Quotient.mk p.asIdeal) =
      r.asIdeal.map (Ideal.Quotient.mk p.asIdeal)) : q = r := by
  refine PrimeSpectrum.ext ?_
  rw [← Ideal.comap_map_mk hpq, ← Ideal.comap_map_mk hpr, h]

/-- The image of `q` in `A/p` is nonzero when `p ≠ q`. -/
private lemma bot_lt_map_quotientMk (p q : PrimeSpectrum A) (hpq : p.asIdeal ≤ q.asIdeal)
    (hne : p ≠ q) :
    (⊥ : Ideal (A ⧸ p.asIdeal)) < q.asIdeal.map (Ideal.Quotient.mk p.asIdeal) := by
  refine lt_of_le_of_ne bot_le fun h => hne ?_
  refine PrimeSpectrum.ext ?_
  rw [← Ideal.comap_map_mk hpq, ← h, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]

/-- The images in `A/p` of two primes between `p` and `q` are strictly ordered when the primes
are. -/
private lemma map_quotientMk_lt_map_quotientMk {p q r : PrimeSpectrum A}
    (hpr : p.asIdeal ≤ r.asIdeal) (hrq : r.asIdeal ≤ q.asIdeal) (hne : r ≠ q) :
    r.asIdeal.map (Ideal.Quotient.mk p.asIdeal) <
      q.asIdeal.map (Ideal.Quotient.mk p.asIdeal) :=
  lt_of_le_of_ne (Ideal.map_mono hrq) fun h =>
    hne (eq_of_map_quotientMk_eq hpr (hpr.trans hrq) h)

/-- The height of the image of `q` in `A/p` is at least one when `p ⊊ q`. -/
private lemma one_le_height_map_quotientMk (p q : PrimeSpectrum A) (hpq : p.asIdeal ≤ q.asIdeal)
    (hne : p ≠ q) : (1 : ℕ∞) ≤ (q.asIdeal.map (Ideal.Quotient.mk p.asIdeal)).height := by
  have : (q.asIdeal.map (Ideal.Quotient.mk p.asIdeal)).IsPrime :=
    Ideal.isPrime_map_quotientMk_of_isPrime hpq
  have : IsDomain (A ⧸ p.asIdeal) := (Ideal.Quotient.isDomain_iff_prime _).2 p.isPrime
  have h := Ideal.height_add_one_le_of_lt_of_isPrime (bot_lt_map_quotientMk p q hpq hne)
  rwa [Ideal.height_bot, zero_add] at h

/-- The height of the image of `q` in `A/p` is at least two when `q` is a non-trivial
specialization of `p` which is not immediate. -/
private lemma two_le_height_map_quotientMk (p q : PrimeSpectrum A) (hpq : p.asIdeal ≤ q.asIdeal)
    (hne : p ≠ q) (hnotimm : ¬ IsImmediateSpecialization p q) :
    (2 : ℕ∞) ≤ (q.asIdeal.map (Ideal.Quotient.mk p.asIdeal)).height := by
  have : IsDomain (A ⧸ p.asIdeal) := (Ideal.Quotient.isDomain_iff_prime _).2 p.isPrime
  have : (q.asIdeal.map (Ideal.Quotient.mk p.asIdeal)).IsPrime :=
    Ideal.isPrime_map_quotientMk_of_isPrime hpq
  -- the failure of immediacy produces a strictly intermediate prime
  obtain ⟨r, hpr, hrq, hrp, hrq'⟩ : ∃ r : PrimeSpectrum A, p.asIdeal ≤ r.asIdeal ∧
      r.asIdeal ≤ q.asIdeal ∧ r ≠ p ∧ r ≠ q := by
    by_contra hcon
    refine hnotimm ((isImmediateSpecialization_iff p q).2
      ⟨(PrimeSpectrum.le_iff_specializes _ _).1 hpq, hne, fun z hpz hzq => ?_⟩)
    by_contra hz
    exact hcon ⟨z, (PrimeSpectrum.le_iff_specializes _ _).2 hpz,
      (PrimeSpectrum.le_iff_specializes _ _).2 hzq, fun h => hz (Or.inl h),
      fun h => hz (Or.inr h)⟩
  have : (r.asIdeal.map (Ideal.Quotient.mk p.asIdeal)).IsPrime :=
    Ideal.isPrime_map_quotientMk_of_isPrime hpr
  have h1 : (1 : ℕ∞) ≤ (r.asIdeal.map (Ideal.Quotient.mk p.asIdeal)).height :=
    one_le_height_map_quotientMk p r hpr (Ne.symm hrp)
  calc (2 : ℕ∞) = 1 + 1 := by norm_num
    _ ≤ (r.asIdeal.map (Ideal.Quotient.mk p.asIdeal)).height + 1 := by gcongr
    _ ≤ (q.asIdeal.map (Ideal.Quotient.mk p.asIdeal)).height :=
      Ideal.height_add_one_le_of_lt_of_isPrime (map_quotientMk_lt_map_quotientMk hpr hrq hrq')

end Height

/-! ### The depth-plus-dimension inequality at `s = 1` -/

/-- **The depth-plus-dimension inequality of [Stacks, Tag 0EFD] at `s = 1`.** Let `T ⊆ Spec(A)`
and let `M` be an `A`-module whose depth at a prime `p ∉ T` is at least one whenever some prime
of `T` is an immediate specialization of `p`.  Then
`depth(M_p) + ht(q/p) > 1` for every pair `p ⊆ q` with `p ∉ T` and `q ∈ T`.

The two primes are distinct, so the height of `q/p` is at least one; if `q` is an immediate
specialization of `p` the hypothesis supplies the missing depth, and if it is not then the
intermediate prime raises the height to two on its own. -/
public theorem one_lt_depth_add_height_quotient_of_depth_immediate
    (A : Type u) [CommRing A] (T : Set (PrimeSpectrum A))
    (M : Type u) [AddCommGroup M] [Module A M]
    (hdepth : ∀ p q : PrimeSpectrum A, p ∉ T → q ∈ T → IsImmediateSpecialization p q →
      (1 : ℕ∞) ≤ Module.depth (Localization.AtPrime p.asIdeal)
        (maximalIdeal (Localization.AtPrime p.asIdeal))
        (LocalizedModule p.asIdeal.primeCompl M))
    (p q : PrimeSpectrum A) (hp : p ∉ T) (hq : q ∈ T) (hpq : p.asIdeal ≤ q.asIdeal) :
    (1 : ℕ∞) < Module.depth (Localization.AtPrime p.asIdeal)
        (maximalIdeal (Localization.AtPrime p.asIdeal))
        (LocalizedModule p.asIdeal.primeCompl M) +
      (q.asIdeal.map (Ideal.Quotient.mk p.asIdeal)).height := by
  have hne : p ≠ q := fun h => hp (h ▸ hq)
  by_cases himm : IsImmediateSpecialization p q
  · exact (show (1 : ℕ∞) < 1 + 1 by norm_num).trans_le
      (add_le_add (hdepth p q hp hq himm) (one_le_height_map_quotientMk p q hpq hne))
  · exact (show (1 : ℕ∞) < 2 by norm_num).trans_le
      ((two_le_height_map_quotientMk p q hpq hne himm).trans le_add_self)

/-! ### Finiteness in degrees at most one -/

/-- **Finiteness of `H^i_T(M)` for `i ≤ 1` from a depth bound on immediate specializations.**
Let `A` be a Noetherian ring with a dualizing complex, let `T ⊆ Spec(A)` be stable under
specialization and let `M` be a finite `A`-module whose depth at a prime `p ∉ T` is at least one
whenever some prime of `T` is an immediate specialization of `p`.  Then the local cohomology
modules `H^i_T(M)` are finite `A`-modules for every `i ≤ 1`.

This is Faltings' criterion [Stacks, Tag 0EFD] at `s = 1`, whose depth-plus-dimension clause is
`one_lt_depth_add_height_quotient_of_depth_immediate`. -/
public theorem finite_localCohomologyWithSupportIn_le_one_of_depth_immediate
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (T : Set (PrimeSpectrum A)) (hT : StableUnderSpecialization T)
    (M : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M]
    (omega : DerivedCategory (ModuleCat.{u} A))
    (homega : Dualizing.IsDualizingComplex (A := A) (K := omega))
    (hdepth : ∀ p q : PrimeSpectrum A, p ∉ T → q ∈ T → IsImmediateSpecialization p q →
      (1 : ℕ∞) ≤ Module.depth (Localization.AtPrime p.asIdeal)
        (maximalIdeal (Localization.AtPrime p.asIdeal))
        (LocalizedModule p.asIdeal.primeCompl M)) :
    ∀ i : ℤ, i ≤ 1 → Module.Finite A
      (localCohomologyWithSupportIn.{u, u} A T
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A M)) i) := by
  refine (finite_localCohomologyWithSupportIn_iff_depth_add_dim A T hT 1 M omega homega).2
    fun p q hp hq hpq => ?_
  rw [ringKrullDim_localization_quotient_eq_height p q hpq]
  refine (natCast_lt_add_iff_eint 1 _ _).1 ?_
  exact_mod_cast one_lt_depth_add_height_quotient_of_depth_immediate A T M hdepth p q hp hq hpq

end Stacks.LocalCohomology

end
