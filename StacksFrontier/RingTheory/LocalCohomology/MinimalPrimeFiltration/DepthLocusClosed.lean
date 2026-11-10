module

public import StacksFrontier.RingTheory.LocalCohomology.FaltingsAnnihilator
public import StacksFrontier.RingTheory.LocalCohomology.FinitenessImmediateSpecialization
public import StacksFrontier.RingTheory.LocalCohomology.MinimalPrimeFiltration.MinimalPointDepth

/-!
# The low-depth locus of a specialization-stable subset lies in a closed subset of it

Let `A` be a Noetherian ring with a dualizing complex, let `T ⊆ Spec(A)` be stable under
specialization and let `M` be a finite `A`-module satisfying the depth-plus-dimension condition
of Faltings' criterion [Stacks, Tag 0EFC] at `s = n` across the boundary of `T`.  This file
proves that the locus

`B = { 𝔮 ∈ T : depth(M_𝔮) < n + 1 }`

is contained in a **closed** subset of `T`.  That is the datum
`AlgebraicGeometry.exists_isDepthTwoExtension_of_isClosed_of_subset` needs at `n = 1`, and it is
the only thing missing from the existence half of [Stacks, Tag 0EI3] along a
specialization-stable subset.

## The argument

[Stacks, Tag 0EFC] produces, for every specialization-stable `S ⊆ T` with the same boundary
condition, an ideal `J` with `V(J) ⊆ T` annihilating `H^i_S(M)` for all `i ≤ n`; so
`V(J) ⊇ Supp(H^i_S(M))` for those `i`.  And
`Stacks.LocalCohomology.exists_mem_support_localCohomologyWithSupportIn_of_depth_lt` puts every
point of `S` that is **minimal in `S`** and has `depth(M_𝔮) < n + 1` into one of those
supports.  So each such ideal catches the low-depth points minimal in its own `S`.

One `S` is not enough — a point of `B` need not be minimal in `T` — so the subsets
`T ⊇ T' ⊇ T'' ⊇ ⋯` of Tag 0EF8 are used, `T^{(k+1)}` being the primes of `T^{(k)}` that are not
minimal in `T^{(k)}`: each is stable under specialization by
`PrimeSpectrum.stableUnderSpecialization_nonminimalPrimes`, a prime of `T^{(k)}` has height at
least `k` (`Stacks.LocalCohomology.le_height_of_mem_nonminimalPrimes_iterate`), and consequently
every prime of `T` is minimal in `T^{(k)}` for some `k` bounded by its height
(`Stacks.LocalCohomology.exists_minimal_nonminimalPrimes_iterate`).  With the heights bounded by
`d` — which holds for a ring with a dualizing complex, those being finite-dimensional — the
closed set is the union of the `d + 1` zero loci `V(J_k)`.

## Main results

* `Stacks.LocalCohomology.le_height_of_mem_nonminimalPrimes_iterate` — a prime in the `k`-th
  iterated nonminimal locus of `T` has height at least `k`.
* `Stacks.LocalCohomology.exists_minimal_nonminimalPrimes_iterate` — every prime of `T` is
  minimal in one of the iterates, at an index bounded by `d`.
* `Stacks.LocalCohomology.exists_isClosed_subset_depth_lt_subset` — the low-depth locus of `T`
  lies in a closed subset of `T`.
* `Stacks.LocalCohomology.exists_isClosed_subset_depth_lt_two_subset` — the same at `n = 1`, with
  the depth-plus-dimension condition replaced by the hypothesis [Stacks, Tag 0EI3] carries: a
  depth bound at the primes outside `T` admitting an immediate specialization into `T`.

## What this does not do

The statement is about a ring.  [Stacks, Tag 0EI3] is about a scheme, and gluing these
affine-local closed sets into a closed subset of `X` contained in `T` is not done here; see the
module documentation of `SpecializationStableExistence.lean` under
`StacksFrontier/AlgebraicGeometry/LocalCohomology/ImprovingCoherentModules/`.

No `@[stacks]` attribute is placed: Tag 0EFC is
`Stacks.LocalCohomology.exists_ideal_le_annihilator_localCohomology_iff`, Tag 0EF8 is the exact
sequence of the minimal-prime filtration, and Tag 0EI3 is the scheme statement, of which this is
an affine-local input and not a covering set.

## References

* [Stacks Project, Tag 0EFC](https://stacks.math.columbia.edu/tag/0EFC)
* [Stacks Project, Tag 0EF8](https://stacks.math.columbia.edu/tag/0EF8)
* [Stacks Project, Tag 0EI3](https://stacks.math.columbia.edu/tag/0EI3)
-/

@[expose] public noncomputable section

open CategoryTheory IsLocalRing
open Stacks.Algebraization (enatToEInt krullDimToEInt)

universe u

attribute [local instance] HasDerivedCategory.standard

namespace Stacks.LocalCohomology

/-! ### The iterated nonminimal loci of a specialization-stable subset -/

/-- The `k`-th iterated nonminimal locus of a specialization-stable subset is again stable under
specialization. -/
public theorem stableUnderSpecialization_nonminimalPrimes_iterate {A : Type u} [CommRing A]
    {T : Set (PrimeSpectrum A)} (hT : StableUnderSpecialization T) (k : ℕ) :
    StableUnderSpecialization (PrimeSpectrum.nonminimalPrimes^[k] T) := by
  induction k with
  | zero => simpa using hT
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact PrimeSpectrum.stableUnderSpecialization_nonminimalPrimes ih

/-- The iterated nonminimal loci of `T` are contained in `T`. -/
public theorem nonminimalPrimes_iterate_subset {A : Type u} [CommRing A]
    (T : Set (PrimeSpectrum A)) (k : ℕ) : PrimeSpectrum.nonminimalPrimes^[k] T ⊆ T := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact (PrimeSpectrum.nonminimalPrimes_subset _).trans ih

/-- **A prime in the `k`-th iterated nonminimal locus of `T` has height at least `k`.** Each
iteration strips the primes minimal in what is left, so a prime surviving `k` of them carries a
strictly increasing chain of `k` primes of `T` below it, and
`Ideal.height_add_one_le_of_lt_of_isPrime` turns that chain into the height bound. -/
public theorem le_height_of_mem_nonminimalPrimes_iterate {A : Type u} [CommRing A]
    (T : Set (PrimeSpectrum A)) (k : ℕ) {p : PrimeSpectrum A}
    (hp : p ∈ PrimeSpectrum.nonminimalPrimes^[k] T) : (k : ℕ∞) ≤ p.asIdeal.height := by
  induction k generalizing p with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply'] at hp
    obtain ⟨-, q, hq, hqp⟩ := PrimeSpectrum.mem_nonminimalPrimes.mp hp
    calc ((k + 1 : ℕ) : ℕ∞) = (k : ℕ∞) + 1 := by push_cast; rfl
      _ ≤ q.asIdeal.height + 1 := by gcongr; exact ih hq
      _ ≤ p.asIdeal.height := Ideal.height_add_one_le_of_lt_of_isPrime hqp

/-- **Every prime of `T` is minimal in one of the iterated nonminimal loci of `T`.** The index is
bounded by any bound `d` for the heights of the primes of `A`: a prime lies in the `k`-th iterate
only for `k ≤ d` by `le_height_of_mem_nonminimalPrimes_iterate`, so the largest such `k` exists,
and at it the prime is no longer nonminimal. -/
public theorem exists_minimal_nonminimalPrimes_iterate {A : Type u} [CommRing A]
    (T : Set (PrimeSpectrum A)) (d : ℕ) {p : PrimeSpectrum A}
    (hd : p.asIdeal.height ≤ (d : ℕ∞)) (hp : p ∈ T) :
    ∃ k ≤ d, p ∈ PrimeSpectrum.nonminimalPrimes^[k] T \
      PrimeSpectrum.nonminimalPrimes (PrimeSpectrum.nonminimalPrimes^[k] T) := by
  classical
  have hbound : ∀ m : ℕ, p ∈ PrimeSpectrum.nonminimalPrimes^[m] T → m ≤ d := by
    intro m hm
    exact_mod_cast (le_height_of_mem_nonminimalPrimes_iterate T m hm).trans hd
  have h0 : p ∈ PrimeSpectrum.nonminimalPrimes^[0] T := by simpa using hp
  obtain ⟨k, hkle, hk, hnk⟩ : ∃ k : ℕ, k ≤ d ∧ p ∈ PrimeSpectrum.nonminimalPrimes^[k] T ∧
      p ∉ PrimeSpectrum.nonminimalPrimes^[k + 1] T := by
    refine ⟨Nat.findGreatest (fun m => p ∈ PrimeSpectrum.nonminimalPrimes^[m] T) d,
      Nat.findGreatest_le d,
      Nat.findGreatest_spec (P := fun m => p ∈ PrimeSpectrum.nonminimalPrimes^[m] T)
        (Nat.zero_le d) h0, fun hcon => ?_⟩
    exact Nat.findGreatest_is_greatest (P := fun m => p ∈ PrimeSpectrum.nonminimalPrimes^[m] T)
      (Nat.lt_succ_self _) (hbound _ hcon) hcon
  refine ⟨k, hkle, hk, fun hcon => hnk ?_⟩
  rw [Function.iterate_succ_apply']
  exact hcon

/-! ### The low-depth locus lies in a closed subset -/

/-- **The low-depth locus of a specialization-stable subset lies in a closed subset of it.** Let
`A` be a Noetherian ring with a dualizing complex, let `T ⊆ Spec(A)` be stable under
specialization, let `M` be a finite `A`-module, let `n : ℕ`, and suppose that
`depth(M_𝔭) + dim((A/𝔭)_𝔮) > n` for every pair `𝔭 ⊆ 𝔮` with `𝔭 ∉ T` and `𝔮 ∈ T` — the
depth-plus-dimension condition of [Stacks, Tag 0EFC].  Suppose moreover that `d` bounds the
heights of the primes of `A`, as it does when `A` has a dualizing complex.  Then there is a
closed `Z ⊆ T` containing every `𝔮 ∈ T` with `depth(M_𝔮) < n + 1`.

At `n = 1` this is the affine-local form of the closed subset that
`AlgebraicGeometry.exists_isDepthTwoExtension_of_isClosed_of_subset` takes as a hypothesis. -/
public theorem exists_isClosed_subset_depth_lt_subset
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (M : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M]
    (T : Set (PrimeSpectrum A)) (hT : StableUnderSpecialization T)
    (n d : ℕ) (hd : ∀ q : PrimeSpectrum A, q.asIdeal.height ≤ (d : ℕ∞))
    (omega : DerivedCategory (ModuleCat.{u} A))
    (homega : Dualizing.IsDualizingComplex (A := A) (K := omega))
    (hdepth : ∀ p q : PrimeSpectrum A, p ∉ T → q ∈ T → p.asIdeal ≤ q.asIdeal →
      enatToEInt
          (Module.depth (Localization.AtPrime p.asIdeal)
            (maximalIdeal (Localization.AtPrime p.asIdeal))
            (LocalizedModule p.asIdeal.primeCompl M)) +
        krullDimToEInt
          (ringKrullDim ((Localization.AtPrime q.asIdeal) ⧸
            p.asIdeal.map (algebraMap A (Localization.AtPrime q.asIdeal)))) > (n : EInt)) :
    ∃ Z : Set (PrimeSpectrum A), IsClosed Z ∧ Z ⊆ T ∧
      ∀ q : PrimeSpectrum A, q ∈ T →
        Module.depth (Localization.AtPrime q.asIdeal)
            (maximalIdeal (Localization.AtPrime q.asIdeal))
            (LocalizedModule q.asIdeal.primeCompl M) < (n : ℕ∞) + 1 → q ∈ Z := by
  classical
  have hJ : ∀ k : ℕ, ∃ J : Ideal A, PrimeSpectrum.zeroLocus (J : Set A) ⊆ T ∧
      ∀ i : ℤ, i ≤ (n : ℤ) → J ≤ Module.annihilator A
        (localCohomologyWithSupportIn.{u, u} A (PrimeSpectrum.nonminimalPrimes^[k] T)
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A M)) i) := by
    intro k
    refine (exists_ideal_le_annihilator_localCohomology_iff A M
      (PrimeSpectrum.nonminimalPrimes^[k] T) T (nonminimalPrimes_iterate_subset T k)
      (stableUnderSpecialization_nonminimalPrimes_iterate hT k) hT (n : ℤ)
      (Int.natCast_nonneg n) omega homega).2 fun p q hp hq hpq =>
      hdepth p q hp (nonminimalPrimes_iterate_subset T k hq) hpq
  choose J hJT hJann using hJ
  refine ⟨⋃ k ∈ Finset.range (d + 1), PrimeSpectrum.zeroLocus (J k : Set A),
    Set.Finite.isClosed_biUnion (Finset.range (d + 1)).finite_toSet
      fun k _ => PrimeSpectrum.isClosed_zeroLocus _,
    Set.iUnion₂_subset fun k _ => hJT k, fun q hq hdep => ?_⟩
  obtain ⟨k, hkd, hmin⟩ := exists_minimal_nonminimalPrimes_iterate T d (hd q) hq
  obtain ⟨i, hi, hsupp⟩ := exists_mem_support_localCohomologyWithSupportIn_of_depth_lt
    A (PrimeSpectrum.nonminimalPrimes^[k] T)
    (stableUnderSpecialization_nonminimalPrimes_iterate hT k) q hmin (ModuleCat.of A M)
    ((n : ℕ∞) + 1) hdep
  have hin : (i : ℤ) ≤ (n : ℤ) := by
    have : (i : ℕ∞) < (n : ℕ∞) + 1 := hi
    rw [← Nat.cast_one, ← Nat.cast_add, Nat.cast_lt] at this
    omega
  refine Set.mem_iUnion₂.mpr ⟨k, Finset.mem_range.mpr (by omega), ?_⟩
  rw [PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe]
  exact (hJann k (i : ℤ) hin).trans (Module.annihilator_le_of_mem_support hsupp)

/-- **The depth-one locus lies in a closed subset of `T`, at the hypotheses of
[Stacks, Tag 0EI3].** Let `A` be a Noetherian ring with a dualizing complex, let
`T ⊆ Spec(A)` be stable under specialization and let `M` be a finite `A`-module whose depth at a
prime `𝔭 ∉ T` is at least one whenever some prime of `T` is an immediate specialization of `𝔭`.
Suppose `d` bounds the heights of the primes of `A`.  Then there is a closed `Z ⊆ T` containing
every `𝔮 ∈ T` with `depth(M_𝔮) < 2`.

This is `Stacks.LocalCohomology.exists_isClosed_subset_depth_lt_subset` at `n = 1`, whose
depth-plus-dimension clause at `s = 1` is
`Stacks.LocalCohomology.one_lt_depth_add_height_quotient_of_depth_immediate`; it is the
affine-local form of the closed subset
`AlgebraicGeometry.exists_isDepthTwoExtension_of_isClosed_of_subset` takes as a hypothesis, and
its hypotheses are exactly the two that [Stacks, Tag 0EI3] carries. -/
public theorem exists_isClosed_subset_depth_lt_two_subset
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (M : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M]
    (T : Set (PrimeSpectrum A)) (hT : StableUnderSpecialization T)
    (d : ℕ) (hd : ∀ q : PrimeSpectrum A, q.asIdeal.height ≤ (d : ℕ∞))
    (omega : DerivedCategory (ModuleCat.{u} A))
    (homega : Dualizing.IsDualizingComplex (A := A) (K := omega))
    (hdepth : ∀ p q : PrimeSpectrum A, p ∉ T → q ∈ T →
      TopologicalSpace.IsImmediateSpecialization p q →
      (1 : ℕ∞) ≤ Module.depth (Localization.AtPrime p.asIdeal)
        (maximalIdeal (Localization.AtPrime p.asIdeal))
        (LocalizedModule p.asIdeal.primeCompl M)) :
    ∃ Z : Set (PrimeSpectrum A), IsClosed Z ∧ Z ⊆ T ∧
      ∀ q : PrimeSpectrum A, q ∈ T →
        Module.depth (Localization.AtPrime q.asIdeal)
            (maximalIdeal (Localization.AtPrime q.asIdeal))
            (LocalizedModule q.asIdeal.primeCompl M) < 2 → q ∈ Z := by
  obtain ⟨Z, hZclosed, hZT, hZ⟩ :=
    exists_isClosed_subset_depth_lt_subset A M T hT 1 d hd omega homega
      fun p q hp hq hpq => by
        rw [ringKrullDim_localization_quotient_eq_height p q hpq]
        refine (natCast_lt_add_iff_eint 1 _ _).1 ?_
        exact_mod_cast
          one_lt_depth_add_height_quotient_of_depth_immediate A T M hdepth p q hp hq hpq
  refine ⟨Z, hZclosed, hZT, fun q hq hdep => hZ q hq (lt_of_lt_of_le hdep ?_)⟩
  norm_num

end Stacks.LocalCohomology

end
