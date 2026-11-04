module

public import StacksFrontier.AlgebraicGeometry.LocalCohomology.DepthDimension.RegularSequences
public import StacksFrontier.RingTheory.Depth.Criteria
public import StacksFrontier.RingTheory.Serre.Defs
public import StacksFrontier.RingTheory.Ideal.AssociatedPrime.Basic
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Localization
public import StacksCore.Tactic.StacksAttribute

/-!
# Depth along specializations

For a finite module over a Noetherian ring, depth at a prime cannot decrease on a suitable
nonempty open subset of the closure of that prime. Moreover, away from finitely many points of
that open subset the depth strictly increases.

## Main results

* `Module.exists_open_depth_localization_ge_and_finite_exceptional` produces the open subset on
  which the localized depth is at least its value at the original prime, with only finitely many
  failures of the strict inequality.

## Implementation notes

The closure `V(p)` is represented by the subtype `PrimeSpectrum.zeroLocus (p.asIdeal : Set A)`,
so `IsOpen` refers to its subspace topology. "All but finitely many" is expressed by finiteness
of the set of points of the open subset at which the strict inequality fails.

## References

* [Stacks Project, Tag 0DWY](https://stacks.math.columbia.edu/tag/0DWY)
-/

@[expose] public section

open IsLocalRing

universe u v

namespace Module

/-- A list of elements of a localization can be cleared of denominators simultaneously: after
multiplying by one common denominator it comes from a list upstairs. -/
private theorem list_common_denominator
    {R : Type*} [CommRing R] (S : Submonoid R) (ys : List (Localization S)) :
    ∃ s : S, ∃ xs : List R,
      xs.length = ys.length ∧
      xs.map (algebraMap R (Localization S)) =
        ys.map ((algebraMap R (Localization S) s.val) * ·) := by
  induction ys with
  | nil => exact ⟨1, [], rfl, rfl⟩
  | cons y ys ih =>
    obtain ⟨a, t, rfl⟩ := IsLocalization.exists_mk'_eq S y
    obtain ⟨s, xs, hlen, hxs⟩ := ih
    refine ⟨t * s, (a * s.val) :: xs.map (t.val * ·), by simp [hlen], ?_⟩
    simp only [List.map_cons, List.map_map, Function.comp_def, map_mul,
      Submonoid.coe_mul, List.cons.injEq]
    have hhead : (algebraMap R (Localization S)) a *
        (algebraMap R (Localization S)) s.val =
        ((algebraMap R (Localization S)) t.val *
          (algebraMap R (Localization S)) s.val) *
          IsLocalization.mk' (Localization S) a t := by
      rw [← (IsLocalization.mk'_spec' (Localization S) a t)]
      ring
    refine ⟨hhead, ?_⟩
    simpa only [List.map_map, Function.comp_def, mul_assoc, mul_left_comm, mul_comm]
      using congrArg (List.map ((algebraMap R (Localization S)) t.val * ·)) hxs

private theorem map_algebraMap_mem_maximalIdeal {R : Type*} [CommRing R] (p : Ideal R)
    [p.IsPrime] {xs : List R} (h : ∀ x ∈ xs, x ∈ p) :
    ∀ y ∈ xs.map (algebraMap R (Localization.AtPrime p)),
      y ∈ maximalIdeal (Localization.AtPrime p) := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
  exact (IsLocalization.AtPrime.to_map_mem_maximal_iff _ p x).mpr (h x hx)

/-- If the depth of `Mₚ` at the maximal ideal equals `e`, then `e` elements of `p` form a regular
sequence on `Mₚ` after mapping them into the localization. -/
private theorem exists_regular_sequence_at_prime
    {R : Type*} [CommRing R] [IsNoetherianRing R]
    {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M]
    (p : Ideal R) [p.IsPrime] (e : ℕ)
    (he : Module.depth (Localization.AtPrime p)
      (maximalIdeal (Localization.AtPrime p))
      (LocalizedModule p.primeCompl M) = (e : ℕ∞)) :
    ∃ xs : List R, xs.length = e ∧ (∀ x ∈ xs, x ∈ p) ∧
      RingTheory.Sequence.IsRegular (LocalizedModule p.primeCompl M)
        (xs.map (algebraMap R (Localization.AtPrime p))) := by
  let S := Localization.AtPrime p
  let N := LocalizedModule p.primeCompl M
  have hnon : maximalIdeal S • (⊤ : Submodule S N) ≠ ⊤ := by
    intro h
    have htop : Module.depth S (maximalIdeal S) N = ⊤ := by
      simp [Module.depth, h]
    exact ENat.natCast_ne_top e (he.symm.trans htop)
  have hbot : (⊤ : Submodule S N) ≠ ⊥ := fun h => hnon (by simp [h])
  have hnil : RingTheory.Sequence.IsRegular N ([] : List S) := by
    refine ⟨RingTheory.Sequence.IsWeaklyRegular.nil S N, ?_⟩
    simpa using hbot
  obtain ⟨ys, hymem, hyreg, hylen⟩ :=
    (Module.depth_quotSMulTop_succ_eq_depth_and_exists_isRegular_append
      (maximalIdeal S) N).2 hnon [] (by simp) hnil
  obtain ⟨t, xs, hlen, hxs⟩ := list_common_denominator p.primeCompl ys
  refine ⟨xs, ?_, ?_, ?_⟩
  · have hylen' : (ys.length : ℕ∞) = (e : ℕ∞) := by
      simpa only [List.nil_append] using hylen.trans he
    exact hlen.trans (by exact_mod_cast hylen')
  · intro x hx
    have hxmap : (algebraMap R S) x ∈
        ys.map ((algebraMap R S) t.val * ·) := by
      rw [← hxs]
      exact List.mem_map_of_mem hx
    obtain ⟨y, hy, hxy⟩ := List.mem_map.mp hxmap
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff S p x).mp
      (hxy ▸ Ideal.mul_mem_left _ _ (hymem y (by simpa using hy)))
  · rw [hxs]
    exact isRegular_map_mul_unit (by simpa using hyreg)
      (IsLocalization.map_units S t)

/-- A sequence of elements of `q` that is regular on the localization at `q` after mapping has
length at most the depth at `q`. -/
private theorem length_le_depth_localized {R : Type*} [CommRing R] [IsNoetherianRing R]
    {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M]
    (q : Ideal R) [q.IsPrime] {xs : List R} (hmem : ∀ x ∈ xs, x ∈ q)
    (hreg : RingTheory.Sequence.IsRegular (LocalizedModule q.primeCompl M)
      (xs.map (algebraMap R (Localization.AtPrime q)))) :
    (xs.length : ℕ∞) ≤ Module.depth (Localization.AtPrime q) (maximalIdeal (Localization.AtPrime q))
      (LocalizedModule q.primeCompl M) := by
  simpa only [List.length_map] using
    length_le_depth_of_regular (map_algebraMap_mem_maximalIdeal q hmem) hreg

/-- If `q` is not an associated prime of `Q`, some element of `q` acts regularly on the
localization of `Q` at `q`. -/
private theorem exists_mem_regular_localized_of_not_associated
    {R : Type*} [CommRing R] [IsNoetherianRing R]
    {Q : Type*} [AddCommGroup Q] [Module R Q] [Module.Finite R Q]
    (q : PrimeSpectrum R) (hq : q.asIdeal ∉ associatedPrimes R Q) :
    ∃ x ∈ q.asIdeal, IsSMulRegular (LocalizedModule q.asIdeal.primeCompl Q) x := by
  let S := Localization.AtPrime q.asIdeal
  let N := LocalizedModule q.asIdeal.primeCompl Q
  have hpos : 1 ≤ Module.depth S (maximalIdeal S) N :=
    ENat.one_le_iff_ne_zero.mpr fun h => hq ((depth_localized_eq_zero_iff q).mp h)
  obtain ⟨z, hzmem, hzreg⟩ :=
    (one_le_depth_iff_exists_isSMulRegular (maximalIdeal S)).mp hpos
  obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq q.asIdeal.primeCompl z
  have hmap : (algebraMap R S) a = (algebraMap R S) s.val *
      IsLocalization.mk' S a s := (IsLocalization.mk'_spec' S a s).symm
  refine ⟨a, (IsLocalization.AtPrime.to_map_mem_maximal_iff S q.asIdeal a).mp ?_, ?_⟩
  · exact hmap ▸ Ideal.mul_mem_left _ _ hzmem
  · have hreg : IsSMulRegular N ((algebraMap R S) a) := by
      rw [hmap]
      exact (IsLocalization.map_units S s).isSMulRegular N |>.mul hzreg
    simpa only [IsSMulRegular, algebraMap_smul] using hreg

/-- A regular sequence of length `n` in `q` whose quotient does not have `q` as an associated
prime extends, so the depth at `q` exceeds `n` strictly. -/
private theorem depth_strict_of_regular_and_not_associated
    {R : Type*} [CommRing R] [IsNoetherianRing R]
    {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M]
    (q : PrimeSpectrum R) (xs : List R)
    (hmem : ∀ x ∈ xs, x ∈ q.asIdeal)
    (hreg : RingTheory.Sequence.IsRegular (LocalizedModule q.asIdeal.primeCompl M)
      (xs.map (algebraMap R (Localization.AtPrime q.asIdeal))))
    (hnot : q.asIdeal ∉ associatedPrimes R
      (M ⧸ (Ideal.ofList xs • (⊤ : Submodule R M)))) :
    (xs.length : ℕ∞) < Module.depth (Localization.AtPrime q.asIdeal)
      (maximalIdeal (Localization.AtPrime q.asIdeal))
      (LocalizedModule q.asIdeal.primeCompl M) := by
  let S := Localization.AtPrime q.asIdeal
  let N := LocalizedModule q.asIdeal.primeCompl M
  obtain ⟨x, hxq, hxreg⟩ := exists_mem_regular_localized_of_not_associated q hnot
  obtain ⟨e⟩ := nonempty_localizedModule_quotient_ofList_equiv
    (M := M) xs q.asIdeal.primeCompl
  have hxreg' : IsSMulRegular
      (N ⧸ (Ideal.ofList (xs.map (algebraMap R S)) • ⊤ : Submodule S N))
      (algebraMap R S x) := by
    simpa only [IsSMulRegular, algebraMap_smul] using
      (LinearEquiv.isSMulRegular_congr e x).mp hxreg
  have hwr : RingTheory.Sequence.IsWeaklyRegular N
      ((xs ++ [x]).map (algebraMap R S)) := by
    rw [List.map_append]
    exact (RingTheory.Sequence.isWeaklyRegular_append_iff N _ _).mpr ⟨hreg.toIsWeaklyRegular,
      (RingTheory.Sequence.isWeaklyRegular_singleton_iff _ _).mpr hxreg'⟩
  have : Nontrivial N := hreg.nontrivial
  have hmem' : ∀ a ∈ xs ++ [x], a ∈ q.asIdeal := fun a ha =>
    (List.mem_append.mp ha).elim (hmem a) fun h => List.mem_singleton.mp h ▸ hxq
  have hreg' : RingTheory.Sequence.IsRegular N ((xs ++ [x]).map (algebraMap R S)) :=
    (IsLocalRing.isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal
      (map_algebraMap_mem_maximalIdeal q.asIdeal hmem')).mpr hwr
  exact (Nat.cast_lt.mpr (by simp)).trans_le (length_le_depth_localized q.asIdeal hmem' hreg')

/-- **Stacks Project, Tag 0DWY.** If the localization of a finite module over a Noetherian ring
has finite depth `e` at `p`, then on a nonempty open subset of `V(p)` its depth is at least `e`,
and is strictly greater than `e` except at finitely many points. -/
@[stacks 0DWY]
theorem exists_open_depth_localization_ge_and_finite_exceptional
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {M : Type v} [AddCommGroup M] [Module A M] [Module.Finite A M]
    (p : PrimeSpectrum A) (e : ℕ)
    (he : Module.depth (Localization.AtPrime p.asIdeal)
      (maximalIdeal (Localization.AtPrime p.asIdeal))
      (LocalizedModule p.asIdeal.primeCompl M) = (e : ℕ∞)) :
    let depthAt := fun q : PrimeSpectrum A ↦
      Module.depth (Localization.AtPrime q.asIdeal)
        (maximalIdeal (Localization.AtPrime q.asIdeal))
        (LocalizedModule q.asIdeal.primeCompl M)
    ∃ U : Set ↑(PrimeSpectrum.zeroLocus (p.asIdeal : Set A)),
      IsOpen U ∧ U.Nonempty ∧
        (∀ q ∈ U, (e : ℕ∞) ≤ depthAt q.1) ∧
        Set.Finite {q | q ∈ U ∧ ¬ (e : ℕ∞) < depthAt q.1} := by
  classical
  obtain ⟨xs, hlen, hmem, hregp⟩ := exists_regular_sequence_at_prime p.asIdeal e he
  obtain ⟨g, hgp, hker, _⟩ := L_choose_g p.asIdeal xs hregp
  let U : Set ↑(PrimeSpectrum.zeroLocus (p.asIdeal : Set A)) :=
    Subtype.val ⁻¹' PrimeSpectrum.basicOpen g
  have hspec : ∀ q ∈ U, (∀ x ∈ xs, x ∈ q.1.asIdeal) ∧
      RingTheory.Sequence.IsRegular (LocalizedModule q.1.asIdeal.primeCompl M)
        (xs.map (algebraMap A (Localization.AtPrime q.1.asIdeal))) := fun q hq => by
    have hpq : p.asIdeal ≤ q.1.asIdeal := (PrimeSpectrum.mem_zeroLocus q.1 _).mp q.2
    exact ⟨fun x hx => hpq (hmem x hx), regular_sequence_at_specialization p q.1 hpq xs hregp g
      ((PrimeSpectrum.mem_basicOpen g q.1).mp hq) hker⟩
  refine ⟨U, ?_, ?_, ?_, ?_⟩
  · exact PrimeSpectrum.isOpen_basicOpen.preimage continuous_subtype_val
  · exact ⟨⟨p, (PrimeSpectrum.mem_zeroLocus p _).mpr fun _ hx => hx⟩,
      (PrimeSpectrum.mem_basicOpen g p).mpr hgp⟩
  · intro q hq
    obtain ⟨hmemq, hregq⟩ := hspec q hq
    simpa only [hlen] using length_le_depth_localized q.1.asIdeal hmemq hregq
  · let Q := M ⧸ (Ideal.ofList xs • (⊤ : Submodule A M))
    have hfin : {q : ↑(PrimeSpectrum.zeroLocus (p.asIdeal : Set A)) |
        q.1.asIdeal ∈ associatedPrimes A Q}.Finite :=
      Set.Finite.preimage
        (f := fun q : ↑(PrimeSpectrum.zeroLocus (p.asIdeal : Set A)) => q.1.asIdeal)
        (fun q _ r _ h => Subtype.ext (PrimeSpectrum.ext h))
        (associatedPrimes.finite A Q)
    refine hfin.subset fun q hq => ?_
    by_contra hn
    obtain ⟨hmemq, hregq⟩ := hspec q hq.1
    exact hq.2 (hlen ▸ depth_strict_of_regular_and_not_associated q.1 xs hmemq hregq hn)

end Module
