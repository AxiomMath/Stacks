module

public import StacksFrontier.AlgebraicGeometry.LocalCohomology.DepthDimension.RegularSequences
public import StacksFrontier.RingTheory.Depth.Criteria
public import Mathlib.RingTheory.Localization.Ideal
public import StacksCore.Tactic.StacksAttribute

/-!
# Depth along an ideal near a prime

Let `I` be an ideal of a Noetherian ring `A` and `M` a finite `A`-module. If the depth of `M`
along `I` at a prime `p` containing `I` is finite, then on a nonempty open subset of the closure
of `p` the depth is at least its value at `p`.

## Main results

* `Module.exists_open_depth_localization_ge` produces this open subset.

## Implementation notes

The closure `V(p)` carries its subspace topology, so an open subset of it need not be open in the
whole prime spectrum. The extension of `I` to each local ring is expressed by `Ideal.map` along
the localization map.

## References

* [Stacks Project, Tag 0DWX](https://stacks.math.columbia.edu/tag/0DWX)
-/

@[expose] public section

universe u v

namespace Module

/-- Every element of a list of elements of a localization can be cleared of denominators
simultaneously: after multiplying by one common denominator the list comes from a list of
elements of the ideal `I` upstairs. -/
private theorem list_common_denominator_in_ideal
    {R : Type*} [CommRing R] (S : Submonoid R) (I : Ideal R)
    (ys : List (Localization S))
    (hmem : ∀ y ∈ ys, y ∈ I.map (algebraMap R (Localization S))) :
    ∃ s : S, ∃ xs : List I,
      xs.length = ys.length ∧
      xs.map (algebraMap R (Localization S) ∘ Subtype.val) =
        ys.map ((algebraMap R (Localization S) s.val) * ·) := by
  induction ys with
  | nil => exact ⟨1, [], rfl, rfl⟩
  | cons y ys ih =>
    obtain ⟨⟨a, t⟩, hyt⟩ :=
      (IsLocalization.mem_map_algebraMap_iff S (Localization S)).mp (hmem y List.mem_cons_self)
    obtain ⟨s, xs, hlen, hxs⟩ := ih fun z hz => hmem z (List.mem_cons_of_mem y hz)
    refine ⟨t * s, ⟨a.val * s.val, I.mul_mem_right _ a.property⟩ :: xs.map
      (fun x => ⟨t.val * x.val, I.mul_mem_left _ x.property⟩), by simp [hlen], ?_⟩
    simp only [List.map_cons, List.map_map, Function.comp_def, map_mul, Submonoid.coe_mul,
      List.cons.injEq]
    refine ⟨?_, ?_⟩
    · rw [← hyt]
      ring
    · simpa [List.map_map, Function.comp_def, mul_assoc, mul_left_comm, mul_comm]
        using congrArg (List.map ((algebraMap R (Localization S)) t.val * ·)) hxs

/-- If the depth of `Mₚ` along the extension of `I` equals `e`, then `e` elements of `I` form a
regular sequence on `Mₚ` after mapping them into the localization. -/
private theorem exists_regular_sequence_at_prime_for_ideal
    {R : Type*} [CommRing R] [IsNoetherianRing R]
    {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M]
    (I : Ideal R) (p : Ideal R) [p.IsPrime] (e : ℕ)
    (he : Module.depth (Localization.AtPrime p)
      (I.map (algebraMap R (Localization.AtPrime p)))
      (LocalizedModule p.primeCompl M) = (e : ℕ∞)) :
    ∃ xs : List R, xs.length = e ∧ (∀ x ∈ xs, x ∈ I) ∧
      RingTheory.Sequence.IsRegular (LocalizedModule p.primeCompl M)
        (xs.map (algebraMap R (Localization.AtPrime p))) := by
  let S := Localization.AtPrime p
  let N := LocalizedModule p.primeCompl M
  let J := I.map (algebraMap R S)
  have hnon : J • (⊤ : Submodule S N) ≠ ⊤ := by
    intro h
    have htop : Module.depth S J N = ⊤ := by simp [Module.depth, h]
    exact ENat.natCast_ne_top e (he.symm.trans htop)
  have hbot : (⊤ : Submodule S N) ≠ ⊥ := fun h => hnon (by simp [h])
  have hnil : RingTheory.Sequence.IsRegular N ([] : List S) :=
    ⟨RingTheory.Sequence.IsWeaklyRegular.nil S N, by simpa using hbot⟩
  obtain ⟨ys, hymem, hyreg, hylen⟩ :=
    (Module.depth_quotSMulTop_succ_eq_depth_and_exists_isRegular_append J N).2
      hnon [] (by simp) hnil
  obtain ⟨s, xs, hlen, hxs⟩ :=
    list_common_denominator_in_ideal p.primeCompl I ys hymem
  refine ⟨xs.map Subtype.val, ?_, ?_, ?_⟩
  · have hylen' : (ys.length : ℕ∞) = (e : ℕ∞) := by
      simpa only [List.nil_append] using hylen.trans he
    simpa using hlen.trans (by exact_mod_cast hylen')
  · intro x hx
    obtain ⟨xI, -, rfl⟩ := List.mem_map.mp hx
    exact xI.property
  · have hseq : ((xs.map Subtype.val).map (algebraMap R S)) =
        ys.map ((algebraMap R S s.val) * ·) := by
      simpa only [List.map_map, Function.comp_def] using hxs
    rw [hseq]
    exact isRegular_map_mul_unit (by simpa using hyreg)
      (IsLocalization.map_units S s)

/-- **Stacks Project, Tag 0DWX.** If `I ⊆ p` and the depth of the finite module `M` along `I` at
`p` is `e`, then the localized depth is at least `e` on a nonempty open subset of `V(p)`. -/
@[stacks 0DWX]
theorem exists_open_depth_localization_ge
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {M : Type v} [AddCommGroup M] [Module A M] [Module.Finite A M]
    (I : Ideal A) (p : PrimeSpectrum A) (_hIp : I ≤ p.asIdeal) (e : ℕ)
    (he : Module.depth (Localization.AtPrime p.asIdeal)
      (Ideal.map (algebraMap A (Localization.AtPrime p.asIdeal)) I)
      (LocalizedModule p.asIdeal.primeCompl M) = (e : ℕ∞)) :
    let depthAt := fun q : PrimeSpectrum A ↦
      Module.depth (Localization.AtPrime q.asIdeal)
        (Ideal.map (algebraMap A (Localization.AtPrime q.asIdeal)) I)
        (LocalizedModule q.asIdeal.primeCompl M)
    ∃ U : Set ↑(PrimeSpectrum.zeroLocus (p.asIdeal : Set A)),
      IsOpen U ∧ U.Nonempty ∧
        ∀ q ∈ U, (e : ℕ∞) ≤ depthAt q.1 := by
  classical
  obtain ⟨xs, hlen, hmem, hregp⟩ :=
    exists_regular_sequence_at_prime_for_ideal I p.asIdeal e he
  obtain ⟨g, hgp, hker, _⟩ := L_choose_g p.asIdeal xs hregp
  let U : Set ↑(PrimeSpectrum.zeroLocus (p.asIdeal : Set A)) :=
    Subtype.val ⁻¹' PrimeSpectrum.basicOpen g
  refine ⟨U, PrimeSpectrum.isOpen_basicOpen.preimage continuous_subtype_val,
    ⟨⟨p, (PrimeSpectrum.mem_zeroLocus p _).mpr fun _ hx => hx⟩,
      (PrimeSpectrum.mem_basicOpen g p).mpr hgp⟩, ?_⟩
  · intro q hq
    have hregq := regular_sequence_at_specialization p q.1
      ((PrimeSpectrum.mem_zeroLocus q.1 _).mp q.2) xs hregp g
      ((PrimeSpectrum.mem_basicOpen g q.1).mp hq) hker
    have hbound := length_le_depth_of_regular
      (J := I.map (algebraMap A (Localization.AtPrime q.1.asIdeal)))
      (xs := xs.map (algebraMap A (Localization.AtPrime q.1.asIdeal)))
      (by
        intro y hy
        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
        exact Ideal.mem_map_of_mem _ (hmem x hx)) hregq
    simpa only [List.length_map, hlen] using hbound

end Module
