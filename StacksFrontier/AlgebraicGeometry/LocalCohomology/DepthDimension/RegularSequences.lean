module

public import Mathlib.RingTheory.Localization.Module
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import StacksFrontier.RingTheory.Depth.Defs.Defs
public import StacksFrontier.RingTheory.Sequence.Regular.Basic

/-!
# Regular sequences under localization

Tools for transporting a regular sequence from one localization of a module to another. The main
one says that a sequence which is regular on `M` localized at `p` stays regular on `M` localized
at any prime `q ⊇ p` at which a suitable element of the ring is invertible.

## Main results

* `Module.isRegular_map_mul_unit`: multiplying every term of a regular sequence by a unit leaves
  it regular.
* `Module.subsingleton_localized_of_le`: a vanishing localization keeps vanishing when the
  submonoid grows.
* `Module.weaklyRegular_of_localized_kernels`: a sequence is weakly regular on a localization as
  soon as the relevant multiplication kernels localize to zero.
* `Module.regular_sequence_at_specialization`: regularity propagates from `p` to a prime above it
  on a basic open set.
* `Module.length_le_depth_of_regular`: the length of a regular sequence in `I` bounds the
  `I`-depth from below.

## Implementation notes

The sequences are lists of elements of the base ring, mapped into the localization by
`algebraMap`; this keeps a single list in play on both sides of a specialization, which is what
makes the comparison of depths possible.

## References

* [Stacks Project, Tag 0DWX](https://stacks.math.columbia.edu/tag/0DWX)
* [Stacks Project, Tag 0DWY](https://stacks.math.columbia.edu/tag/0DWY)
-/

@[expose] public section

universe u v

namespace Module

/-- Multiplying every term of a regular sequence by a unit of the ring leaves it regular. -/
theorem isRegular_map_mul_unit
    {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
    {xs : List R} (h : RingTheory.Sequence.IsRegular M xs)
    {u : R} (hu : IsUnit u) :
    RingTheory.Sequence.IsRegular M (xs.map (u * ·)) := by
  refine ⟨?_, ?_⟩
  · apply RingTheory.Sequence.IsWeaklyRegular.mk
    intro i hi
    simp only [List.getElem_map]
    rw [← List.map_take, Ideal.ofList_map_mul_unit hu]
    exact (hu.isSMulRegular _).mul (h.regular_mod_prev i (by simpa using hi))
  · simpa only [Ideal.ofList_map_mul_unit hu] using h.top_ne_smul

/-- If a module localizes to zero at a submonoid, it localizes to zero at any larger one. -/
theorem subsingleton_localized_of_le
    {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
    {S T : Submonoid R} (hST : S ≤ T)
    (h : Subsingleton (LocalizedModule S M)) :
    Subsingleton (LocalizedModule T M) := by
  rw [LocalizedModule.subsingleton_iff] at h ⊢
  intro m
  obtain ⟨s, hs, hz⟩ := h m
  exact ⟨s, hST hs, hz⟩

/-- A sequence is weakly regular on the localization of `M` at `T` as soon as, for each index,
the kernel of multiplication by that term on the partial quotient localizes to zero at `T`. -/
theorem weaklyRegular_of_localized_kernels
    {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
    (T : Submonoid R) (xs : List R)
    (hker : ∀ i (hi : i < xs.length),
      Subsingleton (LocalizedModule T
        (LinearMap.ker (LinearMap.lsmul R
          (M ⧸ (Ideal.ofList (xs.take i) • ⊤ : Submodule R M)) xs[i])))) :
    RingTheory.Sequence.IsWeaklyRegular (LocalizedModule T M) xs := by
  apply RingTheory.Sequence.IsWeaklyRegular.mk
  intro i hi
  set J : Ideal R := Ideal.ofList (xs.take i)
  rw [LinearEquiv.isSMulRegular_congr ((Submodule.quotEquivOfEq _ _
    (restrictScalars_localized_smul_top T J).symm).trans
      (Submodule.Quotient.restrictScalarsEquiv R _)) xs[i]]
  set φ := Submodule.toLocalizedQuotient T (J • (⊤ : Submodule R M)) with hφ
  have hloc : IsLocalizedModule T φ := by
    rw [hφ]
    infer_instance
  refine isSMulRegular_iff_right_eq_zero_of_smul.mpr fun y hy => ?_
  obtain ⟨⟨m, s⟩, rfl⟩ := IsLocalizedModule.mk'_surjective T φ y
  simp only [Function.uncurry] at *
  rw [← IsLocalizedModule.mk'_smul, IsLocalizedModule.mk'_eq_zero, hφ,
    IsLocalizedModule.eq_zero_iff T
      (Submodule.toLocalizedQuotient T (J • (⊤ : Submodule R M)))] at hy
  obtain ⟨t, ht⟩ := hy
  have hmem : t.val • m ∈ LinearMap.ker
      (LinearMap.lsmul R (M ⧸ (J • ⊤ : Submodule R M)) xs[i]) := by
    rw [LinearMap.mem_ker]
    simp only [LinearMap.lsmul_apply]
    rw [smul_comm] at ht
    exact ht
  obtain ⟨r, hrmem, hr⟩ :=
    (LocalizedModule.subsingleton_iff.mp (hker i hi)) ⟨t.val • m, hmem⟩
  have hr' : r • (t.val • m) = 0 := by simpa using congrArg Subtype.val hr
  rw [IsLocalizedModule.mk'_eq_zero, hφ,
    IsLocalizedModule.eq_zero_iff T (Submodule.toLocalizedQuotient T (J • (⊤ : Submodule R M)))]
  refine ⟨⟨r, hrmem⟩ * t, ?_⟩
  simp only [mul_smul]
  exact hr'

/-- A sequence regular on `M` localized at `p` remains regular on `M` localized at a prime
`q ⊇ p`, provided the relevant multiplication kernels die after inverting an element `g ∉ q`. -/
theorem regular_sequence_at_specialization
    {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
    (p q : PrimeSpectrum R) (hpq : p.asIdeal ≤ q.asIdeal)
    (xs : List R)
    (hregp : RingTheory.Sequence.IsRegular (LocalizedModule p.asIdeal.primeCompl M)
      (xs.map (algebraMap R (Localization.AtPrime p.asIdeal))))
    (g : R) (hgq : g ∉ q.asIdeal)
    (hker : ∀ i (hi : i < xs.length),
      Subsingleton (LocalizedModule (Submonoid.powers g)
        (LinearMap.ker (LinearMap.lsmul R
          (M ⧸ (Ideal.ofList (xs.take i) • ⊤ : Submodule R M)) xs[i])))) :
    RingTheory.Sequence.IsRegular (LocalizedModule q.asIdeal.primeCompl M)
      (xs.map (algebraMap R (Localization.AtPrime q.asIdeal))) := by
  let Q := M ⧸ (Ideal.ofList xs • (⊤ : Submodule R M))
  have key : ∀ P : PrimeSpectrum R, (⊤ : Submodule (Localization.AtPrime P.asIdeal)
      (LocalizedModule P.asIdeal.primeCompl M)) ≠
        Ideal.ofList (xs.map (algebraMap R (Localization.AtPrime P.asIdeal))) • ⊤ ↔
      ¬ Subsingleton (LocalizedModule P.asIdeal.primeCompl Q) := fun P => by
    obtain ⟨e⟩ := nonempty_localizedModule_quotient_ofList_equiv
      (M := M) xs P.asIdeal.primeCompl
    rw [ne_comm, ne_eq, ← Submodule.Quotient.subsingleton_iff, not_iff_not]
    exact (Equiv.subsingleton_congr e.toEquiv).symm
  refine ⟨(RingTheory.Sequence.isWeaklyRegular_map_algebraMap_iff
    (Localization.AtPrime q.asIdeal) _ xs).mpr
      (weaklyRegular_of_localized_kernels q.asIdeal.primeCompl xs fun i hi =>
        subsingleton_localized_of_le (Submonoid.powers_le.mpr hgq) (hker i hi)),
    (key q).mpr fun hs => (key p).mp hregp.top_ne_smul ?_⟩
  exact subsingleton_localized_of_le
    (S := q.asIdeal.primeCompl) (fun _ hx hxp => hx (hpq hxp)) hs

/-- The length of a regular sequence drawn from `I` is a lower bound for the `I`-depth. -/
theorem length_le_depth_of_regular
    {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
    {J : Ideal R} {xs : List R} (hmem : ∀ x ∈ xs, x ∈ J)
    (hreg : RingTheory.Sequence.IsRegular M xs) :
    (xs.length : ℕ∞) ≤ Module.depth R J M := by
  rw [Module.depth]
  split_ifs
  · exact le_top
  · exact le_iSup₂_of_le xs ⟨hmem, hreg⟩ le_rfl

end Module
