module

public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import StacksCore.Tactic.StacksAttribute

/-!
# Standard open coverings of a prime spectrum

A *standard open covering* of a standard open `D(f)` in the prime spectrum of a commutative
ring is a finite family of elements whose standard opens have supremum `D(f)`; taking `f = 1`
gives a standard open covering of the whole spectrum.

This file collects the basic facts about such coverings. A standard open is covered by a
family of standard opens exactly when the covering elements generate the unit ideal after
localizing away from it, every open cover of a standard open admits a finite refinement by
standard opens, and a containment `D(g) ≤ D(f)` is witnessed both by a divisibility relation
between a power of `g` and `f` and by the invertibility of `f` after localizing away from `g`.

## Main definitions

* `PrimeSpectrum.IsStandardOpenCover`: a finite family of elements whose standard opens cover a
  specified standard open.
* `PrimeSpectrum.IsStandardOpenCoverOfSpectrum`: the specialization to the whole spectrum.

## Main results

* `PrimeSpectrum.basicOpen_le_iSup_iff_span_algebraMap_eq_top`: a standard open is contained in
  a union of standard opens exactly when the latter generate the unit ideal in its localization.
* `PrimeSpectrum.exists_finite_basicOpen_refinement`: every open cover of a standard open has a
  finite refinement by standard opens.
* `PrimeSpectrum.exists_pow_eq_mul_of_basicOpen_le`: a containment of standard opens makes a
  positive power of one element a multiple of the other.

## References

* [Stacks Project, Tag 01HS](https://stacks.math.columbia.edu/tag/01HS)
* [Stacks Project, Tag 01HT](https://stacks.math.columbia.edu/tag/01HT)
-/

@[expose] public section

open TopologicalSpace

add_to_stacks 01HS "invertible_on_smaller_open"
  PrimeSpectrum.basicOpen_le_basicOpen_iff_algebraMap_isUnit
add_to_ega "I 1.3.2" "(a) ⇔ (f)" PrimeSpectrum.basicOpen_le_basicOpen_iff_algebraMap_isUnit

namespace PrimeSpectrum

universe u v w

/-- A family `D(g i)`, indexed by `Fin n`, is a standard open covering of `D(f)` when its
supremum is `D(f)`. -/
@[stacks 01HT "part (2)"]
def IsStandardOpenCover {R : Type u} [CommRing R] (f : R) {n : ℕ} (g : Fin n → R) : Prop :=
  ⨆ i, PrimeSpectrum.basicOpen (g i) = PrimeSpectrum.basicOpen f

/-- A standard open covering of `Spec R`, expressed as the case `D(1) = Spec R`. -/
@[stacks 01HT "part (1)"]
abbrev IsStandardOpenCoverOfSpectrum {R : Type u} [CommRing R] {n : ℕ} (g : Fin n → R) : Prop :=
  IsStandardOpenCover (1 : R) g

/-- A standard open `D(f)` is contained in the union of the standard opens `D(g i)` if and only
if the images of the `g i` generate the unit ideal after localizing away from `f`. -/
@[stacks 01HS "cover_iff_unit_ideal"]
theorem basicOpen_le_iSup_iff_span_algebraMap_eq_top
    {R : Type u} [CommRing R] {S : Type v} [CommRing S] [Algebra R S]
    {ι : Type w} (f : R) [IsLocalization.Away f S] (g : ι → R) :
      PrimeSpectrum.basicOpen f ≤ ⨆ i, PrimeSpectrum.basicOpen (g i) ↔
      Ideal.span (Set.range fun i ↦ algebraMap R S (g i)) = ⊤ := by
  rw [← PrimeSpectrum.iSup_basicOpen_eq_top_iff]
  constructor
  · intro h
    refine top_unique fun x _ ↦ ?_
    have hp : PrimeSpectrum.comap (algebraMap R S) x ∈ (PrimeSpectrum.basicOpen f : Set _) :=
      (PrimeSpectrum.localization_away_comap_range S f).symm ▸ ⟨x, rfl⟩
    simpa using h hp
  · intro h p hp
    change p ∈ (PrimeSpectrum.basicOpen f : Set _) at hp
    rw [← PrimeSpectrum.localization_away_comap_range S f] at hp
    obtain ⟨x, rfl⟩ := hp
    simpa using
      (show x ∈ ⨆ i, PrimeSpectrum.basicOpen (algebraMap R S (g i)) from h.symm ▸ trivial)

/-- Every open cover of a standard open in the prime spectrum has a finite
refinement by standard opens. -/
@[stacks 01HS "finite_standard_refinement"]
lemma exists_finite_basicOpen_refinement {R : Type u} [CommSemiring R]
    {ι : Type*} (f : R) (U : ι → Opens (PrimeSpectrum R))
    (hU : PrimeSpectrum.basicOpen f ≤ ⨆ i, U i) :
    ∃ (n : ℕ) (g : Fin n → R) (a : Fin n → ι),
      PrimeSpectrum.basicOpen f = ⨆ j, PrimeSpectrum.basicOpen (g j) ∧
        ∀ j, PrimeSpectrum.basicOpen (g j) ≤ U (a j) := by
  let β := Σ i, {g : R // PrimeSpectrum.basicOpen g ≤ U i ∧
    PrimeSpectrum.basicOpen g ≤ PrimeSpectrum.basicOpen f}
  have hcov : (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) ⊆
      ⋃ b : β, (PrimeSpectrum.basicOpen b.2.1 : Set (PrimeSpectrum R)) := by
    intro p hp
    obtain ⟨i, hpi⟩ := Opens.mem_iSup.mp (hU hp)
    obtain ⟨v, hvb, hpv, hvU⟩ :=
      PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
        (show p ∈ U i ⊓ PrimeSpectrum.basicOpen f from ⟨hpi, hp⟩)
        ((U i ⊓ PrimeSpectrum.basicOpen f).isOpen)
    obtain ⟨g, rfl⟩ := hvb
    exact Set.mem_iUnion.mpr ⟨⟨i, ⟨g, hvU.trans inf_le_left,
      hvU.trans inf_le_right⟩⟩, hpv⟩
  obtain ⟨t, ht⟩ := (PrimeSpectrum.isCompact_basicOpen f).elim_finite_subcover
      (fun b : β ↦ (PrimeSpectrum.basicOpen b.2.1 : Set (PrimeSpectrum R)))
      (fun b ↦ (PrimeSpectrum.basicOpen b.2.1).isOpen) hcov
  let φ : Fin t.card → β := fun j ↦ t.equivFin.symm j
  refine ⟨t.card, fun j ↦ (φ j).2.1, fun j ↦ (φ j).1, ?_, ?_⟩
  · apply le_antisymm
    · intro p hp
      obtain ⟨b, hbt, hpb⟩ := Set.mem_iUnion₂.mp (ht hp)
      refine Opens.mem_iSup.mpr ⟨t.equivFin ⟨b, hbt⟩, ?_⟩
      have hφg : (φ (t.equivFin ⟨b, hbt⟩)).2.1 = b.2.1 :=
        congrArg (fun x : β ↦ x.2.1) (by simp [φ])
      change p ∈ (PrimeSpectrum.basicOpen ((φ (t.equivFin ⟨b, hbt⟩)).2.1) :
        Set (PrimeSpectrum R))
      rwa [hφg]
    · intro p hp
      obtain ⟨j, hpj⟩ := Opens.mem_iSup.mp hp
      exact (φ j).2.2.2 hpj
  · exact fun j ↦ (φ j).2.2.1

/-- If `D(g) ⊆ D(f)`, a positive power of `g` is a multiple of `f`. -/
@[stacks 01HS "power_divisible", ega "I 1.1.9" "partial"]
theorem exists_pow_eq_mul_of_basicOpen_le {R : Type*} [CommRing R] {f g : R}
    (hfg : PrimeSpectrum.basicOpen g ≤ PrimeSpectrum.basicOpen f) :
    ∃ e : ℕ, 1 ≤ e ∧ ∃ a : R, g ^ e = a * f := by
  obtain ⟨n, hn⟩ :=
    Ideal.mem_radical_iff.mp ((PrimeSpectrum.basicOpen_le_basicOpen_iff g f).mp hfg)
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton.mp hn
  exact ⟨n + 1, by lia, a * g, by rw [pow_succ, ha]; ring⟩

end PrimeSpectrum

end
