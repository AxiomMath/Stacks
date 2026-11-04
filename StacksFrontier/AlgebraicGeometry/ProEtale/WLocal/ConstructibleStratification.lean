module

public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Topology.Constructible
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Spectrum.Prime.Constructible.Defs
public import StacksFrontier.Topology.Constructible.NormalForm
public import StacksFrontier.Topology.Stratification.Partition

/-!
# Refining constructible stratifications of an affine spectrum

A finite partition of an affine spectrum into constructible subsets is refined by the partition
according to the vanishing pattern of finitely many ring elements.

## Main definitions

* `AlgebraicGeometry.ProEtale.vanishingPatternStrata`: the family of nonempty strata with a fixed
  vanishing pattern on a finite set of ring elements.

## Main results

* `AlgebraicGeometry.ProEtale.exists_vanishingPatternStrata_refines`: a finite set of ring
  elements whose vanishing-pattern strata refine a prescribed finite constructible partition.

## Implementation notes

The strata are represented as the fibers of the vanishing-pattern map, indexed by points of the
spectrum. Taking the range removes repeated and empty fibers, as in the source's stratification.
A constructible subset is cut out, in the sense that membership only depends on the vanishing
pattern, by the elements occurring in a normal-form presentation of it; those presentations give
each open piece as the complement of the zero locus of a finite set.

## References

* [Stacks Project, Tag 096Y](https://stacks.math.columbia.edu/tag/096Y)
-/

@[expose] public section

namespace AlgebraicGeometry.ProEtale

open PrimeSpectrum

universe u

/-- The nonempty strata of `Spec A` determined by which elements of `E` vanish. -/
def vanishingPatternStrata {A : Type u} [CommRing A] (E : Finset A) :
    Set (Set (PrimeSpectrum A)) :=
  Set.range (fun p : PrimeSpectrum A =>
    {q : PrimeSpectrum A | ∀ f ∈ E, (f ∈ p.asIdeal ↔ f ∈ q.asIdeal)})

/-- Membership in the complement of the zero locus of a finite set is witnessed by one of its
elements. -/
private lemma mem_compl_zeroLocus_iff {A : Type u} [CommRing A] (s : Finset A)
    (r : PrimeSpectrum A) :
    r ∈ (PrimeSpectrum.zeroLocus (↑s : Set A))ᶜ ↔ ∃ f ∈ s, f ∉ r.asIdeal := by
  simp [PrimeSpectrum.mem_zeroLocus, Set.not_subset]

/-- A constructible subset of an affine spectrum is determined by the vanishing pattern of
finitely many ring elements. -/
private lemma exists_finset_determining_constructible {A : Type u} [CommRing A]
    (T : Set (PrimeSpectrum A)) (hT : Topology.IsConstructible T) :
    ∃ E : Finset A, ∀ p q : PrimeSpectrum A,
      (∀ f ∈ E, (f ∈ p.asIdeal ↔ f ∈ q.asIdeal)) → (p ∈ T ↔ q ∈ T) := by
  classical
  obtain ⟨t, ht, hT_eq⟩ :=
    (Topology.isConstructible_iff_exists_finset_biUnion_inter_compl).mp hT
  have hc {U : Set (PrimeSpectrum A)} (hopen : IsOpen U) (hretro : IsRetrocompact U) :
      ∃ s : Finset A, (PrimeSpectrum.zeroLocus (↑s : Set A))ᶜ = U :=
    PrimeSpectrum.isCompact_isOpen_iff.mp
      ⟨(QuasiSeparatedSpace.isRetrocompact_iff_isCompact hopen).mp hretro, hopen⟩
  choose su hsu using fun x : {x // x ∈ t} => hc (ht x.1 x.2).1 (ht x.1 x.2).2.1
  choose sv hsv using fun x : {x // x ∈ t} => hc (ht x.1 x.2).2.2.1 (ht x.1 x.2).2.2.2
  let E : Finset A := t.attach.biUnion (fun x => su x ∪ sv x)
  refine ⟨E, ?_⟩
  intro p q hstatus
  rw [hT_eq]
  simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_compl_iff]
  refine exists_congr fun x => exists_congr fun hx => ?_
  let x' : {x // x ∈ t} := ⟨x, hx⟩
  have hmem (x : {x // x ∈ t}) (s : Finset A) (hs : s ⊆ su x ∪ sv x)
      (U : Set (PrimeSpectrum A))
      (hU : (PrimeSpectrum.zeroLocus (↑s : Set A))ᶜ = U) :
      (p ∈ U ↔ q ∈ U) := by
    rw [← hU, mem_compl_zeroLocus_iff, mem_compl_zeroLocus_iff]
    exact exists_congr fun f =>
      and_congr_right fun hf => not_congr (hstatus f (Finset.mem_biUnion.2
        ⟨x, t.mem_attach x, hs hf⟩))
  exact and_congr (hmem x' _ Finset.subset_union_left _ (hsu x'))
    (not_congr (hmem x' _ Finset.subset_union_right _ (hsv x')))

/-- **Stacks Project, Tag 096Y.** Every finite constructible partition of an affine spectrum is
refined by the stratification according to the vanishing pattern of finitely many elements. -/
@[stacks 096Y]
lemma exists_vanishingPatternStrata_refines {A : Type u} [CommRing A]
    {P : Set (Set (PrimeSpectrum A))} (hP : Setoid.IsPartition P)
    (hP_finite : P.Finite) (hP_constructible : ∀ T ∈ P, Topology.IsConstructible T) :
    ∃ E : Finset A, local_Refines (vanishingPatternStrata E) P := by
  classical
  choose sT hsT using fun T : {T : Set (PrimeSpectrum A) // T ∈ P} =>
    exists_finset_determining_constructible T.val (hP_constructible T.val T.property)
  have := hP_finite.to_subtype
  have hE : (⋃ T : {T // T ∈ P}, (sT T : Set A)).Finite :=
    Set.finite_iUnion fun T => (sT T).finite_toSet
  refine ⟨hE.toFinset, ?_⟩
  rintro _ ⟨p, rfl⟩
  obtain ⟨T, ⟨hTP, hpT⟩, -⟩ := hP.2 p
  exact ⟨T, hTP, fun q hq => (hsT ⟨T, hTP⟩ p q fun f hf =>
    hq f (hE.mem_toFinset.2 (Set.mem_iUnion.mpr ⟨⟨T, hTP⟩, hf⟩))).mp hpT⟩

end AlgebraicGeometry.ProEtale
