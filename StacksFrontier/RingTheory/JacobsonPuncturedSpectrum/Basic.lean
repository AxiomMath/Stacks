module

public import Mathlib.RingTheory.Jacobson.Ideal
public import Mathlib.RingTheory.Spectrum.Prime.Jacobson
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.JacobsonSpace
public import StacksFrontier.RingTheory.ZariskiPair
public import StacksCore.Tactic.StacksAttribute

/-!
# Jacobson complements in Noetherian spectra

The punctured spectrum of a Noetherian local ring is a Jacobson space. More generally, for a
Noetherian ring `R` and an ideal `I` contained in the Jacobson radical of `R`, the open
complement `Spec R \ V(I)` of the vanishing locus of `I` is a Jacobson space.

## Main results

* `PrimeSpectrum.jacobsonSpace_compl_closedPoint`: the punctured spectrum of a Noetherian local
  ring is Jacobson. This is part (1) of Tag 02IM.
* `PrimeSpectrum.jacobsonSpace_compl_zeroLocus_jacobson`: the complement of the vanishing locus of
  the Jacobson radical of a Noetherian ring is Jacobson. This is part (2).
* `PrimeSpectrum.jacobsonSpace_compl_zeroLocus_of_le_jacobson`: the same for any ideal contained in
  the Jacobson radical, i.e. for a Noetherian Zariski pair. This is part (3).

## Implementation notes

A Jacobson scheme is represented by `JacobsonSpace` on its underlying topological space, so an
open complement in an affine spectrum is expressed as the subtype of `PrimeSpectrum R` on the
corresponding complementary set.

The Zariski-pair condition of part (3) is spelled out as `I ≤ Ring.jacobson R`; it is the
predicate `IsContainedInJacobson` of Tag 0ELY.

## References

* [Stacks Project, Tag 02IM](https://stacks.math.columbia.edu/tag/02IM)
* [Stacks Project, Tag 0ELY](https://stacks.math.columbia.edu/tag/0ELY)
-/

@[expose] public section

universe u

namespace PrimeSpectrum

/-- For a Noetherian ring `R` and an ideal `I` contained in the Jacobson radical of `R`, the
complement of the vanishing locus of `I` is a Jacobson space. -/
@[ega "IV 10.5.8" "more general"]
private theorem jacobsonSpace_compl_zeroLocus_aux
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) (hI : I ≤ Ring.jacobson R) :
    JacobsonSpace ↥((PrimeSpectrum.zeroLocus (I : Set R))ᶜ) := by
  let s : Set (PrimeSpectrum R) := (PrimeSpectrum.zeroLocus (I : Set R))ᶜ
  have hs : IsOpen s := (PrimeSpectrum.isClosed_zeroLocus _).isOpen_compl
  have hr (f : R) : Set.range (PrimeSpectrum.comap (algebraMap R (Localization.Away f))) =
      PrimeSpectrum.basicOpen f := PrimeSpectrum.localization_away_comap_range _ f
  let map (f : I) : PrimeSpectrum (Localization.Away (f : R)) → s :=
    fun p => ⟨PrimeSpectrum.comap (algebraMap R (Localization.Away (f : R))) p,
      fun h => (PrimeSpectrum.mem_basicOpen _ _).mp ((hr f).subset ⟨p, rfl⟩) (h f.property)⟩
  have he (f : I) : Topology.IsOpenEmbedding (map f) := by
    apply Topology.IsOpenEmbedding.of_comp (map f) hs.isOpenEmbedding_subtypeVal
    change Topology.IsOpenEmbedding
      (PrimeSpectrum.comap (algebraMap R (Localization.Away (f : R))))
    exact PrimeSpectrum.localization_away_isOpenEmbedding
      (Localization.Away (f : R)) (f : R)
  let U (f : I) : TopologicalSpace.Opens s :=
    ⟨Set.range (map f), (he f).isOpen_range⟩
  have hcover : TopologicalSpace.IsOpenCover U := by
    apply TopologicalSpace.IsOpenCover.of_sets (fun f => (U f).2)
    ext p
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    obtain ⟨f, hfI, hfp⟩ := Set.not_subset.mp p.2
    obtain ⟨q, hq⟩ := (hr f).superset ((PrimeSpectrum.mem_basicOpen _ _).mpr hfp)
    exact ⟨⟨f, hfI⟩, q, Subtype.ext hq⟩
  apply hcover.jacobsonSpace_iff.mpr
  intro f
  change JacobsonSpace (Set.range (map f))
  have : JacobsonSpace (PrimeSpectrum (Localization.Away (f : R))) :=
    PrimeSpectrum.isJacobsonRing_iff_jacobsonSpace.mp
    (isJacobsonRing_of_isContainedInJacobson_of_isLocalization_away I
      (by simpa [IsContainedInJacobson, Ideal.jacobson_bot] using hI)
      (f : R) f.property _)
  exact JacobsonSpace.of_isOpenEmbedding
    (he f).toIsEmbedding.toHomeomorph.symm.isOpenEmbedding

/-- **Stacks Project, Tag 02IM, part (1).** The punctured spectrum of a Noetherian local ring is
a Jacobson space. -/
@[stacks 02IM "part (1)",
  instance,
  ega "IV 10.5.9" "Jacobson part",
  ega "IV 10.5.7" "Noetherian local ring", ega "IV 10.5.8" "local case"]
theorem jacobsonSpace_compl_closedPoint
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] :
    JacobsonSpace ↥(({IsLocalRing.closedPoint R} : Set (PrimeSpectrum R))ᶜ) := by
  have h : PrimeSpectrum.zeroLocus (Ring.jacobson R : Set R) =
      ({IsLocalRing.closedPoint R} : Set (PrimeSpectrum R)) := by
    rw [IsLocalRing.ringJacobson_eq_maximalIdeal]
    exact PrimeSpectrum.zeroLocus_eq_singleton _
  rw [← h]
  exact jacobsonSpace_compl_zeroLocus_aux R (Ring.jacobson R) le_rfl

/-- **Stacks Project, Tag 02IM, part (2).** The complement of the vanishing locus of the Jacobson
radical of a Noetherian ring is a Jacobson space. -/
@[stacks 02IM "part (2)",
  instance,
  ega "IV 10.5.8" "Spec(A)-V(R) Jacobson",
  ega "IV 10.5.9" "Y is Jacobson", ega "IV 10.5.7" "affine case"]
theorem jacobsonSpace_compl_zeroLocus_jacobson
    (R : Type u) [CommRing R] [IsNoetherianRing R] :
    JacobsonSpace
      ↥((PrimeSpectrum.zeroLocus (Ring.jacobson R : Set R))ᶜ) :=
  jacobsonSpace_compl_zeroLocus_aux R (Ring.jacobson R) le_rfl

/-- **Stacks Project, Tag 02IM, part (3).** If `(R, I)` is a Noetherian Zariski pair, that is if
`R` is Noetherian and `I` is contained in the Jacobson radical of `R`, then `Spec R \ V(I)` is a
Jacobson space. -/
@[stacks 02IM "part (3)"]
theorem jacobsonSpace_compl_zeroLocus_of_le_jacobson
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) (hI : I ≤ Ring.jacobson R) :
    JacobsonSpace ↥((PrimeSpectrum.zeroLocus (I : Set R))ᶜ) :=
  jacobsonSpace_compl_zeroLocus_aux R I hI

end PrimeSpectrum
