module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpectrum.Topology

/-!
# Quasi-compactness of the homogeneous spectrum

Let `S = ⨁_{d ≥ 0} 𝒮 d` be a graded ring. The scheme `Proj 𝒮` is quasi-compact exactly when
finitely many positive-degree homogeneous elements generate an ideal whose radical contains the
irrelevant ideal, and for any such family the associated standard opens cover `Proj 𝒮`.

One direction is a finite subcover of the covering of `Proj 𝒮` by the standard opens of all
positive-degree homogeneous elements; the other uses that each standard open of a positive-degree
homogeneous element is affine, hence quasi-compact, so a finite union of them is.

## Main results

* `AlgebraicGeometry.Proj.compactSpace_iff`: the quasi-compactness criterion.
* `AlgebraicGeometry.Proj.iSup_basicOpen_eq_top_of_irrelevant_le_radical`: the standard-open
  covering furnished by a family satisfying the criterion.

## Implementation notes

Quasi-compactness of the scheme is expressed by `CompactSpace` on its underlying topological
space. The finite family is a `Finset`, and each of its members is required to be homogeneous of
some positive degree. The radical condition is stated for the ordinary ideal spanned by these
elements, which need not generate the irrelevant ideal itself. The covering conclusion does not
require homogeneity of the chosen elements, so it is stated without that hypothesis.

## References

* [Stacks Project, Tag 01MD](https://stacks.math.columbia.edu/tag/01MD)
-/

@[expose] public section

namespace AlgebraicGeometry.Proj

universe u w

variable {S : Type u} {σ : Type w} [CommRing S]
  [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮]

/-- The homogeneous elements of some positive degree, as a type. -/
private def PositiveHomogeneousElement :=
  {f : S // ∃ d : ℕ, 0 < d ∧ f ∈ 𝒮 d}

private theorem positiveHomogeneous_basicOpen_cover :
    (⨆ f : PositiveHomogeneousElement 𝒮, Proj.basicOpen 𝒮 f.1) = ⊤ := by
  apply Proj.iSup_basicOpen_eq_top
  rw [HomogeneousIdeal.irrelevant_eq_span]
  refine Ideal.span_le.mpr fun f hf => Ideal.subset_span ?_
  obtain ⟨d, hd, hfd⟩ := Set.mem_iUnion₂.mp hf
  exact ⟨⟨f, d, hd, hfd⟩, rfl⟩

private theorem span_finset_isHomogeneous (s : Finset S)
    (hs : ∀ f ∈ s, ∃ d : ℕ, 0 < d ∧ f ∈ 𝒮 d) :
    (Ideal.span (s : Set S)).IsHomogeneous 𝒮 :=
  Ideal.homogeneous_span _ _ fun f hf => let ⟨d, _, hfd⟩ := hs f hf; ⟨d, hfd⟩

private theorem radical_span_finset_of_basicOpen_cover (s : Finset S)
    (hs : ∀ f ∈ s, ∃ d : ℕ, 0 < d ∧ f ∈ 𝒮 d)
    (hcover : ∀ x : AlgebraicGeometry.Proj 𝒮, ∃ f ∈ s, f ∉ x.asHomogeneousIdeal) :
    (HomogeneousIdeal.irrelevant 𝒮).toIdeal ≤ (Ideal.span (s : Set S)).radical := by
  refine (ProjectiveSpectrum.zeroLocus_empty_iff_irrelevant_le_radical 𝒮
    ⟨_, span_finset_isHomogeneous 𝒮 s hs⟩).mp
    (Set.eq_empty_iff_forall_notMem.mpr fun x hx => ?_)
  rw [ProjectiveSpectrum.mem_zeroLocus] at hx
  obtain ⟨f, hfs, hfx⟩ := hcover x
  exact hfx (hx (Ideal.subset_span hfs))

private theorem exists_mem_basicOpen_of_irrelevant_le_radical (s : Finset S)
    (h : (HomogeneousIdeal.irrelevant 𝒮).toIdeal ≤ (Ideal.span (s : Set S)).radical)
    (x : AlgebraicGeometry.Proj 𝒮) :
    ∃ f ∈ s, x ∈ AlgebraicGeometry.Proj.basicOpen 𝒮 f := by
  by_contra hnone
  have hs : (s : Set S) ⊆ x.asHomogeneousIdeal.toIdeal := fun f hf => by
    by_contra hfnot
    exact hnone ⟨f, hf, by simpa [Proj.mem_basicOpen] using hfnot⟩
  exact x.not_irrelevant_le (h.trans (x.isPrime.radical_le_iff.2 (Ideal.span_le.mpr hs)))

/-- The projective spectrum is quasi-compact exactly when finitely many
positive-degree homogeneous elements generate an ideal whose radical contains
the irrelevant ideal. -/
@[stacks 01MD "quasi-compactness criterion"]
public theorem compactSpace_iff :
    CompactSpace (AlgebraicGeometry.Proj 𝒮) ↔
      ∃ s : Finset S,
        (∀ f ∈ s, ∃ d : ℕ, 0 < d ∧ f ∈ 𝒮 d) ∧
          (HomogeneousIdeal.irrelevant 𝒮).toIdeal ≤ (Ideal.span (s : Set S)).radical := by
  constructor
  · intro
    classical
    let U : PositiveHomogeneousElement 𝒮 → Set (Proj 𝒮) :=
      fun f => (Proj.basicOpen 𝒮 f.1 : Set (Proj 𝒮))
    obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover U
      (fun f => (Proj.basicOpen 𝒮 f.1).2) fun x hx => by
        obtain ⟨f, hfx⟩ := TopologicalSpace.Opens.mem_iSup.mp
          ((positiveHomogeneous_basicOpen_cover 𝒮).ge hx)
        exact Set.mem_iUnion.mpr ⟨f, by simpa [U] using hfx⟩
    have hs : ∀ f ∈ t.image fun f => f.1, ∃ d : ℕ, 0 < d ∧ f ∈ 𝒮 d := fun f hf => by
      obtain ⟨g, -, rfl⟩ := Finset.mem_image.mp hf
      exact g.2
    refine ⟨_, hs, radical_span_finset_of_basicOpen_cover 𝒮 _ hs fun x => ?_⟩
    obtain ⟨g, hgt, hgx⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
    exact ⟨g.1, Finset.mem_image.mpr ⟨g, hgt, rfl⟩, by simpa [U, Proj.mem_basicOpen] using hgx⟩
  · rintro ⟨s, hs, hrad⟩
    have hset : (⋃ f ∈ (s : Set S), (Proj.basicOpen 𝒮 f : Set (Proj 𝒮))) = Set.univ :=
      Set.eq_univ_of_forall fun x => by
        obtain ⟨f, hfs, hfx⟩ := exists_mem_basicOpen_of_irrelevant_le_radical 𝒮 s hrad x
        exact Set.mem_iUnion₂.mpr ⟨f, hfs, hfx⟩
    refine isCompact_univ_iff.mp ?_
    rw [← hset]
    refine s.finite_toSet.isCompact_biUnion fun f hf => ?_
    obtain ⟨d, hd, hfd⟩ := hs f hf
    exact (Proj.isAffineOpen_basicOpen 𝒮 f hfd hd).isCompact

/-- Elements whose span contains the irrelevant ideal up to radical have
standard opens covering the projective spectrum. -/
@[stacks 01MD "standard-open cover", ega "II 2.3.14" "special case"]
public theorem iSup_basicOpen_eq_top_of_irrelevant_le_radical (s : Finset S)
    (h : (HomogeneousIdeal.irrelevant 𝒮).toIdeal ≤ (Ideal.span (s : Set S)).radical) :
    ⨆ f ∈ s, Proj.basicOpen 𝒮 f = ⊤ :=
  top_unique fun x _ => by
    obtain ⟨f, hfs, hfx⟩ := exists_mem_basicOpen_of_irrelevant_le_radical 𝒮 s h x
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨f, TopologicalSpace.Opens.mem_iSup.mpr ⟨hfs, hfx⟩⟩

end AlgebraicGeometry.Proj
