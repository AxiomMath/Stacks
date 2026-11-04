module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.Topology.Irreducible
public import StacksFrontier.AlgebraicGeometry.Properties.Normal

/-!
# Irreducible components of a quasi-compact open in a coproduct of irreducible schemes

A preirreducible space has at most one irreducible component, so an open subspace of an
irreducible space has at most one, and a space covered by finitely many open preirreducible
subsets has finitely many. A coproduct of irreducible schemes is covered by its summands, which
are pairwise disjoint opens; a quasi-compact open subspace therefore meets only finitely many of
them and is preirreducible inside each one that it meets, so it has finitely many irreducible
components.

## Main results

* `subsingleton_irreducibleComponents_of_isPreirreducible`: a preirreducible space has at most
  one irreducible component.
* `finite_irreducibleComponents_isOpen_of_irreducibleSpace`: an open subspace of an irreducible
  space has finitely many irreducible components.
* `finite_irreducibleComponents_of_isPreirreducible_cover`: a space admitting a finite cover by
  open preirreducible sets has finitely many irreducible components.
* `AlgebraicGeometry.finite_irreducibleComponents_of_isCompact_sigma`: a quasi-compact open
  subspace of a coproduct of irreducible schemes has finitely many irreducible components.

## Implementation notes

The finiteness criterion `finite_irreducibleComponents_of_isPreirreducible_cover` is phrased for
a family of open sets indexed by an arbitrary type together with a finite subset of the index
type that already suffices to cover. That is the shape produced by extracting a finite subcover
from quasi-compactness, so no reindexing is needed at the point of use. The key step is that at
most one irreducible component meets any given irreducible open set, which is
`AlgebraicGeometry.component_eq_of_open_irreducible_nhd`.

The coproduct result is stated for an open `U : (∐ Y).Opens` rather than for an open subset of
the underlying space, matching the way quasi-compact opens of a scheme are usually handled.

## References

* [Stacks Project, Tag 004V](https://stacks.math.columbia.edu/tag/004V)
* [Stacks Project, Tag 004W](https://stacks.math.columbia.edu/tag/004W)
* [Stacks Project, Tag 0357](https://stacks.math.columbia.edu/tag/0357)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

/-- A preirreducible space has at most one irreducible component: if it is empty there are
none, and otherwise the whole space is the unique one. -/
theorem subsingleton_irreducibleComponents_of_isPreirreducible {T : Type*} [TopologicalSpace T]
    (hT : IsPreirreducible (Set.univ : Set T)) : (irreducibleComponents T).Subsingleton := by
  rcases isEmpty_or_nonempty T with _ | hN
  · exact fun Z _ W _ => (Set.eq_empty_of_isEmpty Z).trans (Set.eq_empty_of_isEmpty W).symm
  · have : IrreducibleSpace T := { isPreirreducible_univ := hT, toNonempty := hN }
    rw [irreducibleComponents_eq_singleton]
    exact Set.subsingleton_singleton

/-- An open subspace of an irreducible space has finitely many irreducible components; in fact
it has at most one. -/
theorem finite_irreducibleComponents_isOpen_of_irreducibleSpace {T : Type*} [TopologicalSpace T]
    [IrreducibleSpace T] {U : Set T} (hU : IsOpen U) : (irreducibleComponents U).Finite := by
  have : PreirreducibleSpace U := hU.isOpenEmbedding_subtypeVal.preirreducibleSpace
  exact (subsingleton_irreducibleComponents_of_isPreirreducible
    PreirreducibleSpace.isPreirreducible_univ).finite

/-- A topological space covered by finitely many open preirreducible subsets has finitely many
irreducible components, since at most one component meets each member of the cover. -/
theorem finite_irreducibleComponents_of_isPreirreducible_cover {T : Type*} [TopologicalSpace T]
    {ι : Type*} {s : Set ι} (hs : s.Finite) {V : ι → Set T} (hVopen : ∀ i, IsOpen (V i))
    (hVpre : ∀ i, IsPreirreducible (V i)) (hcover : ∀ x : T, ∃ i ∈ s, x ∈ V i) :
    (irreducibleComponents T).Finite := by
  have hmeet (i : ι) :
      {Z | Z ∈ irreducibleComponents T ∧ (Z ∩ V i).Nonempty}.Subsingleton := by
    rintro Z ⟨hZ, ⟨z, hzZ, hzV⟩⟩ W ⟨hW, hWV⟩
    exact AlgebraicGeometry.component_eq_of_open_irreducible_nhd Z W hZ hW (V i) (hVopen i)
      ⟨⟨z, hzV⟩, hVpre i⟩ ⟨z, hzZ, hzV⟩ hWV
  refine Set.Finite.subset (hs.biUnion fun i _ => (hmeet i).finite) ?_
  intro Z hZ
  obtain ⟨z, hzZ⟩ := hZ.1.1
  obtain ⟨i, his, hzV⟩ := hcover z
  exact Set.mem_biUnion his ⟨hZ, ⟨z, hzZ, hzV⟩⟩

namespace AlgebraicGeometry

/-- A quasi-compact open subspace of a coproduct of irreducible schemes has finitely many
irreducible components: it meets only finitely many summands, and it is irreducible inside each
one that it meets. -/
theorem finite_irreducibleComponents_of_isCompact_sigma {ι : Type u} [Small.{u} ι]
    (Y : ι → Scheme.{u}) [∀ i, IrreducibleSpace (Y i)] (U : (∐ Y).Opens)
    (hU : IsCompact (U : Set (∐ Y : Scheme.{u}))) :
    (irreducibleComponents (U : Set (∐ Y : Scheme.{u}))).Finite := by
  have hRopen (i : ι) : IsOpen (Set.range ⇑(Sigma.ι Y i).base) :=
    (Sigma.ι Y i).isOpenEmbedding.isOpen_range
  have hRpre (i : ι) : IsPreirreducible (Set.range ⇑(Sigma.ι Y i).base) := by
    have h := PreirreducibleSpace.isPreirreducible_univ.image ⇑(Sigma.ι Y i).base
      (Sigma.ι Y i).isOpenEmbedding.continuous.continuousOn
    rwa [Set.image_univ] at h
  have hRcover (x : (∐ Y : Scheme.{u})) : ∃ i, x ∈ Set.range ⇑(Sigma.ι Y i).base := by
    obtain ⟨q, rfl⟩ := (sigmaMk Y).surjective x
    obtain ⟨i, y⟩ := q
    exact ⟨i, y, (sigmaMk_mk Y i y).symm⟩
  obtain ⟨t, ht⟩ := hU.elim_finite_subcover (fun i => Set.range ⇑(Sigma.ι Y i).base) hRopen
    fun x _ => Set.mem_iUnion.2 (hRcover x)
  refine finite_irreducibleComponents_of_isPreirreducible_cover (s := (t : Set ι))
    t.finite_toSet (V := fun i => Subtype.val ⁻¹' Set.range ⇑(Sigma.ι Y i).base)
    (fun i => (hRopen i).preimage continuous_subtype_val)
    (fun i => (hRpre i).preimage U.isOpen.isOpenEmbedding_subtypeVal) fun x => ?_
  obtain ⟨i, hit, hxi⟩ := Set.mem_iUnion₂.1 (ht x.2)
  exact ⟨i, hit, hxi⟩

end AlgebraicGeometry

end
