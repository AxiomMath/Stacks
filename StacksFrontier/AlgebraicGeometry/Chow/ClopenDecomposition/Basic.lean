module

public import Mathlib.AlgebraicGeometry.Restrict

/-!
# Decompositions of a scheme into open and closed pieces

A decomposition `X = \coprod_{i \in I} X_i` of a scheme into open and closed subschemes is given
by a family `U : I → X.Opens` which is pairwise disjoint and covers `X`; each piece is then closed,
since its complement is the union of the others. Every point of `X` lies in exactly one piece,
and every nonempty irreducible subset of `X` is contained in exactly one piece.

## Main definitions

* `Stacks.Chow.IsClopenDecomposition` — the predicate that a family of open subschemes is
  pairwise disjoint and covers the scheme.
* `Stacks.Chow.IsClopenDecomposition.index` — the unique index whose piece contains a given point.

## Main results

* `Stacks.Chow.IsClopenDecomposition.isClopen` — each piece is closed as well as open.
* `Stacks.Chow.IsClopenDecomposition.subset_of_isPreirreducible` — an irreducible subset meeting a
  piece is contained in it.
* `Stacks.Chow.IsClopenDecomposition.existsUnique_isPreirreducible` — an irreducible nonempty
  subset is contained in exactly one piece.

## References

* [Stacks Project, Tag 0FDZ](https://stacks.math.columbia.edu/tag/0FDZ)
* [Stacks Project, Tag 02UC](https://stacks.math.columbia.edu/tag/02UC)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u v

namespace Stacks.Chow

variable {X : Scheme.{u}} {I : Type v} {U : I → X.Opens}

/-- A decomposition of a scheme into open and closed subschemes: a family of open subschemes which
is pairwise disjoint and covers the scheme. Each piece is then closed as well, by
`Stacks.Chow.IsClopenDecomposition.isClopen`. -/
structure IsClopenDecomposition {X : Scheme.{u}} {I : Type v} (U : I → X.Opens) : Prop where
  /-- Distinct pieces are disjoint. -/
  disjoint : ∀ i j, i ≠ j → Disjoint (U i) (U j)
  /-- The pieces cover the scheme. -/
  iSup_eq_top : ⨆ i, U i = ⊤

namespace IsClopenDecomposition

/-- Every point of the scheme lies in some piece. -/
theorem exists_mem (h : IsClopenDecomposition U) (x : X) : ∃ i, x ∈ U i :=
  Opens.mem_iSup.1 (h.iSup_eq_top ▸ trivial)

/-- A point lies in at most one piece. -/
theorem eq_of_mem (h : IsClopenDecomposition U) {i j : I} {x : X} (hi : x ∈ U i)
    (hj : x ∈ U j) : i = j := by
  by_contra hij
  exact (h.disjoint i j hij).le_bot (show x ∈ U i ⊓ U j from ⟨hi, hj⟩)

/-- The unique index whose piece contains a given point of the scheme. -/
noncomputable def index (h : IsClopenDecomposition U) (x : X) : I :=
  (h.exists_mem x).choose

/-- A point lies in the piece indexed by `Stacks.Chow.IsClopenDecomposition.index`. -/
theorem mem_index (h : IsClopenDecomposition U) (x : X) : x ∈ U (h.index x) :=
  (h.exists_mem x).choose_spec

/-- `Stacks.Chow.IsClopenDecomposition.index` returns the index of any piece containing the
point. -/
theorem index_eq (h : IsClopenDecomposition U) {i : I} {x : X} (hx : x ∈ U i) :
    h.index x = i :=
  h.eq_of_mem (h.mem_index x) hx

/-- The complement of a piece is the union of the other pieces. -/
theorem compl_eq_iUnion (h : IsClopenDecomposition U) (i : I) :
    ((U i : Set X))ᶜ = ⋃ j : {j : I // j ≠ i}, (U (j : I) : Set X) := by
  ext x
  refine ⟨fun hx ↦ ?_, ?_⟩
  · obtain ⟨j, hj⟩ := h.exists_mem x
    exact Set.mem_iUnion.2 ⟨⟨j, fun hji ↦ hx (hji ▸ hj)⟩, hj⟩
  · rintro hx hxi
    obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hx
    exact j.2 (h.eq_of_mem hj hxi)

/-- Each piece of the decomposition is closed as well as open. -/
theorem isClopen (h : IsClopenDecomposition U) (i : I) : IsClopen (U i : Set X) := by
  refine ⟨?_, (U i).2⟩
  rw [← isOpen_compl_iff, h.compl_eq_iUnion i]
  exact isOpen_iUnion fun j ↦ (U (j : I)).2

/-- An irreducible subset of the scheme meeting a piece of the decomposition is contained in it. -/
theorem subset_of_isPreirreducible (h : IsClopenDecomposition U) {Z : Set X}
    (hZ : IsPreirreducible Z) {i : I} {x : X} (hxZ : x ∈ Z) (hxU : x ∈ U i) :
    Z ⊆ (U i : Set X) := by
  by_contra hsub
  obtain ⟨y, hyZ, hyU⟩ := Set.not_subset.1 hsub
  obtain ⟨z, _, hzi, hzc⟩ := hZ _ _ (U i).2 ((h.isClopen i).1.isOpen_compl) ⟨x, hxZ, hxU⟩
    ⟨y, hyZ, hyU⟩
  exact hzc hzi

/-- A nonempty irreducible subset of the scheme is contained in exactly one piece of the
decomposition. -/
theorem existsUnique_isPreirreducible (h : IsClopenDecomposition U) {Z : Set X}
    (hZ : IsPreirreducible Z) (hne : Z.Nonempty) :
    ∃! i : I, Z ⊆ (U i : Set X) := by
  obtain ⟨x, hxZ⟩ := hne
  obtain ⟨i, hxU⟩ := h.exists_mem x
  exact ⟨i, h.subset_of_isPreirreducible hZ hxZ hxU,
    fun j hj ↦ h.eq_of_mem (hj hxZ) hxU⟩

end IsClopenDecomposition

end Stacks.Chow

end
