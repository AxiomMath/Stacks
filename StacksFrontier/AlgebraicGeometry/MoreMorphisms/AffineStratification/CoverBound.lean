module

public import Mathlib.Topology.Sets.OpenCover
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.AffineStratification.Defs
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.AffineStratification.ReducedInduced

/-!
# The affine stratification number of a scheme with a finite affine open covering

A separated scheme covered by `n + 1` affine opens has affine stratification number at most
`n`: ordering the covering linearly, the differences `U i \ ⋃_{i < j} U j` form an affine
stratification indexed by the covering.

## Main results

* `AlgebraicGeometry.isAffineHom_of_isAffine_source`: a morphism from an affine scheme to a
  separated scheme is affine.
* `AlgebraicGeometry.affineStratificationNumber_le_of_isOpenCover`: the bound.

## Implementation notes

The covering is indexed by a finite linear order, and the stratum attached to an index is the
part of its member of the covering lying in no later member. Each stratum is closed in its
member of the covering, so the reduced induced scheme on it is a closed subscheme of an affine
scheme; its inclusion into the ambient scheme factors through that affine open, whose own
inclusion is affine because the ambient scheme is separated.

## References

* [Stacks Project, Tag 0F2W](https://stacks.math.columbia.edu/tag/0F2W)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.ZariskiAndSeparation.ReducedInducedLocallyClosed

universe u v

namespace AlgebraicGeometry

/-- A morphism from an affine scheme to a separated scheme is affine. -/
theorem isAffineHom_of_isAffine_source {X Y : Scheme.{u}} [IsAffine Y] [X.IsSeparated]
    (f : Y ⟶ X) : IsAffineHom f := by
  have : IsAffineHom (f ≫ terminal.from X) :=
    Subsingleton.elim (terminal.from Y) (f ≫ terminal.from X) ▸ inferInstance
  exact IsAffineHom.of_comp f (terminal.from X)

section Topology

variable {α : Type u} {I : Type v} [LinearOrder I]

/-- The part of the `i`-th member of a linearly indexed family of sets that lies in no later
member. For an open covering these parts form a stratification. -/
private def openCoverStrata (U : I → Set α) (i : I) : Set α := U i \ ⋃ j ∈ {j | i < j}, U j

/-- A point of a later member of the covering lies in no earlier stratum. -/
private lemma notMem_openCoverStrata_of_lt {U : I → Set α} {i j : I} (h : i < j) {x : α}
    (hx : x ∈ U j) : x ∉ openCoverStrata U i :=
  fun hxi => hxi.2 (Set.mem_iUnion₂.mpr ⟨j, h, hx⟩)

/-- Distinct strata of an open covering are disjoint. -/
private lemma openCoverStrata_disjoint (U : I → Set α) (i j : I) (hij : i ≠ j) :
    Disjoint (openCoverStrata U i) (openCoverStrata U j) := by
  refine Set.disjoint_left.mpr fun x hxi hxj => ?_
  rcases lt_or_gt_of_ne hij with h | h
  · exact notMem_openCoverStrata_of_lt h hxj.1 hxi
  · exact notMem_openCoverStrata_of_lt h hxi.1 hxj

/-- A point of the space lies in the stratum of the largest index whose member of the covering
contains it. -/
private lemma exists_mem_openCoverStrata [Finite I] (U : I → Set α)
    (hU : (⋃ i, U i) = Set.univ) (x : α) : ∃ i, x ∈ openCoverStrata U i := by
  classical
  have : Fintype I := Fintype.ofFinite I
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hU ▸ Set.mem_univ x)
  let s : Finset I := Finset.univ.filter fun j => x ∈ U j
  have hs : s.Nonempty := ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
  refine ⟨s.max' hs, (Finset.mem_filter.mp (s.max'_mem hs)).2, fun hlater => ?_⟩
  obtain ⟨k, hk, hxk⟩ := Set.mem_iUnion₂.mp hlater
  exact absurd (s.le_max' k (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxk⟩)) (not_le_of_gt hk)

/-- The strata of a finite open covering cover the space. -/
private lemma openCoverStrata_cover [Finite I] (U : I → Set α) (hU : (⋃ i, U i) = Set.univ) :
    (⋃ i, openCoverStrata U i) = Set.univ :=
  Set.eq_univ_of_forall fun x => Set.mem_iUnion.mpr (exists_mem_openCoverStrata U hU x)

variable [TopologicalSpace α]

/-- A stratum of an open covering is locally closed: it is the intersection of an open set with
the complement of an open set. -/
private lemma openCoverStrata_isLocallyClosed (U : I → Set α) (hU : ∀ i, IsOpen (U i)) (i : I) :
    IsLocallyClosed (openCoverStrata U i) := by
  change IsLocallyClosed (U i ∩ (⋃ j ∈ {j | i < j}, U j)ᶜ)
  exact (hU i).isLocallyClosed.inter
    (isClosed_compl_iff.mpr (isOpen_biUnion fun j _ => hU j)).isLocallyClosed

/-- The closure of a stratum of a finite open covering is covered by the strata of the indices
below it. -/
private lemma openCoverStrata_closure_subset [Finite I] (U : I → Set α)
    (hU : ∀ i, IsOpen (U i)) (hcover : (⋃ i, U i) = Set.univ) (i : I) :
    closure (openCoverStrata U i) ⊆ ⋃ j ∈ {j | j ≤ i}, openCoverStrata U j := by
  intro x hx
  obtain ⟨k, hxk⟩ := exists_mem_openCoverStrata U hcover x
  refine Set.mem_biUnion (show k ≤ i from not_lt.mp fun hik => ?_) hxk
  have hsub : openCoverStrata U i ⊆ (U k)ᶜ := fun y hy hyk =>
    notMem_openCoverStrata_of_lt hik hyk hy
  exact closure_minimal hsub (hU k).isClosed_compl hx hxk.1

/-- The strata of a finite open covering form a locally finite stratification. -/
private lemma openCoverStrata_isLocallyFiniteStratification [Finite I] (U : I → Set α)
    (hU : ∀ i, IsOpen (U i)) (hcover : (⋃ i, U i) = Set.univ) :
    IsLocallyFiniteStratification (openCoverStrata U) :=
  ⟨⟨⟨openCoverStrata_isLocallyClosed U hU, openCoverStrata_disjoint U,
      openCoverStrata_cover U hcover⟩,
    openCoverStrata_closure_subset U hU hcover⟩, locallyFinite_of_finite _⟩

end Topology

/-- On a separated scheme, the reduced induced scheme on a stratum of an affine open covering is
affine and its inclusion is an affine morphism. -/
private lemma isAffine_reducedInduced_openCoverStrata {X : Scheme.{u}} {I : Type v}
    [LinearOrder I] [X.IsSeparated] (U : I → X.Opens) (hUaff : ∀ i, IsAffineOpen (U i)) (i : I)
    (hLC : IsLocallyClosed (openCoverStrata (fun i => (U i : Set X)) i)) :
    IsAffine (reducedInducedScheme (openCoverStrata (fun i => (U i : Set X)) i) hLC) ∧
      IsAffineHom (reducedInducedInclusion (openCoverStrata (fun i => (U i : Set X)) i) hLC) := by
  let B : Set X := ⋃ j ∈ {j | i < j}, (U j : Set X)
  have hBopen : IsOpen B := isOpen_biUnion fun j _ => (U j).2
  let C : Closeds (U i).toScheme :=
    ⟨(U i).ι.base ⁻¹' Bᶜ, hBopen.isClosed_compl.preimage (U i).ι.continuous⟩
  let K := Scheme.IdealSheafData.vanishingIdeal C
  have : IsAffine (U i).toScheme := hUaff i
  have : IsAffine K.subscheme := isAffine_of_isAffineHom K.subschemeι
  have : IsAffineHom (U i).ι := isAffineHom_of_isAffine_source (U i).ι
  have hrange : Set.range (K.subschemeι ≫ (U i).ι).base =
      openCoverStrata (fun i => (U i : Set X)) i := by
    change Set.range ((U i).ι.base ∘ K.subschemeι.base) = _
    rw [Set.range_comp, Scheme.IdealSheafData.range_subschemeι_vanishingIdeal]
    ext x
    refine ⟨?_, fun ⟨hxU, hxB⟩ => ⟨⟨x, hxU⟩, hxB, rfl⟩⟩
    rintro ⟨y, hy, rfl⟩
    exact ⟨y.property, hy⟩
  exact isAffine_reducedInduced_of_range_eq _ hLC (K.subschemeι ≫ (U i).ι) hrange

/-- **[Stacks, Tag 0F2W].** A separated scheme with an open covering by `n + 1` affine opens
has affine stratification number at most `n`. -/
@[stacks 0F2W]
theorem affineStratificationNumber_le_of_isOpenCover (X : Scheme.{u}) [X.IsSeparated] {n : ℕ}
    (U : Fin (n + 1) → X.Opens) (hU : IsOpenCover U) (hUaff : ∀ i, IsAffineOpen (U i)) :
    affineStratificationNumber X ≤ n := by
  refine Nat.sInf_le ⟨?_⟩
  exact { strata := openCoverStrata (fun i => (U i : Set X))
          isLocallyFiniteStratification :=
            openCoverStrata_isLocallyFiniteStratification _ (fun i => (U i).2) hU.iSup_set_eq_univ
          isAffine := fun i => (isAffine_reducedInduced_openCoverStrata U hUaff i _).1
          isAffineHom := fun i => (isAffine_reducedInduced_openCoverStrata U hUaff i _).2 }

end AlgebraicGeometry

end
