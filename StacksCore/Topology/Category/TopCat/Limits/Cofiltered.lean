module

public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.Topology.Category.TopCat.Limits.Basic

/-!
# Opens of a cofiltered limit of topological spaces

Let `F : J ⥤ TopCat` be a cofiltered diagram and `C` a limit cone over `F`. This file proves
Stacks 0A2P: every open subset of `C.pt` is a union of preimages `C.π.app j ⁻¹' U j` of open
subsets of the factors, and every quasi-compact open subset is a single such preimage.

The topology of `C.pt` is the infimum of the topologies induced by the projections `C.π.app j`
(`TopCat.induced_of_isLimit`). For a cone over any diagram, a morphism `f : k ⟶ i` makes the
topology induced by `C.π.app k` finer than the one induced by `C.π.app i`
(`TopCat.induced_π_app_le_induced_π_app`). As `J` is cofiltered, the neighbourhood filters of a
point for these topologies form a nonempty directed family, so a set is a neighbourhood of the
point in `C.pt` exactly when it is one for a single induced topology. For a set `W ⊆ C.pt`, this
says that `interior W` is the union of the preimages under `C.π.app j` of the sets
`interior (Set.kernImage (C.π.app j) W)`, the largest open subsets of `F.obj j` whose preimages
lie in `W` (`TopCat.interior_eq_iUnion_preimage_interior_kernImage`). For an open `W` this is
part 1. These preimages grow along the morphisms of `J`, so the union is directed, and a
quasi-compact subset of `W` lies in one of them (`IsCompact.elim_directed_cover`), which is part 2.

## Main results

* `TopCat.induced_π_app_le_induced_π_app`: for a cone `C` over any `F : J ⥤ TopCat` and a
  morphism `f : k ⟶ i`, the topology induced on `C.pt` by `C.π.app k` is finer than the one
  induced by `C.π.app i`.
* `TopCat.interior_eq_iUnion_preimage_interior_kernImage`: for a limit cone `C` over a cofiltered
  `F` and any `W ⊆ C.pt`, `interior W` is the union over `j` of the preimages of the largest open
  subsets of `F.obj j` whose preimages lie in `W`.
* `TopCat.exists_eq_iUnion_preimage_of_isOpen` (Stacks 0A2P, part 1): every open `W ⊆ C.pt` is
  `⋃ j, C.π.app j ⁻¹' U j` for open subsets `U j ⊆ F.obj j`.
* `TopCat.exists_isOpen_subset_preimage_subset_of_isCompact` (part 2, general form): if `K` is a
  quasi-compact subset of an open `W ⊆ C.pt`, then `K ⊆ C.π.app i ⁻¹' U ⊆ W` for a single index
  `i` and an open `U ⊆ F.obj i`.
* `TopCat.exists_isOpen_eq_preimage_of_isCompact_of_isOpen` (part 2): every quasi-compact open
  `W ⊆ C.pt` is `C.π.app i ⁻¹' U` for a single index `i` and an open `U ⊆ F.obj i`.

## Implementation notes

The universes of `J`, of its morphisms and of the spaces are independent (`J : Type*`,
`[Category* J]`, `F : J ⥤ TopCat`). Mathlib's `TopCat.isTopologicalBasis_cofiltered_limit`, which
gives a basis of preimages from compatible bases of the factors that contain `Set.univ` and are
closed under binary intersections, is stated only for `F : J ⥤ TopCat.{max v u}` with
`J : Type v`, so it is not used here.

`IsCofiltered J` does not make `Nonempty J` an instance, so the field `IsCofiltered.nonempty` is a
local instance in this file.

## References

* [Stacks Project, Tag 0A2P](https://stacks.math.columbia.edu/tag/0A2P)
-/

@[expose] public section

open CategoryTheory Limits Filter Topology

namespace TopCat

variable {J : Type*} [Category* J]

section Cone

variable {F : J ⥤ TopCat} (C : Cone F)

/-- For a cone `C` over `F : J ⥤ TopCat` and a morphism `f : k ⟶ i`, the topology induced on
`C.pt` by `C.π.app k` is finer than the one induced by `C.π.app i`, since `C.π.app i` is
`C.π.app k` followed by the continuous map `F.map f`.

By `nhds_mono` and `nhds_induced`, `comap (C.π.app k) (𝓝 (C.π.app k x))` is therefore at most
`comap (C.π.app i) (𝓝 (C.π.app i x))` for every `x : C.pt`. -/
theorem induced_π_app_le_induced_π_app {k i : J} (f : k ⟶ i) :
    (F.obj k).str.induced (C.π.app k).hom ≤ (F.obj i).str.induced (C.π.app i) := by
  grw [← C.w f, coe_comp, ← induced_compose, induced_mono (F.map f).hom.continuous.le_induced]

/-- For a cone `C` over `F : J ⥤ TopCat`, a morphism `f : k ⟶ i` and `W ⊆ C.pt`, the preimage
under `C.π.app i` of the largest open subset of `F.obj i` whose preimage lies in `W` is contained
in the corresponding preimage for `k`: both are the interiors of `W` for the induced topologies,
and the one induced by `C.π.app k` is finer. -/
private lemma preimage_interior_kernImage_subset {k i : J} (f : k ⟶ i) (W : Set C.pt) :
    C.π.app i ⁻¹' interior (Set.kernImage (C.π.app i) W) ⊆
      C.π.app k ⁻¹' interior (Set.kernImage (C.π.app k) W) := fun x hx ↦ by
  rw [Set.mem_preimage, mem_interior_iff_mem_nhds, ← mem_comap'', ← nhds_induced] at hx ⊢
  exact Set.mem_of_subset_of_mem (nhds_mono <| induced_π_app_le_induced_π_app C (i := i) f) hx

end Cone

variable [IsCofiltered J] {F : J ⥤ TopCat} {C : Cone F}

attribute [local instance] IsCofiltered.nonempty

/-- A family indexed by the objects of the cofiltered category `J` is directed for `r` as soon as
`r (φ i) (φ k)` holds for every morphism `k ⟶ i` (compare `directed_of_isDirected_ge`). -/
private lemma directed_of_isCofiltered {α : Type*} {r : α → α → Prop} {φ : J → α}
    (h : ∀ ⦃k i : J⦄, (k ⟶ i) → r (φ i) (φ k)) : Directed r φ := fun i j ↦
  ⟨IsCofiltered.min i j, h (IsCofiltered.minToLeft i j), h (IsCofiltered.minToRight i j)⟩

/-- Let `C` be a limit cone over a cofiltered diagram `F : J ⥤ TopCat`. For every `W ⊆ C.pt`,
`interior W` is the union over `j` of the preimages under `C.π.app j` of
`interior (Set.kernImage (C.π.app j) W)`, the largest open subset of `F.obj j` whose preimage
lies in `W`. -/
theorem interior_eq_iUnion_preimage_interior_kernImage (hC : IsLimit C) (W : Set C.pt) :
    interior W = ⋃ j, C.π.app j ⁻¹' interior (Set.kernImage (C.π.app j) W) := by
  ext x
  simp only [mem_interior_iff_mem_nhds, Set.mem_iUnion, Set.mem_preimage, ← mem_comap'',
    ← nhds_induced]
  rw [induced_of_isLimit C hC, nhds_iInf]
  refine mem_iInf_of_directed (directed_of_isCofiltered fun k i f ↦ ?_) W
  exact nhds_mono <| induced_π_app_le_induced_π_app C f

/-- **Stacks 0A2P** (part 1). Let `C` be a limit cone over a cofiltered diagram `F : J ⥤ TopCat`.
Every open subset `W` of `C.pt` is `⋃ j, C.π.app j ⁻¹' U j` for open subsets `U j ⊆ F.obj j`.

The tag takes the union over a subset of the index category. The whole index category always
works, since `U j` may be empty. -/
@[stacks 0A2P]
theorem exists_eq_iUnion_preimage_of_isOpen (hC : IsLimit C) {W : Set C.pt} (hW : IsOpen W) :
    ∃ U : ∀ j, Set (F.obj j), (∀ j, IsOpen (U j)) ∧ W = ⋃ j, C.π.app j ⁻¹' U j :=
  ⟨fun j ↦ interior (Set.kernImage (C.π.app j) W), fun _ ↦ isOpen_interior,
    hW.interior_eq.symm.trans (interior_eq_iUnion_preimage_interior_kernImage hC W)⟩

/-- **Stacks 0A2P** (part 2), general form. Let `C` be a limit cone over a cofiltered diagram
`F : J ⥤ TopCat`. If `K` is a quasi-compact subset of an open subset `W` of `C.pt`, then
`K ⊆ C.π.app i ⁻¹' U ⊆ W` for an index `i` and an open subset `U ⊆ F.obj i`.

The tag's statement, `TopCat.exists_isOpen_eq_preimage_of_isCompact_of_isOpen`, is the case
`K = W`. -/
@[stacks 0A2P]
theorem exists_isOpen_subset_preimage_subset_of_isCompact (hC : IsLimit C) {K W : Set C.pt}
    (hK : IsCompact K) (hW : IsOpen W) (hKW : K ⊆ W) :
    ∃ (i : J) (U : Set (F.obj i)), IsOpen U ∧ K ⊆ C.π.app i ⁻¹' U ∧ C.π.app i ⁻¹' U ⊆ W := by
  rw [← hW.interior_eq, interior_eq_iUnion_preimage_interior_kernImage hC] at hKW
  obtain ⟨i, hi⟩ := hK.elim_directed_cover _
    (fun j ↦ isOpen_interior.preimage (C.π.app j).hom.continuous) hKW
    (directed_of_isCofiltered fun _ _ f ↦ preimage_interior_kernImage_subset C f W)
  exact ⟨i, _, isOpen_interior, hi, Set.subset_kernImage_iff.1 interior_subset⟩

/-- **Stacks 0A2P** (part 2). Let `C` be a limit cone over a cofiltered diagram `F : J ⥤ TopCat`.
Every quasi-compact open subset `W` of `C.pt` is `C.π.app i ⁻¹' U` for an index `i` and an open
subset `U ⊆ F.obj i`.

This is the case `K = W` of `TopCat.exists_isOpen_subset_preimage_subset_of_isCompact`. -/
@[stacks 0A2P]
theorem exists_isOpen_eq_preimage_of_isCompact_of_isOpen (hC : IsLimit C) {W : Set C.pt}
    (hWc : IsCompact W) (hWo : IsOpen W) :
    ∃ (i : J) (U : Set (F.obj i)), IsOpen U ∧ W = C.π.app i ⁻¹' U := by
  obtain ⟨i, U, hU, hWU, hUW⟩ :=
    exists_isOpen_subset_preimage_subset_of_isCompact hC hWc hWo subset_rfl
  exact ⟨i, U, hU, hWU.antisymm hUW⟩

end TopCat
