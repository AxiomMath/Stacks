module

public import Mathlib.Topology.Irreducible
public import Mathlib.Topology.Sober
public import StacksCore.Tactic.StacksAttribute

/-!
# The locus where the irreducible components are pairwise disjoint

Let `X` be a topological space whose irreducible components are enumerated by a family
`Z : ι → Set X`. Deleting from `X` every pairwise intersection `Z i ∩ Z j` (`i ≠ j`) leaves
the *disjointness locus* `disjointLocus Z`. This file proves that this locus is open when
`ι` is finite, that it is dense as soon as every `Z i` has a generic point, and that inside
it the components become genuinely disjoint: the pieces
`componentPart Z i = disjointLocus Z ∩ Z i` are open, pairwise disjoint, cover the locus, and
each remains dense in its own component.

This is the topological input to the decomposition of a rational map on a scheme with finitely
many irreducible components into its restrictions to the individual components.

## Main definitions

* `Stacks.Topology.Irreducible.disjointLocus` is the complement of the union of the pairwise
  intersections of a family of sets.
* `Stacks.Topology.Irreducible.componentPart` is the part of `Z i` inside that locus.

## Main results

* `isOpen_disjointLocus`: the locus is open for a finite family of closed sets.
* `dense_disjointLocus`: the locus is dense once the family enumerates all irreducible
  components and each member has a generic point. Finiteness is not needed here.
* `isOpen_componentPart`: each piece is open **in `X`**, not merely in the locus.
* `disjoint_componentPart`, `iUnion_componentPart`: the pieces are pairwise disjoint and
  cover the locus.
* `closure_componentPart`: each piece is dense in its own component, so it is irreducible
  with the same generic point.

## Implementation notes

The family `Z` is an arbitrary indexed family of sets in the definitions, and the hypotheses
that it enumerates the irreducible components injectively and surjectively are explicit
arguments to the individual results, so that each result assumes only what it needs. In
particular `dense_disjointLocus` needs no finiteness of `ι`, `isOpen_disjointLocus` needs no
generic points, and the combinatorial half of the file (everything about `componentPart` as a
set, including the covering and disjointness) needs no topology on `X` whatsoever.

The last section records that an equivalence `ι ≃ {Z // Z ∈ irreducibleComponents X}` supplies
all three enumeration hypotheses at once, which is the form in which the enumeration usually
arises.

Generic points are taken as data (`η : ι → X` with `IsGenericPoint (η i) (Z i)`) rather than
produced from a sobriety assumption, since the consumer of these results already carries them.

`isOpen_componentPart` is stronger than the pieces merely being open in the subspace
`disjointLocus Z`: on the locus, membership in `Z i` is equivalent to *non*-membership in
every other `Z j`, which is an open condition on `X`.

## References

* [Stacks Project, Tag 004V](https://stacks.math.columbia.edu/tag/004V)
* [Stacks Project, Tag 004W](https://stacks.math.columbia.edu/tag/004W)
-/

@[expose] public section

open Set

namespace Stacks.Topology.Irreducible

variable {X : Type*} {ι : Type*}

/-- The locus of points that lie on at most one member of the family `Z`, i.e. the complement
of the union of all pairwise intersections `Z i ∩ Z j` with `i ≠ j`. -/
public def disjointLocus (Z : ι → Set X) : Set X :=
  {x | ∀ i j, i ≠ j → x ∉ Z i ∩ Z j}

/-- A point lies in the disjointness locus iff it lies on no two distinct members of `Z`. -/
public theorem mem_disjointLocus {Z : ι → Set X} {x : X} :
    x ∈ disjointLocus Z ↔ ∀ i j, i ≠ j → x ∉ Z i ∩ Z j :=
  Iff.rfl

/-- The disjointness locus is the complement of the union of the pairwise intersections
`Z i ∩ Z j` with `i ≠ j`. -/
public theorem disjointLocus_eq_compl (Z : ι → Set X) :
    disjointLocus Z = (⋃ i, ⋃ j, ⋃ _ : i ≠ j, Z i ∩ Z j)ᶜ := by
  ext x
  simp only [mem_disjointLocus, mem_compl_iff, mem_iUnion, not_exists]

/-- The part of the `i`-th member of the family lying in the disjointness locus. -/
public def componentPart (Z : ι → Set X) (i : ι) : Set X :=
  disjointLocus Z ∩ Z i

/-- A point lies in `componentPart Z i` iff it lies in the disjointness locus and on `Z i`. -/
public theorem mem_componentPart {Z : ι → Set X} {i : ι} {x : X} :
    x ∈ componentPart Z i ↔ x ∈ disjointLocus Z ∧ x ∈ Z i :=
  Iff.rfl

/-- Each component piece lies in the disjointness locus. -/
public theorem componentPart_subset_disjointLocus (Z : ι → Set X) (i : ι) :
    componentPart Z i ⊆ disjointLocus Z :=
  inter_subset_left

/-- Each component piece lies in its own member of the family. -/
public theorem componentPart_subset (Z : ι → Set X) (i : ι) : componentPart Z i ⊆ Z i :=
  inter_subset_right

/-- Component pieces with distinct indices are disjoint. -/
public theorem disjoint_componentPart {Z : ι → Set X} {i j : ι} (hij : i ≠ j) :
    Disjoint (componentPart Z i) (componentPart Z j) := by
  rw [Set.disjoint_left]
  intro x hxi hxj
  exact hxi.1 i j hij ⟨hxi.2, hxj.2⟩

/-- The component pieces are pairwise disjoint. -/
@[ega "I 7.1.6" "partial"]
public theorem pairwise_disjoint_componentPart (Z : ι → Set X) :
    Pairwise (Function.onFun Disjoint (componentPart Z)) :=
  fun _ _ hij ↦ disjoint_componentPart hij

/-- On the disjointness locus of a covering family, lying on `Z i` is the same as lying on no
other `Z j`. -/
public theorem componentPart_eq_diff {Z : ι → Set X} (hZcov : ⋃ i, Z i = univ) (i : ι) :
    componentPart Z i = disjointLocus Z \ ⋃ j ∈ ({i}ᶜ : Set ι), Z j := by
  ext x
  simp only [mem_componentPart, mem_sdiff, mem_iUnion, mem_compl_iff, mem_singleton_iff,
    not_exists, exists_prop, not_and]
  refine ⟨fun ⟨hx, hxi⟩ ↦ ⟨hx, fun j hj hxj ↦ hx i j (Ne.symm hj) ⟨hxi, hxj⟩⟩,
    fun ⟨hx, hxj⟩ ↦ ⟨hx, ?_⟩⟩
  obtain ⟨j, hj⟩ := iUnion_eq_univ_iff.1 hZcov x
  by_cases hji : j = i
  · exact hji ▸ hj
  · exact absurd hj (hxj j hji)

/-- The component pieces cover the disjointness locus. -/
public theorem iUnion_componentPart {Z : ι → Set X} (hZcov : ⋃ i, Z i = univ) :
    ⋃ i, componentPart Z i = disjointLocus Z := by
  refine (iUnion_subset fun i ↦ componentPart_subset_disjointLocus Z i).antisymm fun x hx ↦ ?_
  obtain ⟨i, hi⟩ := iUnion_eq_univ_iff.1 hZcov x
  exact mem_iUnion.2 ⟨i, hx, hi⟩

section Topology

variable [TopologicalSpace X]

/-- The locus where a finite family of closed sets is pairwise disjoint is open. -/
public theorem isOpen_disjointLocus [Finite ι] {Z : ι → Set X} (hZ : ∀ i, IsClosed (Z i)) :
    IsOpen (disjointLocus Z) := by
  rw [disjointLocus_eq_compl, isOpen_compl_iff]
  exact isClosed_iUnion_of_finite fun i ↦ isClosed_iUnion_of_finite fun j ↦
    isClosed_iUnion_of_finite fun _ ↦ (hZ i).inter (hZ j)

/-- Each component piece of a finite covering family of closed sets is open in the ambient
space, not merely in the disjointness locus. -/
public theorem isOpen_componentPart [Finite ι] {Z : ι → Set X} (hZcl : ∀ i, IsClosed (Z i))
    (hZcov : ⋃ i, Z i = univ) (i : ι) : IsOpen (componentPart Z i) := by
  rw [componentPart_eq_diff hZcov, sdiff_eq]
  refine (isOpen_disjointLocus hZcl).inter ?_
  rw [isOpen_compl_iff]
  exact Set.Finite.isClosed_biUnion (Set.toFinite _) fun j _ ↦ hZcl j

/-- An irreducible component containing a generic point of an irreducible component is that
component. -/
@[ega "0 2.1.6"]
public theorem eq_of_isGenericPoint_mem {Z W : Set X} (hZ : Z ∈ irreducibleComponents X)
    (hW : W ∈ irreducibleComponents X) {x : X} (hx : IsGenericPoint x Z) (hxW : x ∈ W) :
    Z = W := by
  have hZW : Z ⊆ W := by
    rw [← hx]
    exact (isClosed_of_mem_irreducibleComponents W hW).closure_subset_iff.2
      (singleton_subset_iff.2 hxW)
  exact hZW.antisymm (hZ.2 hW.1 hZW)

/-- A set containing a generic point of `S` is dense in `S`. -/
private theorem subset_closure_of_isGenericPoint_mem {x : X} {S T : Set X}
    (hx : IsGenericPoint x S) (hxT : x ∈ T) : S ⊆ closure T :=
  hx.def ▸ closure_mono (singleton_subset_iff.2 hxT)

/-- The irreducible components in an injective enumeration are pairwise non-nested, so a
generic point of one of them lies on no other. -/
@[ega "I 7.1.6" "partial"]
public theorem genericPoint_mem_disjointLocus {Z : ι → Set X}
    (hZ : ∀ i, Z i ∈ irreducibleComponents X) (hZinj : Function.Injective Z) {η : ι → X}
    (hη : ∀ i, IsGenericPoint (η i) (Z i)) (i : ι) : η i ∈ disjointLocus Z := by
  intro j k hjk hmem
  exact hjk (hZinj ((eq_of_isGenericPoint_mem (hZ i) (hZ j) (hη i) hmem.1).symm.trans
    (eq_of_isGenericPoint_mem (hZ i) (hZ k) (hη i) hmem.2)))

/-- An enumeration of all the irreducible components covers the space. -/
public theorem iUnion_eq_univ_of_forall_exists_eq {Z : ι → Set X}
    (hZsurj : ∀ W ∈ irreducibleComponents X, ∃ i, Z i = W) : ⋃ i, Z i = univ := by
  refine eq_univ_of_forall fun x ↦ ?_
  obtain ⟨i, hi⟩ := hZsurj _ (irreducibleComponent_mem_irreducibleComponents x)
  exact mem_iUnion.2 ⟨i, hi ▸ mem_irreducibleComponent⟩

/-- For an injective enumeration of irreducible components, the generic point of `Z i` lies in
the component piece `componentPart Z i`. -/
public theorem genericPoint_mem_componentPart {Z : ι → Set X}
    (hZ : ∀ i, Z i ∈ irreducibleComponents X) (hZinj : Function.Injective Z) {η : ι → X}
    (hη : ∀ i, IsGenericPoint (η i) (Z i)) (i : ι) : η i ∈ componentPart Z i :=
  ⟨genericPoint_mem_disjointLocus hZ hZinj hη i, (hη i).mem⟩

/-- The disjointness locus of an injective enumeration of all the irreducible components is
dense: it contains every generic point. No finiteness of the index is needed. -/
public theorem dense_disjointLocus {Z : ι → Set X} (hZ : ∀ i, Z i ∈ irreducibleComponents X)
    (hZinj : Function.Injective Z) (hZsurj : ∀ W ∈ irreducibleComponents X, ∃ i, Z i = W)
    {η : ι → X} (hη : ∀ i, IsGenericPoint (η i) (Z i)) : Dense (disjointLocus Z) := by
  intro x
  obtain ⟨i, hi⟩ := iUnion_eq_univ_iff.1 (iUnion_eq_univ_of_forall_exists_eq hZsurj) x
  exact subset_closure_of_isGenericPoint_mem (hη i)
    (genericPoint_mem_disjointLocus hZ hZinj hη i) hi

/-- Each component piece is dense in its own irreducible component; in particular it is
irreducible with the same generic point. -/
public theorem closure_componentPart {Z : ι → Set X} (hZ : ∀ i, Z i ∈ irreducibleComponents X)
    (hZinj : Function.Injective Z) {η : ι → X} (hη : ∀ i, IsGenericPoint (η i) (Z i)) (i : ι) :
    closure (componentPart Z i) = Z i := by
  refine ((isClosed_of_mem_irreducibleComponents _ (hZ i)).closure_subset_iff.2
    (componentPart_subset Z i)).antisymm ?_
  exact subset_closure_of_isGenericPoint_mem (hη i) (genericPoint_mem_componentPart hZ hZinj hη i)

/-- The generic point of `Z i` is a generic point of the closure of `componentPart Z i`. -/
public theorem isGenericPoint_closure_componentPart {Z : ι → Set X}
    (hZ : ∀ i, Z i ∈ irreducibleComponents X) (hZinj : Function.Injective Z) {η : ι → X}
    (hη : ∀ i, IsGenericPoint (η i) (Z i)) (i : ι) :
    IsGenericPoint (η i) (closure (componentPart Z i)) :=
  (closure_componentPart hZ hZinj hη i).symm ▸ hη i

section Enumeration

variable (e : ι ≃ {W : Set X // W ∈ irreducibleComponents X})

/-- The family of irreducible components indexed through an equivalence with the set of all
of them. -/
public abbrev componentsOfEquiv (i : ι) : Set X := (e i : Set X)

/-- Each member of `componentsOfEquiv e` is an irreducible component. -/
public theorem componentsOfEquiv_mem_irreducibleComponents (i : ι) :
    componentsOfEquiv e i ∈ irreducibleComponents X :=
  (e i).2

/-- The family `componentsOfEquiv e` is injective. -/
public theorem injective_componentsOfEquiv : Function.Injective (componentsOfEquiv e) :=
  fun _ _ h ↦ e.injective (Subtype.ext h)

/-- Every irreducible component is a member of the family `componentsOfEquiv e`. -/
public theorem exists_componentsOfEquiv_eq (W : Set X) (hW : W ∈ irreducibleComponents X) :
    ∃ i, componentsOfEquiv e i = W :=
  ⟨e.symm ⟨W, hW⟩, congrArg Subtype.val (e.apply_symm_apply ⟨W, hW⟩)⟩

/-- The members of `componentsOfEquiv e` cover the space. -/
public theorem iUnion_componentsOfEquiv : ⋃ i, componentsOfEquiv e i = univ :=
  iUnion_eq_univ_of_forall_exists_eq (exists_componentsOfEquiv_eq e)

/-- With finitely many irreducible components, the disjointness locus of `componentsOfEquiv e`
is open. -/
public theorem isOpen_disjointLocus_componentsOfEquiv [Finite ι] :
    IsOpen (disjointLocus (componentsOfEquiv e)) :=
  isOpen_disjointLocus fun i ↦ isClosed_of_mem_irreducibleComponents _ (e i).2

/-- If each irreducible component has a generic point, the disjointness locus of
`componentsOfEquiv e` is dense. -/
public theorem dense_disjointLocus_componentsOfEquiv {η : ι → X}
    (hη : ∀ i, IsGenericPoint (η i) (componentsOfEquiv e i)) :
    Dense (disjointLocus (componentsOfEquiv e)) :=
  dense_disjointLocus (componentsOfEquiv_mem_irreducibleComponents e)
    (injective_componentsOfEquiv e) (exists_componentsOfEquiv_eq e) hη

/-- With finitely many irreducible components, each component piece of `componentsOfEquiv e`
is open. -/
public theorem isOpen_componentPart_componentsOfEquiv [Finite ι] (i : ι) :
    IsOpen (componentPart (componentsOfEquiv e) i) :=
  isOpen_componentPart (fun j ↦ isClosed_of_mem_irreducibleComponents _ (e j).2)
    (iUnion_componentsOfEquiv e) i

/-- The component pieces of `componentsOfEquiv e` cover its disjointness locus. -/
public theorem iUnion_componentPart_componentsOfEquiv :
    ⋃ i, componentPart (componentsOfEquiv e) i = disjointLocus (componentsOfEquiv e) :=
  iUnion_componentPart (iUnion_componentsOfEquiv e)

end Enumeration

end Topology

end Stacks.Topology.Irreducible
