module

public import Mathlib.Topology.KrullDimension
public import Mathlib.Topology.NoetherianSpace
public import StacksFrontier.Topology.Dimension.SpecializingSurjection
public import StacksFrontier.Topology.Irreducible.DisjointComponentLocus
public import StacksCore.Tactic.StacksAttribute

/-!
# Noetherian spaces of Krull dimension at most one

A Noetherian sober `T0` space `X` with `topologicalKrullDim X ≤ 1` is built out of its
finitely many irreducible components and a discrete remainder: once an open set has been
chosen that meets every component in a neighbourhood of its generic point, what is left over
is a *finite* set of *closed* points. This file proves that, and packages it as a refinement
statement for open covers: every open cover of such a space has a refinement consisting of
one pairwise disjoint piece per irreducible component, each piece dense in its component,
together with a finite set of leftover closed points.

This is the purely topological content of the dimension hypothesis in the one-dimensional
results of the Stacks project, where it is what makes a "`dim ≤ 1`" argument reduce to a
statement about finitely many closed points.

## Main results

* `Stacks.Topology.Dimension.eq_of_specializes_of_topologicalKrullDim_le_zero`,
  `Stacks.Topology.Dimension.isClosed_singleton_of_topologicalKrullDim_le_zero`,
  `Stacks.Topology.Dimension.finite_of_topologicalKrullDim_le_zero`: a `T0` space of Krull
  dimension at most zero has no nontrivial specializations, hence only closed points, and is
  finite as soon as it is Noetherian and sober.
* `Stacks.Topology.Dimension.isClosed_singleton_of_not_irreducibleComponent_subset` and
  `Stacks.Topology.Dimension.finite_of_not_irreducibleComponent_subset`: in a space of Krull
  dimension at most one, a closed set containing no irreducible component consists of closed
  points, and is finite when the space is Noetherian and sober.
* `Stacks.Topology.Dimension.exists_disjoint_subordinate_opens_of_topologicalKrullDim_le_one`:
  the refinement statement. Given an open cover of a Noetherian sober `T0` space of Krull
  dimension at most one there are pairwise disjoint open sets, one per irreducible component,
  each inside a member of the cover and dense in its component, whose union has finite
  complement consisting of closed points.

## Implementation notes

The disjointness of the pieces is not an extra construction: it is
`Stacks.Topology.Irreducible.componentPart`, the part of an irreducible component lying on no
other component, intersected with a member of the cover chosen around the generic point. What
the dimension hypothesis adds is that the complement of the union of those pieces is finite
and discrete, which is proved by exhibiting a chain of three irreducible closed subsets
whenever a point of that complement fails to be closed.

No separation beyond `T0` is used, and no finiteness of the index type of the cover.
Soberness enters only through the existence of generic points of the irreducible components,
and Noetherianness only through their finiteness and the decomposition of a closed set into
finitely many irreducible closed pieces.

## References

* [Stacks Project, Tag 0055](https://stacks.math.columbia.edu/tag/0055)
* [Stacks Project, Tag 0052](https://stacks.math.columbia.edu/tag/0052)
-/

@[expose] public section

open Set Order TopologicalSpace Topology
open IrreducibleCloseds (closureSingleton)

universe u

namespace Stacks.Topology.Dimension

variable {X : Type u} [TopologicalSpace X]

private theorem closurePoint_le_iff {x y : X} :
    closureSingleton y ≤ closureSingleton x ↔ x ⤳ y :=
  specializes_iff_closure_subset.symm

private theorem closurePoint_lt_of_mem_closure_of_ne [T0Space X] {x y : X}
    (hy : y ∈ closure ({x} : Set X)) (hyx : y ≠ x) : closureSingleton y < closureSingleton x := by
  refine lt_of_le_of_ne (closurePoint_le_iff.2 (specializes_iff_mem_closure.2 hy)) fun h ↦ hyx ?_
  exact ((closurePoint_le_iff.1 h.ge).antisymm
    (specializes_iff_mem_closure.2 hy)).eq

/-- A set with a closed generic point is that point. -/
private theorem eq_singleton_of_isGenericPoint_of_isClosed {η : X} {t : Set X}
    (hη : IsGenericPoint η t) (h : IsClosed ({η} : Set X)) : t = {η} := by
  rw [← isGenericPoint_def.1 hη, h.closure_eq]

/-- In a `T0` space of Krull dimension at most zero there are no nontrivial specializations. -/
public theorem eq_of_specializes_of_topologicalKrullDim_le_zero [T0Space X]
    (h : topologicalKrullDim X ≤ 0) {x y : X} (hxy : x ⤳ y) : x = y := by
  have h1 : closureSingleton x ≤ closureSingleton y :=
    krullDim_nonpos_iff_forall_isMax.1 h (closureSingleton y) (closurePoint_le_iff.2 hxy)
  exact (hxy.antisymm (closurePoint_le_iff.1 h1)).eq

/-- In a `T0` space of Krull dimension at most zero every point is closed. -/
public theorem isClosed_singleton_of_topologicalKrullDim_le_zero [T0Space X]
    (h : topologicalKrullDim X ≤ 0) (x : X) : IsClosed ({x} : Set X) := by
  exact closure_subset_iff_isClosed.1 fun y hy ↦
    (eq_of_specializes_of_topologicalKrullDim_le_zero h (specializes_iff_mem_closure.2 hy)).symm

/-- A Noetherian sober `T0` space of Krull dimension at most zero is finite. -/
public theorem finite_of_topologicalKrullDim_le_zero [T0Space X] [NoetherianSpace X]
    [QuasiSober X] (h : topologicalKrullDim X ≤ 0) : (univ : Set X).Finite := by
  rw [← sUnion_irreducibleComponents (X := X)]
  refine NoetherianSpace.finite_irreducibleComponents.sUnion fun C hC ↦ ?_
  obtain ⟨η, hη⟩ := QuasiSober.sober hC.1 (isClosed_of_mem_irreducibleComponents C hC)
  rw [eq_singleton_of_isGenericPoint_of_isClosed hη
    (isClosed_singleton_of_topologicalKrullDim_le_zero h η)]
  exact finite_singleton η

/-- In a space of Krull dimension at most one, a point of a closed set that contains no
irreducible component is a closed point: a nontrivial specialization into it would, together
with the irreducible component above it, give a chain of three irreducible closed sets. -/
public theorem isClosed_singleton_of_not_irreducibleComponent_subset [T0Space X]
    (hdim : topologicalKrullDim X ≤ 1)
    {T : Set X} (hT : IsClosed T) (hTc : ∀ C ∈ irreducibleComponents X, ¬ C ⊆ T)
    {x : X} (hx : x ∈ T) : IsClosed ({x} : Set X) := by
  obtain ⟨C, hC, hCsub⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
    (closure ({x} : Set X)) isIrreducible_singleton.closure
  have hxT : closure ({x} : Set X) ⊆ T :=
    hT.closure_subset_iff.2 (singleton_subset_iff.2 hx)
  set CC : IrreducibleCloseds X :=
    ⟨C, hC.1, isClosed_of_mem_irreducibleComponents C hC⟩ with hCC
  have hlt : closureSingleton x < CC := by
    refine lt_of_le_of_ne hCsub fun h ↦ hTc C hC ?_
    have hcar : closure ({x} : Set X) = C := congrArg IrreducibleCloseds.carrier h
    rw [← hcar]
    exact hxT
  have hx' : closure ({x} : Set X) = {x} := by
    refine Subset.antisymm (fun y hy ↦ ?_) subset_closure
    by_contra hyx
    have hyx' : closureSingleton y < closureSingleton x :=
      closurePoint_lt_of_mem_closure_of_ne hy (by simpa using hyx)
    have hchain : ∃ l : LTSeries (IrreducibleCloseds X), l.length = 2 :=
      ⟨((RelSeries.singleton _ (closureSingleton y)).snoc (closureSingleton x)
        (by simpa using hyx')).snoc CC (by simpa using hlt), rfl⟩
    have h2 : ((2 : ℕ) : WithBot ℕ∞) ≤ 1 := (le_krullDim_iff.2 hchain).trans hdim
    exact absurd h2 (by decide)
  rw [← hx']
  exact isClosed_closure

/-- In a Noetherian sober `T0` space of Krull dimension at most one, a closed set containing
no irreducible component is finite. -/
public theorem finite_of_not_irreducibleComponent_subset [T0Space X] [NoetherianSpace X]
    [QuasiSober X] (hdim : topologicalKrullDim X ≤ 1) {T : Set X} (hT : IsClosed T)
    (hTc : ∀ C ∈ irreducibleComponents X, ¬ C ⊆ T) : T.Finite := by
  obtain ⟨S, hSf, hScl, hSi, hST⟩ := NoetherianSpace.exists_finite_set_isClosed_irreducible hT
  rw [hST]
  refine hSf.sUnion fun t ht ↦ ?_
  obtain ⟨η, hη⟩ := QuasiSober.sober (hSi t ht) (hScl t ht)
  have hηT : η ∈ T := hST ▸ mem_sUnion.2 ⟨t, ht, hη.mem⟩
  rw [eq_singleton_of_isGenericPoint_of_isClosed hη
    (isClosed_singleton_of_not_irreducibleComponent_subset hdim hT hTc hηT)]
  exact finite_singleton η

/-- **The refinement statement for a Noetherian sober space of Krull dimension at most one.**
Every open cover `W` admits, for each irreducible component `C`, an open set `A C` contained
in a member of the cover and dense in `C`, with the `A C` pairwise disjoint; and the
complement of their union is a finite set of closed points.

This is the topological content of a "`dim ≤ 1`" hypothesis: after the generic points have
been separated, only finitely many closed points remain to be dealt with. -/
public theorem exists_disjoint_subordinate_opens_of_topologicalKrullDim_le_one [T0Space X]
    [NoetherianSpace X] [QuasiSober X] (hdim : topologicalKrullDim X ≤ 1)
    {ι : Type*} {W : ι → Set X} (hWo : ∀ i, IsOpen (W i))
    (hWc : ∀ x : X, ∃ i, x ∈ W i) :
    ∃ (A : irreducibleComponents X → Set X) (j : irreducibleComponents X → ι),
      (∀ C, IsOpen (A C)) ∧ (∀ C, A C ⊆ W (j C)) ∧
        (∀ C, closure (A C) = (C : Set X)) ∧
        Pairwise (Function.onFun Disjoint A) ∧
        ((⋃ C, A C)ᶜ).Finite ∧
        ∀ x ∈ ((⋃ C, A C)ᶜ), IsClosed ({x} : Set X) := by
  have : Finite (irreducibleComponents X) :=
    NoetherianSpace.finite_irreducibleComponents.to_subtype
  set Z : irreducibleComponents X → Set X := fun C ↦ (C : Set X) with hZdef
  have hZ : ∀ C, Z C ∈ irreducibleComponents X := fun C ↦ C.2
  have hZinj : Function.Injective Z := Subtype.val_injective
  have hZcl : ∀ C, IsClosed (Z C) := fun C ↦ isClosed_of_mem_irreducibleComponents _ C.2
  have hZcov : ⋃ C, Z C = univ :=
    Irreducible.iUnion_eq_univ_of_forall_exists_eq fun V hV ↦ ⟨⟨V, hV⟩, rfl⟩
  choose η hη using fun C : irreducibleComponents X ↦ QuasiSober.sober C.2.1 (hZcl C)
  choose j hj using fun C : irreducibleComponents X ↦ hWc (η C)
  set A : irreducibleComponents X → Set X :=
    fun C ↦ Irreducible.componentPart Z C ∩ W (j C) with hAdef
  have hAopen : ∀ C, IsOpen (A C) := fun C ↦
    (Irreducible.isOpen_componentPart hZcl hZcov C).inter (hWo _)
  have hηA : ∀ C, η C ∈ A C := fun C ↦
    ⟨Irreducible.genericPoint_mem_componentPart hZ hZinj hη C, hj C⟩
  have hcl : IsClosed ((⋃ C, A C)ᶜ) := (isOpen_iUnion hAopen).isClosed_compl
  have hnc : ∀ V ∈ irreducibleComponents X, ¬ V ⊆ (⋃ C, A C)ᶜ := fun V hV hsub ↦
    hsub (hη ⟨V, hV⟩).mem (mem_iUnion.2 ⟨⟨V, hV⟩, hηA ⟨V, hV⟩⟩)
  refine ⟨A, j, hAopen, fun C ↦ inter_subset_right, fun C ↦ ?_,
    fun C C' hCC' ↦ (Irreducible.disjoint_componentPart hCC').mono inter_subset_left
      inter_subset_left,
    finite_of_not_irreducibleComponent_subset hdim hcl hnc,
    fun x hx ↦ isClosed_singleton_of_not_irreducibleComponent_subset hdim hcl hnc hx⟩
  refine Subset.antisymm ((hZcl C).closure_subset_iff.2
    (inter_subset_left.trans (Irreducible.componentPart_subset Z C))) ?_
  rw [← isGenericPoint_def.1 (hη C)]
  exact closure_mono (singleton_subset_iff.2 (hηA C))

/-! ### The irreducible case

On an irreducible space the only irreducible component is the whole space, so "contains no
irreducible component" is "is not everything". -/

/-- In an irreducible space, a proper subset contains no irreducible component. -/
private theorem not_subset_of_ne_univ [IrreducibleSpace X] {T : Set X} (hne : T ≠ Set.univ) :
    ∀ C ∈ irreducibleComponents X, ¬ C ⊆ T := fun C hC hCT ↦ hne (eq_univ_of_univ_subset
  (((irreducibleComponents_eq_singleton (X := X)) ▸ hC : C ∈ ({univ} : Set (Set X))) ▸ hCT))

/-- In an irreducible space of Krull dimension at most one, every point of a proper closed
subset is a closed point. -/
public theorem isClosed_singleton_of_mem_of_ne_univ [T0Space X] [IrreducibleSpace X]
    (hdim : topologicalKrullDim X ≤ 1) {T : Set X} (hT : IsClosed T) (hne : T ≠ Set.univ)
    {x : X} (hx : x ∈ T) : IsClosed ({x} : Set X) :=
  isClosed_singleton_of_not_irreducibleComponent_subset hdim hT (not_subset_of_ne_univ hne) hx

/-- In a Noetherian sober irreducible space of Krull dimension at most one, a proper closed
subset is finite. -/
public theorem finite_of_isClosed_of_ne_univ [T0Space X] [NoetherianSpace X] [QuasiSober X]
    [IrreducibleSpace X] (hdim : topologicalKrullDim X ≤ 1) {T : Set X} (hT : IsClosed T)
    (hne : T ≠ Set.univ) : T.Finite :=
  finite_of_not_irreducibleComponent_subset hdim hT (not_subset_of_ne_univ hne)

/-- In a sober irreducible space of Krull dimension at most one, a proper irreducible closed
subset has at most one point: its generic point is closed, so the subset is that point. -/
public theorem subsingleton_of_isIrreducible_of_ne_univ [T0Space X] [QuasiSober X]
    [IrreducibleSpace X] (hdim : topologicalKrullDim X ≤ 1) {T : Set X} (hT : IsClosed T)
    (hTi : IsIrreducible T) (hne : T ≠ Set.univ) : T.Subsingleton := by
  obtain ⟨p, hp⟩ := QuasiSober.sober hTi hT
  rw [eq_singleton_of_isGenericPoint_of_isClosed hp
    (isClosed_singleton_of_mem_of_ne_univ hdim hT hne hp.mem)]
  exact subsingleton_singleton

end Stacks.Topology.Dimension
