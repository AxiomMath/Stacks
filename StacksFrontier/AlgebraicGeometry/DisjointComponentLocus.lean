module

public import Mathlib.AlgebraicGeometry.Restrict
public import StacksFrontier.Topology.Irreducible.DisjointComponentLocus
public import StacksCore.Tactic.StacksAttribute

/-!
# The disjointness locus of the irreducible components of a scheme

Let `X` be a scheme whose irreducible components are enumerated by an equivalence
`e : ι ≃ {W // W ∈ irreducibleComponents X}` with a finite index, and let `η i` be a generic
point of the `i`-th component. Deleting every pairwise intersection of the components leaves a
*dense open* subscheme `denseOpen e` of `X`, on which the components cut out pairwise disjoint
*opens* `componentOpen e i` covering it.

This is the scheme-theoretic form of the topological statements in
`StacksFrontier/Topology/Irreducible/DisjointComponentLocus.lean`, packaged as `X.Opens` and as
opens of `(denseOpen e).toScheme`.

## Main definitions

* `Stacks.AlgebraicGeometry.DisjointComponentLocus.denseOpen` is the complement of the union of
  the pairwise intersections of the irreducible components, as an open of `X`.
* `Stacks.AlgebraicGeometry.DisjointComponentLocus.componentOpen` is the part of the `i`-th
  component inside it, as an open of `(denseOpen e).toScheme`.

## Main results

* `dense_denseOpen`: `denseOpen e` is dense.
* `coe_denseOpen`, `coe_componentOpen`: the underlying sets of `denseOpen e` and
  `componentOpen e i`.
* `disjoint_componentOpen`, `iSup_componentOpen`: the component opens are pairwise disjoint and
  cover `denseOpen e`.
* `genericPoint_mem_componentOpen`: the chosen generic point of the `i`-th component lies in the
  `i`-th component open.

## Implementation notes

`componentOpen e i` is the preimage of an open of `X`, not merely an open of the subspace: the
underlying set `componentPart` is already open in `X`, because on the disjointness locus
membership in one component is the *complement* of membership in the others.

Finiteness of `ι` is needed for openness, and the generic points are needed for density; the
two groups of results therefore carry different hypotheses rather than a single bundled one.
Generic points are taken as data rather than extracted from sobriety of `X`.

The index type `ι` is arbitrary (subject to `Finite`) rather than `Fin n`, which costs nothing
and avoids forcing the caller to transport along a cardinality equality.

## References

* [Stacks Project, Tag 004V](https://stacks.math.columbia.edu/tag/004V)
* [Stacks Project, Tag 004W](https://stacks.math.columbia.edu/tag/004W)
-/

@[expose] public section

open CategoryTheory TopologicalSpace AlgebraicGeometry
open Stacks.Topology.Irreducible

universe u

namespace Stacks.AlgebraicGeometry.DisjointComponentLocus

variable {X : Scheme.{u}} {ι : Type*} [Finite ι]
  (e : ι ≃ {W : Set X // W ∈ irreducibleComponents X})

/-- The open subscheme of `X` obtained by deleting every pairwise intersection of the
irreducible components of `X`. -/
@[ega "I 7.1.6" "partial"]
public def denseOpen : X.Opens :=
  ⟨disjointLocus (componentsOfEquiv e), isOpen_disjointLocus_componentsOfEquiv e⟩

/-- The underlying set of `denseOpen e` is the set of points lying on no two distinct irreducible
components. -/
@[simp]
public theorem coe_denseOpen :
    (denseOpen e : Set X) =
      {x | ∀ i j, i ≠ j → x ∉ (e i : Set X) ∩ (e j : Set X)} :=
  rfl

/-- A point lies in `denseOpen e` if and only if it lies on no two distinct irreducible
components. -/
public theorem mem_denseOpen {x : X} :
    x ∈ denseOpen e ↔ ∀ i j, i ≠ j → x ∉ (e i : Set X) ∩ (e j : Set X) :=
  Iff.rfl

/-- Deleting the pairwise intersections of the irreducible components leaves a dense open. -/
@[ega "I 7.1.6" "partial"]
public theorem dense_denseOpen {η : ι → X} (hη : ∀ i, IsGenericPoint (η i) (e i : Set X)) :
    Dense (denseOpen e : Set X) :=
  dense_disjointLocus_componentsOfEquiv e hη

/-- The part of the `i`-th irreducible component lying in `denseOpen e`, as an open of the
dense open subscheme. -/
public def componentOpen (i : ι) : (denseOpen e).toScheme.Opens :=
  (denseOpen e).ι ⁻¹ᵁ ⟨componentPart (componentsOfEquiv e) i,
    isOpen_componentPart_componentsOfEquiv e i⟩

/-- The underlying set of `componentOpen e i` is the set of points of the dense open whose image
in `X` lies on the `i`-th irreducible component. -/
@[simp]
public theorem coe_componentOpen (i : ι) :
    (componentOpen e i : Set (denseOpen e).toScheme) =
      {x : (denseOpen e).toScheme | x.1 ∈ (e i : Set X)} := by
  ext x
  simp only [componentOpen, Scheme.Hom.coe_preimage, Set.mem_preimage,
    Set.mem_ofPred_eq, Opens.coe_mk, mem_componentPart]
  exact ⟨fun h ↦ h.2, fun h ↦ ⟨x.2, h⟩⟩

/-- A point of the dense open lies in `componentOpen e i` if and only if its image in `X` lies on
the `i`-th irreducible component. -/
public theorem mem_componentOpen {i : ι} {x : (denseOpen e).toScheme} :
    x ∈ componentOpen e i ↔ x.1 ∈ (e i : Set X) :=
  Set.ext_iff.1 (coe_componentOpen e i) x

/-- A point of the dense open lies on at most one irreducible component. -/
public theorem val_mem_disjointLocus (x : (denseOpen e).toScheme) (i j : ι) (hij : i ≠ j) :
    x.1 ∉ (e i : Set X) ∩ (e j : Set X) :=
  x.2 i j hij

/-- The component opens of two distinct indices are disjoint. -/
public theorem disjoint_componentOpen {i j : ι} (hij : i ≠ j) :
    Disjoint (componentOpen e i) (componentOpen e j) := by
  rw [disjoint_iff, ← Opens.coe_inj, Opens.coe_inf, Opens.coe_bot, Set.eq_empty_iff_forall_notMem]
  intro x hx
  exact val_mem_disjointLocus e x i j hij
    ⟨(mem_componentOpen e).1 hx.1, (mem_componentOpen e).1 hx.2⟩

/-- The component opens cover the dense open. -/
public theorem iSup_componentOpen : (⨆ i, componentOpen e i) = ⊤ := by
  rw [← Opens.coe_inj, Opens.coe_iSup, Opens.coe_top, Set.eq_univ_iff_forall]
  intro x
  have hx : x.1 ∈ ⋃ i, componentPart (componentsOfEquiv e) i := by
    rw [iUnion_componentPart_componentsOfEquiv e]
    exact x.2
  obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hx
  exact Set.mem_iUnion.2 ⟨i, (mem_componentOpen e).2 hi.2⟩

/-- The chosen generic point of each irreducible component lies in the dense open. -/
public theorem genericPoint_mem_denseOpen {η : ι → X}
    (hη : ∀ i, IsGenericPoint (η i) (e i : Set X)) (i : ι) : η i ∈ denseOpen e :=
  genericPoint_mem_disjointLocus (componentsOfEquiv_mem_irreducibleComponents e)
    (injective_componentsOfEquiv e) hη i

/-- The chosen generic point of the `i`-th irreducible component lies in the `i`-th component
open. -/
public theorem genericPoint_mem_componentOpen {η : ι → X}
    (hη : ∀ i, IsGenericPoint (η i) (e i : Set X)) (i : ι) :
    (⟨η i, genericPoint_mem_denseOpen e hη i⟩ : (denseOpen e).toScheme) ∈ componentOpen e i :=
  (mem_componentOpen e).2
    (genericPoint_mem_componentPart (componentsOfEquiv_mem_irreducibleComponents e)
      (injective_componentsOfEquiv e) hη i).2

/-- There is a dense open `U` of `X`, consisting of the points lying on no two distinct
irreducible components, together with pairwise disjoint opens `V i` of `U` covering it, where
`V i` consists of the points of `U` lying on the `i`-th irreducible component. -/
public theorem exists_denseOpen_componentOpen {η : ι → X}
    (hη : ∀ i, IsGenericPoint (η i) (e i : Set X)) :
    ∃ (U : X.Opens) (V : ι → U.toScheme.Opens),
      Dense (U : Set X) ∧
      (U : Set X) = {x | ∀ i j, i ≠ j → x ∉ (e i : Set X) ∩ (e j : Set X)} ∧
      (∀ i, (V i : Set U.toScheme) = {x : U.toScheme | x.1 ∈ (e i : Set X)}) ∧
      (∀ i j, i ≠ j → Disjoint (V i) (V j)) ∧
      (⨆ i, V i) = ⊤ :=
  ⟨denseOpen e, componentOpen e, dense_denseOpen e hη, coe_denseOpen e, coe_componentOpen e,
    fun _ _ hij ↦ disjoint_componentOpen e hij, iSup_componentOpen e⟩

end Stacks.AlgebraicGeometry.DisjointComponentLocus
