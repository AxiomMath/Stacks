module

public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksFrontier.Topology.Dimension.DimensionLEOne
public import StacksFrontier.Topology.Irreducible.DisjointComponentLocus

/-!
# Where the irreducible components of a one-dimensional space meet

On a Noetherian sober space of Krull dimension at most one, two distinct irreducible components
meet in a *finite* set of *closed* points. Equivalently, the complement of
`Stacks.Topology.Irreducible.disjointLocus` — the locus of points lying on at most one
component — is finite and consists of closed points.

## Main results

* `StacksTag09NX.finite_compl_disjointLocus`: the complement of the disjointness locus of an
  injective enumeration of all the irreducible components is finite.
* `StacksTag09NX.isClosed_singleton_of_notMem_disjointLocus`: each of its points is closed.
* `StacksTag09NX.finite_inter_of_ne`, `StacksTag09NX.discreteTopology_inter_of_ne`: two distinct
  components of the enumeration meet in a finite, hence discrete, set.
* `StacksTag09NX.discreteTopology_compl_disjointLocus`,
  `StacksTag09NX.discreteTopology_compl_disjointLocus_irreducibleComponents`: the *whole*
  non-disjointness locus is a discrete subspace.
* `StacksTag09NX.finite_inter_irreducibleComponents`,
  `StacksTag09NX.discreteTopology_inter_irreducibleComponents`: the same for two distinct
  irreducible components of a Noetherian scheme of dimension at most one, with no enumeration to
  supply.

## Implementation notes

The closed-point statement does not need the space to be Noetherian; the finiteness statement does.
Only `≤ 1` is assumed, so the results include the zero-dimensional case.

`discreteTopology_of_finite_of_isClosed` does not assume the ambient space `T1`, unlike
`Set.Finite.isDiscrete`.

## References

* [Stacks Project, Tag 09NX](https://stacks.math.columbia.edu/tag/09NX)
* [Stacks Project, Tag 09NE](https://stacks.math.columbia.edu/tag/09NE)
-/

public section

open Set TopologicalSpace Stacks.Topology.Irreducible AlgebraicGeometry

universe u

namespace StacksTag09NX

section General

variable {X : Type*} [TopologicalSpace X]

/-- A finite set all of whose points are closed in the ambient space is discrete. -/
public theorem discreteTopology_of_finite_of_isClosed {s : Set X} (hs : s.Finite)
    (hcl : ∀ x ∈ s, IsClosed ({x} : Set X)) : DiscreteTopology ↥s := by
  have : Finite ↥s := hs.to_subtype
  have : T1Space ↥s := ⟨fun x ↦ by
    have hx : ({x} : Set ↥s) = Subtype.val ⁻¹' ({(x : X)} : Set X) := by
      ext y
      simp [Subtype.ext_iff]
    rw [hx]
    exact (hcl x.1 x.2).preimage continuous_subtype_val⟩
  infer_instance

variable [T0Space X] [QuasiSober X] {ι : Type*} [Finite ι] {Z : ι → Set X}

/-- The complement of the disjointness locus of an enumeration of the irreducible components is
closed and contains no irreducible component. -/
private theorem isClosed_and_forall_not_subset_compl_disjointLocus
    {Y : Type*} [TopologicalSpace Y] [QuasiSober Y] {κ : Type*} [Finite κ] {Z : κ → Set Y}
    (hZ : ∀ i, Z i ∈ irreducibleComponents Y) (hZinj : Function.Injective Z)
    (hZsurj : ∀ W ∈ irreducibleComponents Y, ∃ i, Z i = W) :
    IsClosed (disjointLocus Z)ᶜ ∧ ∀ C ∈ irreducibleComponents Y, ¬ C ⊆ (disjointLocus Z)ᶜ := by
  have hZcl : ∀ i, IsClosed (Z i) := fun i ↦ isClosed_of_mem_irreducibleComponents _ (hZ i)
  choose η hη using fun i : κ ↦ QuasiSober.sober (hZ i).1 (hZcl i)
  refine ⟨(isOpen_disjointLocus hZcl).isClosed_compl, ?_⟩
  rintro _ hW hsub
  obtain ⟨i, rfl⟩ := hZsurj _ hW
  exact hsub (hη i ▸ subset_closure (mem_singleton (η i)))
    (genericPoint_mem_disjointLocus hZ hZinj hη i)

/-- **A point lying on two distinct irreducible components of a sober space of Krull dimension
at most one is closed.** -/
public theorem isClosed_singleton_of_notMem_disjointLocus
    (hdim : topologicalKrullDim X ≤ 1) (hZ : ∀ i, Z i ∈ irreducibleComponents X)
    (hZinj : Function.Injective Z)
    (hZsurj : ∀ W ∈ irreducibleComponents X, ∃ i, Z i = W)
    {x : X} (hx : x ∉ disjointLocus Z) : IsClosed ({x} : Set X) := by
  obtain ⟨hcl, hC⟩ := isClosed_and_forall_not_subset_compl_disjointLocus hZ hZinj hZsurj
  exact Stacks.Topology.Dimension.isClosed_singleton_of_not_irreducibleComponent_subset
    hdim hcl hC hx

variable [NoetherianSpace X]

/-- **The locus where the irreducible components of a Noetherian sober space of Krull dimension at
most one fail to be disjoint is finite.** -/
public theorem finite_compl_disjointLocus (hdim : topologicalKrullDim X ≤ 1)
    (hZ : ∀ i, Z i ∈ irreducibleComponents X) (hZinj : Function.Injective Z)
    (hZsurj : ∀ W ∈ irreducibleComponents X, ∃ i, Z i = W) :
    ((disjointLocus Z)ᶜ).Finite := by
  obtain ⟨hcl, hC⟩ := isClosed_and_forall_not_subset_compl_disjointLocus hZ hZinj hZsurj
  exact Stacks.Topology.Dimension.finite_of_not_irreducibleComponent_subset hdim hcl hC

/-- **The whole locus where the irreducible components of a Noetherian sober space of Krull
dimension at most one fail to be disjoint is a discrete subspace.** -/
public theorem discreteTopology_compl_disjointLocus (hdim : topologicalKrullDim X ≤ 1)
    (hZ : ∀ i, Z i ∈ irreducibleComponents X) (hZinj : Function.Injective Z)
    (hZsurj : ∀ W ∈ irreducibleComponents X, ∃ i, Z i = W) :
    DiscreteTopology ↥((disjointLocus Z)ᶜ) :=
  discreteTopology_of_finite_of_isClosed (finite_compl_disjointLocus hdim hZ hZinj hZsurj)
    fun _ hx ↦ isClosed_singleton_of_notMem_disjointLocus hdim hZ hZinj hZsurj hx

/-- **Two distinct members of an enumeration of the irreducible components meet in a finite
set.** -/
public theorem finite_inter_of_ne (hdim : topologicalKrullDim X ≤ 1)
    (hZ : ∀ i, Z i ∈ irreducibleComponents X) (hZinj : Function.Injective Z)
    (hZsurj : ∀ W ∈ irreducibleComponents X, ∃ i, Z i = W) {i j : ι} (hij : i ≠ j) :
    (Z i ∩ Z j).Finite :=
  (finite_compl_disjointLocus hdim hZ hZinj hZsurj).subset fun _ hx hmem ↦ hmem i j hij hx

/-- **Two distinct members of an enumeration of the irreducible components meet in a discrete
set.** -/
public theorem discreteTopology_inter_of_ne (hdim : topologicalKrullDim X ≤ 1)
    (hZ : ∀ i, Z i ∈ irreducibleComponents X) (hZinj : Function.Injective Z)
    (hZsurj : ∀ W ∈ irreducibleComponents X, ∃ i, Z i = W) {i j : ι} (hij : i ≠ j) :
    DiscreteTopology ↥(Z i ∩ Z j) :=
  discreteTopology_of_finite_of_isClosed (finite_inter_of_ne hdim hZ hZinj hZsurj hij)
    fun _ hx ↦ isClosed_singleton_of_notMem_disjointLocus hdim hZ hZinj hZsurj
      fun hmem ↦ hmem i j hij hx

end General

section Scheme

variable (X : Scheme.{u}) [IsNoetherian X]

/-- **On a Noetherian scheme of dimension at most one the locus where the irreducible components
fail to be disjoint is finite.** -/
public theorem finite_compl_disjointLocus_irreducibleComponents
    (hdim : topologicalKrullDim (X : Type u) ≤ 1) :
    ((disjointLocus (Subtype.val : irreducibleComponents (X : Type u) → Set X))ᶜ).Finite := by
  have : Finite (irreducibleComponents (X : Type u)) :=
    NoetherianSpace.finite_irreducibleComponents.to_subtype
  have _ : NoetherianSpace (X : Type u) := IsNoetherian.noetherianSpace
  exact finite_compl_disjointLocus hdim (fun C ↦ C.2) Subtype.val_injective
    fun W hW ↦ ⟨⟨W, hW⟩, rfl⟩

/-- **A point of a Noetherian scheme of dimension at most one lying on two distinct irreducible
components is closed.** -/
public theorem isClosed_singleton_of_notMem_disjointLocus_irreducibleComponents
    (hdim : topologicalKrullDim (X : Type u) ≤ 1) {x : X}
    (hx : x ∉ disjointLocus (Subtype.val : irreducibleComponents (X : Type u) → Set X)) :
    IsClosed ({x} : Set X) := by
  have : Finite (irreducibleComponents (X : Type u)) :=
    NoetherianSpace.finite_irreducibleComponents.to_subtype
  exact isClosed_singleton_of_notMem_disjointLocus hdim (fun C ↦ C.2) Subtype.val_injective
    (fun W hW ↦ ⟨⟨W, hW⟩, rfl⟩) hx

/-- **Two distinct irreducible components of a Noetherian scheme of dimension at most one meet
in a finite set.** -/
public theorem finite_inter_irreducibleComponents
    (hdim : topologicalKrullDim (X : Type u) ≤ 1) {V W : Set X}
    (hV : V ∈ irreducibleComponents (X : Type u))
    (hW : W ∈ irreducibleComponents (X : Type u)) (hVW : V ≠ W) : (V ∩ W).Finite := by
  have : Finite (irreducibleComponents (X : Type u)) :=
    NoetherianSpace.finite_irreducibleComponents.to_subtype
  have _ : NoetherianSpace (X : Type u) := IsNoetherian.noetherianSpace
  exact finite_inter_of_ne hdim (fun C ↦ C.2) Subtype.val_injective
    (fun W hW ↦ ⟨⟨W, hW⟩, rfl⟩) (i := ⟨V, hV⟩) (j := ⟨W, hW⟩) (Subtype.coe_ne_coe.mp hVW)

/-- **Two distinct irreducible components of a Noetherian scheme of dimension at most one meet in a
discrete set.** -/
public theorem discreteTopology_inter_irreducibleComponents
    (hdim : topologicalKrullDim (X : Type u) ≤ 1) {V W : Set X}
    (hV : V ∈ irreducibleComponents (X : Type u))
    (hW : W ∈ irreducibleComponents (X : Type u)) (hVW : V ≠ W) :
    DiscreteTopology ↥(V ∩ W) := by
  have : Finite (irreducibleComponents (X : Type u)) :=
    NoetherianSpace.finite_irreducibleComponents.to_subtype
  have _ : NoetherianSpace (X : Type u) := IsNoetherian.noetherianSpace
  exact discreteTopology_inter_of_ne hdim (fun C ↦ C.2) Subtype.val_injective
    (fun W hW ↦ ⟨⟨W, hW⟩, rfl⟩) (i := ⟨V, hV⟩) (j := ⟨W, hW⟩) (Subtype.coe_ne_coe.mp hVW)

/-- **On a Noetherian scheme of dimension at most one the whole locus where the irreducible
components fail to be disjoint is a discrete subspace.** -/
public theorem discreteTopology_compl_disjointLocus_irreducibleComponents
    (hdim : topologicalKrullDim (X : Type u) ≤ 1) :
    DiscreteTopology
      ↥((disjointLocus (Subtype.val : irreducibleComponents (X : Type u) → Set X))ᶜ) := by
  have : Finite (irreducibleComponents (X : Type u)) :=
    NoetherianSpace.finite_irreducibleComponents.to_subtype
  have _ : NoetherianSpace (X : Type u) := IsNoetherian.noetherianSpace
  exact discreteTopology_compl_disjointLocus hdim (fun C ↦ C.2) Subtype.val_injective
    fun W hW ↦ ⟨⟨W, hW⟩, rfl⟩

end Scheme

end StacksTag09NX

end
