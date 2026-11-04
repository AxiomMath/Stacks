module

public import Mathlib.Topology.ClusterPt
public import Mathlib.Topology.Sober
public import StacksFrontier.Topology.Dimension.Krull
public import StacksFrontier.Topology.Separation.IsolatedPoint

/-!
# Isolated points are generic, and the complement of a non-generic point is dense

A point `x` of a topological space is *generic* when `closure {x}` is an irreducible component,
that is, when `x ∈ genericPoints`. This file records the one implication relating genericity to
the topology of the singleton `{x}`:

**an isolated point is generic.** If `{x}` is open then `closure {x}` is already maximal among
irreducible subsets: an irreducible `Z` containing `x` meets the open set `{x}`, so by
irreducibility every neighbourhood of every point of `Z` meets `{x}`, which says exactly that
`Z ⊆ closure {x}`.

Read contrapositively this says that **the complement of a non-generic point is dense**, since
`{x}ᶜ` is dense precisely when `{x}` is not open. That is the form in which it is used: a
closed point of a curve is not a generic point, so its complement is a dense open subset, which
is the hypothesis of [Stacks, Tag 0CE3] on the genus of a finite cover.

No separation, soberness, Noetherianness or finite-dimensionality is needed for any of this.

## Main results

* `Stacks.Topology.mem_genericPoints_of_isIsolatedPoint`: an isolated point is generic.
* `Stacks.Topology.dense_compl_singleton_of_notMem_genericPoints`: the complement of a
  non-generic point is dense.

## References

* [Stacks Project, Tag 0CE3](https://stacks.math.columbia.edu/tag/0CE3)
-/

@[expose] public section

open TopologicalSpace

namespace Stacks.Topology

variable {T : Type*} [TopologicalSpace T]

/-- **An isolated point is a generic point**: if `{x}` is open then `closure {x}` is an
irreducible component.

The closure of a point is always irreducible, so only maximality is at issue. Let `Z` be
irreducible with `closure {x} ⊆ Z` and let `z ∈ Z`. Every open `V` containing `z` meets `Z`,
and `{x}` meets `Z` in `x`; irreducibility of `Z` therefore makes `Z ∩ V ∩ {x}` nonempty, so
`x ∈ V`. As `V` was an arbitrary neighbourhood of `z` this says `z ∈ closure {x}`. -/
theorem mem_genericPoints_of_isIsolatedPoint {x : T} (hx : IsIsolatedPoint x) :
    x ∈ genericPoints T := by
  refine ⟨isIrreducible_singleton.closure, fun Z hZ hle z hz => ?_⟩
  rw [mem_closure_iff]
  intro V hV hzV
  obtain ⟨w, -, hwV, hwx⟩ :=
    hZ.2 V {x} hV hx ⟨z, hz, hzV⟩ ⟨x, hle (subset_closure rfl), rfl⟩
  exact ⟨x, hwx ▸ hwV, rfl⟩

/-- **The complement of a non-generic point is dense.** The complement of a singleton is dense
exactly when the singleton is not open, and an open singleton would make its point generic by
`Stacks.Topology.mem_genericPoints_of_isIsolatedPoint`. -/
theorem dense_compl_singleton_of_notMem_genericPoints {x : T} (hx : x ∉ genericPoints T) :
    Dense ({x}ᶜ : Set T) :=
  dense_compl_singleton_iff_not_open.2 fun h => hx (mem_genericPoints_of_isIsolatedPoint h)

/-! ### Closed points of a space with no zero-dimensional component -/

/-- **A closed point of a space none of whose irreducible components is zero-dimensional is not
a generic point.** The closure of such a point is the point itself, so were it a component it
would be a zero-dimensional one, the Krull dimension of a one-point space being `0`. -/
theorem notMem_genericPoints_of_isClosed_singleton {x : T} (hx : IsClosed ({x} : Set T))
    (h : ∀ C ∈ irreducibleComponents T, topologicalKrullDim C ≠ 0) : x ∉ genericPoints T := by
  intro hmem
  have hcomp : ({x} : Set T) ∈ irreducibleComponents T :=
    hx.closure_eq ▸ (hmem : closure {x} ∈ irreducibleComponents T)
  refine h _ hcomp ?_
  have : Subsingleton ({x} : Set T) := ⟨fun a b ↦ Subtype.ext (a.2.trans b.2.symm)⟩
  have : Nonempty ({x} : Set T) := ⟨⟨x, rfl⟩⟩
  exact topologicalKrullDim_eq_zero_of_discreteTopology_nonempty

/-- **The complement of a closed point of a space none of whose irreducible components is
zero-dimensional is dense.** This is the hypothesis `Dense (U : Set X)` of [Stacks, Tag 0CE3]
for `U = {x}ᶜ`: on a curve every irreducible component is one-dimensional, so no closed point
is generic and no closed point has to be removed from the open set over which a finite cover is
compared. -/
theorem dense_compl_singleton_of_isClosed_singleton {x : T} (hx : IsClosed ({x} : Set T))
    (h : ∀ C ∈ irreducibleComponents T, topologicalKrullDim C ≠ 0) : Dense ({x}ᶜ : Set T) :=
  dense_compl_singleton_of_notMem_genericPoints (notMem_genericPoints_of_isClosed_singleton hx h)

end Stacks.Topology

end
