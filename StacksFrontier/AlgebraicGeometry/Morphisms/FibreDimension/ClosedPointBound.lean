module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.Topology.JacobsonSpace
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.Openness
public import StacksFrontier.Topology.Dimension.LocalKrullDim

/-!
# A fibre-dimension bound checked at closed points holds everywhere

Let `p : S ⟶ X` be a morphism of schemes locally of finite type with `S` a Jacobson space — for
instance a scheme locally of finite type over a field. The function sending a point `z` of `S` to
the local dimension at `z` of the scheme-theoretic fibre of `p` through `z` is upper
semicontinuous: the locus where it is at most `n` is open, by
`AlgebraicGeometry.isOpen_setOf_fiberDimensionAt_le` (Tag 02FZ). Hence the locus where the bound
*fails* is closed, and in a Jacobson space a nonempty locally closed set contains a point which
is closed in the whole space. So a bound that holds at every closed point of `S` holds at every
point of `S`.

This is the step that upgrades a fibre computation performed over closed points of the base — the
only points at which a residue-field computation is available in the applications — to the bound
over all points, which is what a dimension count of the total space consumes. The upgrade is not
cosmetic: over a non-closed point of `X` the fibre of `p` is genuinely larger than over a closed
point, and only semicontinuity rules out that the larger fibres contribute.

## Main results

* `AlgebraicGeometry.fiberDimensionAt_le_of_isClosed_singleton`: a bound on the local fibre
  dimension at the closed points of the source holds at every point of the source.
* `AlgebraicGeometry.fiberDimensionAt_le_of_isClosed_singleton_target`: the same with the bound
  supplied as a bound on the dimension of the whole fibre over each closed point of the
  *target*. Closed points of the source map to closed points of the target because `p` is locally
  of finite type and `X` is Jacobson ([Stacks, Tag 01TB]), and the local dimension of a space at
  a point is at most its dimension.

## Implementation notes

The Jacobson hypotheses are stated as instance arguments on the underlying spaces rather than as
a finite-type structure morphism to a field, so that they can be discharged either by
`AlgebraicGeometry.LocallyOfFiniteType.jacobsonSpace` or directly.

No `@[stacks]` attribute is attached: these are the general reduction step, not the statement of
a tag. The tags they rest on are registered where they are proved, Tag 02FZ on
`AlgebraicGeometry.isOpen_setOf_fiberDimensionAt_le` and Tag 01TB on
`AlgebraicGeometry.Scheme.Hom.closePoints_subset_preimage_closedPoints`.

## References

* [Stacks Project, Tag 02FZ](https://stacks.math.columbia.edu/tag/02FZ)
* [Stacks Project, Tag 01TB](https://stacks.math.columbia.edu/tag/01TB)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

/-- **A containment of closed sets in a Jacobson space may be checked at the closed points.**
If every point of `N` which is closed in the ambient space lies in the closed set `L`, then all
of `N` does: `N` is the closure of its closed points, and that closure is contained in the
closed set `L`.

This is what makes an identification of a *set* of points available only over closed points —
where a residue-field computation can be run — enough to identify the set itself. The
hypothesis that `N` is closed is needed: it is what makes `N` the closure of the closed points
it contains. -/
theorem Set.subset_of_isClosed_of_closedPoints_subset {T : Type*} [TopologicalSpace T]
    [JacobsonSpace T] {N L : Set T} (hN : IsClosed N) (hL : IsClosed L)
    (h : ∀ w ∈ N, IsClosed {w} → w ∈ L) : N ⊆ L := by
  conv_lhs => rw [← JacobsonSpace.closure_inter_closedPoints hN]
  refine closure_minimal (fun w hw ↦ h w hw.1 hw.2) hL

namespace AlgebraicGeometry

/-- **The dimension of a scheme-theoretic fibre is the dimension of the set-theoretic fibre.**
The scheme-theoretic fibre of `p` over `x` is homeomorphic to the subspace `p ⁻¹' {x}` of the
source, so a set containing that subspace bounds the dimension of the fibre. -/
theorem topologicalKrullDim_fiber_le_of_preimage_subset {S X : Scheme.{u}} (p : S ⟶ X) (x : X)
    {d : WithBot ℕ∞} (Z : Set S) (hZ : p.base ⁻¹' {x} ⊆ Z)
    (hdim : topologicalKrullDim Z ≤ d) : topologicalKrullDim (p.fiber x) ≤ d :=
  le_trans (le_of_eq (IsHomeomorph.topologicalKrullDim_eq _ (p.fiberHomeo x).isHomeomorph))
    (le_trans (topologicalKrullDim_le_of_subset hZ) hdim)

/-- **A fibre-dimension bound verified at the closed points of the source holds everywhere.**
Let `p : S ⟶ X` be locally of finite type with `S` a Jacobson space. If for every point `z` of
`S` whose singleton is closed the fibre of `p` through `z` has local dimension at most `m` at
`z`, then the same bound holds at every point of `S`.

The locus where the bound fails is closed, by upper semicontinuity of the local fibre dimension
([Stacks, Tag 02FZ]); were it nonempty it would contain a closed point of `S`, where the bound is
assumed. -/
theorem fiberDimensionAt_le_of_isClosed_singleton {S X : Scheme.{u}} (p : S ⟶ X)
    [LocallyOfFiniteType p] [JacobsonSpace S] {m : ℕ}
    (h : ∀ z : S, IsClosed {z} →
      topologicalKrullDimAt (p.fiber (p z)) (p.asFiber z) ≤ (m : WithBot ℕ∞))
    (z : S) : topologicalKrullDimAt (p.fiber (p z)) (p.asFiber z) ≤ (m : WithBot ℕ∞) := by
  by_contra hz
  set C : Set S := {w : S |
    topologicalKrullDimAt (p.fiber (p w)) (p.asFiber w) ≤ (m : WithBot ℕ∞)}ᶜ with hCdef
  have hC : IsClosed C := (isOpen_setOf_fiberDimensionAt_le p m).isClosed_compl
  have hzC : z ∈ C := hz
  obtain ⟨w, hwC, hw⟩ := nonempty_inter_closedPoints ⟨z, hzC⟩ hC.isLocallyClosed
  exact hwC (h w hw)

/-- **A bound on the dimension of the fibres over the closed points of the target holds at every
point of the source.** Let `p : S ⟶ X` be locally of finite type with both `S` and `X` Jacobson
spaces. If the fibre of `p` over every closed point of `X` has dimension at most `m`, then at
every point `z` of `S` the fibre through `z` has local dimension at most `m` at `z`.

This is `AlgebraicGeometry.fiberDimensionAt_le_of_isClosed_singleton` together with the fact that
a closed point of `S` maps to a closed point of `X` ([Stacks, Tag 01TB]) and that the local
dimension of a space at a point is bounded by its dimension. It is the shape in which a fibre
computation at closed points — where the fibre is identified with an explicit scheme over the
residue field — produces the hypothesis of a dimension count over the whole source. -/
theorem fiberDimensionAt_le_of_isClosed_singleton_target {S X : Scheme.{u}} (p : S ⟶ X)
    [LocallyOfFiniteType p] [JacobsonSpace S] [JacobsonSpace X] {m : ℕ}
    (h : ∀ x : X, IsClosed {x} → topologicalKrullDim (p.fiber x) ≤ (m : WithBot ℕ∞))
    (z : S) : topologicalKrullDimAt (p.fiber (p z)) (p.asFiber z) ≤ (m : WithBot ℕ∞) := by
  refine fiberDimensionAt_le_of_isClosed_singleton p (fun w hw ↦ ?_) z
  have hpw : IsClosed {p w} := by
    have : p w ∈ closedPoints X := p.closePoints_subset_preimage_closedPoints hw
    exact this
  exact le_trans (topologicalKrullDimAt_le_topologicalKrullDim _) (h (p w) hpw)

end AlgebraicGeometry

end
