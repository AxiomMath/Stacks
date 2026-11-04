module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import StacksFrontier.Topology.Dimension.NowhereDense
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A closed subscheme through no generic point has smaller dimension

Let `X` be a scheme whose underlying space is Noetherian and let `Z ⊆ X` be a closed subscheme
no generic point of `X` lying on it. Then

  `dim Z + 1 ≤ dim X`,

so in particular `dim Z ≤ d` whenever `dim X ≤ d + 1`. This is the dimension estimate the
induction of [Stacks, Tag 0FDX] runs on: the effective Cartier divisor it cuts out there misses
every generic point of `X`, hence drops the dimension.

The topological content is `IsNowhereDense.topologicalKrullDim_add_one_le`
of `StacksFrontier.Topology.Dimension.NowhereDense`, for which this file supplies the two
translations a scheme needs: that the hypothesis "no generic point of `X` lies on `Z`" is
nowhere density of the image of `Z`, and that the dimension of the scheme `Z` is the dimension
of that image.

## Main results

* `Stacks.Divisors.topologicalKrullDim_eq_range_of_isClosedImmersion` — the dimension of the
  source of a closed immersion is the dimension of its image.
* `Stacks.Divisors.isNowhereDense_iff_forall_genericPoints_notMem` — for a closed subset of a
  Noetherian scheme, nowhere density is exactly missing every generic point.
* `Stacks.Divisors.topologicalKrullDim_add_one_le_of_forall_genericPoints_notMem` — the drop,
  for a closed immersion.
* `Stacks.Divisors.topologicalKrullDim_le_of_forall_genericPoints_notMem` — its bounded form.
* `Stacks.Divisors.topologicalKrullDim_subscheme_add_one_le_of_forall_genericPoints_notMem`,
  `Stacks.Divisors.topologicalKrullDim_subscheme_le_of_forall_genericPoints_notMem` — the same
  two statements for the closed subscheme of a quasi-coherent ideal, which is the form the
  divisor API produces.

## Implementation notes

No `@[stacks]` attribute is placed: the estimate is a step inside the proof of [Stacks,
Tag 0FDX] rather than a tag of its own, and the two tags that come closest say something else —
[Stacks, Tag 056N] is the local statement about `topologicalKrullDimAt` at a point of an
effective Cartier divisor, proved in
`StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.DimensionDrop`, and [Stacks, Tag 02RK]
is the delta-dimension statement about the components of such a divisor, proved in
`StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.PrimeDivisorDimension`.

The Noetherian hypothesis is on the underlying space and is not removable; the counterexample
is recorded in the module documentation of
`StacksFrontier.Topology.Dimension.NowhereDense`.

## References

* [Stacks Project, Tag 0FDX](https://stacks.math.columbia.edu/tag/0FDX)
* [Stacks Project, Tag 056N](https://stacks.math.columbia.edu/tag/056N)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Topology

universe u

namespace Stacks.Divisors

/-! ### The dimension of a closed subscheme is the dimension of its image -/

/-- **The dimension of the source of a closed immersion is the dimension of its image.** A closed
immersion is a homeomorphism onto its range, and the topological dimension is a homeomorphism
invariant. -/
theorem topologicalKrullDim_eq_range_of_isClosedImmersion {X Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] :
    topologicalKrullDim Z = topologicalKrullDim (Set.range i.base) :=
  IsHomeomorph.topologicalKrullDim_eq _
    (IsClosedImmersion.isClosedEmbedding i).isEmbedding.toHomeomorph.isHomeomorph

/-! ### Missing every generic point is nowhere density -/

/-- **For a closed subset of a Noetherian scheme, nowhere density is exactly missing every
generic point of the scheme.** A scheme is sober, so the irreducible components correspond to
their generic points, and a closed set contains such a component exactly when it contains its
generic point. -/
theorem isNowhereDense_iff_forall_genericPoints_notMem {X : Scheme.{u}}
    [NoetherianSpace (X : Type u)] {S : Set X} (hS : IsClosed S) :
    IsNowhereDense S ↔ ∀ x ∈ genericPoints (X : Type u), x ∉ S := by
  rw [hS.isNowhereDense_iff_forall_irreducibleComponents_not_subset]
  refine ⟨fun h x hx hxS => h (closure {x}) hx ?_, fun h W hW hWS => ?_⟩
  · exact hS.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hxS)
  · set x := (genericPoints.ofComponent (α := (X : Type u)) ⟨W, hW⟩).1 with hxdef
    have hgen : closure {x} = W :=
      genericPoints.isGenericPoint_ofComponent (α := (X : Type u)) ⟨W, hW⟩
    exact h x (genericPoints.ofComponent (α := (X : Type u)) ⟨W, hW⟩).2
      (hWS (hgen.subset (subset_closure (Set.mem_singleton x))))

/-! ### The dimension drop -/

/-- The image of a closed immersion through no generic point is nowhere dense. -/
private theorem isNowhereDense_range_of_forall_genericPoints_notMem {X Z : Scheme.{u}}
    [NoetherianSpace (X : Type u)] (i : Z ⟶ X) [IsClosedImmersion i]
    (h : ∀ x ∈ genericPoints (X : Type u), x ∉ Set.range i.base) :
    IsNowhereDense (Set.range i.base) :=
  (isNowhereDense_iff_forall_genericPoints_notMem
    (IsClosedImmersion.isClosedEmbedding i).isClosed_range).mpr h

/-- **A closed subscheme through no generic point of `X` has dimension at least one less.** The
image of the closed immersion is closed and nowhere dense, so
`IsNowhereDense.topologicalKrullDim_add_one_le` applies. -/
@[ega "IV 4.1.2.1" "rare ⇒ dim(Z) < dim(Y)"]
theorem topologicalKrullDim_add_one_le_of_forall_genericPoints_notMem {X Z : Scheme.{u}}
    [NoetherianSpace (X : Type u)] (i : Z ⟶ X) [IsClosedImmersion i]
    (h : ∀ x ∈ genericPoints (X : Type u), x ∉ Set.range i.base) :
    topologicalKrullDim Z + 1 ≤ topologicalKrullDim X := by
  rw [topologicalKrullDim_eq_range_of_isClosedImmersion i]
  exact (isNowhereDense_range_of_forall_genericPoints_notMem i h).topologicalKrullDim_add_one_le
    (IsClosedImmersion.isClosedEmbedding i).isClosed_range

/-- **The bounded form of the drop.** If `dim X ≤ d + 1` then a closed subscheme through no
generic point of `X` has `dim ≤ d`. This is the shape an induction on the dimension consumes. -/
theorem topologicalKrullDim_le_of_forall_genericPoints_notMem {X Z : Scheme.{u}}
    [NoetherianSpace (X : Type u)] (i : Z ⟶ X) [IsClosedImmersion i]
    (h : ∀ x ∈ genericPoints (X : Type u), x ∉ Set.range i.base) (d : ℕ)
    (hd : topologicalKrullDim X ≤ ((d + 1 : ℕ) : WithBot ℕ∞)) :
    topologicalKrullDim Z ≤ (d : WithBot ℕ∞) := by
  rw [topologicalKrullDim_eq_range_of_isClosedImmersion i]
  exact (isNowhereDense_range_of_forall_genericPoints_notMem i
    h).topologicalKrullDim_le_of_le_natCast_succ
    (IsClosedImmersion.isClosedEmbedding i).isClosed_range d hd

/-! ### The form the divisor API produces -/

/-- **The drop for the closed subscheme of a quasi-coherent ideal.** The support of the ideal is
the image of the closed immersion, by
`AlgebraicGeometry.Scheme.IdealSheafData.range_subschemeι`. -/
theorem topologicalKrullDim_subscheme_add_one_le_of_forall_genericPoints_notMem {X : Scheme.{u}}
    [NoetherianSpace (X : Type u)] (D : X.IdealSheafData)
    (h : ∀ x ∈ genericPoints (X : Type u), x ∉ D.supportSet) :
    topologicalKrullDim D.subscheme + 1 ≤ topologicalKrullDim X :=
  topologicalKrullDim_add_one_le_of_forall_genericPoints_notMem D.subschemeι
    (by rwa [show Set.range D.subschemeι.base = D.supportSet from D.range_subschemeι])

/-- **The bounded form for the closed subscheme of a quasi-coherent ideal.** If `dim X ≤ d + 1`
and no generic point of `X` lies in the support of `D`, then `dim D ≤ d`. -/
theorem topologicalKrullDim_subscheme_le_of_forall_genericPoints_notMem {X : Scheme.{u}}
    [NoetherianSpace (X : Type u)] (D : X.IdealSheafData)
    (h : ∀ x ∈ genericPoints (X : Type u), x ∉ D.supportSet) (d : ℕ)
    (hd : topologicalKrullDim X ≤ ((d + 1 : ℕ) : WithBot ℕ∞)) :
    topologicalKrullDim D.subscheme ≤ (d : WithBot ℕ∞) :=
  topologicalKrullDim_le_of_forall_genericPoints_notMem D.subschemeι
    (by rwa [show Set.range D.subschemeι.base = D.supportSet from D.range_subschemeι]) d hd

end Stacks.Divisors

end
