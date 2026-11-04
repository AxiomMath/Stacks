module

public import StacksFrontier.AlgebraicGeometry.Variety.FibreDimension
public import StacksFrontier.Topology.Dimension.LocalKrullDim
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Bounding the dimension of the source by the dimensions of the fibres and the target

Let `f : X ⟶ Y` be a morphism of schemes locally of finite type over a field `k`. Part (3) of
[Stacks, Tag 0B2L] bounds the dimension of `X` at a point `x` by the dimension of the fibre
through `x` plus the dimension of `Y` at `f x`. Taking the supremum over `x` turns this
pointwise statement into a bound on `dim X` itself: if every fibre has local dimension at most
`d` and `dim Y ≤ e`, then `dim X ≤ d + e`.

This is the shape in which a fibrewise dimension count is used to bound the dimension of a
total space, for instance that of the non-smooth locus of a family of divisors in the proof of
[Stacks, Tag 0FD6].

## Main results

* `AlgebraicGeometry.topologicalKrullDim_le_add_of_topologicalKrullDimAt_fiber_le`: the bound
  `dim X ≤ d + e` from `dim_x(X_{f x}) ≤ d` for every `x` and `dim Y ≤ e`.
* `AlgebraicGeometry.topologicalKrullDim_lt_of_topologicalKrullDimAt_fiber_le`: the same bound
  read as a strict inequality `dim X < c` when `d + e < c`.
* `AlgebraicGeometry.topologicalKrullDimAt_fiber_le_of_topologicalKrullDim_fiber_le`: the
  pointwise hypothesis of the two results above is implied by a bound on the dimension of every
  fibre as a whole.
* `TopologicalSpace.topologicalKrullDim_le_of_isClosed_singleton`: in a Jacobson space a bound on
  the local dimension at the closed points bounds the dimension of the whole space.
* `AlgebraicGeometry.topologicalKrullDim_le_of_isClosed_singleton_fiber_add_target`: the bound
  `dim X ≤ d` from `dim_x(X_{f x}) + dim_{f x} Y ≤ d` at the **closed points** of `X` only, the
  fibre and the target being bounded together rather than separately.

## Implementation notes

Dimensions take values in `WithBot ℕ∞`, which has no subtraction, so the bound is additive:
there is no "`dim X - dim Y ≤ d`" to state. The supremum over the points of `X` is the identity
`dim X = ⨆ x, dim_x(X)`, which is
`TopologicalSpace.topologicalKrullDim_eq_iSup_localKrullDim` read through
`TopologicalSpace.topologicalKrullDimAt_eq_localKrullDim`; an empty `X` is covered because the
supremum over an empty family is `⊥`.

## References

* [Stacks Project, Tag 0B2L](https://stacks.math.columbia.edu/tag/0B2L)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace TopologicalSpace

/-- **The dimension of a Jacobson space is read off its closed points.** If the local dimension
of `T` at each of its closed points is at most `d`, then `dim T ≤ d`.

A chain of irreducible closed subsets of `T` lies inside every open neighbourhood of any point of
its bottom member (`TopologicalSpace.length_le_topologicalKrullDim_of_mem`), so its length is at
most the local dimension at such a point; and the bottom member, being nonempty and closed,
contains a point closed in `T` because `T` is Jacobson. An empty `T` is covered: both sides are
then taken over no chains at all. -/
theorem topologicalKrullDim_le_of_isClosed_singleton {T : Type*} [TopologicalSpace T]
    [JacobsonSpace T] {d : WithBot ℕ∞}
    (h : ∀ z : T, IsClosed ({z} : Set T) → topologicalKrullDimAt T z ≤ d) :
    topologicalKrullDim T ≤ d := by
  unfold topologicalKrullDim Order.krullDim
  refine iSup_le fun p => ?_
  obtain ⟨z, hzmem, hz⟩ := nonempty_inter_closedPoints
    (RelSeries.head p).isIrreducible'.nonempty (RelSeries.head p).isClosed'.isLocallyClosed
  refine le_trans ?_ (h z hz)
  rw [topologicalKrullDimAt_eq_localKrullDim]
  unfold localKrullDim
  exact le_iInf fun U => le_iInf fun hU => le_iInf fun hzU =>
    length_le_topologicalKrullDim_of_mem p U hU z hzU hzmem

end TopologicalSpace

namespace AlgebraicGeometry

/-- The dimension of a topological space is the supremum of its local dimensions. This is
`TopologicalSpace.topologicalKrullDim_eq_iSup_localKrullDim` read through the identification of
`localKrullDim` with `topologicalKrullDimAt`. -/
lemma topologicalKrullDim_eq_iSup_dimAt (Z : Type*) [TopologicalSpace Z] :
    topologicalKrullDim Z = ⨆ z : Z, topologicalKrullDimAt Z z := by
  rw [topologicalKrullDim_eq_iSup_localKrullDim]
  simp_rw [topologicalKrullDimAt_eq_localKrullDim]

/-- A bound on the dimension of every fibre of `f`, taken as a whole, gives the pointwise bound
on the local dimension of the fibre that the results below ask for: the local dimension of a
space at a point never exceeds the dimension of the space. -/
theorem topologicalKrullDimAt_fiber_le_of_topologicalKrullDim_fiber_le {X Y : Scheme.{u}}
    (f : X ⟶ Y) {d : WithBot ℕ∞} (h : ∀ y : Y, topologicalKrullDim (f.fiber y) ≤ d) (x : X) :
    topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) ≤ d :=
  (topologicalKrullDimAt_le_topologicalKrullDim (f.asFiber x)).trans (h (f x))

/-- **A bound on the fibres and on the target bounds the source.** For `f : X ⟶ Y` a morphism of
schemes locally of finite type over a field `k`, if every fibre of `f` has local dimension at
most `d` at the point of it determined by a point of `X`, and `dim Y ≤ e`, then
`dim X ≤ d + e`.

This is the supremum over `x : X` of
`AlgebraicGeometry.topologicalKrullDimAt_le_fiber_add_topologicalKrullDimAt_target`, which is
part (3) of [Stacks, Tag 0B2L]; no irreducibility of `X` is needed. -/
@[ega "IV 10.6.1" "(iii), special case", ega "IV 5.6.7" "special case"]
theorem topologicalKrullDim_le_add_of_topologicalKrullDimAt_fiber_le
    (k : Type u) [Field k] {X Y : Scheme.{u}}
    (pX : X ⟶ Spec (.of k)) (pY : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType pX] [LocallyOfFiniteType pY]
    (f : X ⟶ Y) (hf : f ≫ pY = pX) {d e : WithBot ℕ∞}
    (hfib : ∀ x : X, topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) ≤ d)
    (hY : topologicalKrullDim Y ≤ e) :
    topologicalKrullDim X ≤ d + e := by
  rw [topologicalKrullDim_eq_iSup_dimAt]
  refine iSup_le fun x => ?_
  refine (topologicalKrullDimAt_le_fiber_add_topologicalKrullDimAt_target k pX pY f hf x).trans ?_
  exact add_le_add (hfib x) ((topologicalKrullDimAt_le_topologicalKrullDim (f x)).trans hY)

/-- **A fibrewise bound putting the source strictly below a given dimension.** The strict form of
`AlgebraicGeometry.topologicalKrullDim_le_add_of_topologicalKrullDimAt_fiber_le`: with the fibres
bounded by `d` and the target by `e`, the source has dimension `< c` as soon as `d + e < c`. -/
theorem topologicalKrullDim_lt_of_topologicalKrullDimAt_fiber_le
    (k : Type u) [Field k] {X Y : Scheme.{u}}
    (pX : X ⟶ Spec (.of k)) (pY : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType pX] [LocallyOfFiniteType pY]
    (f : X ⟶ Y) (hf : f ≫ pY = pX) {c d e : WithBot ℕ∞}
    (hfib : ∀ x : X, topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) ≤ d)
    (hY : topologicalKrullDim Y ≤ e) (hlt : d + e < c) :
    topologicalKrullDim X < c :=
  lt_of_le_of_lt
    (topologicalKrullDim_le_add_of_topologicalKrullDimAt_fiber_le k pX pY f hf hfib hY) hlt

/-- **The fibre-and-target bound needs holding only at the closed points of the source.** For
`f : X ⟶ Y` a morphism of schemes locally of finite type over a field `k`, if at every point `x`
of `X` which is closed in `X` the sum of the local dimension of the fibre through `x` and the
local dimension of `Y` at `f x` is at most `d`, then `dim X ≤ d`.

This is part (3) of [Stacks, Tag 0B2L] —
`AlgebraicGeometry.topologicalKrullDimAt_le_fiber_add_topologicalKrullDimAt_target`, the upper
bound, which needs no irreducibility — taken at the closed points only, together with
`TopologicalSpace.topologicalKrullDim_le_of_isClosed_singleton`, which is what makes the closed
points enough: `X` is a Jacobson space, being locally of finite type over a field.

Unlike `AlgebraicGeometry.topologicalKrullDim_le_add_of_topologicalKrullDimAt_fiber_le`, the two
dimensions are bounded *together*. That is what allows a fibre bound varying from point to point
and trading against the local dimension of the target, with no uniform bound on either: it is
the form the dimension count of [Stacks, Tag 0FD6] takes when `X` is not assumed
equidimensional, the fibre of the non-smooth locus over a point `y` of local dimension `n_y`
having dimension `r - (n_y + 1)` and the sum being `r - 1` whatever `n_y` is. -/
@[ega "IV 10.6.1" "(iii), special case",
  ega "IV 5.6.7" "special case",
  sga "6 X 3.3" "special case"]
theorem topologicalKrullDim_le_of_isClosed_singleton_fiber_add_target
    (k : Type u) [Field k] {X Y : Scheme.{u}}
    (pX : X ⟶ Spec (.of k)) (pY : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType pX] [LocallyOfFiniteType pY]
    (f : X ⟶ Y) (hf : f ≫ pY = pX) {d : WithBot ℕ∞}
    (hfib : ∀ x : X, IsClosed ({x} : Set X) →
      topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) + topologicalKrullDimAt Y (f x) ≤ d) :
    topologicalKrullDim X ≤ d :=
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace pX
  topologicalKrullDim_le_of_isClosed_singleton fun x hx =>
    (topologicalKrullDimAt_le_fiber_add_topologicalKrullDimAt_target k pX pY f hf x).trans
      (hfib x hx)

end AlgebraicGeometry

end
