module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.Topology.JacobsonSpace
public import StacksCore.Tactic.StacksAttribute

/-!
# Closed points in a fibre specializing from a given point

Let `f : X ⟶ S` be locally of finite type, let `x ∈ X` and set `s = f x`. The fibre `X_s` is
locally of finite type over the residue field `κ(s)`, hence a Jacobson space, so the points of
`X_s` which are closed in `X_s` and to which `x` specializes are dense in the closure of `x` in
`X_s`.

Stacks 053U asks the same of the smaller set of those points which in addition specialize to a
prescribed `x'`, where `x ⤳ x'` and `x'` is closed in its own fibre `X_{f x'}`. The tag is
`AlgebraicGeometry.closure_closedPoints_between_fiber_eq_iff` in
`StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.ClosedPointsBetweenInFibres`, which proves its
density conclusion and determines the exact range of validity of that conclusion: it holds if
and only if `x = x'` or `f x ≠ f x'`. The half of that equivalence concerning a nontrivial
specialization inside one fibre is computed here, in
`AlgebraicGeometry.closure_closedPoints_between_fiber_subset_singleton_of_eq_base`: when `x'`
lies in the fibre of `x`, a point of `X_s` closed in `X_s` which specializes to `x'` *is* `x'`,
so the set of the tag is `{x'}`, whose closure is `{x'}`, and the density forces the closure of
`x` in `X_s` to be a single point — which it is not for `X = 𝔸¹` over a field with `x` its
generic point and `x'` a closed point of it. The source relates `f x` and `f x'` by no
hypothesis, so this is a gap in its statement rather than an artefact of the formalization.

## Main results

* `AlgebraicGeometry.eq_of_fiberι_specializes_of_isClosed`: a point of a fibre closed in that
  fibre is the only point of the fibre it specializes to.
* `AlgebraicGeometry.subsingleton_setOf_isClosed_and_specializes_fiberι`: the set of Stacks 053U
  is a subsingleton when `x'` lies in the fibre of `x`.
* `AlgebraicGeometry.closure_closedPoints_between_fiber_subset_singleton_of_eq_base`: when `x'`
  lies in the fibre of `x`, the density conclusion of Stacks 053U forces the closure of `x` in
  `X_s` to be contained in a single point. This is the forward implication of
  `AlgebraicGeometry.closure_closedPoints_between_fiber_eq_iff`.
* `AlgebraicGeometry.closure_closedPoints_specializing_fiber_eq`: the points of `X_s` closed in
  `X_s` to which `x` specializes, with nothing required of them at `x'`, are dense in the
  closure of `x` in `X_s`.
* `AlgebraicGeometry.closure_closedPoints_between_fiber_eq_of_forall_isOpen`: the density
  conclusion of Stacks 053U follows from the existence, in every open neighbourhood of `x` in
  `X_s`, of a point closed in `X_s` lying between `x` and `x'`.
* `AlgebraicGeometry.closure_closedPoints_between_fiber_eq_of_isClosed` and
  `AlgebraicGeometry.closure_closedPoints_between_fiber_eq_of_quasiFiniteAt`: the density
  conclusion of Stacks 053U when `x` is already closed in `X_s`, in particular when `f` is
  quasi-finite at `x`; these need nothing of `f` and of the two base points.

## Implementation notes

`a ⤳ b` is Mathlib's `Specializes`, which holds exactly when `b` lies in the closure of `{a}`;
it is the source's `a ⤳ b`. Points of `X_s` are `f.fiber s` and are carried back to `X` by
`f.fiberι s`, with `f.asFiber x : f.fiber (f x)` the canonical point over `x`. Density in the
closure of `x` in `X_s` is written as an equality of closures, which also records the
containment.

## References

* [Stacks Project, Tag 053U](https://stacks.math.columbia.edu/tag/053U)
* [Stacks Project, Tag 053S](https://stacks.math.columbia.edu/tag/053S)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- A point of a fibre which is closed in that fibre specializes to no other point of the fibre:
the fibre inclusion is an embedding, so specialization inside `X` between points of the fibre is
specialization inside the fibre. -/
public theorem eq_of_fiberι_specializes_of_isClosed {X S : Scheme.{u}} (f : X ⟶ S) {s : S}
    {y z : f.fiber s} (hy : IsClosed ({y} : Set (f.fiber s)))
    (hyz : f.fiberι s y ⤳ f.fiberι s z) : z = y :=
  ((f.fiberι s).isEmbedding.specializes_iff.mp hyz).mem_closed hy (Set.mem_singleton y)

/-- A point of `X_s` to which `x` specializes lies in the closure of `x` in `X_s`. -/
private theorem mem_closure_asFiber_of_specializes {X S : Scheme.{u}} (f : X ⟶ S) (x : X)
    {y : f.fiber (f x)} (hxy : x ⤳ f.fiberι (f x) y) :
    y ∈ closure ({f.asFiber x} : Set (f.fiber (f x))) := by
  rw [← specializes_iff_mem_closure]
  exact (f.fiberι (f x)).isEmbedding.specializes_iff.mp
    (by simpa only [Scheme.Hom.fiberι_asFiber] using hxy)

/-- The set of Stacks 053U is contained in the closure of `x` in `X_s`. -/
private theorem setOf_subset_closure_asFiber {X S : Scheme.{u}} (f : X ⟶ S) (x x' : X) :
    {y : f.fiber (f x) | IsClosed ({y} : Set (f.fiber (f x))) ∧
        x ⤳ f.fiberι (f x) y ∧ f.fiberι (f x) y ⤳ x'} ⊆
      closure ({f.asFiber x} : Set (f.fiber (f x))) := by
  rintro y ⟨-, hxy, -⟩
  exact mem_closure_asFiber_of_specializes f x hxy

/-- If `x` lies in the closure of the set of Stacks 053U, that closure is the closure of `x`
in `X_s`. -/
private theorem closure_setOf_eq_of_asFiber_mem_closure {X S : Scheme.{u}} (f : X ⟶ S) (x x' : X)
    (h : f.asFiber x ∈ closure {y : f.fiber (f x) | IsClosed ({y} : Set (f.fiber (f x))) ∧
        x ⤳ f.fiberι (f x) y ∧ f.fiberι (f x) y ⤳ x'}) :
    closure {y : f.fiber (f x) | IsClosed ({y} : Set (f.fiber (f x))) ∧
        x ⤳ f.fiberι (f x) y ∧ f.fiberι (f x) y ⤳ x'} =
      closure ({f.asFiber x} : Set (f.fiber (f x))) :=
  le_antisymm (closure_minimal (setOf_subset_closure_asFiber f x x') isClosed_closure)
    (closure_minimal (Set.singleton_subset_iff.mpr h) isClosed_closure)

/-- When `x'` lies in the fibre of `x`, the set of Stacks 053U has at most one element: a point
of `X_s` closed in `X_s` which specializes to `x'` is `x'`. -/
public theorem subsingleton_setOf_isClosed_and_specializes_fiberι {X S : Scheme.{u}} (f : X ⟶ S)
    (x : X) (z : f.fiber (f x)) :
    {y : f.fiber (f x) | IsClosed ({y} : Set (f.fiber (f x))) ∧
        x ⤳ f.fiberι (f x) y ∧ f.fiberι (f x) y ⤳ f.fiberι (f x) z}.Subsingleton := by
  rintro y₁ ⟨hy₁, -, h₁⟩ y₂ ⟨hy₂, -, h₂⟩
  exact (eq_of_fiberι_specializes_of_isClosed f hy₁ h₁).symm.trans
    (eq_of_fiberι_specializes_of_isClosed f hy₂ h₂)

/-- **A nontrivial specialization inside one fibre is outside the range of validity of the
density conclusion of Stacks 053U.** Let `x'` lie in the fibre of `x`, say
`x' = f.fiberι (f x) z`. Then that conclusion for `x ⤳ x'` forces the closure of `x` in `X_s` to
be contained in `{z}`: the set of the tag is contained in `{z}`, because a point of `X_s` closed
in `X_s` specializing to `x'` is `x'`, and a subset of a singleton has closure inside that
singleton once the point is closed.

So for any `x` whose closure in its own fibre has more than one point — the generic point of the
affine line over a field, with `x'` a closed point of it — the conclusion fails, and this is the
forward implication of `AlgebraicGeometry.closure_closedPoints_between_fiber_eq_iff`, the form
in which Stacks 053U is proved. The source relates `f x` and `f x'` by no hypothesis, so its
statement, read literally, overreaches here. -/
public theorem closure_closedPoints_between_fiber_subset_singleton_of_eq_base
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X) (z : f.fiber (f x))
    (h : closure {y : f.fiber (f x) | IsClosed ({y} : Set (f.fiber (f x))) ∧
        x ⤳ f.fiberι (f x) y ∧ f.fiberι (f x) y ⤳ f.fiberι (f x) z} =
      closure ({f.asFiber x} : Set (f.fiber (f x)))) :
    closure ({f.asFiber x} : Set (f.fiber (f x))) ⊆ ({z} : Set (f.fiber (f x))) := by
  rw [← h]
  rcases Set.eq_empty_or_nonempty {y : f.fiber (f x) | IsClosed ({y} : Set (f.fiber (f x))) ∧
      x ⤳ f.fiberι (f x) y ∧ f.fiberι (f x) y ⤳ f.fiberι (f x) z} with hempty | ⟨y, hy⟩
  · simp [hempty]
  · have hz : IsClosed ({z} : Set (f.fiber (f x))) := by
      rw [eq_of_fiberι_specializes_of_isClosed f hy.1 hy.2.2]
      exact hy.1
    exact closure_minimal
      (fun w hw ↦ (eq_of_fiberι_specializes_of_isClosed f hw.1 hw.2.2).symm) hz

/-- **The closed points of a fibre specializing from `x` are dense in the closure of `x`.** For
`f` locally of finite type the points of `X_s` which are closed in `X_s` and to which `x`
specializes are dense in the closure of `x` in `X_s`, because `X_s` is a Jacobson space. Nothing
is required of these points at a second point `x'`, which is what Stacks 053U
(`AlgebraicGeometry.closure_closedPoints_between_fiber_eq_iff`) adds. -/
public theorem closure_closedPoints_specializing_fiber_eq {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (x : X) :
    closure {y : f.fiber (f x) | IsClosed ({y} : Set (f.fiber (f x))) ∧
        x ⤳ f.fiberι (f x) y} =
      closure ({f.asFiber x} : Set (f.fiber (f x))) := by
  have hset : {y : f.fiber (f x) | IsClosed ({y} : Set (f.fiber (f x))) ∧
      x ⤳ f.fiberι (f x) y} =
      closure ({f.asFiber x} : Set (f.fiber (f x))) ∩ closedPoints (f.fiber (f x)) := by
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, mem_closedPoints_iff]
    constructor
    · rintro ⟨hy, hxy⟩
      exact ⟨mem_closure_asFiber_of_specializes f x hxy, hy⟩
    · rintro ⟨hy, hclosed⟩
      refine ⟨hclosed, ?_⟩
      simpa only [Scheme.Hom.fiberι_asFiber] using
        (f.fiberι (f x)).isEmbedding.specializes_iff.mpr (specializes_iff_mem_closure.mpr hy)
  rw [hset]
  exact JacobsonSpace.closure_inter_closedPoints isClosed_closure

/-- The density conclusion of Stacks 053U follows from the existence, in every open neighbourhood
of `x` in `X_s`, of a point of `X_s` closed in `X_s` lying between `x` and `x'`. -/
public theorem closure_closedPoints_between_fiber_eq_of_forall_isOpen {X S : Scheme.{u}}
    (f : X ⟶ S) (x x' : X)
    (h : ∀ U : Set (f.fiber (f x)), IsOpen U → f.asFiber x ∈ U →
      ∃ y ∈ U, IsClosed ({y} : Set (f.fiber (f x))) ∧
        x ⤳ f.fiberι (f x) y ∧ f.fiberι (f x) y ⤳ x') :
    closure {y : f.fiber (f x) | IsClosed ({y} : Set (f.fiber (f x))) ∧
        x ⤳ f.fiberι (f x) y ∧ f.fiberι (f x) y ⤳ x'} =
      closure ({f.asFiber x} : Set (f.fiber (f x))) :=
  closure_setOf_eq_of_asFiber_mem_closure f x x' (mem_closure_iff.mpr h)

/-- **The density conclusion of Stacks 053U when `x` is already closed in its fibre.** The set
of the tag then contains `x` itself, and every member of it lies in the closure of `x` in `X_s`,
so no hypothesis on `f` or on the two base points is needed. The conclusion in general is
`AlgebraicGeometry.closure_closedPoints_between_fiber_eq_iff`. -/
public theorem closure_closedPoints_between_fiber_eq_of_isClosed {X S : Scheme.{u}} (f : X ⟶ S)
    (x x' : X) (hxx' : x ⤳ x')
    (hx : IsClosed ({f.asFiber x} : Set (f.fiber (f x)))) :
    closure {y : f.fiber (f x) | IsClosed ({y} : Set (f.fiber (f x))) ∧
        x ⤳ f.fiberι (f x) y ∧ f.fiberι (f x) y ⤳ x'} =
      closure ({f.asFiber x} : Set (f.fiber (f x))) := by
  refine closure_setOf_eq_of_asFiber_mem_closure f x x' (subset_closure ⟨hx, ?_, ?_⟩)
  · simpa only [Scheme.Hom.fiberι_asFiber] using specializes_refl x
  · simpa only [Scheme.Hom.fiberι_asFiber] using hxx'

/-- **The density conclusion of Stacks 053U when `f` is quasi-finite at `x`.** The point `x` is
then isolated, hence closed, in its fibre. -/
public theorem closure_closedPoints_between_fiber_eq_of_quasiFiniteAt {X S : Scheme.{u}}
    (f : X ⟶ S) [LocallyOfFiniteType f] (x x' : X) (hxx' : x ⤳ x')
    (hx : f.QuasiFiniteAt x) :
    closure {y : f.fiber (f x) | IsClosed ({y} : Set (f.fiber (f x))) ∧
        x ⤳ f.fiberι (f x) y ∧ f.fiberι (f x) y ⤳ x'} =
      closure ({f.asFiber x} : Set (f.fiber (f x))) :=
  closure_closedPoints_between_fiber_eq_of_isClosed f x x' hxx'
    hx.isClopen_singleton_asFiber.isClosed

end AlgebraicGeometry

end
