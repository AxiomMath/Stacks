module

public import Mathlib.AlgebraicGeometry.Fiber
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.ClosedPointsInFibres

/-!
# The conclusion of Stacks 053U inside a single fibre

Let `f : X ⟶ S` be a morphism of schemes, let `x` and `x'` be points of `X` lying over the same
point `s = f x`, and suppose the conclusion of Stacks 053U holds for the pair `(x, x')`: the
points of `X_s` which are closed in `X_s` and lie between `x` and `x'` are dense in the closure
of `x` in `X_s`. Then `x` itself is closed in `X_s`.

This is the one situation admitted by the hypotheses of Stacks 053U as printed in which its
conclusion fails, read as a consequence rather than as a counterexample: the set of the tag is
then a subsingleton, so the density forces the closure of `x` in `X_s` to be a single point.

## Main results

* `AlgebraicGeometry.isClosed_asFiber_of_closure_closedPoints_between_fiber_eq`: the conclusion
  of Stacks 053U for a pair of points of one fibre forces the first to be closed in that fibre.

## Implementation notes

Nothing here is registered under 053U. The tag itself, under its own hypotheses together with
the exact range of validity of its conclusion, is
`AlgebraicGeometry.closure_closedPoints_between_fiber_eq_iff` in
`StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.ClosedPointsBetweenInFibres`, whose forward
implication is the same computation carried out through
`AlgebraicGeometry.closure_closedPoints_between_fiber_subset_singleton_of_eq_base`. The result
here differs from that forward implication in assuming nothing about `f`, about the pair
`(x, x')` beyond their lying over one point, and nothing about closedness: it is the form used
by `AlgebraicGeometry.isClosed_asFiber_of_stacks053UAsPrinted` in
`StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.SpecializationChainToClosedSpecialization` to
derive from the tag as printed that every morphism locally of finite type has discrete fibres.

## References

* [Stacks Project, Tag 053U](https://stacks.math.columbia.edu/tag/053U)
-/

public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry

/-- **The conclusion of Stacks 053U forces `x` to be closed in its fibre whenever `x'` lies in
that same fibre.** The set of the tag is then a subsingleton — a point of `X_s` closed in `X_s`
which specializes to `x'` *is* `x'` — and a subsingleton cannot have the closure of `x` as its
closure unless that closure is `{x}`: the empty set has empty closure, and a single closed point
`y` has closure `{y}`, which contains `x` only if `y = x`.

This is the engine of the refutation of the tag as printed: it needs only one morphism locally of
finite type with a point not closed in its own fibre, and then
`AlgebraicGeometry.exists_chain_isImmediateSpecialization_isClosed_fiber` supplies the `x'` in
the same fibre. See `StacksDraft.Examples.Scheme.ClosedPointsInFibreNotDense`. -/
public theorem isClosed_asFiber_of_closure_closedPoints_between_fiber_eq {X S : Scheme.{u}}
    (f : X ⟶ S) (x x' : X) (hfib : f x' = f x)
    (hdense : closure {y : f.fiber (f x) | IsClosed ({y} : Set (f.fiber (f x))) ∧
        x ⤳ f.fiberι (f x) y ∧ f.fiberι (f x) y ⤳ x'} =
      closure ({f.asFiber x} : Set (f.fiber (f x)))) :
    IsClosed ({f.asFiber x} : Set (f.fiber (f x))) := by
  obtain ⟨z, hz⟩ : x' ∈ Set.range (f.fiberι (f x)) := (f.range_fiberι (f x)).ge hfib
  have hsub : {y : f.fiber (f x) | IsClosed ({y} : Set (f.fiber (f x))) ∧
      x ⤳ f.fiberι (f x) y ∧ f.fiberι (f x) y ⤳ x'}.Subsingleton := by
    rw [← hz]
    exact subsingleton_setOf_isClosed_and_specializes_fiberι f x z
  rcases hsub.eq_empty_or_singleton with hempty | ⟨y, hy⟩
  · rw [hempty, closure_empty] at hdense
    exact absurd (hdense.symm.le (subset_closure (Set.mem_singleton (f.asFiber x))))
      (Set.notMem_empty (f.asFiber x))
  · have hyclosed : IsClosed ({y} : Set (f.fiber (f x))) := (hy.ge (Set.mem_singleton y)).1
    rw [hy, hyclosed.closure_eq] at hdense
    have hxy : f.asFiber x = y :=
      Set.mem_singleton_iff.mp (hdense.ge (subset_closure (Set.mem_singleton _)))
    rw [← closure_eq_iff_isClosed, ← hdense, hxy]

end AlgebraicGeometry

end
