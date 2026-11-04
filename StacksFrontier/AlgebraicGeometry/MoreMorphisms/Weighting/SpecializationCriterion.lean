module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.SmoothSupportClopen
public import StacksFrontier.AlgebraicGeometry.Properties.Noetherian
public import StacksCore.Tactic.StacksAttribute

/-!
# Local constancy on a locally Noetherian scheme from invariance along specializations

On a locally Noetherian scheme a function that takes the same value at a point and at each of
its specializations is locally constant. This is the criterion that reduces the local constancy
required of the weighted fibre sums in the definition of a weighting to a statement about
specializations in the base of a chart, which is locally Noetherian as soon as the target of the
weighted morphism is, the chart morphism being étale.

## Main results

* `AlgebraicGeometry.isLocallyConstant_of_specializes_eq_of_isLocallyNoetherian` — a function on
  a locally Noetherian scheme that is invariant along specializations is locally constant.
* `AlgebraicGeometry.isLocallyNoetherian_of_etale` — the source of an étale morphism with
  locally Noetherian target is locally Noetherian.

## Implementation notes

The topological content is `Stacks.Chow.isLocallyConstant_of_specializes_eq`, which asks for a
quasi-sober space with a locally Noetherian topology. Both inputs are automatic for a scheme:
quasi-sobriety is a Mathlib instance, and the topology underlying a locally Noetherian scheme is
locally Noetherian by `AlgebraicGeometry.isLocallyNoetherianSpace_of_isLocallyNoetherian`. The
source lemma phrases invariance as `∀ x y, x ⤳ y → n x = n y`, i.e. the value at a point equals
the value at the generalizations of that point; the statement below phrases it the other way
round, as `∀ v v', v' ⤳ v → F v' = F v`, and the two are exchanged by swapping the arguments.

`AlgebraicGeometry.isLocallyNoetherian_of_etale` is a one-line consequence of the Mathlib
theorem `AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian`, an étale morphism being
locally of finite type. Mathlib states that theorem rather than registering it as an instance,
to avoid a loop in instance search, so the étale version is stated here as a theorem too.

## References

* [Stacks Project, Tag 0F3A](https://stacks.math.columbia.edu/tag/0F3A)
* [Stacks Project, Tag 01OZ](https://stacks.math.columbia.edu/tag/01OZ)
* [Stacks Project, Tag 01T6](https://stacks.math.columbia.edu/tag/01T6)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- A function on a locally Noetherian scheme which takes the same value at every specialization
of a point as at the point itself is locally constant. -/
theorem isLocallyConstant_of_specializes_eq_of_isLocallyNoetherian {V : Scheme.{u}}
    [IsLocallyNoetherian V] {β : Type*} {F : V → β}
    (hF : ∀ v v' : V, v' ⤳ v → F v' = F v) : IsLocallyConstant F :=
  Stacks.Chow.isLocallyConstant_of_specializes_eq
    (AlgebraicGeometry.isLocallyNoetherianSpace_of_isLocallyNoetherian V)
    fun x y hxy ↦ hF y x hxy

end AlgebraicGeometry
