module

public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# Curves over a field

A curve over a field is a variety whose underlying space has Krull dimension one. This is the
definitional starting point for the theory of curves: the variety condition supplies
integrality, separatedness and finite type over the field, and the dimension condition cuts
the theory down to the one-dimensional case.

## Main definitions

* `AlgebraicGeometry.IsCurve` is the property that a variety over a field has dimension one.

## Main results

* `AlgebraicGeometry.isCurve_iff` characterizes curves as varieties of dimension one.

## Implementation notes

As for `AlgebraicGeometry.IsVariety`, the structure morphism to the spectrum of the field is an
explicit argument. The variety condition is inherited as a typeclass parent, and the dimension
condition uses the Krull dimension of the underlying topological space. Downstream users can
therefore recover the variety structure by typeclass inference and the dimension equality by the
projection `IsCurve.topologicalKrullDim_eq_one`; `isCurve_iff` provides the corresponding
propositional rewriting interface.

## References

* [Stacks Project, Tag 0A23](https://stacks.math.columbia.edu/tag/0A23)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 0A23.** A curve over a field is a variety of Krull dimension one. -/
@[stacks 0A23, stacks 03RE "the curve clause", ega "II 7.4.2" "special case"]
public class IsCurve (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) : Prop
    extends IsVariety k f where
  topologicalKrullDim_eq_one : topologicalKrullDim X = 1

/-- A scheme over a field is a curve exactly when it is a variety of Krull dimension one. -/
@[simp] public theorem isCurve_iff (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) :
    IsCurve k f ↔ IsVariety k f ∧ topologicalKrullDim X = 1 :=
  ⟨fun h => ⟨h.toIsVariety, h.topologicalKrullDim_eq_one⟩,
    fun ⟨hv, hd⟩ => { toIsVariety := hv, topologicalKrullDim_eq_one := hd }⟩

end AlgebraicGeometry
