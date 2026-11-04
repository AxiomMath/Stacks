module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.Permanence
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.QuasiCompactMonomorphicPoint

/-!
# Decency of the source of an étale morphism

An algebraic space étale over a decent algebraic space is itself decent. This is the decent
half of **Stacks 0ABU**.

## Main results

* `AlgebraicGeometry.Space.isDecentSpace_of_isEtale`: the source of an étale morphism of
  algebraic spaces over `S` whose target is decent is decent.

## Implementation notes

`AlgebraicGeometry.Space.IsDecentSpace` spells the definition of Stacks 03I8 with condition
(4) of Stacks 03JV, a quasi-compact monomorphism from the spectrum of a field, whereas the
argument of Stacks 0ABU runs on condition (1), finiteness of the fibres of a chart and of its
self-intersection. The passage between the two shapes is the equivalence of those two
conditions,
`AlgebraicGeometry.Space.isDecentSpace_iff_hasFiniteChartAndRelationFibersAtEveryPoint`, and
the argument itself is
`AlgebraicGeometry.Space.hasFiniteChartAndRelationFibersAtEveryPoint_of_isEtale`.

That argument needs no algebraicity of either presheaf, but the equivalence does, so both the
source and the target are assumed to be algebraic spaces here — which is what Stacks 0ABU
assumes, its morphism being a morphism of algebraic spaces.

Stacks 0ABU also asserts that the source of an étale morphism with reasonable target is
reasonable. That half is a different argument — the fibre of a chart over the source is an
*open subscheme* of its fibre over the target, the diagonal of an étale morphism being an open
immersion, so a degree bound for the latter bounds the former — and is carried out by
`AlgebraicGeometry.Space.isReasonableSpace_of_isEtale` in
`StacksFrontier.AlgebraicGeometry.Spaces.Decent.EtaleSourceReasonableness`, which is why the
attribute below names the case it proves.

## References

* [Stacks Project, Tag 0ABU](https://stacks.math.columbia.edu/tag/0ABU)
* [Stacks Project, Tag 03I8](https://stacks.math.columbia.edu/tag/03I8)
* [Stacks Project, Tag 03JV](https://stacks.math.columbia.edu/tag/03JV)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **Stacks 0ABU, the decent case.** An algebraic space over `S` étale over a decent
algebraic space over `S` is decent. -/
@[stacks 0ABU "decent"]
theorem isDecentSpace_of_isEtale (f : X ⟶ Y) (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (hf : IsEtale B S hS f)
    (hdec : IsDecentSpace B S hS Y) :
    IsDecentSpace B S hS X :=
  (isDecentSpace_iff_hasFiniteChartAndRelationFibersAtEveryPoint B S hS X hX).2
    (hasFiniteChartAndRelationFibersAtEveryPoint_of_isEtale B S hS f hf
      ((isDecentSpace_iff_hasFiniteChartAndRelationFibersAtEveryPoint B S hS Y hY).1 hdec))

end AlgebraicGeometry.Space

end
