module

public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.FittingIdeals
public import StacksFrontier.Topology.Sheaves.Modules.Differentials.Functoriality
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.FiberDimension
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.Defs
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.Relative

/-!
# At-worst-nodal morphisms of relative dimension one

A morphism of schemes `f : X ⟶ S` is *at-worst-nodal of relative dimension one* when it is
syntomic of relative dimension one and the closed subscheme `Sing(f) ⊆ X` cut out by the first
Fitting ideal of the sheaf of relative differentials `Ω_{X/S}` is unramified over `S`.

This is condition (2) of [Stacks, Tag 0C59]; the equivalent fibrewise condition there is that
`f` be flat and locally of finite presentation with every nonempty fibre equidimensional of
dimension one and with at-worst-nodal singularities.

## Main definitions

* `AlgebraicGeometry.relativeSingularIdeal`: the ideal sheaf of the relative singular subscheme.
* `AlgebraicGeometry.IsAtWorstNodalOfRelativeDimensionOne`: the predicate above.

## References

* [Stacks Project, Tag 0C5A](https://stacks.math.columbia.edu/tag/0C5A)
* [Stacks Project, Tag 0C59](https://stacks.math.columbia.edu/tag/0C59)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- The relative singular subscheme `Sing(f) ⊆ X` of a morphism of schemes: the closed
subscheme cut out by the first Fitting ideal of the sheaf of relative differentials
`Ω_{X/S}`. -/
public def relativeSingularIdeal {X S : Scheme.{u}} (f : X ⟶ S) : X.IdealSheafData :=
  fittingIdeal (Scheme.Hom.relativeDifferentials f) 1

/-- A morphism is at-worst-nodal of relative dimension one if it is syntomic of relative
dimension one and its relative singular subscheme is unramified over the base. -/
@[stacks 0C5A]
public abbrev IsAtWorstNodalOfRelativeDimensionOne {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  SyntomicOfRelativeDimension 1 f ∧ Unramified ((relativeSingularIdeal f).subschemeι ≫ f)

/-- An at-worst-nodal morphism of relative dimension one is syntomic of relative
dimension one. -/
public theorem IsAtWorstNodalOfRelativeDimensionOne.syntomicOfRelativeDimension
    {X S : Scheme.{u}} {f : X ⟶ S} (hf : IsAtWorstNodalOfRelativeDimensionOne f) :
    SyntomicOfRelativeDimension 1 f :=
  hf.1

/-- The relative singular subscheme of an at-worst-nodal morphism of relative dimension one is
unramified over the base. -/
public theorem IsAtWorstNodalOfRelativeDimensionOne.unramified_relativeSingular
    {X S : Scheme.{u}} {f : X ⟶ S} (hf : IsAtWorstNodalOfRelativeDimensionOne f) :
    Unramified ((relativeSingularIdeal f).subschemeι ≫ f) :=
  hf.2

end AlgebraicGeometry

end
