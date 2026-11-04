module

public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentationPoint
public import StacksFrontier.AlgebraicGeometry.Topologies.Ph.StandardCoverings
public import StacksCore.Tactic.StacksAttribute

/-!
# Standard h coverings

A standard h covering of an affine scheme `T` is a finite family of morphisms of finite
presentation from affine schemes to `T` which admits a refinement by a standard ph covering
of `T`.

## Main definitions

* `AlgebraicGeometry.IsStandardHCovering`: the predicate that a family is a standard h
  covering.

## Main results

There are no results beyond the definition.

## Implementation notes

A family and its refining standard ph covering are both represented by
`CategoryTheory.PreZeroHypercover`, and a refinement is a morphism from the latter to the
former, so the refinement condition is the existence of a standard ph covering admitting such
a morphism.  As for `AlgebraicGeometry.IsPHCovering` the refining covering is pinned to the
scheme universe `u` while the family itself is indexed in an independent universe; the
definition is exposed so that clients can use its finiteness, affineness, finite-presentation
and refinement components directly.

## References

* [Stacks Project, Tag 0EUY](https://stacks.math.columbia.edu/tag/0EUY)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u v

namespace AlgebraicGeometry

/-- **Stacks 0EUY, part (1).** A family `fᵢ : Xᵢ ⟶ T` over an affine scheme `T` is a
**standard h covering** when its index type is finite, every `Xᵢ` is affine, every `fᵢ` is of
finite presentation, and some standard ph covering of `T` refines the family. -/
@[stacks 0EUY "part (1)"]
public noncomputable def IsStandardHCovering {T : Scheme.{u}} [IsAffine T] {I : Type v}
    {X : I → Scheme.{u}} (f : ∀ i, X i ⟶ T) : Prop :=
  Finite I ∧ (∀ i, IsAffine (X i)) ∧ (∀ i, FinitePresentation (f i)) ∧
    ∃ 𝒰 : PreZeroHypercover.{u} T,
      StandardPHCovering 𝒰.f ∧
        Nonempty (𝒰.Hom ({ I₀ := I, X := X, f := f } : PreZeroHypercover.{v} T))

end AlgebraicGeometry
