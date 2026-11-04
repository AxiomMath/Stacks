module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparisonTopologies
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SmoothCoverings

/-!
# Stability properties of the syntomic coverings of algebraic spaces

Let `S` be a scheme contained in a big fppf site `B`. The syntomic covering families of
algebraic spaces over `S`, `AlgebraicGeometry.Space.IsSyntomicCovering`, are the covering
families of the syntomic topology of Stacks 03YH. A singleton family on an isomorphism is one
of them.

## Main results

* `AlgebraicGeometry.Space.isSyntomicCovering_of_isIso`: **Stacks 041B**, the isomorphism
  clause.

## Implementation notes

An isomorphism is a smooth covering (`AlgebraicGeometry.Space.isSmoothCovering_of_isIso`,
**Stacks 041D**), and a smooth covering is a syntomic covering
(`AlgebraicGeometry.Space.isSyntomicCovering_of_isSmoothCovering`, **Stacks 0DFB**). The proof
composes the two, and so uses no stability of syntomic morphisms of algebraic spaces under
composition or base change.

## References

* [Stacks Project, Tag 041B](https://stacks.math.columbia.edu/tag/041B)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 041B**, the isomorphism clause. An isomorphism of algebraic spaces over `S`,
regarded as a family indexed by a point, is a syntomic covering. -/
@[stacks 041B "part (1), isomorphisms"]
lemma isSyntomicCovering_of_isIso
    {X' X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X' ⟶ X) [IsIso f]
    (hX : IsAlgebraicSpace B S hS X) :
    IsSyntomicCovering B S hS (fun _ : Unit ↦ X') (fun _ ↦ f) :=
  isSyntomicCovering_of_isSmoothCovering B S hS (isSmoothCovering_of_isIso B S hS f hX)

end AlgebraicGeometry.Space

end
