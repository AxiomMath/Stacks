module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.LocallyQuasiFiniteAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactMorphism

/-!
# Quasi-finite 1-morphisms of algebraic stacks (Stacks 0G2M)

Following Stacks 0G2M, a 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks over `S` *is quasi-finite*
when it is locally quasi-finite and quasi-compact. Both conjuncts are predicates already in the
library: `AlgebraicGeometry.Stack.AlgebraicStacks.IsLocallyQuasiFinite` (**Stacks 06PU**) and
`AlgebraicGeometry.Stack.IsQuasiCompactMorphism` (**Stacks 050U**).

## Main definitions

* `AlgebraicGeometry.Stack.AlgebraicStacks.IsQuasiFinite`: a 1-morphism of algebraic stacks is
  quasi-finite when it is locally quasi-finite and quasi-compact.

## Implementation notes

This is quasi-finiteness of an *arbitrary* 1-morphism of algebraic stacks, so both conjuncts are
taken at that generality. The two leaf names `IsLocallyQuasiFinite` and `IsQuasiCompact` each also
name a different notion in `AlgebraicGeometry.Stack`, namely the Stacks 04XB relative property of
a 1-morphism representable by algebraic spaces; those take a 1-morphism of categories fibred in
groupoids and are not the predicates used here. The quasi-compactness conjunct is spelled
`AlgebraicGeometry.Stack.IsQuasiCompactMorphism` for that reason, its leaf name being the
unambiguous one.

## References

* [Stacks Project, Tag 050U](https://stacks.math.columbia.edu/tag/050U)
* [Stacks Project, Tag 06PU](https://stacks.math.columbia.edu/tag/06PU)
* [Stacks Project, Tag 0G2M](https://stacks.math.columbia.edu/tag/0G2M)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack.AlgebraicStacks

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks over `S` *is quasi-finite*
when it is locally quasi-finite (**Stacks 06PU**) and quasi-compact (**Stacks 050U**). -/
@[stacks 0G2M]
abbrev IsQuasiFinite {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) : Prop :=
  IsLocallyQuasiFinite B S hS f ∧ Stack.IsQuasiCompactMorphism B S hS f

end AlgebraicGeometry.Stack.AlgebraicStacks

end
