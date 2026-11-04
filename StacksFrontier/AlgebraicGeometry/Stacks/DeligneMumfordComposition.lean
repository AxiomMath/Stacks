module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.FibreProductComparison
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyComp
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentabilityComp
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationComposition

/-!
# Composition of Deligne–Mumford morphisms of algebraic stacks (Stacks 050K)

Stacks 050K says that all of the separation axioms of Definition 04YW are stable under
composition. The Deligne–Mumford case — the composite of two Deligne–Mumford 1-morphisms of
algebraic stacks over `S` is Deligne–Mumford — is
`AlgebraicGeometry.Stack.AlgebraicStacks.isDM_comp`, proved in
`StacksFrontier.AlgebraicGeometry.Stacks.SeparationComposition` alongside the three other clauses of
Stacks 050K, and re-exported here.

There the relative diagonal of the composite is factored as

    𝒳 ⟶ 𝒳 ×_𝒴 𝒳 ⟶ 𝒳 ×_𝒵 𝒳,

the first map being the relative diagonal of `f` and the second the comparison 1-morphism of
Stacks 050H. The first factor is representable by algebraic spaces and unramified because `f` is
Deligne–Mumford; the second is, by Stacks 050H parts (1) and (4), because `g` is. Stacks 0301 and
Stacks 045B then give the composite, unramifiedness of morphisms of algebraic spaces being stable
under composition by Stacks 03ZI.

## References

* [Stacks Project, Tag 050K](https://stacks.math.columbia.edu/tag/050K)
* [Stacks Project, Tag 04YW](https://stacks.math.columbia.edu/tag/04YW)
* [Stacks Project, Tag 050H](https://stacks.math.columbia.edu/tag/050H)
-/
