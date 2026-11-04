module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.FibreProductComparisonSeparation
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDiagonalRepresentable
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyComp
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentabilityComp
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationComposition

/-!
# Composition of quasi-separated 1-morphisms of algebraic stacks (Stacks 050K)

Stacks 050K says that all of the separation axioms of Definition 04YW are stable under
composition. The quasi-separated case — the composite of two quasi-separated 1-morphisms of
algebraic stacks over `S` is quasi-separated — is
`AlgebraicGeometry.Stack.AlgebraicStacks.isQuasiSeparated_comp`, proved in
`StacksFrontier.AlgebraicGeometry.Stacks.SeparationComposition` alongside the three other clauses of
Stacks 050K, and re-exported here.

There the relative diagonal of the composite is factored as

    𝒳 ⟶ 𝒳 ×_𝒴 𝒳 ⟶ 𝒳 ×_𝒵 𝒳,

the first map being the relative diagonal of `f` and the second the comparison 1-morphism of
Stacks 050H. The first factor is quasi-compact and quasi-separated because `f` is quasi-separated;
the second is, by Stacks 050H part (7), because `g` is. Stacks 0301 and Stacks 045B then give the
composite. Quasi-separatedness of Stacks 04YW is a *conjunction* of two conditions of Stacks 04XB,
so the argument is run once at each of quasi-compactness and quasi-separatedness of morphisms of
algebraic spaces.

Unlike `AlgebraicGeometry.Stack.IsDM`, the quasi-separatedness condition of Stacks 04YW does not
carry representability by algebraic spaces of the relative diagonal as a conjunct, so the witness
Stacks 045B needs is supplied by **Stacks 04XS**, part (1), through
`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_relativeDiagonal_algebraicStacks`: it is
automatic for a 1-morphism of *algebraic* stacks, so nothing is assumed there that the
Deligne–Mumford case gets from its hypothesis.

## References

* [Stacks Project, Tag 045B](https://stacks.math.columbia.edu/tag/045B)
* [Stacks Project, Tag 04XS](https://stacks.math.columbia.edu/tag/04XS)
* [Stacks Project, Tag 04YW](https://stacks.math.columbia.edu/tag/04YW)
* [Stacks Project, Tag 050H](https://stacks.math.columbia.edu/tag/050H)
* [Stacks Project, Tag 050K](https://stacks.math.columbia.edu/tag/050K)
-/
