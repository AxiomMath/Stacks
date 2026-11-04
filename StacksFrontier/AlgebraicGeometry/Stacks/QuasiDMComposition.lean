module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteMorphismProperty
public import StacksFrontier.AlgebraicGeometry.Stacks.FibreProductComparisonSeparation
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDiagonalRepresentable
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyComp
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentabilityComp
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationComposition

/-!
# Composition of quasi-DM 1-morphisms of algebraic stacks (Stacks 050K)

Stacks 050K says that all of the separation axioms of Definition 04YW are stable under
composition. The quasi-DM case — the composite of two quasi-DM 1-morphisms of algebraic stacks
over `S` is quasi-DM — is `AlgebraicGeometry.Stack.AlgebraicStacks.isQuasiDM_comp`, proved in
`StacksFrontier.AlgebraicGeometry.Stacks.SeparationComposition` alongside the three other clauses of
Stacks 050K, and re-exported here.

There the relative diagonal of the composite is factored as

    𝒳 ⟶ 𝒳 ×_𝒴 𝒳 ⟶ 𝒳 ×_𝒵 𝒳,

the first map being the relative diagonal of `f` and the second the comparison 1-morphism of
Stacks 050H. The first factor is locally quasi-finite because `f` is quasi-DM; the second is, by
Stacks 050H part (5), because `g` is. Stacks 0301 and Stacks 045B then give the composite.

Like the quasi-separatedness condition of Stacks 04YW, the quasi-DM condition of Stacks 04YW is
the bare Stacks 04XB quantifier on the relative diagonal and carries no representability witness.
The representability witness that Stacks 045B nevertheless takes is not asked of the caller: it is
supplied by **Stacks 04XS**, part (1), through
`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_relativeDiagonal_algebraicStacks`, which
makes it automatic for a 1-morphism of *algebraic* stacks. The variant of the condition that does
carry the witness as a conjunct is
`AlgebraicGeometry.Stack.AlgebraicStacks.IsQuasiDMWithRepresentableDiagonal`, which that
same result shows to be the same proposition.

## References

* [Stacks Project, Tag 0427](https://stacks.math.columbia.edu/tag/0427)
* [Stacks Project, Tag 045B](https://stacks.math.columbia.edu/tag/045B)
* [Stacks Project, Tag 04XS](https://stacks.math.columbia.edu/tag/04XS)
* [Stacks Project, Tag 04YW](https://stacks.math.columbia.edu/tag/04YW)
* [Stacks Project, Tag 050H](https://stacks.math.columbia.edu/tag/050H)
* [Stacks Project, Tag 050K](https://stacks.math.columbia.edu/tag/050K)
-/
