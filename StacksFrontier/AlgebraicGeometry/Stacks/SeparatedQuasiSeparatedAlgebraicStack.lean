module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionProper
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparatedDiagonalConditions
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationAxioms

/-!
# Separated and quasi-separated 1-morphisms of algebraic stacks (Stacks 04YW, 050E)

Following Stacks 04YW, a 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks over `S` *is separated* when
its relative diagonal `Δ_f : 𝒳 ⟶ 𝒳 ×_{f, 𝒴, f} 𝒳` is proper, and *is quasi-separated* when `Δ_f`
is quasi-compact and quasi-separated. Both notions are the Stacks 04XB relative properties of the
relative diagonal, which is representable by algebraic spaces by Stacks 04XS, part (1).

Those two conditions are `AlgebraicGeometry.Stack.AlgebraicStacks.IsSeparated` and
`AlgebraicGeometry.Stack.AlgebraicStacks.IsQuasiSeparated`, and **Stacks 050E** — that a separated
1-morphism is quasi-separated — is
`AlgebraicGeometry.Stack.AlgebraicStacks.isQuasiSeparated_of_isSeparated`. This module makes them
available together with the properness and closed-immersion theory of morphisms of algebraic
spaces that the proof of Stacks 050E runs on, which is what its consumers need alongside the two
conditions.

## Implementation notes

Separatedness is `AlgebraicGeometry.Stack.IsProper` of the relative diagonal, which is the
Stacks 04XB property for `AlgebraicGeometry.Space.IsProper` written out as a quantifier over
represented base changes. Quasi-separatedness is the conjunction of
`AlgebraicGeometry.Stack.IsQuasiCompact` (**Stacks 03HE**) and
`AlgebraicGeometry.Stack.IsQuasiSeparated` (**Stacks 03HL**, part (3)) of that same diagonal; the
single-quantifier spelling of the same proposition, obtained by introducing the Stacks 04XB data
once rather than twice, is `AlgebraicGeometry.Stack.AlgebraicStacks.isQuasiSeparated_iff_forall`.
Neither is routed through `AlgebraicGeometry.Stack.HasRelativeProperty` (**Stacks 03YK**), for the
reason recorded in `AlgebraicGeometry.Stack.SeparatedMorphism`: that definition carries
`[P.IsStableUnderBaseChange]` and `[P.IsLocalAtTarget …]` as instance arguments which this library
does not have for the conjunction, and since it does not *use* them the longhand quantifier is the
same proposition with no hypothesis on the property.

The relative diagonal is `AlgebraicGeometry.Stack.relativeDiagonal` into
`AlgebraicGeometry.Stack.twoFibreProduct`, at the universes the 2-category
`AlgebraicGeometry.Stack.AlgebraicStacks` is formed at — the same spelling
`AlgebraicGeometry.Stack.IsDM` (**Stacks 04YW**, the DM condition) uses, so the three conditions of
Stacks 04YW are stated about one and the same 1-morphism.

Representability by algebraic spaces of `Δ_f` is not a conjunct of either definition, unlike in
`AlgebraicGeometry.Stack.IsDM`: it is automatic for a 1-morphism of *algebraic* stacks by
Stacks 04XS, part (1)
(`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_relativeDiagonal_algebraicStacks`),
and the properties of Stacks 04XB are stated for an arbitrary 1-morphism, so no witness is needed
in order to state them.

Stacks 050E is proved exactly as the source does, clause by clause on the same quantified data,
so no comparison lemma between the two quantifiers is needed: given a represented base change
`g` of `Δ_f`, separatedness supplies `AlgebraicGeometry.Space.IsProper g`, whose second component
is finite type and hence contains quasi-compactness of `g`, and whose first component is
separatedness of `g`, which gives quasi-separatedness of `g` through
`AlgebraicGeometry.Space.isQuasiCompact_of_isClosedImmersion` applied to the relative diagonal
of `g` — this is the quasi-separated half of **Stacks 03KK**, available here because the library
spells both separatedness and quasi-separatedness of a morphism of algebraic spaces as a property
of its relative diagonal.

## References

* [Stacks Project, Tag 03HE](https://stacks.math.columbia.edu/tag/03HE)
* [Stacks Project, Tag 03HL](https://stacks.math.columbia.edu/tag/03HL)
* [Stacks Project, Tag 03KK](https://stacks.math.columbia.edu/tag/03KK)
* [Stacks Project, Tag 04XS](https://stacks.math.columbia.edu/tag/04XS)
* [Stacks Project, Tag 04YW](https://stacks.math.columbia.edu/tag/04YW)
* [Stacks Project, Tag 050E](https://stacks.math.columbia.edu/tag/050E)
-/
