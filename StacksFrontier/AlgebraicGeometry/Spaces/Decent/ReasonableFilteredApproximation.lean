module

public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ReasonableFilteredApproximation.DirectedApproximation
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ReasonableFilteredApproximation.QuotientStages
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ReasonableFilteredApproximation.OpenSubrelations
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ReasonableFilteredApproximation.QuotientDiagram
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ReasonableFilteredApproximation.Existence

/-!
# Stacks 03K0: a quasi-compact reasonable algebraic space is a filtered colimit of
quasi-compact quasi-separated ones

Stacks 03K0 asserts that a quasi-compact reasonable algebraic space `X` over `S` is the
colimit, in sheaves, of a directed system of quasi-compact and quasi-separated algebraic
spaces `X i`, and that the system can be arranged so that

1. `colim (X i)(T) = X(T)` for every quasi-compact test scheme `T` over `S`,
2. the transition morphisms and the coprojections are surjective and étale, and
3. when `X` is a scheme the `X i` are schemes and all those morphisms are local
   isomorphisms.

`AlgebraicGeometry.Space.CorrectedDirectedApproximation` is that conclusion with clause (1)
corrected, and `AlgebraicGeometry.Space.exists_correctedDirectedApproximation` proves it for
every quasi-compact reasonable `X`. **No quasi-separatedness is assumed of `X`**, and the
system produced is not constant.

## Clause (1) is corrected here

Clause (1) as the source writes it, over all quasi-compact test schemes, is false: it forces
`X` itself to be quasi-separated. That refutation is
`AlgebraicGeometry.Space.isAbsolutelyQuasiSeparated_of_directedApproximation` below, stated for
`AlgebraicGeometry.Space.DirectedApproximation`, the source's literal conclusion; for a
quasi-compact scheme the literal statement holds exactly when the scheme is quasi-separated
(`AlgebraicGeometry.Space.nonempty_directedApproximation_iff`). The clause proved here keeps the
injectivity half over every quasi-compact test scheme, as the source has it, and restricts the
surjectivity half to test schemes that are quasi-compact **and quasi-separated**, which is what
the source's own argument supports: a section over `T` is assembled from a descent datum on
`T' ×_T T'` for an affine étale cover `T' → T`, and that fibre product is quasi-compact only
when the diagonal of `T` is.

The refutation is made unconditional in
`AlgebraicGeometry.Space.exists_quasiCompact_reasonable_isEmpty_directedApproximation` of
`StacksFrontier.AlgebraicGeometry.Spaces.Decent.ReasonableFilteredApproximationCounterexample`:
the doubled-origin scheme of Example 01KL is quasi-compact
(`AlgebraicGeometry.compactSpace_scheme`), not quasi-separated
(`AlgebraicGeometry.not_quasiSeparatedSpace_scheme`) and reasonable
(`AlgebraicGeometry.Space.isReasonableSpace_yoneda`, the composite `(θ) ⇒ (ζ) ⇒ (ε) ⇒ (δ)` of
the diagram of Stacks 03JX), so it is a quasi-compact reasonable algebraic space for which the
conclusion of 03K0 as stated is unattainable.

## The system, and why it is not constant

Following the source: by Stacks 03H6 take an affine étale surjective chart `U ⟶ X` and form
`R = U ×_X U`, so that `X = U/R`. The index category is the quasi-compact open subschemes
`R' ⊆ R` on which the two projections still form an étale equivalence relation on `U`, ordered
by inclusion, and the stage at `R'` is the quotient `U/R'`.

The content is that this index set is directed and cofinal in the quasi-compact opens of `R`:
every quasi-compact open `A ⊆ R` is contained in one, which is
`exists_compact_open_subrelation_of_hasUniversallyBoundedFibers`. Reasonableness bounds the
fibre degrees of `U ⟶ X` by some `N` (Stacks 03JL); after enlarging `A` to contain the image of
the unit `e : U ⟶ R`, which is open because `e` is a section of the étale map `s` (Stacks 024T),
the iterates `A ^ (n + 1) = c(A ^ n ×_{s, U, t} A)` are quasi-compact opens, and on the points
over an algebraically closed field `A ^ n` is the set of pairs joined by a chain of `n` steps in
`A`. A chain longer than `N` repeats a point in a fibre of `U(k) ⟶ X(k)` and can be shortened,
so the iterates stabilise at `N` and `A ^ N` is the required subrelation.

`R` itself is quasi-compact exactly when `X` is quasi-separated, so for a general reasonable `X`
no single stage carries all of `R` and the system is genuinely non-constant; only when `X` is
quasi-separated does the index set have a largest element, `R` itself. The construction is the
same in both cases, and no case distinction is made.

Each stage is an algebraic space by Stacks 02WW, quasi-compact because `U` is affine, and
quasi-separated by Stacks 07S4 because `R' ⟶ U ×_{Spec ℤ} U` is quasi-compact. Clause (3) comes
from choosing the chart to be a local isomorphism when `X` is representable.

## Both conclusions live here, and neither is an instance of the other

This module carries the source's **literal** conclusion and the **corrected** one side by side,
because the refutation is a statement about the literal one and the construction is a statement
about the corrected one:

* `AlgebraicGeometry.Space.DirectedApproximation` has clause (1) over all quasi-compact test
  schemes, exactly as the source writes it. It is the subject of
  `AlgebraicGeometry.Space.isAbsolutelyQuasiSeparated_of_directedApproximation`, which refutes
  it, and of `AlgebraicGeometry.Space.nonempty_directedApproximation_iff`, which says that for
  a quasi-compact *scheme* it holds precisely when the scheme is quasi-separated.
* `AlgebraicGeometry.Space.CorrectedDirectedApproximation` has clause (1) over quasi-compact
  *quasi-separated* test schemes, and is what
  `AlgebraicGeometry.Space.exists_correctedDirectedApproximation` produces for every
  quasi-compact reasonable `X`.

The two differ only in that quantifier and in the encoding of the colimit cocone — the literal
one names the coprojections as a natural transformation into a constant functor, the corrected
one carries a `CategoryTheory.Limits.Cocone` together with an isomorphism of its vertex with
`X` — and their index categories sit in different universes (`Cat.{u, u}` against `Cat.{0, u}`),
so there is no conversion between them in either direction. Neither theorem subsumes the other:
`AlgebraicGeometry.Space.exists_directedApproximation_of_isAbsolutelyQuasiSeparated` is the only
case in which the literal clause (1) is available at all, and it is necessarily the constant
system, while `AlgebraicGeometry.Space.exists_correctedDirectedApproximation` says nothing about
the literal clause (1) and cannot, since for a non-quasi-separated `X` that clause is false.

## Main definitions

* `AlgebraicGeometry.Space.CorrectedDirectedApproximation` — the conclusion of Stacks 03K0 with
  clause (1) in its corrected form: the filtered index category, the diagram, the colimit
  comparison, and the three clauses.

## Main results

* `AlgebraicGeometry.Space.exists_correctedDirectedApproximation` — **Stacks 03K0**: every
  quasi-compact reasonable algebraic space carries such an approximation.

## Implementation notes

Everything between the two public declarations is in the namespace
`AlgebraicGeometry.Space.ReasonableApproximation` and private to this module.

"Quasi-compact quasi-separated test scheme" is transcribed as an object `T` of the big fppf
site of `S` whose underlying scheme is a `CompactSpace` and a `QuasiSeparatedSpace`; the site's
cardinal cutoff is a framework artifact and not part of the mathematical hypothesis.
`colim (X i)(T) = X(T)` is transcribed as the two halves of bijectivity of the canonical map out
of a filtered colimit of sets: every section of `X` over `T` is the image of a section of some
stage, and two sections of stages with the same image are identified by some pair of transition
maps.

The index category is the preorder of qualifying opens, made a `Cat.{0, u}` by
`smallPreorderCategory`; filteredness is `smallPreorderCategory_isFiltered` applied to the
directedness supplied by the subrelation statement above. The subrelation statement is proved
first in the form `exists_compact_open_subrelation_of_bounded_geometric_fibers`, where the
hypothesis is a cardinality bound on the geometric fibres of the relation, and the bound is then
produced from Stacks 03JL by `exists_uniform_finite_card_scheme_fibers`, whose input in turn is
the finiteness of the sections of a finite locally free morphism to a field spectrum.

Surjectivity of a morphism of algebraic spaces is transcribed as `AlgebraicGeometry.Space.
IsSurjective`, surjectivity on the point sets of Stacks 03BU, which Stacks 03MD identifies with
the represented-base-change form used by the atlases of this library. Quasi-separatedness of the
stages is the absolute one of Stacks 03BS part (3), over `Spec ℤ`, which is what
"quasi-separated algebraic space" means in the Stacks chapter on decent spaces.

## References

* [Stacks Project, Tag 03K0](https://stacks.math.columbia.edu/tag/03K0)
* [Stacks Project, Tag 03H6](https://stacks.math.columbia.edu/tag/03H6)
* [Stacks Project, Tag 03JL](https://stacks.math.columbia.edu/tag/03JL)
* [Stacks Project, Tag 024T](https://stacks.math.columbia.edu/tag/024T)
* [Stacks Project, Tag 02WW](https://stacks.math.columbia.edu/tag/02WW)
* [Stacks Project, Tag 07S4](https://stacks.math.columbia.edu/tag/07S4)
* [Stacks Project, Tag 03BS](https://stacks.math.columbia.edu/tag/03BS)
-/
