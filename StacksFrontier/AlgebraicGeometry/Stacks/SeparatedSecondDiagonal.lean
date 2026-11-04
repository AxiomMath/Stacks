module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.UniversallyClosed
public import StacksFrontier.AlgebraicGeometry.Stacks.HigherDiagonalSeparation
public import StacksFrontier.AlgebraicGeometry.Stacks.ProperAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDiagonalFiniteType
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationAxioms

/-!
# Stacks 04Z0, part (1): separated morphisms and the first two diagonals

Let `S` be a scheme contained in a big fppf site `B` and let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of
algebraic stacks over `S`, with no representability assumption. Part (1) of Stacks 04Z0 says that
`f` is separated, in the sense of Definition 04YW, exactly when its first relative diagonal
`Δ_{f,1} : 𝒳 ⟶ 𝒳 ×_{f, 𝒴, f} 𝒳` and its second relative diagonal `Δ_{f,2}`, the relative
diagonal of `Δ_{f,1}`, are universally closed in the relative sense of Properties of Stacks,
Section 04XB. This file proves it.

Definition 04YW asks of a separated `f` exactly that `Δ_{f,1}` be proper, and properness of a
morphism of algebraic spaces is separatedness, finite type and universal closedness
(**Stacks 03ZM**), with finite type being local finite type together with quasi-compactness. So
the equivalence splits into four clauses on `Δ_{f,1}`, read chart by chart:

* **universal closedness** is the first conjunct on the right, on the nose;
* **separatedness** of `Δ_{f,1}` is universal closedness of `Δ_{f,2}`, which is the equivalence
  of the first and the last condition of part (1) of **Stacks 04YZ**;
* **local finite type** of `Δ_{f,1}` is unconditional, by part (2) of **Stacks 04XS**;
* **quasi-compactness** of `Δ_{f,1}` follows from its universal closedness by **Stacks 04XW**, a
  universally closed morphism of algebraic spaces being quasi-compact.

The last two steps are the source's own proof, which deduces properness of `Δ_{f,1}` from its
being quasi-compact, separated, universally closed and locally of finite type; the second step is
the source's appeal to Lemma 04YZ, and the reading of Stacks 04XW chart by chart is the source's
appeal to Stacks 045F, which for the Section 04XB conditions as they are written here is no step
at all.

The source omits the forward implication. It is immediate from the same splitting: properness of
`Δ_{f,1}` gives its universal closedness and its separatedness directly, and the latter is
universal closedness of `Δ_{f,2}` by part (1) of Stacks 04YZ again.

## Main results

* `AlgebraicGeometry.Stack.isSeparated_iff_universallyClosed_diagonals`: **Stacks 04Z0**,
  part (1).

## Implementation notes

The four conditions on `Δ_{f,1}` are the Section 04XB predicates
`AlgebraicGeometry.Stack.UniversallyClosed`, `AlgebraicGeometry.Stack.IsSeparated` and
`AlgebraicGeometry.Stack.IsProper` of
`StacksFrontier.AlgebraicGeometry.Stacks.SeparatedMorphism`, and the proof never leaves the
quantifier: all three are literally universally quantified statements over the algebraic spaces
representing the base changes of a diagonal along scheme-valued points, with the same binders in
the same order, so the splitting of `AlgebraicGeometry.Space.IsProper` into its three conjuncts
is performed under those binders and the monotonicity step of **Stacks 045F** that the source
invokes is not needed as a separate lemma.

`AlgebraicGeometry.Space.isQuasiCompact_of_universallyClosed` — **Stacks 04XW** — needs the
source and the target of the chart morphism to be algebraic spaces. Both are: the chart morphism
is `AlgebraicGeometry.algebraicSpaceMap` of a bundled object of
`AlgebraicGeometry.AlgebraicSpaces`, so the source's algebraicity is that bundle's `property` and
the target is a representable presheaf, by `AlgebraicGeometry.isAlgebraicSpace_yoneda`. This is
the shape in which
`AlgebraicGeometry.Stack.isUnramified_relativeDiagonal_of_isRepresentableByAlgebraicSpaces`
supplies the same two witnesses.

No representability hypothesis on `f` is needed anywhere: part (1) of Stacks 04YZ carries none,
and part (2) of Stacks 04XS is the unconditional form for a 1-morphism of *algebraic* stacks of
what part (2) of Stacks 04YQ states for a representable one.

The two diagonals are the algebraic-stacks-level
`AlgebraicGeometry.Stack.relativeDiagonalAlgebraicStacks`, so the second diagonal is literally
the first applied twice; the target of the first is already the algebraic stack
`AlgebraicGeometry.Stack.twoFibreProductAlgebraicStack`, which is why no separate target bundle
is needed. This is the spelling of the three sibling parts of Stacks 04Z0 in
`StacksFrontier.AlgebraicGeometry.Stacks.DMSecondDiagonal`,
`StacksFrontier.AlgebraicGeometry.Stacks.QuasiDMSecondDiagonal` and
`StacksFrontier.AlgebraicGeometry.Stacks.QuasiSeparatedSecondDiagonal`.

## References

* [Stacks Project, Tag 04Z0](https://stacks.math.columbia.edu/tag/04Z0)
* [Stacks Project, Tag 03ZM](https://stacks.math.columbia.edu/tag/03ZM)
* [Stacks Project, Tag 045F](https://stacks.math.columbia.edu/tag/045F)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 04XS](https://stacks.math.columbia.edu/tag/04XS)
* [Stacks Project, Tag 04XW](https://stacks.math.columbia.edu/tag/04XW)
* [Stacks Project, Tag 04YQ](https://stacks.math.columbia.edu/tag/04YQ)
* [Stacks Project, Tag 04YW](https://stacks.math.columbia.edu/tag/04YW)
* [Stacks Project, Tag 04YZ](https://stacks.math.columbia.edu/tag/04YZ)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}

/-- **Stacks 04Z0, part (1).** A 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks over `S` — with no
representability hypothesis — is separated, in the sense of Definition 04YW, if and only if its
first relative diagonal `Δ_{f,1} : 𝒳 ⟶ 𝒳 ×_{f, 𝒴, f} 𝒳` and its second relative diagonal
`Δ_{f,2}`, the relative diagonal of `Δ_{f,1}`, are both universally closed in the relative sense
of Properties of Stacks, Section 04XB.

Definition 04YW is properness of `Δ_{f,1}`, and properness of a morphism of algebraic spaces is
separatedness, finite type and universal closedness. Universal closedness of `Δ_{f,1}` is the
first conjunct on the right; its separatedness is universal closedness of `Δ_{f,2}` by part (1)
of Stacks 04YZ; it is unconditionally locally of finite type by part (2) of Stacks 04XS; and it
is quasi-compact because it is universally closed, by Stacks 04XW. -/
@[stacks 04Z0 "separated"]
theorem isSeparated_iff_universallyClosed_diagonals (f : 𝒳 ⟶ 𝒴) :
    AlgebraicStacks.IsSeparated B S hS f ↔
      (UniversallyClosed B S hS (relativeDiagonalAlgebraicStacks B S hS f).hom ∧
        UniversallyClosed B S hS (relativeDiagonalAlgebraicStacks B S hS
          (relativeDiagonalAlgebraicStacks B S hS f)).hom) := by
  have htfae := isSeparated_firstRelativeDiagonal_tfae B S hS f
  have hlft := (isLocallyOfFiniteType_relativeDiagonal_of_isAlgebraicStack B S hS f).2
  refine ⟨fun h => ⟨fun U y hy F hF he => (h U y hy F hF he).2.2,
    (htfae.out 1 4).mp fun U y hy F hF he => (h U y hy F hF he).1⟩, fun h => ?_⟩
  have hsep := (htfae.out 1 4).mpr h.2
  intro U y hy F hF he
  refine ⟨hsep U y hy F hF he, ⟨hlft U y hy F hF he, ?_⟩, h.1 U y hy F hF he⟩
  exact Space.isQuasiCompact_of_universallyClosed B S hS
    ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩).property
    (isAlgebraicSpace_yoneda B S hS (Over.mk U.hom)) _ (h.1 U y hy F hF he)

end AlgebraicGeometry.Stack

end
