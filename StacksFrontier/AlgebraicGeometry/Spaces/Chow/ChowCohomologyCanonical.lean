module

public import Mathlib.Algebra.DirectSum.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.BivariantCanonical

/-!
# Chow cohomology over the constructed Chow groups

In the situation of Stacks 0EDT let `X/B` be good.  **Stacks 0ERK** calls the *Chow cohomology*
of `X` the graded `ℤ`-algebra

  `A^*(X) = ⊕_p A^p(X)`,  where  `A^p(X) = A^p(X ⟶ X)`,

whose degree `p` part is the group of bivariant classes of degree `p` for the identity morphism
of `X`.

## Main definitions

* `AlgebraicGeometry.Space.chowCohomologyComponentCanonical` — **Stacks 0ERK**, the degree `p`
  part `A^p(X)` of the Chow cohomology of `X`, namely `A^p(X ⟶ X)`.
* `AlgebraicGeometry.Space.chowCohomologyCanonical` — **Stacks 0ERK**, the graded group
  `A^*(X)`.

## Implementation notes

Both are abbreviations of `AlgebraicGeometry.Space.BivariantClassCanonical`, so the pointwise
abelian group structure on `A^p(X ⟶ X)` propagates to `A^*(X)` through the `DirectSum`
instances with no further declaration.  Degrees range over `ℤ` and a class has finite support.

Unlike `AlgebraicGeometry.Space.chowCohomology`, nothing here is parameterized: the Chow groups
are the constructed `AlgebraicGeometry.Space.chowGroupCanonical` of Stacks 0EQ6 and the three
operations a bivariant class commutes with are the constructed ones on cycles of Stacks 0EP1,
Stacks 0EP8 and Stacks 0ER1.  See the implementation notes of
`StacksFrontier.AlgebraicGeometry.Spaces.Chow.BivariantCanonical`.

### The multiplication is not carried

Stacks 0ERK calls `A^*(X)` a graded `ℤ`-algebra, the product being composition of bivariant
classes, `A^p(X ⟶ X) × A^q(X ⟶ X) ⟶ A^{p+q}(X ⟶ X)`.  What is defined here is the graded group,
and the `@[stacks 0ERK]` attributes say so.  The non-commutativity remark following Stacks 0ERK,
and the assertion that Chern classes lie in the centre, are therefore not stated either.

The obstruction is precise.  For the identity morphism the base change of a test space
`g : Y' ⟶ X` is `pullback (𝟙 X) g`, which is isomorphic to `Y'` through `pullback.snd (𝟙 X) g`
but is not that object, so composing `c ∩ (d ∩ -)` asks for the cap operation of `c` on
`pullback (𝟙 X) g` to be read back on `Y'`.  That transport is proper pushforward along an
isomorphism as a map of `AlgebraicGeometry.Space.chowGroupCanonical`, which is an instance of
Stacks 0EQC and is not constructed here.  Beyond the transport, the composite would have to be
shown to satisfy the three naturality axioms, which needs each of the three cycle-level
operations — Stacks 0EP1, Stacks 0EP8 and Stacks 0ER1 — to commute with pushforward along that
isomorphism.

The diagnosis is confirmed by the scheme side, where the Chow groups and the three operations
are constructed: there the composite cap operation `Stacks.Chow.bivariantCompositeCap`
(`StacksFrontier.AlgebraicGeometry.Chow.BivariantComposition.Basic`) carries exactly the hypothesis
`Stacks.Chow.ProperPushforwardDescends`, and being the composite is the predicate
`Stacks.Chow.IsBivariantClassComposition` rather than a construction, so the product of bivariant
classes is not built there either.

## References

* [Stacks Project, Tag 0ERK](https://stacks.math.columbia.edu/tag/0ERK)
* [Stacks Project, Tag 0ERJ](https://stacks.math.columbia.edu/tag/0ERJ)
* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
* [Stacks Project, Tag 0EQ6](https://stacks.math.columbia.edu/tag/0EQ6)
-/

@[expose] public noncomputable section

open CategoryTheory

universe v u

namespace AlgebraicGeometry.Space

/-- The degree `p` part `A^p(X)` of the Chow cohomology of a good algebraic space `X/B`: the
group `A^p(X ⟶ X)` of bivariant classes of degree `p` for the identity morphism of `X`, over the
constructed Chow groups of Stacks 0EQ6. -/
@[stacks 0ERK "the degree p part A^p(X) = A^p(X → X), over the constructed Chow groups of \
Stacks 0EQ6"]
abbrev chowCohomologyComponentCanonical (D : BaseSpaceDimensionSituation.{u}) {X : D.Ambient}
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (p : ℤ) :=
  BivariantClassCanonical.{v} D sX hX sX hX (𝟙 X) (Category.id_comp sX) p

/-- The Chow cohomology `A^*(X)` of a good algebraic space `X/B`: the graded group whose degree
`p` part is the group `A^p(X ⟶ X)` of bivariant classes of degree `p` for the identity morphism
of `X`, over the constructed Chow groups of Stacks 0EQ6.

This is the graded group and not the graded `ℤ`-algebra, whose product is composition of
bivariant classes. -/
@[stacks 0ERK "the graded group A^*(X) = ⊕_p A^p(X → X) over the constructed Chow groups of \
Stacks 0EQ6, not the ℤ-algebra: the product is composition of bivariant classes, which needs \
proper pushforward along an isomorphism to respect rational equivalence (Stacks 0EQC)"]
abbrev chowCohomologyCanonical (D : BaseSpaceDimensionSituation.{u}) {X : D.Ambient}
    (sX : X ⟶ D.space) (hX : D.IsGood sX) :=
  DirectSum ℤ fun p ↦ chowCohomologyComponentCanonical.{v} D sX hX p

end AlgebraicGeometry.Space

end
