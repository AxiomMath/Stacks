module

public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ConditionComparisons
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.VeryReasonableImpliesReasonable
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ZariskiLocallyQuasiSeparatedVeryReasonable
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteEtaleAtlasQuasiSeparated

/-!
# Every scheme is a reasonable algebraic space

The diagram of Stacks 03JX places condition `(θ)` — the algebraic space is representable, that
is, it is a scheme — at the head of the chain `(θ) ⇒ (ζ) ⇒ (ε) ⇒ (δ)`, whose last term is
reasonableness. The three arrows are proved in three separate modules of this library, none of
which imports another; this module composes them, so that the conclusion the source draws from
its diagram — a scheme is a reasonable algebraic space, with no separation hypothesis
whatsoever — is available as a single statement.

## Main results

* `AlgebraicGeometry.Space.isVeryReasonableSpace_of_isRepresentable`: **Stacks 03JX,
  `(θ) ⇒ (ε)`.** A scheme is a very reasonable algebraic space.
* `AlgebraicGeometry.Space.isReasonableSpace_of_isRepresentable`: **Stacks 03JX,
  `(θ) ⇒ (δ)`.** A scheme is a reasonable algebraic space.

## Implementation notes

The three arrows composed here are
`AlgebraicGeometry.Space.isAbsolutelyZariskiLocallyQuasiSeparated_of_isRepresentable`
(`StacksFrontier/AlgebraicGeometry/Spaces/Decent/ConditionComparisons.lean`),
`AlgebraicGeometry.Space.isVeryReasonableSpace_of_isAbsolutelyZariskiLocallyQuasiSeparated`
(`StacksFrontier/AlgebraicGeometry/Spaces/Decent/ZariskiLocallyQuasiSeparatedVeryReasonable.lean`)
and `AlgebraicGeometry.Space.isReasonableSpace_of_isVeryReasonableSpace`
(`StacksFrontier/AlgebraicGeometry/Spaces/Decent/VeryReasonableImpliesReasonable.lean`).

Condition `(ζ)` is an absolute separation condition, so it is stated for a big fppf site
containing the terminal scheme. That is not an extra hypothesis on the caller:
`AlgebraicGeometry.BigFppfSite.contains_terminal` discharges it for every big fppf site, and the
statements below therefore take no `hZ` argument.

## References

* [Stacks Project, Tag 03JX](https://stacks.math.columbia.edu/tag/03JX)
* [Stacks Project, Tag 03I8](https://stacks.math.columbia.edu/tag/03I8)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

/-- **Stacks Tag 03JX, `(θ) ⇒ (ε)`.** A representable algebraic space over `S` — a scheme — is
very reasonable: it admits a jointly surjective family of étale charts by schemes whose two
self-intersection projections are quasi-compact.

The affine opens of the representing scheme cut out a Zariski covering of `X` by quasi-separated
open subspaces, which is condition `(ζ)`, and `(ζ) ⇒ (ε)` refines such a covering to the
required family of charts. -/
theorem isVeryReasonableSpace_of_isRepresentable (hX : IsAlgebraicSpace B S hS X)
    (h : X.IsRepresentable) : IsVeryReasonableSpace B S hS X :=
  isVeryReasonableSpace_of_isAbsolutelyZariskiLocallyQuasiSeparated B S hS
    B.contains_terminal X hX
    (isAbsolutelyZariskiLocallyQuasiSeparated_of_isRepresentable B S hS X
      B.contains_terminal hX h)

/-- **Stacks Tag 03JX, `(θ) ⇒ (δ)`: every scheme is a reasonable algebraic space.** A
representable algebraic space over `S` is reasonable — every étale chart of it by an affine
scheme has universally bounded fibres — and **no separation hypothesis is needed**:
reasonableness is strictly weaker than quasi-separatedness, and the source's diagram reaches it
from representability alone, through Zariski local quasi-separatedness and very reasonableness.

This is the arrow that brings the most elementary objects of the theory — quasi-compact schemes,
including ones which are not quasi-separated — under the hypotheses of the lemmas of this
chapter that assume only quasi-compactness and reasonableness, Stacks 03K0 among them. -/
theorem isReasonableSpace_of_isRepresentable (hX : IsAlgebraicSpace B S hS X)
    (h : X.IsRepresentable) : IsReasonableSpace B S hS X :=
  isReasonableSpace_of_isVeryReasonableSpace B S hS X hX
    (isVeryReasonableSpace_of_isRepresentable B S hS X hX h)

/-- **Every object of the site is a reasonable algebraic space.** The presheaf represented by an
object of the big fppf site over `S` is an algebraic space by Stacks 02X0 and representable by
construction, so `AlgebraicGeometry.Space.isReasonableSpace_of_isRepresentable` applies to it. -/
theorem isReasonableSpace_yoneda (U : BigFppfOver B S hS) :
    IsReasonableSpace B S hS (yoneda.obj U) :=
  isReasonableSpace_of_isRepresentable B S hS _ (isAlgebraicSpace_yoneda B S hS U)
    ⟨⟨U, ⟨Functor.representableByEquiv.symm (Iso.refl _)⟩⟩⟩

end AlgebraicGeometry.Space

end
