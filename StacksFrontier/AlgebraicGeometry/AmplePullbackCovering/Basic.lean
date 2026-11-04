module

public import StacksFrontier.AlgebraicGeometry.SectionExtension.AmpleConsumers
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Stacks Tag 0B3E: the covering set is complete, and the attribute is attached here

Stacks Tag 0B3E says that for `L` an ample invertible `𝒪_X`-module and `i : X' ⟶ X` a morphism of
schemes satisfying at least one of

1. `i` quasi-compact and an immersion,
2. `X'` quasi-compact and `i` an immersion,
3. `i` quasi-compact and a homeomorphism onto its image,
4. `X'` quasi-compact and a homeomorphism onto its image,

the pullback `i^* L` is ample on `X'`. That is the tag's **single** assertion, and it is carried by
one theorem.

**The mathematics is not proved here; it is proved elsewhere in the library.** It is
`Stacks.SectionExtension.isAmple_pullbackModule`
(`../SectionExtension/AmpleConsumers.lean:163`), which is Tag 0B3E's statement with no premise and
no hypothesis the tag lacks. This file only carries the attribute. The attribute belongs on
`Stacks.SectionExtension.isAmple_pullbackModule`, and once it is there this declaration can be
deleted.

## How the premise of the general case is discharged

`StacksFrontier/AlgebraicGeometry/AmplePullback/Basic.lean` proves the general case
(`Stacks.AmplePullback.isAmple_modulePullback`, `:273`) on one premise,
`Stacks.AmplePullback.BasicOpenIsPowNonvanishing` (`:233`) — every basic open of an affine `X_s` is
itself an `X_t` — and does not carry the attribute, because that premise is not a hypothesis of
Tag 0B3E. That premise is a theorem for
an ample `L`: `Stacks.SectionExtension.isSectionRatio_of_isAmple`
(`../SectionExtension/Ample.lean:501`) proves the surjectivity half of Stacks Tag 01PW from
ampleness alone, and `Stacks.SectionExtension.basicOpenIsPowNonvanishing_of_isSectionRatio`
(`../SectionExtension/Consumers.lean:86`) turns it into the premise. Since Tag 0B3E hypothesizes
ampleness of `L` outright, the discharge is free and the conclusion is unconditional.

So Tag 0B3E is **proved** in this library, with the four-way disjunction
collapsed by `Stacks.AmpleLocallyClosed.compactSpace_and_isEmbedding_iff`, the nonvanishing loci
pulled back by Stacks Tag 0H78, the basis transported by
`Stacks.AmpleLocallyClosed.isBasisNonvanishing_pullback`, and Stacks Tags 01PX and 01PV returning
ampleness — the one remaining input supplied by the ample case of Tag 01PW.

## Main results

* `Stacks.AmplePullbackCovering.isAmple_modulePullback_of_immersion_or_isEmbedding`: **Stacks Tag
  0B3E**, in the shape of its Stacks statement, with no premise.

## Implementation notes

The statement is that of Tag 0B3E with its vocabulary replaced by the library's. The replacements
are
`Stacks.Ample.IsAmple` for Tag 01PS's `IsAmple` — the repository's Tag 01PS, which
`Stacks.Ample.isAmple_iff_isOpen` shows equivalent to the literal shape of 01PS with the
nonvanishing locus carrying its own openness witness — `Stacks.Ample.IsInvertibleModule` for
Tag 01CS's `IsInvertible`, and `Stacks.AmpleLocallyClosed.pullbackModule i L` for
`(modulePullback i.toLRSHom.toShHom).obj L`, which is that `abbrev`'s definition on the nose.

## References

* [Stacks Project, Tag 0B3E](https://stacks.math.columbia.edu/tag/0B3E)
* [Stacks Project, Tag 01PW](https://stacks.math.columbia.edu/tag/01PW)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open Stacks.Ample

universe u

namespace Stacks.AmplePullbackCovering

/-- **Stacks Tag 0B3E.** For `L` an ample invertible `𝒪_X`-module and `i : X' ⟶ X` a
quasi-compact immersion, an immersion of a quasi-compact scheme, a quasi-compact homeomorphism
onto its image, or a homeomorphism onto its image out of a quasi-compact scheme, the pullback
`i^* L` is ample on `X'`.

The proof is `Stacks.SectionExtension.isAmple_pullbackModule`; see the module documentation for
why the attribute sits here rather than there. -/
@[stacks 0B3E, ega "II 4.6.13" "(i bis), absolute case"]
theorem isAmple_modulePullback_of_immersion_or_isEmbedding {X X' : Scheme.{u}} (i : X' ⟶ X)
    (L : X.Modules) [IsInvertibleModule X L] (hL : IsAmple X L)
    (hi : (QuasiCompact i ∧ IsImmersion i) ∨ (CompactSpace X' ∧ IsImmersion i) ∨
      (QuasiCompact i ∧ Topology.IsEmbedding i) ∨
      (CompactSpace X' ∧ Topology.IsEmbedding i)) :
    IsAmple X' (Stacks.AmpleLocallyClosed.pullbackModule i L) :=
  Stacks.SectionExtension.isAmple_pullbackModule i L hL hi

end Stacks.AmplePullbackCovering

end
