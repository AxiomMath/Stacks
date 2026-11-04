module

public import StacksFrontier.AlgebraicGeometry.Scheme.NaiveCotangentSmoothCriterion
import StacksCore.Tactic.StacksAttribute

/-!
# The spaces-chapter printing of the smoothness criterion on the naive cotangent complex

[Stacks, Tag 0D12] (More on Morphisms of Spaces, Lemma 76.21.8) is printed in the
algebraic-spaces chapter, but what it states is, word for word, [Stacks, Tag 0D0N] (More on
Morphisms, Lemma 37.13.7): *let `f : X → Y` be a morphism of schemes; then `f` is smooth if and
only if it is locally of finite presentation, `H⁻¹(NL_{X/Y}) = 0`, and
`H⁰(NL_{X/Y}) = Ω_{X/Y}` is finite locally free.* The two statements agree character for
character in the upstream tex, so the tag is registered here on the declaration that already
proves 0D0N rather than restated.

## Main results

* `Stacks.Smooth.smooth_iff_isZero_homology_negOne_and_isFiniteLocallyFree` carries
  **[Stacks, Tag 0D12]** in addition to [Stacks, Tag 0D0N].

## Implementation notes

The printed hypothesis of 0D12 is "a morphism of schemes", and it is a slip for "a morphism of
algebraic spaces over `S`": its own proof reduces to "the case of schemes, which is More on
Morphisms, Lemma 37.13.7", a reduction that would be vacuous if the statement were already
about schemes, and every genuinely spaces-level lemma of the surrounding section opens "Let `S`
be a scheme. Let `f : X → Y` be a morphism of algebraic spaces over `S`" — the base scheme that
0D12's printing lacks. The spaces-level reading is therefore a *different* statement from what
0D12 prints, and this file does not claim it: it claims exactly the text of the tag, which is
the scheme statement, and that is the theorem the registered declaration proves.

## References

* [Stacks Project, Tag 0D12](https://stacks.math.columbia.edu/tag/0D12), Lemma 76.21.8.
* [Stacks Project, Tag 0D0N](https://stacks.math.columbia.edu/tag/0D0N), Lemma 37.13.7, the
  same statement in the chapter on morphisms of schemes.
-/

add_to_stacks 0D12 "the tag prints the statement of 0D0N verbatim, for a morphism of schemes;
registered on the declaration proving 0D0N rather than restated"
  Stacks.Smooth.smooth_iff_isZero_homology_negOne_and_isFiniteLocallyFree
