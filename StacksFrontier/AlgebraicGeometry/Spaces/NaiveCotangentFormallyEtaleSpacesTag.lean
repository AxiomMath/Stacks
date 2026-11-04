module

public import StacksFrontier.AlgebraicGeometry.Scheme.NaiveCotangentFormallyEtale
import StacksCore.Tactic.StacksAttribute

/-!
# The spaces-chapter printing of formal étaleness on the naive cotangent complex

[Stacks, Tag 0D11] (More on Morphisms of Spaces, Lemma 76.21.7) is printed in the
algebraic-spaces chapter, but what it states is, word for word, [Stacks, Tag 0D0M] (More on
Morphisms, Lemma 37.13.6): *let `f : X → Y` be a morphism of schemes; then the following are
equivalent, (1) `f` is formally étale, (2) `H^{-1}(NL_{X/Y}) = H^0(NL_{X/Y}) = 0`.* The two
statements agree character for character in the upstream tex — the same morphism of schemes, the
same two conditions, the same two degrees — so the tag is registered here on the declaration
that already proves 0D0M rather than restated.

## Main results

* `Stacks.Smooth.formallyEtale_iff_isZero_homology_naiveCotangentComplex` carries
  **[Stacks, Tag 0D11]** in addition to [Stacks, Tag 0D0M]: a morphism of schemes `f : X ⟶ S`
  is `AlgebraicGeometry.FormallyEtale` if and only if both cohomology sheaves of
  `AlgebraicGeometry.Scheme.naiveCotangentComplex f` vanish, in degree `-1` and in degree `0`.

## Implementation notes

The printed hypothesis of 0D11 is "a morphism of schemes", and it is a slip for "a morphism of
algebraic spaces over `S`": the lemma's own proof cites the spaces-level 76.21.6 =
[Stacks, Tag 0D10] and the spaces-level 76.14.6 = [Stacks, Tag 04G9], both of which open "Let
`S` be a scheme. Let `f : X → Y` be a morphism of algebraic spaces over `S`", and both of which
would be the wrong citations for a morphism of schemes — the schemes chapter proves those two
statements as 37.13.5 and 37.6.7, which is what 0D0M cites in their place. The base scheme `S`
that every genuinely spaces-level lemma of the surrounding section carries is also absent from
0D11's printing. The spaces-level reading is therefore a *different* statement from what 0D11
prints, and this file does not claim it: it claims exactly the text of the tag, which is the
scheme statement, and that is the theorem the registered declaration proves.

Three things would be wanted before the spaces-level reading could be stated and proved, and
none of them is in this library yet:

* the spaces-level [Stacks, Tag 0D10], formal smoothness of a morphism of algebraic spaces read
  off `H^{-1}(NL_{X/Y}) = 0` together with local projectivity of `H^0(NL_{X/Y}) = Ω_{X/Y}`.
  Only the schemes-level [Stacks, Tag 0D0L] is available, as
  `Stacks.Smooth.formallySmooth_iff_isZero_homology_negOne_and_isLocallyProjective_homology_zero`;
* the degree-zero clause of the spaces-level [Stacks, Tag 0D0Y], identifying
  `H^0(NL_{X/Y})` with `AlgebraicGeometry.Space.sheafOfDifferentials f`. Without it the
  vanishing of `H^0` cannot be traded for the `Ω_{X/Y} = 0` that
  `AlgebraicGeometry.Space.formallyUnramified_iff_isZero_sheafOfDifferentials`
  ([Stacks, Tag 04G9]) consumes;
* a cohomology-sheaf API for `AlgebraicGeometry.Space.naiveCotangentComplex`
  ([Stacks, Tag 0D0V]), whose universe shape differs from that of
  `AlgebraicGeometry.Space.Modules` in which `sheafOfDifferentials` lands.

The two inputs that the spaces-level reading shares with the scheme statement are already
proved at the level of algebraic spaces:
`AlgebraicGeometry.Space.formallyEtale_iff_formallySmooth_and_formallyUnramified`
([Stacks, Tag 04G4]) splits formal étaleness into formal smoothness and formal unramifiedness,
and `AlgebraicGeometry.Space.formallyUnramified_iff_isZero_sheafOfDifferentials`
([Stacks, Tag 04G9]) reads formal unramifiedness off `Ω_{X/Y}`.

## References

* [Stacks Project, Tag 0D11](https://stacks.math.columbia.edu/tag/0D11), Lemma 76.21.7.
* [Stacks Project, Tag 0D0M](https://stacks.math.columbia.edu/tag/0D0M), Lemma 37.13.6, the
  same statement in the chapter on morphisms of schemes.
* [Stacks Project, Tag 0D10](https://stacks.math.columbia.edu/tag/0D10), Lemma 76.21.6, the
  formal-smoothness criterion that the printed proof of 0D11 cites.
* [Stacks Project, Tag 04G9](https://stacks.math.columbia.edu/tag/04G9), Lemma 76.14.6, the
  formal-unramifiedness criterion that the printed proof of 0D11 cites.
-/

add_to_stacks 0D11 "the tag prints the statement of 0D0M verbatim, for a morphism of schemes;
registered on the declaration proving 0D0M rather than restated"
  Stacks.Smooth.formallyEtale_iff_isZero_homology_naiveCotangentComplex
