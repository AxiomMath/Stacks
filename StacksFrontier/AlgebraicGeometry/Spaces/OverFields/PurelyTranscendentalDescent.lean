module

public import StacksFrontier.AlgebraicGeometry.Spaces.OverFields.PurelyTranscendentalDescent.AlgebraMapSections
public import StacksFrontier.AlgebraicGeometry.Spaces.OverFields.PurelyTranscendentalDescent.QuasiCompactReduction
public import StacksFrontier.AlgebraicGeometry.Spaces.OverFields.PurelyTranscendentalDescent.FinitePresentationCase
public import StacksFrontier.AlgebraicGeometry.Spaces.OverFields.PurelyTranscendentalDescent.Descent

/-!
# Schemes descend along purely transcendental field extensions

A quasi-separated algebraic space over a field `k` is a scheme as soon as it becomes a scheme
after base change along a purely transcendental extension `K/k`. Being a scheme is
`CategoryTheory.Functor.IsRepresentable` for the presheaf underlying the space, and the base
change along `K/k` is restriction along `Spec K ⟶ Spec k`, that is
`OverShriek.relocalizeRestrict` applied to the induced morphism of the site.

## Main results

* `AlgebraicGeometry.Space.isRepresentable_of_isRepresentable_purelyTranscendental_baseChange`:
  **Stacks 0B85**.

## Implementation notes

The proof follows the source. A purely transcendental extension is the fraction field of a
polynomial ring (Stacks 030E, part 3, which is `PurelyTranscendental`), hence the directed union
of its finite type `k`-subalgebras `A`, each of which is a localization of a finite polynomial
algebra. Stacks 07SR produces an `A` with `X_A` a scheme
(`AlgebraicGeometry.Space.exists_fgSubalgebra_isRepresentable_relocalizeRestrict`), and
`A = k[x_1, …, x_n][1/f]`.

Both branches of the source's case split are proved. When `k` is infinite there are
`a_1, …, a_n ∈ k` with `f(a_1, …, a_n) ≠ 0`, which define a `k`-algebra map `A → k`, hence a
section of `Spec k ⟶ Spec A` along which `X_A` base changes back to `X`. When `k` is finite
there is in general no such map, so Stacks 09NS writes `X` as a limit of spaces of finite
presentation over `k` with affine transition morphisms and Stacks 07SR lets us assume
`X → Spec k` of finite presentation; a closed point of `|X|` is then represented by a closed
immersion from the spectrum of a finite extension `κ/k` of some degree `d` (Stacks 0AHB
together with the Hilbert Nullstellensatz, Stacks 00FV), and for `n` large and prime to `d` the
degree `n` extension `k'/k` is cyclic Galois and admits a `k`-algebra map from `A`, so `X_{k'}`
is a scheme, `X = X_{k'}/G` (Stacks 0B86) and `Spec(κ ⊗_k k')` is the spectrum of a field, so
the fibre of `X_{k'} ⟶ X` over the point is a single point and Stacks 0BA1 — the input of
Stacks 0B87 — puts the point in the schematic locus.

The reduction to the quasi-compact case, which the source leaves to the reader, is proved here:
`AlgebraicGeometry.PurelyTranscendentalDescent.exists_zariski_cover_with_quasiCompact_members`
covers an algebraic space by quasi-compact open subspaces and
`AlgebraicGeometry.PurelyTranscendentalDescent.isRepresentable_of_zariskiCover` glues the
conclusion back.

In this library Stacks 07SR asks the index set of the inverse system to be smaller than the
cofinality of the size cutoff of the big fppf site. The finite field branch therefore runs on an
enlargement of the site whose cutoff has cofinality above the old cutoff
(`AlgebraicGeometry.BigFppfSite.exists_isContained_lt_cof`): there `X` is small, Stacks 09NS
provides an approximation indexed by a small set, and representability is transported back
(`AlgebraicGeometry.isRepresentable_of_isRepresentable_changeBigSite`).

## Files

The development is split into the following files:

* `PurelyTranscendentalDescent.AlgebraMapSections`
* `PurelyTranscendentalDescent.QuasiCompactReduction`
* `PurelyTranscendentalDescent.FinitePresentationCase`
* `PurelyTranscendentalDescent.Descent`

## References

* [Stacks Project, Tag 00FV](https://stacks.math.columbia.edu/tag/00FV)
* [Stacks Project, Tag 030E](https://stacks.math.columbia.edu/tag/030E)
* [Stacks Project, Tag 07SR](https://stacks.math.columbia.edu/tag/07SR)
* [Stacks Project, Tag 09NS](https://stacks.math.columbia.edu/tag/09NS)
* [Stacks Project, Tag 0AHB](https://stacks.math.columbia.edu/tag/0AHB)
* [Stacks Project, Tag 0B85](https://stacks.math.columbia.edu/tag/0B85)
* [Stacks Project, Tag 0B86](https://stacks.math.columbia.edu/tag/0B86)
* [Stacks Project, Tag 0B87](https://stacks.math.columbia.edu/tag/0B87)
-/
