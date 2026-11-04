module

public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekAffineComparison.OpenImmersion
import StacksCore.Tactic.StacksAttribute

/-!
# The upper shriek of an open immersion is restriction

Let `S` be a quasi-compact quasi-separated scheme and let `j : X ⟶ Y` be a morphism of
`AlgebraicGeometry.FTS S`, the category of schemes separated and of finite type over `S` of
[Stacks, Tag 0F42], whose underlying morphism of schemes is an open immersion.
[Stacks, Tag 0AU0] (Lemma 48.17.1) says that there is a canonical isomorphism `j^! = j^*`, where
`j^*` is restriction of complexes to the open `X`. This file states exactly that:

  `j^! ≅ j^* : D_QCoh(𝒪_Y) ⥤ D_QCoh(𝒪_X)`,

with `j^*` the exact restriction `Stacks.Duality.OpenImmersion.restrictedDerivedRestrict` and
`j^!` the functor `Stacks.Duality.upperShriek` of [Stacks, Tag 0A9Y].

## Main results

* `Stacks.Duality.upperShriekIsoRestrictOfOpenImmersion` — **[Stacks, Tag 0AU0]**: `j^! ≅ j^*`.

## Implementation notes

*The proof is the one already in the library.* The source's proof is "take `X̄ = Y`; the right
adjoint of `R(𝟙_Y)_*` is the identity, so `j^! = j^*` by definition". That computation is
`Stacks.Duality.upperShriekIsoDerivedPullbackOfOpenImmersion`, which lands in the derived pullback
`Lj^*`; it is composed here with
`Stacks.Duality.restrictedDerivedRestrictIsoQuasiCoherentDerivedPullback`, which identifies `Lj^*`
with restriction along an open immersion. Nothing is reproved.

*Which compactification.* `Stacks.Duality.upperShriek` takes the compactification as an
argument, and the statement is made at `Stacks.Duality.openCompactification`, the
compactification `X̄ = Y` of the source's proof. This is the reading of Tag 0AU0 itself: the source
proves it from [Stacks, Tag 0A9E] alone, by computing `j^!` at the compactification it chooses,
and the passage from that one compactification to any other is the comparison isomorphism of
[Stacks, Tag 0AA0] (independence of the compactification), a separate result that the source's
notation `j^!` presupposes. A statement for an arbitrary compactification of `j` is the
composite of this one with the open-immersion case of Tag 0AA0, whose proof in the source
goes through [Stacks, Tag 0A9P]; it is a statement about Tag 0AA0, not about Tag 0AU0.

*Generality.* The source works over a Noetherian base and on `D⁺_QCoh`. The construction of
`Stacks.Duality.upperShriek` uses only a quasi-compact quasi-separated base, and both functors
here are defined on the unbounded `D_QCoh`, so the isomorphism is stated there; it restricts to
the source's.

## References

* [Stacks Project, Tag 0AU0](https://stacks.math.columbia.edu/tag/0AU0)
* [Stacks Project, Tag 0A9Y](https://stacks.math.columbia.edu/tag/0A9Y)
* [Stacks Project, Tag 0AA0](https://stacks.math.columbia.edu/tag/0AA0)
* [Stacks Project, Tag 0A9E](https://stacks.math.columbia.edu/tag/0A9E)
* [Stacks Project, Tag 0F42](https://stacks.math.columbia.edu/tag/0F42)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Duality

variable {S : Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S] {X Y : AlgebraicGeometry.FTS S}
  (j : X ⟶ Y) [IsOpenImmersion j.left]

/-- **Stacks Project, Tag 0AU0 (Lemma 48.17.1).** Let `j : X ⟶ Y` be a morphism of
`AlgebraicGeometry.FTS S` whose underlying morphism of schemes is an open immersion. Then the
exceptional inverse image of `j` is restriction to `X`:

  `j^! ≅ j^* : D_QCoh(𝒪_Y) ⥤ D_QCoh(𝒪_X)`.

Here `j^!` is computed at the compactification `X̄ = Y` of `Stacks.Duality.openCompactification`,
the one the source's proof chooses. The isomorphism is the source's: the right adjoint of
`R(𝟙_Y)_*` is the identity (`Stacks.Duality.upperShriekIsoDerivedPullbackOfOpenImmersion`), and
`Lj^*` is restriction along an open immersion
(`Stacks.Duality.restrictedDerivedRestrictIsoQuasiCoherentDerivedPullback`). -/
@[stacks 0AU0 "j^! = j^* with j^* the restriction to the open X, j^! computed at the \
compactification X-bar = Y that the source's proof chooses; over a quasi-compact quasi-separated \
base and on the unbounded D_QCoh"]
def upperShriekIsoRestrictOfOpenImmersion :
    upperShriek j (openCompactification j) ≅ OpenImmersion.restrictedDerivedRestrict j.left :=
  upperShriekIsoDerivedPullbackOfOpenImmersion j ≪≫
    (restrictedDerivedRestrictIsoQuasiCoherentDerivedPullback j.left).symm

end Stacks.Duality

end
