module

public import StacksFrontier.AlgebraicGeometry.RelativeVeryAmpleTwist.DegreeOne
public import StacksFrontier.AlgebraicGeometry.ProjTwistPowers.Clause

/-!
# Stacks Tag 01VN: a relatively very ample invertible module is relatively ample

Let `f : X ⟶ S` be a morphism of schemes and `L` an invertible `𝒪_X`-module. If `f` is
quasi-compact and `L` is very ample relative to `f` — [Stacks, Tag 01VM]: there are a
quasi-coherent `𝒪_S`-module `E` and an immersion `i : X ⟶ 𝐏(E) = Proj_S(Sym(E))` over `S` with
`L ≅ i^* 𝒪_{𝐏(E)}(1)` — then `L` is ample relative to `f` in the sense of [Stacks, Tag 01VH]:
`L` restricts to an ample invertible module on `f⁻¹(V)` for every affine open `V ⊆ S`.

## Main results

* `Stacks.RelativeAmple.isRelativelyAmple_of_isRelativelyVeryAmple`: **Stacks Tag 01VN.**

## Proof

The theorem combines two results:

* `Stacks.Tag01VMVeryAmple.isRelativelyAmple_of_isRelativelyVeryAmple`, which takes
  [Stacks, Tag 01VM] at the named twist `𝒪_{𝐏(E)}(1)` to relative ampleness, through
  `Stacks.RelativeAmpleBasisRoute.isRelativelyAmple_of_hasRelativeBasisImmersion`, assuming
  `Stacks.Tag01VNChartBasis.ProjOneBasisClause`: clause (3) of [Stacks, Tag 01Q3] for `𝒪(1)` on
  the `Proj` of a graded ring generated in degree one over its degree-zero part; and
* `Stacks.AlgebraicGeometry.ProjTwistPowers.projOneBasisClause`, which proves that clause.

The two definitions it is stated between are the ones the neighbouring tags use:
`Stacks.RelativeAmple.IsRelativelyAmple` is the notion of Tag 01VH and the conclusion of both
halves of Tag 01VJ, and `Stacks.Tag01VMVeryAmple.IsRelativelyVeryAmple` is the notion of Tag 01VM,
naming `𝒪_{𝐏(E)}(1)` rather than quantifying over a characterisation of it.

## Implementation notes

Invertibility of `L` is an instance binder rather than a conjunct of the hypothesis, as it is in
both of the definitions involved and as the source's preamble has it ("let `L` be an invertible
`𝒪_X`-module").

## References

* [Stacks Project, Tag 01VN](https://stacks.math.columbia.edu/tag/01VN)
* [Stacks Project, Tag 01VM](https://stacks.math.columbia.edu/tag/01VM)
* [Stacks Project, Tag 01VH](https://stacks.math.columbia.edu/tag/01VH)
* [Stacks Project, Tag 01Q3](https://stacks.math.columbia.edu/tag/01Q3)
* [EGA II, Proposition 4.6.2]
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace Stacks.RelativeAmple

/-- **Stacks Tag 01VN** (EGA II, Proposition 4.6.2). Let `f : X ⟶ S` be a morphism of schemes and
`L` an invertible `𝒪_X`-module. If `f` is quasi-compact and `L` is very ample relative to `f`,
then `L` is ample relative to `f`.

Relative very ampleness is [Stacks, Tag 01VM] at the named twist of the projective bundle:
an immersion `i : X ⟶ 𝐏(E)` over `S` into the projective bundle of a quasi-coherent
`𝒪_S`-module `E`, with `L ≅ i^* 𝒪_{𝐏(E)}(1)`. Relative ampleness is [Stacks, Tag 01VH]:
quasi-compactness of `f` together with ampleness of `L|_{f⁻¹V}` for every affine open `V ⊆ S`. -/
@[stacks 01VN]
theorem isRelativelyAmple_of_isRelativelyVeryAmple {X S : Scheme.{u}} (f : X ⟶ S)
    (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L] (hf : QuasiCompact f)
    (hL : Stacks.Tag01VMVeryAmple.IsRelativelyVeryAmple f L) :
    IsRelativelyAmple f L :=
  Stacks.Tag01VMVeryAmple.isRelativelyAmple_of_isRelativelyVeryAmple
    Stacks.AlgebraicGeometry.ProjTwistPowers.projOneBasisClause.{u, u} f L hf hL

end Stacks.RelativeAmple

end
