module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FiniteType
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableSource
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Types

/-!
# A formal algebraic space of finite type over a locally Noetherian one

Let `S` be a scheme contained in a big fppf site `B` and let `f : X ⟶ Y` be a morphism of
formal algebraic spaces over `S`. **Stacks 0AQ7** says that `X` is locally Noetherian as soon
as `Y` is locally Noetherian and `f` is locally of finite type. **Stacks 0AQ8** is the base
changed form: a fibre product `Z ×_Y X` is locally Noetherian as soon as `Z` is locally
Noetherian and `f` is locally of finite type.

## Main results

* **Stacks 0AQ7** is not proved here: it is
  `AlgebraicGeometry.FormalSpace.isLocallyNoetherian_source_of_isLocallyOfFiniteType'` in
  `StacksFrontier.AlgebraicGeometry.FormalSpace.FiniteTypeNoetherianRefined`.
* **Stacks 0AQ8** is not proved here: its forms are
  `AlgebraicGeometry.FormalSpace.isLocallyNoetherian_of_isPullback'` in
  `StacksFrontier.AlgebraicGeometry.FormalSpace.FiniteTypeNoetherianRefined` and
  `AlgebraicGeometry.FormalSpace.isLocallyNoetherian_of_isPullback_of_isLocallyOfFiniteType` in
  `StacksFrontier.AlgebraicGeometry.FormalSpace.LocallyNoetherianSource`.

## Implementation notes

The proof is the one of the source. A locally Noetherian `Y` comes with an atlas `{Vⱼ ⟶ Y}`
as in Definition 0AIM whose members are Noetherian affine formal algebraic spaces. Each fibre
product `Wⱼ = Vⱼ ×_Y X` is a formal algebraic space by Stacks 0AJ3, in the shape
`AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_pullback_of_representable` proves it, so
it carries an atlas `{U_{ji} ⟶ Wⱼ}` by affine formal algebraic spaces. The composites
`U_{ji} ⟶ Wⱼ ⟶ X` are representable by algebraic spaces and étale, being composites of such,
and they are jointly surjective because `{Wⱼ ⟶ X}` is — the second projection of a fibre
product being a base change of `Vⱼ ⟶ Y` — and each `{U_{ji} ⟶ Wⱼ}` is. That exhibits the
atlas of `X` the conclusion asks for, and what is left is that its members are Noetherian.

Two results of other tags supply that last step, and each is an explicit hypothesis here:

* `h0ANL` is Stacks 0ANL, condition (1) implies condition (3), restricted to the squares of
  affine charts that the argument uses: a morphism locally of finite type is locally of finite
  type on every commuting square whose vertical maps are representable étale maps from affine
  formal algebraic spaces. It is stated as an implication out of `hf`, since that is the
  condition Stacks 0ANL derives it from. Applied to the square formed by `U_{ji} ⟶ X` and
  `Vⱼ ⟶ Y` it makes `U_{ji} ⟶ Vⱼ` locally of finite type.
* `h0AKP` is Stacks 0AKP, part (6): an affine formal algebraic space which is locally of
  finite type over a Noetherian one is Noetherian. The library has parts (1) and (2) of that
  tag, `AlgebraicGeometry.FormalSpace.isAffineFormalAlgebraicSpace_of_relative_isAffineHom`
  and `AlgebraicGeometry.FormalSpace.isCountablyIndexed_of_relative_isAffineHom`, but not part
  (6), whose proof runs through the adic\* case of part (5). The hypothesis is quantified over
  all affine formal algebraic spaces and mentions neither `X` nor `f`; no Noetherianness of a
  chart of `X` is assumed.

The unconditional statement,
`AlgebraicGeometry.FormalSpace.isLocallyNoetherian_source_of_isLocallyOfFiniteType'`, proves
that last step instead: Stacks 0ANL by
`AlgebraicGeometry.FormalSpace.isLocallyOfFiniteTypeOnEverySquare_of_isLocallyOfFiniteType`,
and the Noetherianness of the charts by
`AlgebraicGeometry.FormalSpace.isNoetherian_of_isRepresentable'`.

The hypotheses `hset`, `hstageset` and `h0AIU` are the hypotheses of
`AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_pullback_of_representable`, the form of
Stacks 0AJ3 used for the fibre products, and are carried here for that reason: `h0AIU` is
Stacks 0AIU, that a directed colimit of algebraic spaces along thickenings is a formal
algebraic space, and the other two are the set-theoretic condition of Stacks 0AIS for the
fibre products and for their charts, which does not follow from the corresponding conditions
on the members of a covering family.

That `X` is a formal algebraic space is the hypothesis `hX`: it is part of the source's
setting, `f` being a morphism of formal algebraic spaces, and the atlas built below does not
give the set-theoretic condition of Stacks 0AIS on `X` by itself.

Stacks 0AQ8 is deduced exactly as in the source, from Stacks 0AQ5 and Stacks 0AQ7. It needs no
hypothesis beyond those of Stacks 0AQ7 for the projection `Z ×_Y X ⟶ Z`, because that
projection is a base change of `f` and is therefore representable by algebraic spaces, so that
the fibre product is a formal algebraic space by Stacks 0AJI rather than by hypothesis; only
the set-theoretic condition of Stacks 0AIS on it is left to assume.

## References

* [Stacks Project, Tag 0AIM](https://stacks.math.columbia.edu/tag/0AIM)
* [Stacks Project, Tag 0AJ3](https://stacks.math.columbia.edu/tag/0AJ3)
* [Stacks Project, Tag 0AJI](https://stacks.math.columbia.edu/tag/0AJI)
* [Stacks Project, Tag 0AKP](https://stacks.math.columbia.edu/tag/0AKP)
* [Stacks Project, Tag 0AKY](https://stacks.math.columbia.edu/tag/0AKY)
* [Stacks Project, Tag 0ANL](https://stacks.math.columbia.edu/tag/0ANL)
* [Stacks Project, Tag 0AQ5](https://stacks.math.columbia.edu/tag/0AQ5)
* [Stacks Project, Tag 0AQ7](https://stacks.math.columbia.edu/tag/0AQ7)
* [Stacks Project, Tag 0AQ8](https://stacks.math.columbia.edu/tag/0AQ8)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

end AlgebraicGeometry.FormalSpace

end
