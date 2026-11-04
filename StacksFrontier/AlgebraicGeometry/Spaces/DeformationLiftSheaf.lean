module

public import StacksFrontier.AlgebraicGeometry.Spaces.DeformationLiftSheaf.LiftSubfunctor
public import StacksFrontier.AlgebraicGeometry.Spaces.DeformationLiftSheaf.ConormalRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.DeformationLiftSheaf.ConormalLiftSheaf

/-!
# The sheaf of infinitesimal lifts of a morphism of algebraic spaces

Let `X ⊂ X'` and `Y ⊂ Y'` be thickenings of algebraic spaces over a base algebraic space `T`,
let `a : X ⟶ Y` be a morphism and let `A : a^*𝒞_{Y/Y'} ⟶ 𝒞_{X/X'}` be a map of
`𝒪_X`-modules. For an algebraic space `U'` étale over `X'`, write `U = X ×_{X'} U'` for the
induced thickening inside `U'`. This file constructs the rule of [Stacks, Tag 061B]
```
U' ↦ {a' : U' ⟶ Y' | (1) a' is over T, (2) a'|_U = a|_U, (3) a' induces A|_U on conormals}
```
as a subfunctor of the presheaf of morphisms into `Y'` on the spaces-étale site of `X'`, and
proves that it is a sheaf of sets (Stacks 061A); likewise for the rule cut out by (1) and (2)
alone.

## Main definitions

* `AlgebraicGeometry.Space.spacesEtaleHomPresheaf`: the presheaf on the spaces-étale site of an
  algebraic space `X` whose sections over `U` are the morphisms `U ⟶ Z` into a fixed algebraic
  space `Z`.
* `AlgebraicGeometry.Space.thickeningBaseChange` and
  `AlgebraicGeometry.Space.thickeningProjection`: the thickening `U = X ×_{X'} U'` of an
  algebraic space `U'` étale over `X'`, and its cartesian projection to `U'`.
* `AlgebraicGeometry.Space.thickeningHomPresheaf`: the presheaf on the spaces-étale site of `X'`
  whose sections over `U'` are the morphisms `X ×_{X'} U' ⟶ Z`.
* `AlgebraicGeometry.Space.IsLiftOver`: conditions (1) and (2) of Stacks 061A on
  `a' : U' ⟶ Y'`.
* `AlgebraicGeometry.Space.liftSubfunctor`: the rule `U' ↦ {a' | IsLiftOver a'}`, as a
  subfunctor of `AlgebraicGeometry.Space.spacesEtaleHomPresheaf`.
* `AlgebraicGeometry.Space.IsConormalLiftAtSubspace`: condition (3) of Stacks 061A, for an
  arbitrary pair of closed subspaces `Z ⊆ X'`, `ZH ⊆ Y'`, an edge `α : Z ⟶ ZH`, a prescribed
  `A : α^*𝒞_{ZH/Y'} ⟶ 𝒞_{Z/X'}` and a morphism `a' : W ⟶ Y'` over `φ : W ⟶ X'`: the square of
  inclusions over `a'` commutes, and its canonical map of conormal modules of Stacks 04CP is the
  inverse image of `A`.
* `AlgebraicGeometry.Space.conormalLiftSubfunctor`: **the rule of Equation Stacks 061B**, at all
  three conditions, for arbitrary thickenings, `a` and `A`.

## Main results

* `AlgebraicGeometry.Space.isSheaf_spacesEtaleHomPresheaf`: morphisms into a fixed algebraic
  space form a sheaf on the spaces-étale site (Stacks 04P2 read on that site).
* `AlgebraicGeometry.Space.isSheaf_thickeningHomPresheaf`: the same for the morphisms out of
  `X ×_{X'} U'`, by continuity of base change along the inclusion of the thickening.
* `AlgebraicGeometry.Space.isSheaf_liftSubfunctor`: the rule cut out by conditions (1) and (2)
  is a sheaf.
* `AlgebraicGeometry.Space.preimageSquare_of_isLiftOver`: a lift in the sense of (1) and (2)
  makes the square of inclusions that condition (3) is about commute.
* `AlgebraicGeometry.Space.conormalMap_comp_restriction`,
  `AlgebraicGeometry.Space.preimageSquare_comp` and
  `AlgebraicGeometry.Space.IsConormalLiftAtSubspace.comp`: restriction stability of
  condition (3), from the composition law of the canonical conormal map (Stacks 04G2) and the
  coherence of the inverse-image comparisons (Stacks 03LU).
* `AlgebraicGeometry.Space.isPullback_preimageProjection`,
  `AlgebraicGeometry.Space.isEtale_preimageProjection`,
  `AlgebraicGeometry.Space.isIso_conormalMap_of_isEtale` and
  `AlgebraicGeometry.Space.isEtaleCovering_preimageProjection`: the inverse image of a closed
  subspace along an étale morphism, the invertibility of its conormal map (the flat clause of
  Stacks 04CQ), and the covering its projections form.
* `AlgebraicGeometry.Space.conormalMap_eq_of_isEtaleCovering`,
  `AlgebraicGeometry.Space.IsConormalLiftAtSubspace.of_isEtaleCovering` and
  `AlgebraicGeometry.Space.isConormalLiftAtSubspace_of_isEtaleCovering`: condition (3) is étale
  local.
* `AlgebraicGeometry.Space.isSheaf_conormalLiftSubfunctor`: **Stacks 061A.** The rule of
  Stacks 061B is a sheaf of sets on the spaces-étale site of `X'`, for arbitrary thickenings,
  `a` and `A`.
* `AlgebraicGeometry.Space.conormalLiftSubfunctor_eq_liftSubfunctor_of_isZero` and
  `AlgebraicGeometry.Space.conormalLiftSubfunctor_eq_liftSubfunctor_of_eq_top`: condition (3)
  is vacuous when `𝒞_{Y/Y'}` vanishes, in particular when `Y = Y'` (Stacks 061D).

## Implementation notes

**Condition (3).** The source's "induced map `a^*𝒞_{Y/Y'}|_U ⟶ 𝒞_{X/X'}|_U`" is the canonical map
`AlgebraicGeometry.Space.conormalMap` of Stacks 04CP at the square of inclusions over `a'`, and
"the restriction of `A` to `U`" is the inverse image of `A` along the projection `U ⟶ X`,
followed by the same canonical map at the square over the structure morphism of `U'`. The
inverse image `U = φ⁻¹(X)` is a closed subspace by Stacks 083Q, and the two sides are composed
at a common type by `AlgebraicGeometry.Space.modulePullbackCompIso`. The comparison isomorphism
of Stacks 04CO plays no part.

**How `U = X ×_{X'} U'` is read.** Conditions (1) and (2) read `U` as the value at `U'` of the
base-change functor `AlgebraicGeometry.Space.spacesBaseChange` along the inclusion `X ⟶ X'`,
which makes both conditions equalities of two natural families of morphisms. Condition (3) reads
`U` as the preimage subfunctor, the reading in which `U` is a closed subspace of `U'` and so has
a conormal module. The two readings are reconciled by
`AlgebraicGeometry.Space.preimageSquare_of_isLiftOver`.

**The first-order hypothesis is not carried.** Stacks 061A assumes `X ⊂ X'` and `Y ⊂ Y'` are
first order thickenings, but neither its statement of the rule nor its proof uses the order:
the rule is defined for any thickening, and conormal modules exist for any closed subspace.
Omitting the hypothesis strengthens the statements.

**The base.** The base of Stacks 061A is an algebraic space, while the letter `B` denotes the
ambient big fppf site. The site is therefore written `C` here and the base algebraic space `T`;
"over `T`" is the datum of two structure morphisms together with a commutativity equation.

**Universes.** The objects and the morphisms of the spaces-étale site of an algebraic space over
a `BigFppfSite.{u}` live in `Type (u + 1)`, so the presheaf of morphisms is `Type (u + 1)`
valued, as are the other set-valued sheaves on this site in this development.

## References

* [Stacks Project, Tag 061A](https://stacks.math.columbia.edu/tag/061A)
* [Stacks Project, Tag 061D](https://stacks.math.columbia.edu/tag/061D)
* [Stacks Project, Tag 04P2](https://stacks.math.columbia.edu/tag/04P2)
* [Stacks Project, Tag 04CP](https://stacks.math.columbia.edu/tag/04CP)
* [Stacks Project, Tag 04G2](https://stacks.math.columbia.edu/tag/04G2)
* [Stacks Project, Tag 083Q](https://stacks.math.columbia.edu/tag/083Q)
* [Stacks Project, Tag 05ZK](https://stacks.math.columbia.edu/tag/05ZK)
* [Stacks Project, Tag 03G0](https://stacks.math.columbia.edu/tag/03G0)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
-/
