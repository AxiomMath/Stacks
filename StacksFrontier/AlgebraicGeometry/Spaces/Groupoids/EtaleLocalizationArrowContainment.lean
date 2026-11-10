module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.EtaleLocalizationArrowContainment.SectionContainment
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.EtaleLocalizationArrowContainment.FibrePair
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.EtaleLocalizationArrowContainment.StrongSplitting

/-!
# The arrow containment of Stacks 03FM

Let `(U, R, s, t, c)` be a groupoid scheme over `S` in the strong splitting situation of
Stacks 04RL at a point `u ∈ U`, let `(U', Z_univ, s', t', c')` be the finite part of its
realization (Stacks 04RU) with its étale projection `g : U' ⟶ U`, and write `R' = R|_{U'}`.
The point `u'` of `U'` is the pair `(u, Z_u)`, where `Z_u ⊂ F_u = R ×_{s, U} Spec κ(u)` is the
open and closed piece supplied by the étale localization of Situation 04RL, whose support is
the set of arrows from `u` to `u`.

`StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/EtaleLocalizationStrongSplitting.lean` exhibits
`Z_univ` as an *open finite subgroupoid* of `R'` — conditions (a) and (b) of Stacks 04RK — and
`StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/EtaleLocalizationSplittingExistence.lean`
produces `U'`, `g` and `u'`.  **This file supplies the one step those two leave open**: the
containment `{r' ∈ |R'| : s'(r') = u', t'(r') = u'} ⊆ |Z_univ|`, which is the `contains_arrows`
field of `AlgebraicGeometry.GroupoidInAlgebraicSpaces.StrongSplitting`, and with it the
conclusion of Stacks 03FM.

The two ingredients the containment needs, neither of which the finite-part development has,
are supplied here.  The first is a *membership criterion* for `Z_univ` on sections: the library
describes `Z_univ` only by the universal property of Stacks 04PE (2), so
`AlgebraicGeometry.Space.FinitePartUniversalOpen.exists_lift_universalOpen_iff` turns that
property into the statement that a section of the ambient fibre product `U' ×_{g, U, s} R`
whose `U'`-component is a section `x` of `U'` factors through `Z_univ` exactly when the pair of
the identity and its `R`-component factors through the open subspace `Z_x` which `x` names.
The second is the *restriction of the point* `u'` along a morphism `Spec k ⟶ Spec κ(u)`:
`AlgebraicGeometry.Space.objectsPair_restrict_fibrePoint_isBaseChange` identifies the pair named
at the restricted point with the base change `Z_u ×_{Spec κ(u)} Spec k`.

Composing the two reduces membership in `Z_univ` over a restriction of `u'` to a condition on
the arrow alone — `AlgebraicGeometry.Space.exists_lift_universalOpen_fibrePoint_iff`: the target
of the arrow carries every point of the test scheme to `u`.  That is
`AlgebraicGeometry.Space.exists_lift_fibrePair_iff`, the geometric content of the choice of
`Z_u`, proved by descending through Yoneda to the site and then to schemes, where membership in
an open subscheme is a condition on the set-theoretic image.

With that criterion the Stacks proof goes through.  Given a field-valued point `z'` of `R'`
whose source and target are both `u'`, a common field-valued extension makes the source lift and
the target lift of `z'` restrictions of `u'` — along two possibly *different* morphisms to
`Spec κ(u)`, which is why the containment is stated for a pair of sections of `U'` rather than
one.  Over that extension the criterion produces the section of `Z_univ` of the Stacks proof,
the triple `(s ∘ z, Z_u ×_{Spec κ(u), s ∘ z} Spec k, z)`; and its image under `t'` is again `u'`
because the pair at the target is the twist of the pair at the source by the arrow, while
composing with the arrow does not change the target of an arrow.

## Main definitions

* `AlgebraicGeometry.Space.FinitePartUniversalOpen.objectsPair`: the pair `(g ∘ x, Z_x)` of
  Stacks 04PC which a section `x` of `U'` names.
* `AlgebraicGeometry.Space.FinitePartUniversalOpen.targetPairAt`: the pair which `t'` names at
  a section of `Z_univ`, i.e. the twist of the pair at its source by its arrow.
* `AlgebraicGeometry.Space.FinitePartUniversalOpen.CutsOut`: a predicate on arrows cuts out the
  open subspace which a section of `U'` names.
* `AlgebraicGeometry.Space.ArrowToPoint`: the predicate `Z_u` cuts out — the target of the arrow
  carries every point of the test scheme to `u`.
* `AlgebraicGeometry.Space.fibreValuedPoint`: **the point `u'` of `|U'|`**, and
  `AlgebraicGeometry.Space.residueValuedPoint` the point `u` of `|U|`.
* `AlgebraicGeometry.Space.restrictedStrongSplitting`: **`Z_univ` as a strong splitting of
  `R|_{U'}` at `u'`**, which is condition (1) of Stacks 04RK.

## Main results

* `AlgebraicGeometry.Space.FinitePartUniversalOpen.exists_lift_universalOpen_iff`: **the
  membership criterion for `Z_univ` on sections**, from the universal property of
  Stacks 04PE (2).
* `AlgebraicGeometry.Space.objectsPair_restrict_fibrePoint_isBaseChange`: **the restriction of
  the point `u'` along `Spec k ⟶ Spec κ(u)`**, identified with `Z_u ×_{Spec κ(u)} Spec k`.
* `AlgebraicGeometry.Space.exists_lift_fibrePair_iff`: **membership in `Z_u` is the condition
  that the target of the arrow be `u`** — the geometric content of Situation 04RL's choice
  of `Z_u`.
* `AlgebraicGeometry.Space.exists_lift_universalOpen_fibrePoint_iff`,
  `AlgebraicGeometry.Space.cutsOut_fibrePoint`,
  `AlgebraicGeometry.Space.targetInvariant_arrowToPoint` and
  `AlgebraicGeometry.Space.arrowToPoint_of_target`: the two previous results combined, in the
  form the containment consumes.
* `AlgebraicGeometry.Space.FinitePartUniversalOpen.target_eq_of_cutsOut`: **the target of the
  lift is the prescribed target section**, by the twist description of `t'`.
* `AlgebraicGeometry.Space.FinitePartUniversalOpen.exists_toRestriction_eq`: **the arrow
  containment on sections**.
* `AlgebraicGeometry.Space.contains_arrows_fibreValuedPoint`: **the arrow containment**, the
  `contains_arrows` field of `AlgebraicGeometry.GroupoidInAlgebraicSpaces.StrongSplitting`.
* `AlgebraicGeometry.Space.isStronglySplitAt_fibreValuedPoint` and
  `AlgebraicGeometry.Space.pointsMap_fibreValuedPoint`: `R|_{U'}` is strongly split at `u'`,
  and `u'` lies over `u`.
* `AlgebraicGeometry.Space.exists_stronglySplit_of_strongSplittingSituation`: **Stacks 03FM**.

## Implementation notes

### Carried hypotheses

The generic half of the file (everything in `AlgebraicGeometry.Space.FinitePartUniversalOpen`
and the four lemmas about subfunctors, open immersions and the site preceding it) carries no
hypothesis beyond the fields of `AlgebraicGeometry.Space.FinitePartUniversalOpen`; of those it
uses `universalOpen`, `universalOpen_base`, `universalOpen_spec` and `objectsEquiv` through
`objectsInclusion_spec`, and the composition, unit and inverse of the finite part through the
twist lemmas of
`StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/More/FinitePart/GroupoidAssembly.lean`.
`objectProjection_etale`, `universalOpen_containsUnit` and `universalOpen_closed` are not
used there.

The fibre half carries exactly the hypotheses of the `Fibre` section of
`StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/EtaleLocalizationSplittingExistence.lean`: a
groupoid scheme `G` over `S` whose source and target are separated and locally of finite type
(through `AlgebraicGeometry.Space.realizationFinitePart`), a point `u` of the object scheme,
the four hypotheses `hS`, `hU`, `hR`, `hP` that the big fppf site contains the base scheme, the
object scheme, the arrow scheme and the scheme of composable pairs — the four that
`Stacks.Groupoids.GroupoidScheme.realization` needs in order to exist — the hypothesis `hK`
that it contains `Spec κ(u)`, an open `W` of the scheme-theoretic fibre `F_u`, the hypothesis
`hW` that the points of `W` are exactly the arrows whose target is `u`, and the hypothesis
`hWfin` that `W` is finite over `κ(u)`.  `hW` is the only hypothesis the geometric content uses
and it is used exactly once, in
`AlgebraicGeometry.Space.exists_lift_fibrePair_iff`; `hWfin` is used only to build the pair
`(u, Z_u)`, through `AlgebraicGeometry.Space.fibreFiniteOpenSubspace`.

The final statement carries only `hS`, `hU`, `hR`, `hP`, `hK` together with the fields of
`AlgebraicGeometry.Space.StrongSplittingSituation`, all of which are consumed: the
separatedness and local finite type of the source and target through
`AlgebraicGeometry.Space.realizationFinitePart`, and the finiteness of the set of arrows from
`u` to itself together with the quasi-finiteness of `s` along it through
`AlgebraicGeometry.Space.StrongSplittingSituation.exists_fiberOpens_stabilizer`, which supplies
`W`, `hW` and `hWfin`.

### Why the containment is stated for two sections of `U'`

Equality of points of `|U'|` is equality up to a common field-valued extension, so the
hypotheses `s'(r') = u'` and `t'(r') = u'` give, after amalgamating two extensions, a single
field `Ω` on which the source lift and the target lift of the representative are restrictions
of `u'`.  They are restrictions along two morphisms `Spec Ω ⟶ Spec κ(u)` which need not agree —
a point of `|U'|` over `u` determines a pair only up to the choice of an embedding of `κ(u)`.
`AlgebraicGeometry.Space.FinitePartUniversalOpen.exists_toRestriction_eq` and
`AlgebraicGeometry.Space.FinitePartUniversalOpen.target_eq_of_cutsOut` are therefore stated for
a pair `m₁`, `m₂` of sections of `U'` sharing one cutting predicate, rather than for a single
section; this is also what makes the twist computation work, since the predicate is invariant
under composing an arrow with another arrow on the right.

### Restated private declarations

`pair_eq_of_subspace_eq` is `private` in
`StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/More/FinitePart/GroupoidAssembly.lean`, so it is
restated here with its statement unchanged and its proof transcribed, the name distinguished by a
prime: `AlgebraicGeometry.Space.FinitePartUniversalOpen.pair_eq_of_subspace_eq'`.  The private
`IsPairBaseChange`, `isPairBaseChange_objectsInclusion`, `isPairBaseChange_targetClassify`,
`isPairBaseChange_subspace`, `ambientBaseMap`, `eq_pullback_lift` and
`pair_eq_of_isPairBaseChange` of that file are **not** restated: the base-change data is used
here in the unbundled form that `finiteOpenSubspaceEquiv` returns
(`AlgebraicGeometry.Space.FinitePartUniversalOpen.objectsPair_isBaseChange` and
`targetPairAt_isBaseChange`), the comparison of ambient fibre products is avoided in favour of
`AlgebraicGeometry.Space.FinitePartUniversalOpen.exists_lift_of_pairSquares`, and the
comparison of pairs is done with
`AlgebraicGeometry.Space.FinitePartUniversalOpen.pair_eq_of_exists_lift_iff`, which tests the
open subspaces on morphisms out of representable presheaves.

### What is not reached

*Stacks 0DTC*, the splitting case, is untouched: its open `Z_u` is supported on the fibre of
the stabilizer, so the predicate of `AlgebraicGeometry.Space.ArrowToPoint` does not cut it out
and the obstruction recorded in the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/EtaleLocalizationSplittingExistence.lean` —
identifying the unit of the finite part with the Yoneda image of `e : U ⟶ R` — remains.  No
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.Splitting` or
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.QuasiSplitting` is produced.

*No attribute is attached*, here or elsewhere.

### Shape of the proofs

Rewriting with `CategoryTheory.Category.assoc` is unreliable in the presheaf categories used
here, as the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/EtaleLocalizationStrongSplitting.lean` already
record; every reassociation in this file is therefore done in term mode with `Category.assoc`
applied to explicit arguments and `congrArg`.  For the same reason the two sections of a fibre
product that a diagram chase compares are not rewritten into each other but related by
`AlgebraicGeometry.Space.pullback_lift_congr`, and equalities of
existential statements are transported with `iff_of_eq (congrArg ...)` rather than by `rw`.
The sections `φ₀`, `ψ₀` of the ambient fibre product in
`AlgebraicGeometry.Space.FinitePartUniversalOpen.target_eq_of_cutsOut` are universally
quantified variables of an inner `have` rather than `set` abbreviations, because a local
definition is unfolded by `rw` at exactly the wrong moment.

## References

* [Stacks Project, Tag 03FM](https://stacks.math.columbia.edu/tag/03FM)
* [Stacks Project, Tag 04PC](https://stacks.math.columbia.edu/tag/04PC)
* [Stacks Project, Tag 04PE](https://stacks.math.columbia.edu/tag/04PE)
* [Stacks Project, Tag 04RK](https://stacks.math.columbia.edu/tag/04RK)
* [Stacks Project, Tag 04RL](https://stacks.math.columbia.edu/tag/04RL)
* [Stacks Project, Tag 04RR](https://stacks.math.columbia.edu/tag/04RR)
* [Stacks Project, Tag 04RT](https://stacks.math.columbia.edu/tag/04RT)
* [Stacks Project, Tag 04RU](https://stacks.math.columbia.edu/tag/04RU)
* [Stacks Project, Tag 0DTC](https://stacks.math.columbia.edu/tag/0DTC)
-/
