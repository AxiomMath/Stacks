module

public import StacksFrontier.Deformation.Artin.Obstruction.FieldCohomology.BaseChangeSquare
public import StacksFrontier.Deformation.Artin.Obstruction.FieldCohomology.LiftTransition

/-!
# The cohomology of the obstruction complex at a field-valued point

Let `𝒳` be endowed with a naive obstruction theory (Stacks 07YP), let `y ⟶ x` be a morphism
lying over a ring map `A ⟶ B` of charted objects, and let `k` be a `B`-algebra which is a
field. The functoriality map `E_x ⟶ E_y` of clause (3) of the definition induces a map
`E_x ⊗^L_A k ⟶ E_y ⊗^L_B k` of derived base changes, and Stacks 07YT asserts that this map is
an isomorphism on cohomology in degrees `0` and `1`.

The argument of the source is in two halves. Over a field, `Ext^i_A(E, k)` is the `k`-linear
dual of `H^{-i}(E ⊗^L_A k)` (Stacks 07YK), naturally in the source ring, so the two
cohomology maps are the duals of the two `Ext` pullbacks in degrees `0` and `-1`, and a map
of `k`-vector spaces whose dual is bijective is bijective. Those two `Ext` pullbacks are in
turn bijective because the naive obstruction theory identifies `Ext^{-1}_A(E_x, −)` and
`Ext^0_A(E_x, −)` with `Inf_x` and `T_x` compatibly with the transitions of Stacks 07YA, and
those transitions are bijective at field coefficients by condition (RS*), which gives
`Lift(x, A[k]) = Lift(z, k[k]) = Lift(y, B[k])` for `z = x|_{Spec k}`.

Everything but that last step is proved here, and of that step the half concerning lift classes
is proved as well. The bijectivity of the (RS*) transition on lift classes and on infinitesimal
automorphisms with coefficients in `k` is carried as an explicit hypothesis of
`Deformation.Artin.bijective_homologyFunctor_map_naiveObstructionFieldBaseChangeMap`, so that
statement is Stacks 07YT with the Rim–Schlessinger input assumed rather than derived. The
hypothesis on lift classes is then discharged in
`Deformation.Artin.bijective_homologyFunctor_map_naiveObstructionFieldBaseChangeMap_of_infAut`,
which is Stacks 07YT with only the step on infinitesimal automorphisms assumed. That step is
still assumed, so no statement here carries the tag.

The Rim–Schlessinger input itself is proved here in the form the source uses it, as
`Deformation.Artin.baseChangeLiftClassesEquiv`: for a ring map `A ⟶ A'` and a semilinear
bijection `M ⟶ N` of coefficients, `A[M] = A ×_{A'} A'[N]` is a fibre-product square with a
square-zero surjection on one side, so (RS*) identifies the lifts of `x` over `Spec A[M]`
with the lifts of `x|_{Spec A'}` over `Spec A'[N]`. The source factors
`Lift(x, A[k]) = Lift(y, B[k])` through `Lift(z, k[k])`, but one application suffices: at
`A' = B` and `N = k` the comparison of the two module structures on `k` is bijective, so the
square is already `A[k] = A ×_B B[k]`. That the resulting bijection *is* the transition of
Stacks 07YA is `Deformation.Artin.isoFiberArrow_squareLiftEquivalence_fac`, which identifies
the comparison of lifts carried by (RS*) with pullback of lifts along the other leg of the
square.

The transition on lift classes is however constructed here, and pinned down:
`Deformation.Artin.squareZeroLiftBaseChangeMap` is pullback of lifts along the induced morphism
`Spec C[N] ⟶ Spec A[M]`, it has the defining property of the transition, and by
`Deformation.Artin.eq_of_isSquareZeroLiftBaseChange` nothing else does. The hypothesis on lift
classes is therefore equivalent to bijectivity of that single map, which is the form
`Deformation.Artin.bijective_homologyFunctor_map_naiveObstructionFieldBaseChangeMap_of_bijective`
takes. The hypothesis on infinitesimal automorphisms is not reduced the same way: an
automorphism of the trivial lift of `y` conjugates one solution of the defining property into
another, so that property determines the transition on `Inf` only up to conjugacy.

The geometric half of that identification rests on a comparison of lifts across a
categorical pullback square which is independent of the deformation-theoretic setting: a
lift of an object `x` of the fibre over one corner along the arrow into the pullback corner
is the same thing as a lift of the restriction of `x` to the common corner along the other
branch. That is `Deformation.Artin.squareLiftEquivalence`, and it is where (RS*) is used.

## Main definitions

* `Deformation.Artin.fieldSiteModule` — a field receiving a ring map from `R`, viewed as a
  module of the chosen big site over `R`.
* `Deformation.Artin.fieldSiteModuleComparison` — the comparison of the two module structures
  that a ring map `A ⟶ A'` puts on a field receiving `A'`.
* `Deformation.Artin.naiveObstructionFieldBaseChangeMap` — the map
  `E_x ⊗^L_A k ⟶ E_y ⊗^L_B k` induced by the functoriality map of a naive obstruction theory.
* `Deformation.Artin.categoricalPullbackIsoFiberRestrict` — the lift of `F x` across `G`
  carried by a lift of `x` across the first projection of a categorical pullback.
* `Deformation.Artin.squareLiftEquivalence` — the lifts of `x` across the arrow into the
  pullback corner of a square whose comparison functor is an equivalence, as the lifts of the
  restriction of `x` across the other branch.
* `Deformation.Artin.squareZeroRingBaseMap` — the ring map `A[M] ⟶ A'[N]` of trivial
  square-zero extensions attached to a ring map and a semilinear map of coefficients.
* `Deformation.Artin.algebraOverMapOfRingHom` and `Deformation.Artin.squareZeroOverBaseMap` — the
  two morphisms `Spec A' ⟶ Spec A` and `Spec A'[N] ⟶ Spec A[M]` of objects of the site over
  `S`.
* `Deformation.Artin.baseChangeLiftClassesEquiv` — the Rim–Schlessinger identification
  `Lift(x, A[M]) = Lift(x|_{Spec A'}, A'[N])`.
* `Deformation.Artin.squareZeroLiftBaseChange` — the pullback of a lift of `x` over
  `Spec A[M]` along `Spec C[N] ⟶ Spec A[M]`, as a lift of `y` over `Spec C[N]`.
* `Deformation.Artin.squareZeroLiftBaseChangeMap` — the transition of Stacks 07YA on
  isomorphism classes of lifts.
* `Deformation.Artin.isoFiberCongrBase` — the lifts of an object across a functor, read at an
  isomorphic object.

## Main results

* `Deformation.Artin.bijective_of_bijective_dualPrecomp` — a `k`-linear map whose dual is
  bijective is bijective.
* `Deformation.Artin.bijective_homologyFunctor_map_derivedBaseChangeMap` — bijectivity of the
  pullback of `Ext^i` classes into a field across a change of source ring gives bijectivity of
  `H^{-i}` of the induced map of derived base changes. This is the Stacks 07YK half.
* `Deformation.Artin.bijective_extRestrictScalars_zero_of_bijective_tangentTransition` and
  `Deformation.Artin.bijective_extRestrictScalars_negOne_of_bijective_infTransition` — the
  naive obstruction theory half: bijectivity of the transitions of Stacks 07YA gives
  bijectivity of the pullback of `Ext^0`, resp. `Ext^{-1}`, along the functoriality map.
* `Deformation.Artin.bijective_homologyFunctor_map_naiveObstructionFieldBaseChangeMap` — the
  two halves combined.
* `Deformation.Artin.squareZeroRingBaseMap_isPullback` — the ring square
  `A[M] = A ×_{A'} A'[N]`, in the orientation condition (RS*) reads a square.
* `Deformation.Artin.baseChangeSquare_isEquivalence` — condition (RS*) applied to that
  square.
* `Deformation.Artin.eq_of_isSquareZeroLiftBaseChange` — the transition of Stacks 07YA on lift
  classes is single-valued.
* `Deformation.Artin.isSquareZeroLiftBaseChange_squareZeroLiftBaseChangeMap` — pullback of
  lifts along `Spec C[N] ⟶ Spec A[M]` realizes that transition.
* `Deformation.Artin.bijective_homologyFunctor_map_naiveObstructionFieldBaseChangeMap_of_bijective`
  — Stacks 07YT with the hypothesis on lift classes reduced to bijectivity of that one map.
* `Deformation.Artin.isoFiberArrow_squareLiftEquivalence_fac` — the comparison of lifts carried
  by (RS*) is pullback of lifts along the other leg of the square.
* `Deformation.Artin.bijective_squareZeroLiftBaseChangeMap` — the transition of Stacks 07YA on
  lift classes is bijective whenever the semilinear map of coefficients is. This is the
  Rim–Schlessinger step for the tangent half of Stacks 07YT.
* `Deformation.Artin.bijective_homologyFunctor_map_naiveObstructionFieldBaseChangeMap_of_infAut`
  — Stacks 07YT with only the Rim–Schlessinger step on infinitesimal automorphisms assumed.

## Implementation notes

The field coefficient is `ULift k`, read as an `A`-module by restriction of scalars, because
that is the shape in which Stacks 07YK is available: the ring and field universes there are
independent and the modules live in a common universe above both. Here all the rings of a
naive obstruction theory live in `Type u` and its modules in `ModuleCat.{u}`, so every
universe of Stacks 07YK is instantiated to `u`.

Two pullbacks of `Ext` classes over a change of rings occur, differing only in the spelling of
the coefficient module: `Deformation.Artin.extRestrictScalars` lands in
`Ext_A(E_x, Res_{A → B}(Res_{B → k} k))`, which is what the naive obstruction theory's
conditions produce, and `DerivedCategory.extIntoFieldRestriction` lands in
`Ext_A(E_x, Res_{A → k} k)`, which is what Stacks 07YK consumes.
`Deformation.Artin.extIntoFieldRestriction_eq_extPushforward` identifies the second with the
first followed by the canonical comparison of the two restrictions, and that comparison is an
isomorphism, so the two have the same bijectivity.

The hypotheses that the two copies of the field are modules of the chosen big site are needed
because the tangent and infinitesimal-automorphism functors are defined only on those modules;
they are satisfiable by taking the big site large enough, and the definition of a naive
obstruction theory already carries a hypothesis of this kind in its condition (iv).

## References

* [Stacks Project, Tag 07YT](https://stacks.math.columbia.edu/tag/07YT)
* [Stacks Project, Tag 07YP](https://stacks.math.columbia.edu/tag/07YP)
* [Stacks Project, Tag 07YK](https://stacks.math.columbia.edu/tag/07YK)
-/
