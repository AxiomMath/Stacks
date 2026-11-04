module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FinitePushforwardStalk.ComparisonMap
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FinitePushforwardStalk.Injectivity
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FinitePushforwardStalk.Bijectivity
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FinitePushforwardStalk.DirectSum

/-!
# Stalks of direct images along a finite morphism

Let `f : X ⟶ Y` be a morphism in a big étale site, let `y` be a geometric point of `Y` and let
`F` be a sheaf of sets on the small étale site of `X`. For every lift `x` of `y` through `f`
there is a canonical map from the stalk of the direct image `f_* F` at `y` to the stalk of `F`
at `x`: the stalk at `x` of the inverse image of `f_* F` is the stalk of `f_* F` at `y`
(Tag 03Q1), and the counit of the adjunction `f^* ⊣ f_*` maps `f^* f_* F` to `F`. Assembling
these over all lifts gives the comparison map

  `(f_* F)_y ⟶ ∏_{x ↦ y} F_x`

whose bijectivity for a *finite* morphism `f` is Tag 03QP. This file constructs that comparison
map, computes it on germs, proves it natural in the sheaf, proves that for finite `f` the
indexing set of lifts is finite, and proves the bijectivity.

## Main definitions

* `AlgebraicGeometry.geometricPointLift` — a lift of a geometric point through a morphism,
  regarded as a geometric point of the source.
* `AlgebraicGeometry.pushforwardEtaleStalkComponent` — the canonical map from the stalk of a
  direct image at `y` to the stalk at a geometric point `x` of the source lying over `y`.
* `AlgebraicGeometry.liftedEtaleNeighborhood` — the base change of an étale neighborhood of `y`,
  pointed by the lift, as an étale neighborhood of `x`.
* `AlgebraicGeometry.finitePushforwardStalkComponent` — the same canonical map, indexed by a
  lift of `y` rather than by a geometric point of the source.
* `AlgebraicGeometry.finitePushforwardStalkToProduct` — the comparison map into the product of
  the stalks over all lifts.

## Main results

* `AlgebraicGeometry.finite_lifts_of_isFinite` — a finite morphism admits only finitely many
  lifts of a point of a field spectrum, hence the product above is a finite product.
* `AlgebraicGeometry.pushforwardEtaleStalkComponent_germ` — the comparison on germs: the germ
  at `y` of a section of `f_* F` over an étale neighborhood `U`, i.e. of a section of `F` over
  `U ×_Y X`, is sent to the germ at `x` of its restriction to any pointed étale neighborhood
  of `x` over `U ×_Y X`.
* `AlgebraicGeometry.finitePushforwardStalkComponent_germ` and
  `AlgebraicGeometry.finitePushforwardStalkToProduct_germ` — the same for the lift-indexed
  component and for the comparison map, with the pointed neighborhood taken to be
  `liftedEtaleNeighborhood` itself.
* `AlgebraicGeometry.pushforwardEtaleStalkComponent_natural`,
  `AlgebraicGeometry.finitePushforwardStalkToProduct_natural` — naturality in the sheaf.
* `AlgebraicGeometry.finitePushforwardStalkEquivOfBijective` and its two properties — the
  product decomposition of the stalk, *assuming* the comparison map is bijective.
* `AlgebraicGeometry.finitePushforwardStalkToProduct_bijective` — **the comparison map is
  bijective for a finite morphism**, which is part (1) of Tag 03QP for sheaves of sets.
* `AlgebraicGeometry.finitePushforwardStalkEquiv` and its two properties — the unconditional
  product decomposition of the stalk obtained from that bijectivity.
* `AlgebraicGeometry.stalkPushforwardIsoDirectSum` and its two properties — the same statement
  for abelian sheaves, where the finite product is the direct sum.

## Implementation notes

Bijectivity is proved by exhibiting, for every family `U x` of étale neighbourhoods of the
lifts, a single étale neighbourhood `V` of `y` whose base change `V ×_Y X` is partitioned by
open-and-closed pieces, one refining each `U x`: that is
`AlgebraicGeometry.EtaleNeighborhoodPartition`. Surjectivity then glues the given germs over
such a partition, and injectivity shrinks a neighbourhood of `y` until the two sections agree
on each piece.

Such a partition exists for a finite morphism because of two separate inputs. Property (A) of
Tag 04DM supplies, for one étale neighbourhood of one lift, an étale neighbourhood of `y` and an
open piece of its base change mapping into that neighbourhood. Separating the lifts from one
another instead needs the étale decomposition of a finite morphism with purely inseparable
residue field extensions, from which the geometric fibre of the base change over a small enough
neighbourhood of `y` has at most one point in each piece; disjointness of the pieces is then the
injectivity of the assignment of a piece to a lift.

**Cofinality of `liftedEtaleNeighborhood` is *not* what makes the argument work: that statement
is false, finiteness notwithstanding.** A morphism `liftedEtaleNeighborhood B f y x U ⟶ V` in
the neighbourhood category of `x` is a morphism `U ×_Y X ⟶ V` *over `X`* carrying the chosen
point of the former to that of the latter, so cofinality would ask the *whole* base change to
map into an arbitrarily small neighbourhood of one lift. Take `k` algebraically closed,
`Y = Spec k`, `X = Spec (k × k)` with `f` its structure morphism — finite and étale — and `y`
the geometric point `Spec k ⟶ Y` with residue field `k`. There are two lifts; let `V ↪ X` be the
open immersion of the component containing `x`, an étale neighbourhood of `x`. For any
neighbourhood `U` of `y` the base change `U ×_Y X` is `U ⊔ U`, and a morphism to `V` over `X`
would factor the structure morphism of `U ⊔ U` through `V ↪ X`, forcing the second copy into the
first component. No `U` admits one, so no cofinal subfamily of this shape exists. It is the
*pieces* of a partition of the base change, not the base change itself, that map into a
prescribed neighbourhood of a single lift.

The abelian statement is not independent work: the forgetful functor to sets commutes with the
étale stalk, which is a filtered colimit, so the bijectivity above transports to it; and the
index set of lifts being finite, the coproduct of abelian groups over it is also their product,
which is what turns the product decomposition into a direct-sum decomposition.

The finiteness of the set of lifts is proved directly from the fibre product, rather than read
off a decomposition of the base change: the base change of a finite morphism along a point of
the spectrum of a field is a finite morphism to an affine scheme, hence the fibre product is
the spectrum of a module-finite algebra, and lifts correspond injectively to algebra maps of
that algebra into the field.

## File layout

* `FinitePushforwardStalk.ComparisonMap` — finiteness of the lifts, and the comparison map with its
  germs and naturality.
* `FinitePushforwardStalk.Injectivity` — injectivity of the components of the comparison map.
* `FinitePushforwardStalk.Bijectivity` — neighbourhood partitions, surjectivity, and bijectivity.
* `FinitePushforwardStalk.DirectSum` — the direct-sum decomposition for abelian sheaves.

## References

* [Stacks Project, Tag 03QP](https://stacks.math.columbia.edu/tag/03QP)
* [Stacks Project, Tag 03Q1](https://stacks.math.columbia.edu/tag/03Q1)
* [Stacks Project, Tag 040R](https://stacks.math.columbia.edu/tag/040R)
* [Stacks Project, Tag 04DM](https://stacks.math.columbia.edu/tag/04DM)
-/
