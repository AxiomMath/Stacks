module

public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import StacksFrontier.CategoryTheory.Sites.LocallyBijectiveUniverse
public import StacksFrontier.CategoryTheory.Sites.Point.UniverseChange

/-!
# Points of the small étale site in a larger universe

For a scheme `S : Scheme.{u}` the small étale site `S.Etale` is a `Type (u + 1)` with
`Category.{u}`, and Mathlib's points of that site — the fibre functors
`AlgebraicGeometry.Scheme.pointSmallEtale` attached to a morphism from the spectrum of a separably
closed field — are points relative to the universe `u`: their fibre functors land in `Type u`.
Consequently they compute stalks of sheaves of `Type u` and detect isomorphisms of such sheaves,
and nothing more.

Étale cohomology on this site is written with coefficients in `Type (max (u + 1) v)`, which is
incomparable to `Type u`. This file supplies the two facts that are needed there and that Mathlib
does not have: that local bijectivity detects `J.W` for presheaves of `Type (max (u + 1) v)`, and
that the small étale site has enough points relative to `max (u + 1) v`, with the conservative
family given explicitly as the universe lifts of a family of geometric points.

## Main results

* `AlgebraicGeometry.Scheme.wEqualsLocallyBijective_smallEtaleTopology_type`: a morphism of
  presheaves of `Type (max (u + 1) v)` on the small étale site becomes an isomorphism after
  sheafification exactly when it is locally bijective. The `_type` suffix distinguishes it from
  the `AddCommGrpCat`-coefficient instance of the same shape in
  `StacksFrontier.AlgebraicGeometry.EtaleCohomology.Sheafification.SmallEtaleLocallyBijective`,
  which is a different statement about a different coefficient category.
* `AlgebraicGeometry.Scheme.isConservative_pointSmallEtale_ulift`: the universe lifts of a family
  of points `pointSmallEtale (s i)` whose images cover `S`, indexed by a `u`-small type, form a
  conservative family of points relative to `max (u + 1) v`.
* `AlgebraicGeometry.Scheme.hasEnoughPoints_smallEtaleTopology`: the small étale site has enough
  points relative to `max (u + 1) v`.

## Implementation notes

The universe `v` is unconstrained; `max (u + 1) v` is the form the coefficient universe takes in
practice, and both results are instances of statements proved for an arbitrary site, so they say
nothing specific to the étale topology beyond the side conditions it satisfies. None of the three
is declared as an instance: their heads mention the universe `max (u + 1) v` with `v` free, and an
instance of that shape makes instance resolution fail on the universe constraint
`max (u + 1) v =?= w₀` — a hard error rather than a backtrack — for goals such as
`WEqualsLocallyBijective (Type (u + 1))` that Mathlib can already discharge. The general statement
`CategoryTheory.GrothendieckTopology.wEqualsLocallyBijective_type`, whose universe is cut out by
the essential smallness hypothesis rather than guessed, is what proves the first result here.
-/

@[expose] public section

open CategoryTheory

universe v u

namespace AlgebraicGeometry.Scheme

/-- On the small étale site of `S : Scheme.{u}`, a morphism of presheaves of
`Type (max (u + 1) v)` becomes an isomorphism after sheafification if and only if it is locally
injective and locally surjective.

Mathlib has this only for coefficient categories whose hom types lie in `Type u`, so in particular
for `Type (u + 1)` but not for `Type (max (u + 1) v)` with `v` unconstrained; it is what blocks
`ObjectProperty.IsConservativeFamilyOfPoints.mk'` at the latter universe. -/
theorem wEqualsLocallyBijective_smallEtaleTopology_type (S : Scheme.{u}) :
    S.smallEtaleTopology.WEqualsLocallyBijective (Type (max (u + 1) v)) :=
  GrothendieckTopology.wEqualsLocallyBijective_type _

/-- A family of points of the small étale site of `S`, given by morphisms `s i` from spectra of
separably closed fields whose images cover `S` and indexed by a `u`-small type, remains
conservative after its universe is raised: the lifted points, which are points relative to
`max (u + 1) v`, jointly reflect isomorphisms of sheaves of `Type (max (u + 1) v)`.

This is `AlgebraicGeometry.Scheme.isConservative_pointSmallEtale` pushed along
`CategoryTheory.GrothendieckTopology.Point.ulift`. The smallness of the index type is what
Mathlib's sieve criterion for conservativity needs; it is automatic for the families used in
practice, which are indexed by the points of `S`. -/
theorem isConservative_pointSmallEtale_ulift {ι : Type*} [Small.{u} ι] {S : Scheme.{u}}
    {Ω : ι → Type u} [∀ i, Field (Ω i)] [∀ i, IsSepClosed (Ω i)]
    (s : ∀ i, Spec (.of (Ω i)) ⟶ S) (hs : ⋃ i, Set.range (s i) = .univ) :
    (ObjectProperty.ofObj
        (fun i ↦ (pointSmallEtale (s i)).ulift.{max (u + 1) v})).IsConservativeFamilyOfPoints := by
  rw [← GrothendieckTopology.isConservativeFamily_iff_ofObj]
  exact GrothendieckTopology.IsConservativeFamily.ulift.{max (u + 1) v}
    ((GrothendieckTopology.isConservativeFamily_iff_ofObj _).2
      (isConservative_pointSmallEtale s hs))

/-- The small étale site of `S : Scheme.{u}` has enough points relative to `max (u + 1) v`: there
is a `max (u + 1) v`-small family of points relative to that universe which jointly reflects
isomorphisms of sheaves of `Type (max (u + 1) v)`.

Mathlib provides this for the universe `u` only, the fibre functors of
`AlgebraicGeometry.Scheme.pointSmallEtale` taking values in `Type u`. -/
theorem hasEnoughPoints_smallEtaleTopology (S : Scheme.{u}) :
    GrothendieckTopology.HasEnoughPoints.{max (u + 1) v} S.smallEtaleTopology :=
  GrothendieckTopology.hasEnoughPoints_ulift.{max (u + 1) v} _

end AlgebraicGeometry.Scheme
