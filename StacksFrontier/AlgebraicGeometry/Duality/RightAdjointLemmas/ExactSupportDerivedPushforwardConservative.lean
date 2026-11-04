module

public import StacksFrontier.AlgebraicGeometry.ClosedPushforward.Basic
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.ExactSupportDerived
public import StacksFrontier.RingTheory.Dualizing.DerivedHomBaseChange.Conservative

/-!
# Derived pushforward along a closed quotient morphism reflects isomorphisms

Let `i : Z ⟶ X` be a closed quotient morphism of ringed spaces. Pushforward of sheaves of
modules `i_* : Mod(O_Z) ⥤ Mod(O_X)` is exact and fully faithful ([Stacks, Tag 08KS]), so the
induced functor `Ri_* : D(O_Z) ⥤ D(O_X)` reflects isomorphisms: a morphism of `D(O_Z)` which
becomes invertible after `Ri_*` was already invertible.

This is what lets a statement in `D(O_Z)` be proved after applying `i_*`, which is the first
step of the proof of [Stacks, Tag 0B4B] — "since `i_*` is exact and fully faithful it suffices
to prove the isomorphism after applying `i_*`". Only this *reflection* step is supplied here;
the identification of the pushed-forward complex is a separate matter.

All names below live in the namespace
`RingedSpaceModuleAdjunction.ClosedQuotientMorphismOfRingedSpaces`.

## Main results

* `reflectsIsomorphisms_modulePushforward`: pushforward reflects isomorphisms, being fully
  faithful.
* `reflectsIsomorphisms_mapDerivedCategory_modulePushforward`: derived pushforward reflects
  isomorphisms.

## Implementation notes

Nothing is new: the abstract input is
`CategoryTheory.Functor.reflectsIsomorphisms_mapDerivedCategory`, which says that an exact
additive functor reflecting isomorphisms induces a functor of unbounded derived categories
reflecting isomorphisms — the derived category morphism is invertible exactly when it is so on
every cohomology object, and the functor commutes with taking cohomology. Its three hypotheses
are already available for `i_*`: additivity and preservation of finite limits for any pushforward
(`Stacks.ClosedImmersion.additive_modulePushforward`,
`Stacks.ClosedImmersion.preservesFiniteLimits_modulePushforward`), preservation of finite
colimits from the closed-embedding hypothesis ([Stacks, Tag 08KS], available on `S` as
`preservesFiniteColimits_modulePushforward`), and reflection of isomorphisms from full
faithfulness (`fullyFaithfulModulePushforward`, the [Stacks, Tag 08KS] clause).

`reflectsIsomorphisms_modulePushforward` is recorded as an instance so that the derived
statement is available to instance search as well; both are stated for the bundled closed
quotient morphism, whose fields carry the hypotheses.

## References

* [Stacks Project, Tag 08KS](https://stacks.math.columbia.edu/tag/08KS)
* [Stacks Project, Tag 0B4B](https://stacks.math.columbia.edu/tag/0B4B)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

universe u

namespace RingedSpaceModuleAdjunction.ClosedQuotientMorphismOfRingedSpaces

variable (S : ClosedQuotientMorphismOfRingedSpaces.{u})

/-- **Pushforward along a closed quotient morphism of ringed spaces reflects isomorphisms.** It
is fully faithful by the [Stacks, Tag 08KS] clause `fullyFaithfulModulePushforward`, and a fully
faithful functor reflects isomorphisms. -/
instance reflectsIsomorphisms_modulePushforward :
    (modulePushforward S.i).ReflectsIsomorphisms :=
  S.fullyFaithfulModulePushforward.reflectsIsomorphisms

/-- **Derived pushforward along a closed quotient morphism of ringed spaces reflects
isomorphisms.** A morphism of `D(O_Z)` whose image under `Ri_*` is invertible is invertible.

Pushforward is additive, exact ([Stacks, Tag 08KS]) and reflects isomorphisms, and an exact
additive functor reflecting isomorphisms induces one on unbounded derived categories that
reflects isomorphisms: invertibility in the derived category is tested on cohomology objects,
and an exact functor commutes with those. -/
instance reflectsIsomorphisms_mapDerivedCategory_modulePushforward :
    (modulePushforward S.i).mapDerivedCategory.ReflectsIsomorphisms :=
  Functor.reflectsIsomorphisms_mapDerivedCategory _

end RingedSpaceModuleAdjunction.ClosedQuotientMorphismOfRingedSpaces

end
