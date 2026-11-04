module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullbackAssociativity
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullbackRightUnitality
public import StacksCore.Tactic.StacksAttribute

/-!
# The coherence of Tag 03EL, assembled

Let `(f, f♯) : (Sh(C), O_C) ⟶ (Sh(D), O_D)` be a morphism of ringed topoi. The comparison
`f^*(F ⊗_{O_D} G) ≅ f^*F ⊗_{O_C} f^*G` of **Tag 03EL** and the comparison `ν : f^*O_D ≅ O_C` of
the units are owed three coherences before they are a monoidal structure, and those three are
collected in `Stacks.SheafOfModules.RingedToposPullback.PullbackCoherence`. Each is proved, in
its own file:

* `Stacks.SheafOfModules.RingedToposPullback.associativity`,
* `Stacks.SheafOfModules.RingedToposPullback.leftUnitality`,
* `Stacks.SheafOfModules.RingedToposPullback.rightUnitality`.

This file is the one line that puts them together, and the monoidal structures that follow.

## Main definitions

* `Stacks.SheafOfModules.RingedToposPullback.pullbackCoherence`: the three coherences of Tag 03EL
  as one `PullbackCoherence`, **unconditional**.
* `Stacks.SheafOfModules.RingedToposPullback.pullbackMonoidal`: the pullback of sheaves of
  modules as a monoidal functor, unconditionally.
* `Stacks.SheafOfModules.RingedToposPullback.pushforwardModulesLaxMonoidal`: the pushforward of
  sheaves of modules as a lax monoidal functor, unconditionally. Registered as an instance.

## Implementation notes

`PullbackCoherence` is a `Prop`, so the assembly is a theorem and its three fields are the three
named proofs with no transport: each of them is stated character for character as the
corresponding field, at the structure's own four independent universes
(`X : RingedTopos.{v, u, w}`, `Y : RingedTopos.{v', u', w'}`).

`pushforwardModulesLaxMonoidal` is an **instance**; `pullbackMonoidal` is not. The pushforward
carries no other lax monoidal structure that instance search can find, and consumers of the
differential graded transport need the instance to form the direct image of a sheaf of
differential graded algebras. The pullback, by contrast, is a functor between two categories
which already carry the strict monoidal structure of Tag 01CA, and
`Stacks.SheafOfModules.RingedToposPullback.monoidal` is deliberately not an instance there; that
choice is kept here.

## References

* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory AlgebraicGeometry CategoryTheory.Sheaf
open AlgebraicGeometry.SheafOfModules Stacks.Sheaves.RingedToposModules

universe w w' v u v' u'

attribute [local instance] Stacks.SheafOfModules.Strict.monoidalUnderlyingRingSheaf

namespace Stacks.SheafOfModules.RingedToposPullback

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
  (f : Stacks.Sheaves.RingedToposModules.RingedToposHom X Y)

/-- **The coherence of Tag 03EL, proved.** The comparison
`f^*(F ⊗_{O_D} G) ≅ f^*F ⊗_{O_C} f^*G` is compatible with the associator and with both unitors,
the unit object being matched by `ν : f^*O_D ≅ O_C`. The three fields are
`Stacks.SheafOfModules.RingedToposPullback.associativity`, `leftUnitality` and `rightUnitality`;
there is no hypothesis, and the four universes of the two ringed topoi stay independent. -/
@[stacks 03EL "the comparison of the pullback with the tensor product is a monoidal structure: \
the three coherences"]
theorem pullbackCoherence : PullbackCoherence f where
  associativity := associativity f
  leftUnitality := leftUnitality f
  rightUnitality := rightUnitality f

/-- **The pullback of sheaves of modules along a morphism of ringed topoi is a monoidal
functor.** This is `Stacks.SheafOfModules.RingedToposPullback.monoidal` at the coherence, so it
carries no hypothesis. Deliberately **not** an instance, for the reason recorded there: both
categories already carry the strict monoidal structure of Tag 01CA, and this file registers no
second monoidal pairing on them. -/
@[instance_reducible]
noncomputable def pullbackMonoidal : f.pullbackModules.Monoidal :=
  monoidal f (pullbackCoherence f)

/-- **The pushforward of sheaves of modules along a morphism of ringed topoi is lax monoidal.**
This is `Stacks.SheafOfModules.RingedToposPullback.pushforwardLaxMonoidal` at the coherence, so
it carries no hypothesis. It is an instance: nothing else in the library equips this functor with
a lax monoidal structure, and the direct image of a sheaf of differential graded algebras is
formed from it. -/
@[instance_reducible]
noncomputable instance pushforwardModulesLaxMonoidal : (pushforwardModules f).LaxMonoidal :=
  pushforwardLaxMonoidal f (pullbackCoherence f)

end Stacks.SheafOfModules.RingedToposPullback

end
