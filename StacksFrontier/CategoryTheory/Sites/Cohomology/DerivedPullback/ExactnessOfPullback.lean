module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import StacksCore.Tactic.StacksAttribute

/-!
# Exactness properties of pullback for a morphism of ringed topoi

Let `f : (Sh(C), O) ⟶ (Sh(C'), O')` be a morphism of ringed topoi. Stacks 06YY constructs the
derived pullback `Lf^*` as the total left derived functor of degreewise pullback. This file
records the exactness properties of the underlying pullback functor on sheaves of modules that
that construction rests on.

All of them come from one source: pullback of sheaves of modules is a left adjoint, with
pushforward as its right adjoint. That is Stacks 03D7, available here as
`Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules`.

## Main results

* `pullbackModules_additive`: pullback is additive.
* `pullbackModules_preservesColimitsOfSizeZero` and `pullbackModules_preservesFiniteColimits`:
  pullback preserves small and finite colimits; in particular it is right exact.

## References

* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w w' v u v' u'

namespace Stacks.Sheaves.DerivedPullback

open AlgebraicGeometry Stacks.Sheaves.RingedToposModules

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify X.J AddCommGrpCat.{w}] [HasSheafify Y.J AddCommGrpCat.{w'}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]

/-- Pullback of sheaves of modules along a morphism of ringed topoi is additive. It is a left
adjoint, by Stacks 03D7, hence preserves binary coproducts and the initial object; in a
category with binary biproducts that is additivity. -/
instance pullbackModules_additive (f : RingedToposHom X Y) :
    (f.pullbackModules).Additive := by
  have adj := pullbackAdjPushforwardModules f
  have := adj.isLeftAdjoint
  have : PreservesColimitsOfShape (Discrete WalkingPair) (f.pullbackModules) :=
    adj.leftAdjoint_preservesColimits.preservesColimitsOfShape
  have : PreservesColimitsOfShape (Discrete PEmpty.{1}) (f.pullbackModules) :=
    adj.leftAdjoint_preservesColimits.preservesColimitsOfShape
  have : PreservesBinaryBiproducts (f.pullbackModules) :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  exact Functor.additive_of_preservesBinaryBiproducts _

/-- Pullback of sheaves of modules along a morphism of ringed topoi preserves colimits of
small shape: it is a left adjoint, by Stacks 03D7, so it preserves colimits of every shape,
and preservation at one size gives preservation at size zero. -/
instance pullbackModules_preservesColimitsOfSizeZero (f : RingedToposHom X Y) :
    PreservesColimitsOfSize.{0, 0} (f.pullbackModules) :=
  (pullbackAdjPushforwardModules f).leftAdjoint_preservesColimits

/-- Pullback of sheaves of modules along a morphism of ringed topoi preserves finite
colimits; in particular it is right exact. -/
instance pullbackModules_preservesFiniteColimits (f : RingedToposHom X Y) :
    PreservesFiniteColimits (f.pullbackModules) where

end Stacks.Sheaves.DerivedPullback
