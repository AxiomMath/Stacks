module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullbackBraiding
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullbackCoherence
public import StacksFrontier.CategoryTheory.Monoidal.ReseatFunctorBraided

/-!
# The pullback of modules along a morphism of ringed topoi is braided

Let `f : (Sh(C), O_C) ⟶ (Sh(D), O_D)` be a morphism of ringed topoi.
`Stacks.SheafOfModules.RingedToposPullback.pullbackMonoidal` makes `f^*` a monoidal functor for
the symmetric monoidal structures of Tag 01CA, with the comparison of **Tag 03EL** as its oplax
tensorator, and `Stacks.SheafOfModules.RingedToposPullback.braiding` says that this comparison
commutes with the braidings. Together they make `f^*` a braided monoidal functor.

## Main definitions

* `Stacks.SheafOfModules.RingedToposPullback.pullbackBraided`: `f^*` as a braided functor, whose
  underlying monoidal structure is `pullbackMonoidal`.
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory AlgebraicGeometry CategoryTheory.Sheaf
open AlgebraicGeometry.SheafOfModules Stacks.Sheaves.RingedToposModules

universe w w' v u v' u'

attribute [local instance] Stacks.SheafOfModules.Strict.monoidalUnderlyingRingSheaf
  Stacks.SheafOfModules.Strict.braidedUnderlyingRingSheaf

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

/-- **The pullback of sheaves of modules along a morphism of ringed topoi is a braided monoidal
functor** for the symmetric monoidal structures of Tag 01CA: the monoidal structure is
`pullbackMonoidal`, and its oplax tensorator, the comparison of Tag 03EL, commutes with the
braidings by `Stacks.SheafOfModules.RingedToposPullback.braiding`. Not an instance, for the same
reason as `pullbackMonoidal`. -/
@[instance_reducible]
noncomputable def pullbackBraided : f.pullbackModules.Braided :=
  letI := pullbackMonoidal f
  Functor.Braided.ofOplax _ (braiding f)

/-- The monoidal structure underlying `pullbackBraided` is `pullbackMonoidal`. -/
theorem pullbackBraided_toMonoidal : (pullbackBraided f).toMonoidal = pullbackMonoidal f :=
  rfl

end Stacks.SheafOfModules.RingedToposPullback

end
