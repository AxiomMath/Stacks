module

public import StacksFrontier.CategoryTheory.Sites.RingedLocalization.RingedToposHomModulesComparison
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullback
public import StacksFrontier.CategoryTheory.Sites.Modules.FlatMorphisms.RingedTopoi
public import StacksFrontier.CategoryTheory.Sites.RingedLocalization.FlatPullbackExact
import StacksCore.Tactic.StacksAttribute
import all StacksFrontier.CategoryTheory.Sites.RingedLocalization.RingedToposHomModulesComparison

/-!
# Additions to the ringed topos comparison of module categories

Declarations extending
`StacksFrontier.CategoryTheory.Sites.RingedLocalization.RingedToposHomModulesComparison`, kept in
their own module.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPushforward Stacks.Sheaves.ToposPullback

namespace AlgebraicGeometry.RingedToposHom

universe v u w v' u' w'

section Comparison

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget RingCat.{w})]
  [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  (f : RingedToposHom X Y)

section PullbackModules

variable [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]

omit [X.J.HasSheafCompose (forget AddCommGrpCat.{w})] in
/-- The pullback of sheaves of modules along `f` is the pullback along the four-field morphism
`f.toRingedToposModulesHom`. -/
theorem pullbackModules_eq_pullbackModules_toRingedToposModulesHom (f : RingedToposHom X Y) :
    f.toModulesHom.pullbackModules =
      Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules f.toRingedToposModulesHom :=
  congrArg (fun g => Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules g)
    (toModulesHom_eq_toRingedToposModulesHom f)

end PullbackModules

end Comparison

section Flat

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w}}
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]

end Flat

end AlgebraicGeometry.RingedToposHom

end
