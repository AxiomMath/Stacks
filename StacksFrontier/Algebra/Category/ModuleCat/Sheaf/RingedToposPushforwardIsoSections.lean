module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullbackTensorComp

/-!
# The comparison of the two direct images of sheaves of modules is the identity

Let `f : (Sh(C), O_C) ⟶ (Sh(D), O_D)` be a morphism of ringed topoi
(`AlgebraicGeometry.RingedToposHom`). The direct image of a sheaf of `O_C`-modules can be
computed through the four-field morphism of ringed topoi of the modules development or as
`AlgebraicGeometry.RingedToposHom.pushforwardModules`; the two are identified by
`AlgebraicGeometry.RingedToposHom.toModulesPushforwardIso`. Both have the direct image `f_*` of
the underlying sheaf of sets of the module as their underlying sheaf of sets, and the
identification is built from the identity of that sheaf: it is the identity on underlying
sheaves of sets, and it fixes every local section.

## Main results

* `AlgebraicGeometry.RingedToposHom.moduleSheafFunctor_map_toModulesPushforwardIso_hom_app_eq_id`:
  on underlying sheaves of sets the identification is the identity morphism of `f_*` of the
  underlying sheaf of sets of the module.
* `AlgebraicGeometry.RingedToposHom.toModulesPushforwardIso_hom_app_val_app`,
  `AlgebraicGeometry.RingedToposHom.toModulesPushforwardIso_inv_app_val_app`: the
  identification, in either direction, is the identity on the sections over every object of the
  site.

## Implementation notes

`AlgebraicGeometry.RingedToposHom.moduleSheafFunctor_map_toModulesPushforwardIso_hom_app` states
the first result as the `eqToHom` of the equality of the two underlying sheaves of sets, which is
the form an `eqToHom` computation wants. The form here, with the identity of the direct image of
the underlying sheaf of sets on the right, is the one to rewrite with when the morphisms around
the comparison are stated at that direct image: deciding afresh that the two readings of the
direct image have the same underlying sheaf, at a composite morphism of ringed topoi or at a
direct image of a direct image, is expensive, and here it is decided once, at a variable morphism
and a variable module.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.RingedToposHom

universe v u w v' u' w'

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget RingCat.{w})]
  [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]

/-- **The comparison of the two direct images of sheaves of modules is the identity on
underlying sheaves of sets.** Both are the direct image `f_*` of the underlying sheaf of sets of
the module — restriction of scalars does not touch it. -/
lemma moduleSheafFunctor_map_toModulesPushforwardIso_hom_app_eq_id (f : RingedToposHom X Y)
    (F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map
        (f.toModulesPushforwardIso.hom.app F) =
      𝟙 (f.toToposHom.pushforward.obj
        (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) F)) := by
  rw [moduleSheafFunctor_map_toModulesPushforwardIso_hom_app]
  rfl

/-- **The comparison of the two direct images of sheaves of modules is the identity on
sections.** The two sheaves of modules have the same underlying sheaf of sets, and so the same
sections over an object of the site; the comparison fixes each of them. -/
lemma toModulesPushforwardIso_hom_app_val_app (f : RingedToposHom X Y)
    (F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (Z : Y.Cᵒᵖ)
    (x : ((Stacks.Sheaves.RingedToposModules.pushforwardModules
      f.toModulesHom).obj F).val.obj Z) :
    (f.toModulesPushforwardIso.hom.app F).val.app Z x = x :=
  rfl

/-- **The comparison of the two direct images of sheaves of modules is the identity on
sections**, read in the other direction. -/
lemma toModulesPushforwardIso_inv_app_val_app (f : RingedToposHom X Y)
    (F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (Z : Y.Cᵒᵖ)
    (x : ((pushforwardModules f).obj F).val.obj Z) :
    (f.toModulesPushforwardIso.inv.app F).val.app Z x = x :=
  rfl

end AlgebraicGeometry.RingedToposHom

end
