module

public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSpellingBridge
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedToposModulesPullbackToposGeneral

/-!
# The comparison of the two pushforwards of modules along a morphism of ringed sites, on
underlying sheaves of sets, at independent universes

For a morphism of ringed sites `f`,
`AlgebraicGeometry.RingedSite.HomGeneral.pushforwardModulesToposIsoGeneral` compares the
pushforward of sheaves of modules of the modules development with the pushforward along the
functor of the underlying sites. Both have the direct image `f_* F` as underlying sheaf of sets,
and the comparison is the identity there. This file records that, with the object and morphism
universes of the two sites independent of each other — as they are for `ε : X_étale ⟶ X_Zar`,
whose source has objects one universe up from its target.

`Stacks.Sheaves.GradedAlgebraEssentiallySmall.moduleSheafFunctor_map_pushforwardModulesIso_hom_app`
is the same statement for the first factor with both topoi at the same universes; the input here
is its universe-general form
`AlgebraicGeometry.RingedToposHom.moduleSheafFunctor_map_pushforwardModulesIso`. The second
factor, `AlgebraicGeometry.RingedSite.HomGeneral.pushforwardToposIsoGeneral`, is built from the
identity of the underlying sheaf of sets, so it contributes nothing.

## Main results

* `HomGeneral.moduleSheafFunctor_map_pushforwardModulesToposIsoGeneral_hom_app` and
  `HomGeneral.moduleSheafFunctor_map_pushforwardModulesToposIsoGeneral_inv_app`: the comparison
  is the identity on underlying sheaves of sets.
* `HomGeneral.pushforwardModulesToposIsoGeneral_hom_app_val_app` and
  `HomGeneral.pushforwardModulesToposIsoGeneral_inv_app_val_app`: the comparison is the identity
  on local sections.

## References

* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
-/

@[expose] public section

open CategoryTheory
open Stacks.Sheaves.RingedToposModules

universe uX vX uY vY w

namespace AlgebraicGeometry.RingedSite

variable {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})] [Y.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  (f : HomGeneral X Y)

/-- **The comparison of the two pushforwards of sheaves of modules along a morphism of ringed
sites is the identity on underlying sheaves of sets**, at independent object and morphism
universes of the two sites. -/
theorem HomGeneral.moduleSheafFunctor_map_pushforwardModulesToposIsoGeneral_hom_app
    (N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf (toRingedTopos X).O)) :
    (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf (toRingedTopos Y).O)).map
        (f.pushforwardModulesToposIsoGeneral.hom.app N) =
      CategoryStruct.id (f.toRingedToposHom.toToposHom.pushforward.obj
        (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf (toRingedTopos X).O) N)) :=
  (congrArg (Sheaf.moduleSheafFunctor
      (Stacks.SheafOfModules.Tensor.ringSheaf (toRingedTopos Y).O)).map
    (NatTrans.comp_app
      (AlgebraicGeometry.RingedToposHom.pushforwardModulesIso f.toRingedToposHom).hom
      f.pushforwardToposIsoGeneral.hom N)).trans
    (((Sheaf.moduleSheafFunctor
        (Stacks.SheafOfModules.Tensor.ringSheaf (toRingedTopos Y).O)).map_comp _ _).trans
      ((congrArg (· ≫ CategoryStruct.id _)
        (AlgebraicGeometry.RingedToposHom.moduleSheafFunctor_map_pushforwardModulesIso
          f.toRingedToposHom N)).trans (Category.comp_id _)))

/-- The inverse of the comparison of the two pushforwards of sheaves of modules is the identity on
underlying sheaves of sets. -/
theorem HomGeneral.moduleSheafFunctor_map_pushforwardModulesToposIsoGeneral_inv_app
    (N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf (toRingedTopos X).O)) :
    (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf (toRingedTopos Y).O)).map
        (f.pushforwardModulesToposIsoGeneral.inv.app N) =
      CategoryStruct.id (f.toRingedToposHom.toToposHom.pushforward.obj
        (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf (toRingedTopos X).O) N)) := by
  have h := congrArg (Sheaf.moduleSheafFunctor
    (Stacks.SheafOfModules.Tensor.ringSheaf (toRingedTopos Y).O)).map
      (f.pushforwardModulesToposIsoGeneral.inv_hom_id_app N)
  rw [CategoryTheory.Functor.map_comp,
    f.moduleSheafFunctor_map_pushforwardModulesToposIsoGeneral_hom_app] at h
  exact (Category.comp_id _).symm.trans (h.trans (CategoryTheory.Functor.map_id _ _))

/-- The comparison of the two pushforwards of sheaves of modules along a morphism of ringed sites
is the identity on local sections, at independent universes. -/
theorem HomGeneral.pushforwardModulesToposIsoGeneral_hom_app_val_app
    (N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf (toRingedTopos X).O))
    (W : Y.Cᵒᵖ)
    (s : ((pushforwardModules f.toRingedToposHom.toRingedToposModulesHom).obj N).val.obj W) :
    (f.pushforwardModulesToposIsoGeneral.hom.app N).val.app W s = s :=
  congrArg (fun k => k.hom.app W s)
    (f.moduleSheafFunctor_map_pushforwardModulesToposIsoGeneral_hom_app N)

/-- The inverse of the comparison of the two pushforwards of sheaves of modules along a morphism
of ringed sites is the identity on local sections, at independent universes. -/
theorem HomGeneral.pushforwardModulesToposIsoGeneral_inv_app_val_app
    (N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf (toRingedTopos X).O))
    (W : Y.Cᵒᵖ) (s : (f.toRingedToposSiteHom.pushforwardTopos.obj N).val.obj W) :
    (f.pushforwardModulesToposIsoGeneral.inv.app N).val.app W s = s :=
  congrArg (fun k => k.hom.app W s)
    (f.moduleSheafFunctor_map_pushforwardModulesToposIsoGeneral_inv_app N)

end AlgebraicGeometry.RingedSite

end
