module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorIsoTransposeCharacterization
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSiteHomGeneralPushforwardSections
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSiteHomGeneralPushforwardUnderlying

/-!
# The unit of Stacks 03D7 carries a pure tensor through Stacks 03EL, on sections

Let `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed sites presented by a functor `u`, at
independent universes, and `F`, `G` two `𝒪_Y`-modules. The comparison
`c : f^*(F ⊗ G) ⟶ f^*F ⊗ f^*G` of **Stacks 03EL** is characterized by its adjoint transpose
(`Stacks.SheafOfModules.eq_pullbackTensorIso_hom_app_iff`), and for a morphism of ringed sites the
direct image is restriction along `u`, so that characterization can be read on local sections:
for local sections `x` of `F` and `y` of `G` over `V`,

`f_*(c)(η_{F ⊗ G}(x ⊗ y)) = η_F(x) ⊗ η_G(y)` over `u(V)`,

where `η` is the unit of the adjunction `f^* ⊣ f_*` of Stacks 03D7. This is the statement that the
unit is monoidal, the form in which a computation on sections of a right adjoint compares its
tensor products with those of the source.

## Main results

* `HomGeneral.pullbackModulesToposIsoGeneral_inv_app_val_app_unit`: the units of the two
  presentations of `f^* ⊣ f_*` (along the morphism of ringed topoi and along the functor of sites)
  agree on sections through the comparison of the two pullbacks.
* `HomGeneral.pushforwardModules_map_val_app`: the direct image of a morphism is, on sections over
  `V`, the morphism over `u(V)`.
* `HomGeneral.pullbackTensorIso_hom_val_app_unit_tmul`: the same statement as the first, with the
  direct image read on sections.
* `HomGeneral.unit_comp_pushforward_pullbackTensorIso_hom_val_app_tmul`: the unit of `f^* ⊣ f_*`
  followed by the direct image of Stacks 03EL sends `x ⊗ y` to `η(x) ⊗ η(y)`.

All names are in the namespace `AlgebraicGeometry.RingedSite`.

## References

* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
-/


@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open Stacks.Sheaves.RingedToposModules Stacks.PresheafOfModules.ChangeOfRings
open scoped TensorProduct

universe uX vX uY vY w

namespace AlgebraicGeometry.RingedSite

open Stacks.SheafOfModules

variable {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}} (f : HomGeneral X Y)
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X.J.HasSheafCompose (forget CommRingCat.{w})] [Y.J.HasSheafCompose (forget CommRingCat.{w})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})] [Y.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  (F G : SheafOfModules.{w} (Tensor.ringSheaf (toRingedTopos Y).O))

/-- **The unit of Stacks 03D7 carries a pure tensor through Stacks 03EL**: for a morphism of
ringed sites `f` and local sections `x` of `F`, `y` of `G` over `V`, the unit of `f^* ⊣ f_*` at
`F ⊗ G` followed by the direct image of the comparison `f^*(F ⊗ G) ⟶ f^*F ⊗ f^*G` sends `x ⊗ y`
to `η_F(x) ⊗ η_G(y)`, a local section of `f^*F ⊗ f^*G` over `u(V)`. -/
theorem HomGeneral.unit_comp_pushforward_pullbackTensorIso_hom_val_app_tmul (V : Y.Cᵒᵖ)
    (x : F.val.obj V) (y : G.val.obj V) :
    ((pullbackAdjPushforwardModules f.toRingedToposHom.toRingedToposModulesHom).unit.app
          (((Functor.uncurry.obj (Tensor.sheafTensor (toRingedTopos Y).O))).obj (F, G)) ≫
        (pushforwardModules f.toRingedToposHom.toRingedToposModulesHom).map
          ((pullbackTensorIso f.toRingedToposHom.toRingedToposModulesHom).hom.app (F, G))).val.app V
        (((PresheafOfModules.sheafificationAdjunction
            (R := Stacks.Sheaves.RingedToposModules.commRingSheaf Y.J (toRingedTopos Y).O.obj
              (Tensor.ringSheaf (toRingedTopos Y).O).property) (𝟙 _)).unit.app
          (F.val ⊗ G.val)).app V
          (x ⊗ₜ[(ringPresheaf (toRingedTopos Y).O.obj).obj V] y)) =
      _root_.PresheafOfModules.Hom.app ((PresheafOfModules.sheafificationAdjunction
          (R := Tensor.ringSheaf (toRingedTopos X).O)
          (𝟙 (Tensor.ringSheaf (toRingedTopos X).O).obj)).unit.app
        (PresheafOfModules.tensorObj (O := (toRingedTopos X).O.obj)
          ((f.toRingedToposHom.toRingedToposModulesHom.pullbackModules).obj F).val
          ((f.toRingedToposHom.toRingedToposModulesHom.pullbackModules).obj G).val))
        (f.u.op.obj V)
        (((pullbackAdjPushforwardModules f.toRingedToposHom.toRingedToposModulesHom).unit.app
            F).val.app V x ⊗ₜ[((toRingedTopos X).O.obj ⋙ forget₂ CommRingCat RingCat).obj
          (f.u.op.obj V)]
          ((pullbackAdjPushforwardModules f.toRingedToposHom.toRingedToposModulesHom).unit.app
            G).val.app V y) := by
  have h := (eq_pullbackTensorIso_hom_app_iff f.toRingedToposHom.toRingedToposModulesHom F G
    ((pullbackTensorIso f.toRingedToposHom.toRingedToposModulesHom).hom.app (F, G))).mp rfl
  have h2 := congrArg (fun q => pairingApp (Tensor.ringSheaf (toRingedTopos Y).O)
    (N := (pushforwardModules f.toRingedToposHom.toRingedToposModulesHom).obj
      (((Tensor.sheafTensor (toRingedTopos X).O).obj
        ((f.toRingedToposHom.toRingedToposModulesHom.pullbackModules).obj F)).obj
        ((f.toRingedToposHom.toRingedToposModulesHom.pullbackModules).obj G))) q V x y) h
  exact (pairingApp_pairingOfTensorHom _ V x y).symm.trans
    (h2.trans (f.pairingApp_prodMap_comp_pushforward_tensorSectionPairing _ _ V x y))

omit [X.J.HasSheafCompose (forget CommRingCat.{w})] [Y.J.HasSheafCompose (forget CommRingCat.{w})]
  [HasWeakSheafify Y.J AddCommGrpCat.{w}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- **The units of the two presentations of `f^* ⊣ f_*` agree on sections.** The unit of the
adjunction presented by the functor of sites, carried back by the comparison
`HomGeneral.pullbackModulesToposIsoGeneral` of the two pullbacks, is the unit of the adjunction of
the morphism of ringed topoi: both direct images are restriction along `u`. -/
theorem HomGeneral.pullbackModulesToposIsoGeneral_inv_app_val_app_unit
    [EssentiallySmall.{w} Y.C] [LocallySmall.{w} X.C]
    (V : Y.Cᵒᵖ) (x : F.val.obj V) :
    (f.pullbackModulesToposIsoGeneral.inv.app F).val.app (f.u.op.obj V)
        ((f.toRingedToposSiteHom.pullbackPushforwardAdjunctionToposGeneral.unit.app F).val.app
          V x) =
      ((pullbackAdjPushforwardModules f.toRingedToposHom.toRingedToposModulesHom).unit.app
          F).val.app V x := by
  have h := unit_app_comp_hom_app_eq_unit_app_comp_map_leftAdjointUniq_inv
    (pullbackAdjPushforwardModules f.toRingedToposHom.toRingedToposModulesHom)
    f.pushforwardModulesToposIsoGeneral
    f.toRingedToposSiteHom.pullbackPushforwardAdjunctionToposGeneral F
  have e1 : ((pullbackAdjPushforwardModules f.toRingedToposHom.toRingedToposModulesHom).unit.app F ≫
        f.pushforwardModulesToposIsoGeneral.hom.app
          (f.toRingedToposHom.toRingedToposModulesHom.pullbackModules.obj F)).val.app V x =
      (f.pushforwardModulesToposIsoGeneral.hom.app
          (f.toRingedToposHom.toRingedToposModulesHom.pullbackModules.obj F)).val.app V
        (((pullbackAdjPushforwardModules f.toRingedToposHom.toRingedToposModulesHom).unit.app
          F).val.app V x) := rfl
  have e2 : (f.toRingedToposSiteHom.pullbackPushforwardAdjunctionToposGeneral.unit.app F ≫
        f.toRingedToposSiteHom.pushforwardTopos.map
          (f.pullbackModulesToposIsoGeneral.inv.app F)).val.app V x =
      (f.pullbackModulesToposIsoGeneral.inv.app F).val.app (f.u.op.obj V)
        ((f.toRingedToposSiteHom.pullbackPushforwardAdjunctionToposGeneral.unit.app F).val.app
          V x) := rfl
  exact e2.symm.trans ((congrArg (fun k => k.val.app V x) h).symm.trans
    (e1.trans (f.pushforwardModulesToposIsoGeneral_hom_app_val_app _ V _)))

omit [X.J.HasSheafCompose (forget CommRingCat.{w})] [Y.J.HasSheafCompose (forget CommRingCat.{w})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- The direct image of a morphism of sheaves of modules along the morphism of ringed topoi of a
morphism of ringed sites is, on sections over `V`, the morphism over `u(V)`. -/
theorem HomGeneral.pushforwardModules_map_val_app
    {A A' : SheafOfModules.{w} (Tensor.ringSheaf (toRingedTopos X).O)} (h : A ⟶ A') (V : Y.Cᵒᵖ)
    (s : ((pushforwardModules f.toRingedToposHom.toRingedToposModulesHom).obj A).val.obj V) :
    ((pushforwardModules f.toRingedToposHom.toRingedToposModulesHom).map h).val.app V s =
      h.val.app (f.u.op.obj V) s := by
  have hn := congrArg (fun k => k.val.app V s)
    (f.pushforwardModulesToposIsoGeneral.hom.naturality h)
  have e1 : ((pushforwardModules f.toRingedToposHom.toRingedToposModulesHom).map h ≫
        f.pushforwardModulesToposIsoGeneral.hom.app A').val.app V s =
      (f.pushforwardModulesToposIsoGeneral.hom.app A').val.app V
        (((pushforwardModules f.toRingedToposHom.toRingedToposModulesHom).map h).val.app V s) :=
    rfl
  have e2 : (f.pushforwardModulesToposIsoGeneral.hom.app A ≫
        f.toRingedToposSiteHom.pushforwardTopos.map h).val.app V s =
      h.val.app (f.u.op.obj V) ((f.pushforwardModulesToposIsoGeneral.hom.app A).val.app V s) :=
    rfl
  exact ((f.pushforwardModulesToposIsoGeneral_hom_app_val_app _ V _).symm.trans
    (e1.symm.trans (hn.trans e2))).trans
    (congrArg (h.val.app (f.u.op.obj V))
      (f.pushforwardModulesToposIsoGeneral_hom_app_val_app _ V s))

/-- `HomGeneral.unit_comp_pushforward_pullbackTensorIso_hom_val_app_tmul` with the direct image
read on sections: the comparison of Stacks 03EL over `u(V)`, applied to the unit image of `x ⊗ y`,
is `η_F(x) ⊗ η_G(y)`. -/
theorem HomGeneral.pullbackTensorIso_hom_val_app_unit_tmul (V : Y.Cᵒᵖ)
    (x : F.val.obj V) (y : G.val.obj V) :
    ((pullbackTensorIso f.toRingedToposHom.toRingedToposModulesHom).hom.app (F, G)).val.app
        (f.u.op.obj V)
      (((pullbackAdjPushforwardModules f.toRingedToposHom.toRingedToposModulesHom).unit.app
          (((Functor.uncurry.obj (Tensor.sheafTensor (toRingedTopos Y).O))).obj (F, G))).val.app V
        (((PresheafOfModules.sheafificationAdjunction
            (R := Stacks.Sheaves.RingedToposModules.commRingSheaf Y.J (toRingedTopos Y).O.obj
              (Tensor.ringSheaf (toRingedTopos Y).O).property) (𝟙 _)).unit.app
          (F.val ⊗ G.val)).app V
          (x ⊗ₜ[(ringPresheaf (toRingedTopos Y).O.obj).obj V] y))) =
      _root_.PresheafOfModules.Hom.app ((PresheafOfModules.sheafificationAdjunction
          (R := Tensor.ringSheaf (toRingedTopos X).O)
          (𝟙 (Tensor.ringSheaf (toRingedTopos X).O).obj)).unit.app
        (PresheafOfModules.tensorObj (O := (toRingedTopos X).O.obj)
          ((f.toRingedToposHom.toRingedToposModulesHom.pullbackModules).obj F).val
          ((f.toRingedToposHom.toRingedToposModulesHom.pullbackModules).obj G).val))
        (f.u.op.obj V)
        (((pullbackAdjPushforwardModules f.toRingedToposHom.toRingedToposModulesHom).unit.app
            F).val.app V x ⊗ₜ[((toRingedTopos X).O.obj ⋙ forget₂ CommRingCat RingCat).obj
          (f.u.op.obj V)]
          ((pullbackAdjPushforwardModules f.toRingedToposHom.toRingedToposModulesHom).unit.app
            G).val.app V y) :=
  (f.pushforwardModules_map_val_app _ V _).symm.trans
    (f.unit_comp_pushforward_pullbackTensorIso_hom_val_app_tmul F G V x y)

end AlgebraicGeometry.RingedSite

end
