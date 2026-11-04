module

public import StacksFrontier.Deformation.ToposThickening.Helpers.ThickeningTargetPushforward
public import StacksFrontier.Deformation.ToposThickening.FixedActionFlatness
public import StacksFrontier.Deformation.ToposThickening.Helpers.ExtDescentTensorPairing

/-!
# The kernel map of a morphism of extensions along a morphism of thickenings

Let `D : Y₂ ⟶ Y₁` be a morphism of the targets of two first order thickenings `i₁ : X ⟶ Y₁`,
`i₂ : X ⟶ Y₂` (`Deformation.ToposThickening.ThickeningTargetMorphism`), `E₁`, `E₂` extensions of
`F₁` by `ℐ₁ ⊗ F₁` and of `F₂` by `ℐ₂ ⊗ F₂` whose canonical actions are the identity, and
`u : E₁ ⟶ j_*E₂` a map of the middle terms lying over `θ : F₁ ⟶ Ψ₀F₂`. Then on the kernels `u` is
the comparison `ℐ₁ ⊗ F₁ ⟶ ℐ₁ ⊗ Ψ₀F₂ ⟶ Ψ₀(ℐ₂ ⊗ F₂)`
(`Deformation.ToposThickening.ThickeningTargetMorphism.idealTensorMap`): on a section `a·x` of
the kernel, `u(a·x) = j^♯(a)·u(x)`, which is `j_*` of the action of `ℐ₂` on `u(x)`. No flatness or
first order condition on `j` is needed.

This module is a helper and carries no `@[stacks]` attribute.

## Main results

* `Deformation.ToposThickening.ThickeningTargetMorphism.f_comp_eq_idealTensorMap_comp`.

## References

* [Stacks Project, Tag 08MB](https://stacks.math.columbia.edu/tag/08MB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry (RingedTopos RingedToposHom)
open Stacks.Sheaves.ToposPushforward (pushforwardCommRingFunctor pushforwardModuleFunctor)
open Stacks.SheafOfModules.FlatSquareZero (ringMap reductionTensorMap multiplicationMap)

universe v u v₁ u₁ v₂ u₂ w

namespace Deformation.ToposThickening.ThickeningTargetMorphism

variable {X : RingedTopos.{v, u, w}} {Y₁ : RingedTopos.{v₁, u₁, w}} {Y₂ : RingedTopos.{v₂, u₂, w}}
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y₁.J.HasSheafCompose (forget RingCat.{w})]
  [Y₂.J.HasSheafCompose (forget RingCat.{w})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y₁.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y₂.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {i₁ : RingedToposHom X Y₁} {i₂ : RingedToposHom X Y₂} (D : ThickeningTargetMorphism i₁ i₂)
  [Y₁.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y₂.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  (hi₁ : FirstOrderThickening i₁) (hi₂ : FirstOrderThickening i₂)
  [Y₁.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify Y₁.J AddCommGrpCat.{w}]
  [Y₂.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify Y₂.J AddCommGrpCat.{w}]
  [HasSheafify Y₁.J AddCommGrpCat.{w}] [HasSheafify Y₂.J AddCommGrpCat.{w}]

omit [Y₁.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify Y₁.J AddCommGrpCat.{w}]
  [HasSheafify Y₁.J AddCommGrpCat.{w}] in
/-- **`j_*` of an extension with the identity action, on a section `ā ⊗ ȳ`.** For `x` a section of
`j_*E` and `a` a section of `ℐ₁`, the image under `j_*` of the inclusion of `j_*(λ(a) ⊗ x̄)` is
`j^♯(a)·x`. -/
theorem pushforwardModules_map_f_tensorSectionPairing {F : SheafOfModules.{w}
      (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i₂))}
    (E : Abelian.YonedaExtension ((structureRestrict i₂).obj F)
      ((structureRestrict i₂).obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i₂)).flip.obj F).obj hi₂.I)) 0)
    (hE : (extensionActionMap hi₂ E).1 =
      𝟙 (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i₂)).flip.obj F).obj hi₂.I))
    (U : Y₁.Cᵒᵖ) (a : hi₁.I.val.obj U) (x : (D.j.pushforwardModules.obj E.Z.left).val.obj U) :
    (D.j.toToposHom.pushforward ⋙ Sheaf.sectionsFunctor.{w} Y₁.J U).map
        ((Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y₂.O)).map E.f)
        ((D.j.toToposHom.pushforward ⋙ Sheaf.sectionsFunctor.{w} Y₁.J U).map
          (Stacks.SheafOfModules.tensorSectionPairing hi₂.I F)
          (Functor.prodObjMk (P := D.j.toToposHom.pushforward ⋙ Sheaf.sectionsFunctor.{w} Y₁.J U)
            (A := Sheaf.moduleSheaf _ hi₂.I) (B := Sheaf.moduleSheaf _ F)
            (D.idealSection hi₁ hi₂ U a)
            ((D.j.toToposHom.pushforward ⋙ Sheaf.sectionsFunctor.{w} Y₁.J U).map
              ((Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y₂.O)).map E.g)
              x))) =
      (show (Stacks.SheafOfModules.Tensor.ringSheaf Y₁.O).obj.obj U from hi₁.incl.val.app U a) •
        x := by
  let P := D.j.toToposHom.pushforward ⋙ Sheaf.sectionsFunctor.{w} Y₁.J U
  have hS := congrArg (fun m => P.map m
    (Functor.prodObjMk (P := P) (A := Sheaf.moduleSheaf _ ((structureRestrict i₂).obj hi₂.I))
      (B := Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y₂.O) E.Z.left)
      (D.idealSection hi₁ hi₂ U a) x)) (actionMap_sheafSets hi₂ E)
  simp only [hE] at hS
  refine Eq.trans ?_ (hS.trans ?_)
  · refine Eq.trans ?_ (Functor.map_prodMap_comp_prodObjMk P _ _ _ _ _).symm
    refine Eq.trans ?_ (P.map_comp_apply _ _ _).symm
    exact congrArg (fun t => P.map ((Sheaf.moduleSheafFunctor _).map E.f)
      (P.map (Stacks.SheafOfModules.tensorSectionPairing hi₂.I F) (Functor.prodObjMk (P := P)
        (A := Sheaf.moduleSheaf _ hi₂.I) (B := Sheaf.moduleSheaf _ F) t _)))
      (P.map_id_apply _ _).symm
  · refine (Functor.map_prodMap_comp_prodObjMk P _ _ _ _ _).trans ?_
    refine (congrArg₂ (fun t t' => P.map (Sheaf.moduleSMulHom _ E.Z.left)
      (Functor.prodObjMk (P := P) (A := Sheaf.ringSheaf _)
        (B := Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y₂.O) E.Z.left) t t'))
      (D.idealSection_spec hi₁ hi₂ U a) (P.map_id_apply _ _)).trans ?_
    exact (Stacks.SheafOfModules.smul_eq_map_moduleSMulHom (J := Y₁.J)
      (Φ := D.j.toToposHom.pushforward) U _ _).symm

/-- **The kernel map of a morphism of extensions along a morphism of thickenings.** For extensions
`E₁`, `E₂` of `F₁`, `F₂` by `ℐ₁ ⊗ F₁`, `ℐ₂ ⊗ F₂` with the identity actions, and a map
`u : E₁ ⟶ j_*E₂` of the middle terms over `θ : F₁ ⟶ Ψ₀F₂`, the restriction of `u` to the kernels
is `ℐ₁ ⊗ θ` followed by the comparison `ℐ₁ ⊗ Ψ₀F₂ ⟶ Ψ₀(ℐ₂ ⊗ F₂)`. -/
theorem f_comp_eq_idealTensorMap_comp {F₁ : SheafOfModules.{w}
      (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i₁))}
    {F₂ : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i₂))}
    (θ : F₁ ⟶ D.basePushforward.obj F₂)
    (E₁ : Abelian.YonedaExtension ((structureRestrict i₁).obj F₁)
      ((structureRestrict i₁).obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i₁)).flip.obj F₁).obj hi₁.I)) 0)
    (hE₁ : (extensionActionMap hi₁ E₁).1 =
      𝟙 (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i₁)).flip.obj F₁).obj hi₁.I))
    (E₂ : Abelian.YonedaExtension ((structureRestrict i₂).obj F₂)
      ((structureRestrict i₂).obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i₂)).flip.obj F₂).obj hi₂.I)) 0)
    (hE₂ : (extensionActionMap hi₂ E₂).1 =
      𝟙 (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i₂)).flip.obj F₂).obj hi₂.I))
    (u : E₁.Z.left ⟶ D.j.pushforwardModules.obj E₂.Z.left)
    (hu : u ≫ D.j.pushforwardModules.map E₂.g ≫ (D.restrictIso F₂).hom =
      E₁.g ≫ (structureRestrict i₁).map θ) :
    E₁.f ≫ u =
      (structureRestrict i₁).map (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i₁)).obj
          hi₁.I).map θ ≫ D.idealTensorMap hi₁ hi₂ F₂) ≫
        (D.restrictIso (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i₂)).flip.obj F₂).obj
          hi₂.I)).inv ≫ D.j.pushforwardModules.map E₂.f := by
  have : Epi E₁.g := (yonedaExtension_shortExact E₁).epi_g
  have := Stacks.SheafOfModules.FlatSquareZero.reductionTensorMap_epi i₁.fSharp hi₁.I E₁.Z.left F₁
    E₁.g
  refine (cancel_epi (reductionTensorMap i₁.fSharp hi₁.I E₁.Z.left F₁ E₁.g)).1 ?_
  rw [← Category.assoc, ← multiplicationMap_eq_comp_f hi₁ F₁ E₁ hE₁]
  refine tensorSheaf_hom_ext Y₁.O fun U a x => ?_
  let P := D.j.toToposHom.pushforward ⋙ Sheaf.sectionsFunctor.{w} Y₁.J U
  have R7 : θ.val.app U (E₁.g.val.app U x) =
      (D.j.pushforwardModules.map E₂.g).val.app U (u.val.app U x) :=
    (congrArg (fun φ => φ.val.app U x) hu).symm
  refine (congrArg (u.val.app U)
    (Stacks.SheafOfModules.FlatSquareZero.multiplicationMap_tmul i₁.fSharp hi₁.I E₁.Z.left
      hi₁.incl U a x)).trans ?_
  refine (map_smul (u.val.app U).hom _ x).trans ?_
  refine (D.pushforwardModules_map_f_tensorSectionPairing hi₁ hi₂ E₂ hE₂ U a
    (u.val.app U x)).symm.trans ?_
  symm
  refine (congrArg (fun y => (D.j.pushforwardModules.map E₂.f).val.app U
    ((D.restrictIso (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i₂)).flip.obj F₂).obj
      hi₂.I)).inv.val.app U ((D.idealTensorMap hi₁ hi₂ F₂).val.app U
        ((((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i₁)).obj hi₁.I).map θ).val.app
          U y))))
    (Stacks.SheafOfModules.FlatSquareZero.reductionTensorMap_tmul i₁.fSharp hi₁.I E₁.Z.left F₁
      E₁.g U a x)).trans ?_
  refine (congrArg (fun y => (D.j.pushforwardModules.map E₂.f).val.app U
    ((D.restrictIso (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i₂)).flip.obj F₂).obj
      hi₂.I)).inv.val.app U ((D.idealTensorMap hi₁ hi₂ F₂).val.app U y)))
    (Stacks.SheafOfModules.sheafTensor_obj_map_unit_tmul θ U a (E₁.g.val.app U x))).trans ?_
  refine (congrArg (fun y => (D.j.pushforwardModules.map E₂.f).val.app U
    ((D.restrictIso (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i₂)).flip.obj F₂).obj
      hi₂.I)).inv.val.app U y))
    (D.idealTensorMap_val_app_unit hi₁ hi₂ F₂ U a (θ.val.app U (E₁.g.val.app U x)))).trans ?_
  refine (congrArg (fun y => (D.j.pushforwardModules.map E₂.f).val.app U y)
    (D.restrictIso_inv_val_app _ U _)).trans ?_
  exact congrArg (fun w => (D.j.pushforwardModules.map E₂.f).val.app U
    (P.map (Stacks.SheafOfModules.tensorSectionPairing hi₂.I F₂)
      (Functor.prodObjMk (P := P) (A := Sheaf.moduleSheaf _ hi₂.I) (B := Sheaf.moduleSheaf _ F₂)
        (D.idealSection hi₁ hi₂ U a) w))) R7

end Deformation.ToposThickening.ThickeningTargetMorphism

end
