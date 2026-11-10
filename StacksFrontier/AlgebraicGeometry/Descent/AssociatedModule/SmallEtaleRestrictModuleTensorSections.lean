module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.ZariskiPullbackTensor
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSiteHomGeneralPullbackTensorUnit
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSiteHomGeneralPushforwardUnderlying

/-!
# The units of the associated-module adjunction at `ε`, on sections

Let `S` be a scheme of a big étale site and `ε : (S_étale, 𝒪) ⟶ (S_Zar, 𝒪_S)` the morphism of
ringed sites of Stacks 070R. The adjunction `ε^* ⊣ ε_*` has two presentations: the adjunction of
the morphism of ringed topoi `AlgebraicGeometry.SmallEtale.toZariskiRingedToposModulesHom`, whose
pullback carries Stacks 03EL, and the associated-module adjunction of Stacks 03DU (4),
`AlgebraicGeometry.SmallEtale.associatedModuleAdjunction`, whose unit and counit are the ones the
equivalence of Descent, Proposition 03DX (2) is stated with. The two pullbacks are identified by
`AlgebraicGeometry.SmallEtale.pullbackModulesToZariskiIso`. This file records that the two units
agree on local sections through that identification, and the value on sections of the comparison
of Stacks 03EL read through an identification of the pullback, which is what a computation of
`AlgebraicGeometry.SmallEtale.restrictModuleTensorIso` on pure tensors consumes.

## Main results

* `AlgebraicGeometry.SmallEtale.pullbackModulesToZariskiIso_inv_app_val_app_unit` and
  `pullbackModulesToZariskiIso_hom_app_val_app_unit`: the units of the two presentations agree on
  sections.
* `Stacks.SheafOfModules.pullbackTensorIsoTransport_hom_val_app`: the comparison of Stacks 03EL
  read through an identification of the pullback, on sections.
* `Stacks.SheafOfModules.sheafTensor_uncurry_map_val_app_unit_tmul_forget₂`,
  `sheafTensor_obj_map_val_app_unit_tmul_forget₂`, `sheafTensor_map_app_val_app_unit_tmul_forget₂`:
  tensor products of morphisms on a pure tensor, with the scalar ring spelled through `forget₂`.
* `AlgebraicGeometry.RingedSite.HomGeneral.pullbackTensorIsoTransport_hom_val_app_unit_tmul`:
  for a morphism of ringed sites `f`, an identification `α : f^* ≅ L` and units `η` carried by
  `α⁻¹` to the unit of `f^* ⊣ f_*`, Stacks 03EL read through `α` sends `η(x ⊗ y)` to
  `η x ⊗ η y`.
* `AlgebraicGeometry.RingedSite.HomGeneral.tensorCounitComposite` and
  `tensorCounitComposite_val_app_unit_tmul`: **the lax comparison
  `P𝓜 ⊗ P𝓝 ⟶ P(𝓜 ⊗ 𝓝)` of a presentation `L ⊣ P` of `f^* ⊣ f_*` sends `x ⊗ y` to `x ⊗ y`**;
  `tensorCounitComposite_leftAdjointUniq_val_app_unit_tmul` is the case of the identification
  of the pullback by uniqueness of left adjoints
  (`pullbackModulesToposIsoGeneral_trans_leftAdjointUniq_inv_app_val_app_unit`).
* `AlgebraicGeometry.SmallEtale.pullbackTensorIsoTransport_hom_val_app_unit_tmul`: the case of
  `ε` and the associated-module adjunction.
* `AlgebraicGeometry.SmallEtale.restrictModuleTensorIso_inv_val_app_unit_tmul`: **the inverse of
  `AlgebraicGeometry.SmallEtale.restrictModuleTensorIso` sends `x ⊗ y` to `x ⊗ y`.**

**No `@[stacks]` attribute.** Tags 03EL, 03DU and 03D7 are registered on the declarations this
file computes with; the statements here are their values on sections.

## References

* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
* [Stacks Project, Tag 070R](https://stacks.math.columbia.edu/tag/070R)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open Stacks.Sheaves.RingedToposModules Stacks.PresheafOfModules.ChangeOfRings
open scoped TensorProduct

universe u

namespace Stacks.SheafOfModules

section Transport

universe w w' v u₁ v' u'

variable {X : AlgebraicGeometry.RingedTopos.{v, u₁, w}}
    {Y : AlgebraicGeometry.RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
  (f : Stacks.Sheaves.RingedToposModules.RingedToposHom X Y)
  {L : _root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O) ⥤
    _root_.SheafOfModules.{w} (Tensor.ringSheaf X.O)}
  (α : f.pullbackModules ≅ L)

/-- The comparison of Stacks 03EL read through an identification `α` of the pullback, on
sections: `α⁻¹`, then the comparison, then `α ⊗ α`. -/
theorem pullbackTensorIsoTransport_hom_val_app
    (M N : _root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O)) (U : X.Cᵒᵖ)
    (z : (L.obj (((Tensor.sheafTensor Y.O).obj M).obj N)).val.obj U) :
    (pullbackTensorIsoTransport f α M N).hom.val.app U z =
      ((Functor.uncurry.obj (Tensor.sheafTensor X.O)).map
          ((α.hom.app M, α.hom.app N) : (_, _) ⟶ (_, _))).val.app U
        (((pullbackTensorIso f).hom.app (M, N)).val.app U ((α.inv.app _).val.app U z)) :=
  rfl

omit [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [Y.J.HasSheafCompose (forget RingCat.{w'})] [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [HasWeakSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
  [X.J.HasSheafCompose (forget RingCat.{w})] [X.J.HasSheafCompose (forget AddCommGrpCat.{w})] in
/-- The tensor product of two morphisms of sheaves of modules on the sheafification-unit image of a
pure tensor, with the scalar ring of the pure tensor spelled through `forget₂`. -/
theorem sheafTensor_uncurry_map_val_app_unit_tmul_forget₂
    {A₁ A₂ B₁ B₂ : _root_.SheafOfModules.{w} (Tensor.ringSheaf X.O)} (f₁ : A₁ ⟶ A₂)
    (f₂ : B₁ ⟶ B₂) (U : X.Cᵒᵖ) (x : A₁.val.obj U) (y : B₁.val.obj U) :
    _root_.PresheafOfModules.Hom.app ((Functor.uncurry.obj (Tensor.sheafTensor X.O)).map
        ((f₁, f₂) : ((A₁, B₁) : _ × _) ⟶ (A₂, B₂))).val U
      (_root_.PresheafOfModules.Hom.app ((PresheafOfModules.sheafificationAdjunction
          (R := Tensor.ringSheaf X.O) (𝟙 (Tensor.ringSheaf X.O).obj)).unit.app
        (PresheafOfModules.tensorObj (O := X.O.obj) A₁.val B₁.val)) U
        (x ⊗ₜ[(X.O.obj ⋙ forget₂ CommRingCat RingCat).obj U] y)) =
      _root_.PresheafOfModules.Hom.app ((PresheafOfModules.sheafificationAdjunction
          (R := Tensor.ringSheaf X.O) (𝟙 (Tensor.ringSheaf X.O).obj)).unit.app
        (PresheafOfModules.tensorObj (O := X.O.obj) A₂.val B₂.val)) U
        (f₁.val.app U x ⊗ₜ[(X.O.obj ⋙ forget₂ CommRingCat RingCat).obj U] f₂.val.app U y) :=
  Tensor.sheafTensor_uncurry_map_val_app_unit_tmul X.O f₁ f₂ U x y

omit [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [Y.J.HasSheafCompose (forget RingCat.{w'})] [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [HasWeakSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
  [X.J.HasSheafCompose (forget RingCat.{w})] [X.J.HasSheafCompose (forget AddCommGrpCat.{w})] in
/-- Tensoring on the left by a sheaf of modules, applied to a morphism, on the
sheafification-unit image of a pure tensor. -/
theorem sheafTensor_obj_map_val_app_unit_tmul_forget₂
    {A B₁ B₂ : _root_.SheafOfModules.{w} (Tensor.ringSheaf X.O)} (g : B₁ ⟶ B₂) (U : X.Cᵒᵖ)
    (x : A.val.obj U) (y : B₁.val.obj U) {y' : B₂.val.obj U} (hy : g.val.app U y = y') :
    _root_.PresheafOfModules.Hom.app (((Tensor.sheafTensor X.O).obj A).map g).val U
      (_root_.PresheafOfModules.Hom.app ((PresheafOfModules.sheafificationAdjunction
          (R := Tensor.ringSheaf X.O) (𝟙 (Tensor.ringSheaf X.O).obj)).unit.app
        (PresheafOfModules.tensorObj (O := X.O.obj) A.val B₁.val)) U
        (x ⊗ₜ[(X.O.obj ⋙ forget₂ CommRingCat RingCat).obj U] y)) =
      _root_.PresheafOfModules.Hom.app ((PresheafOfModules.sheafificationAdjunction
          (R := Tensor.ringSheaf X.O) (𝟙 (Tensor.ringSheaf X.O).obj)).unit.app
        (PresheafOfModules.tensorObj (O := X.O.obj) A.val B₂.val)) U
        (x ⊗ₜ[(X.O.obj ⋙ forget₂ CommRingCat RingCat).obj U] y') := by
  subst hy
  have e : ((Tensor.sheafTensor X.O).obj A).map g =
      (Functor.uncurry.obj (Tensor.sheafTensor X.O)).map
        ((𝟙 A, g) : ((A, B₁) : _ × _) ⟶ (A, B₂)) := by
    simp only [Functor.uncurry_obj_map, CategoryTheory.Functor.map_id, NatTrans.id_app,
      Category.id_comp]
  rw [e]
  exact sheafTensor_uncurry_map_val_app_unit_tmul_forget₂ (𝟙 A) g U x y

omit [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [Y.J.HasSheafCompose (forget RingCat.{w'})] [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [HasWeakSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
  [X.J.HasSheafCompose (forget RingCat.{w})] [X.J.HasSheafCompose (forget AddCommGrpCat.{w})] in
/-- Tensoring on the right by a sheaf of modules, applied to a morphism, on the
sheafification-unit image of a pure tensor. -/
theorem sheafTensor_map_app_val_app_unit_tmul_forget₂
    {A₁ A₂ B : _root_.SheafOfModules.{w} (Tensor.ringSheaf X.O)} (g : A₁ ⟶ A₂) (U : X.Cᵒᵖ)
    (x : A₁.val.obj U) (y : B.val.obj U) {x' : A₂.val.obj U} (hx : g.val.app U x = x') :
    _root_.PresheafOfModules.Hom.app (((Tensor.sheafTensor X.O).map g).app B).val U
      (_root_.PresheafOfModules.Hom.app ((PresheafOfModules.sheafificationAdjunction
          (R := Tensor.ringSheaf X.O) (𝟙 (Tensor.ringSheaf X.O).obj)).unit.app
        (PresheafOfModules.tensorObj (O := X.O.obj) A₁.val B.val)) U
        (x ⊗ₜ[(X.O.obj ⋙ forget₂ CommRingCat RingCat).obj U] y)) =
      _root_.PresheafOfModules.Hom.app ((PresheafOfModules.sheafificationAdjunction
          (R := Tensor.ringSheaf X.O) (𝟙 (Tensor.ringSheaf X.O).obj)).unit.app
        (PresheafOfModules.tensorObj (O := X.O.obj) A₂.val B.val)) U
        (x' ⊗ₜ[(X.O.obj ⋙ forget₂ CommRingCat RingCat).obj U] y) := by
  subst hx
  have e : ((Tensor.sheafTensor X.O).map g).app B =
      (Functor.uncurry.obj (Tensor.sheafTensor X.O)).map
        ((g, 𝟙 B) : ((A₁, B) : _ × _) ⟶ (A₂, B)) := by
    simp only [Functor.uncurry_obj_map, CategoryTheory.Functor.map_id, Category.comp_id]
  rw [e]
  exact sheafTensor_uncurry_map_val_app_unit_tmul_forget₂ g (𝟙 B) U x y

end Transport

/-- Two tensored morphisms applied one after the other to the sheafification-unit image of a pure
tensor: `(g₁ ⊗ 𝟙) ∘ (𝟙 ⊗ g₂)` sends the image of `a ⊗ b` to the image of `g₁ a ⊗ g₂ b`. -/
private theorem sheafTensor_map_obj_map_val_app_unit_tmul_forget₂.{w, v, u₁}
    {X : AlgebraicGeometry.RingedTopos.{v, u₁, w}}
    [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    {A B M N : _root_.SheafOfModules.{w} (Tensor.ringSheaf X.O)} (g₁ : A ⟶ M) (g₂ : B ⟶ N)
    (U : X.Cᵒᵖ) (a : A.val.obj U) (b : B.val.obj U) {x : M.val.obj U} {y : N.val.obj U}
    (hx : g₁.val.app U a = x) (hy : g₂.val.app U b = y) :
    _root_.PresheafOfModules.Hom.app (((Tensor.sheafTensor X.O).map g₁).app N).val U
      (_root_.PresheafOfModules.Hom.app (((Tensor.sheafTensor X.O).obj A).map g₂).val U
        (_root_.PresheafOfModules.Hom.app ((PresheafOfModules.sheafificationAdjunction
            (R := Tensor.ringSheaf X.O) (𝟙 (Tensor.ringSheaf X.O).obj)).unit.app
          (PresheafOfModules.tensorObj (O := X.O.obj) A.val B.val)) U
          (a ⊗ₜ[(X.O.obj ⋙ forget₂ CommRingCat RingCat).obj U] b))) =
      _root_.PresheafOfModules.Hom.app ((PresheafOfModules.sheafificationAdjunction
          (R := Tensor.ringSheaf X.O) (𝟙 (Tensor.ringSheaf X.O).obj)).unit.app
        (PresheafOfModules.tensorObj (O := X.O.obj) M.val N.val)) U
        (x ⊗ₜ[(X.O.obj ⋙ forget₂ CommRingCat RingCat).obj U] y) :=
  (congrArg (_root_.PresheafOfModules.Hom.app (((Tensor.sheafTensor X.O).map g₁).app N).val U)
    (sheafTensor_obj_map_val_app_unit_tmul_forget₂ g₂ U a b hy)).trans
    (sheafTensor_map_app_val_app_unit_tmul_forget₂ g₁ U a y hx)

end Stacks.SheafOfModules

namespace AlgebraicGeometry.RingedSite

section TransportUnit

open Stacks.SheafOfModules

universe uX vX uY vY w

variable {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}} (f : HomGeneral X Y)
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X.J.HasSheafCompose (forget CommRingCat.{w})] [Y.J.HasSheafCompose (forget CommRingCat.{w})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})] [Y.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  {L : _root_.SheafOfModules.{w} (Tensor.ringSheaf (toRingedTopos Y).O) ⥤
    _root_.SheafOfModules.{w} (Tensor.ringSheaf (toRingedTopos X).O)}
  (α : f.toRingedToposHom.toRingedToposModulesHom.pullbackModules ≅ L)
  (η : ∀ (F : _root_.SheafOfModules.{w} (Tensor.ringSheaf (toRingedTopos Y).O)) (V : Y.Cᵒᵖ),
    F.val.obj V → (L.obj F).val.obj (f.u.op.obj V))
  (hη : ∀ (F : _root_.SheafOfModules.{w} (Tensor.ringSheaf (toRingedTopos Y).O)) (V : Y.Cᵒᵖ)
    (x : F.val.obj V), (α.inv.app F).val.app (f.u.op.obj V) (η F V x) =
      ((pullbackAdjPushforwardModules f.toRingedToposHom.toRingedToposModulesHom).unit.app
        F).val.app V x)

omit [X.J.HasSheafCompose (forget CommRingCat.{w})] [Y.J.HasSheafCompose (forget CommRingCat.{w})]
  [HasWeakSheafify Y.J AddCommGrpCat.{w}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
include hη in
/-- A family of units `η` for an identification `α` of the pullback is carried by `α` from the
unit of `f^* ⊣ f_*`. -/
theorem HomGeneral.alpha_hom_app_val_app_unit
    (F : _root_.SheafOfModules.{w} (Tensor.ringSheaf (toRingedTopos Y).O)) (V : Y.Cᵒᵖ)
    (x : F.val.obj V) :
    (α.hom.app F).val.app (f.u.op.obj V)
        (((pullbackAdjPushforwardModules f.toRingedToposHom.toRingedToposModulesHom).unit.app
          F).val.app V x) = η F V x := by
  rw [← hη F V x]
  exact congrArg (fun k => k.val.app (f.u.op.obj V) (η F V x)) (α.inv_hom_id_app F)

omit [X.J.HasSheafCompose (forget CommRingCat.{w})]
  [Y.J.HasSheafCompose (forget CommRingCat.{w})] in
include hη in
/-- **Stacks 03EL read through an identification of the pullback carries a pure tensor to a pure
tensor**: if `α : f^* ≅ L` and `η` is a family of units for `L` carried by `α⁻¹` to the unit of
`f^* ⊣ f_*`, then the comparison `L(F ⊗ G) ⟶ L F ⊗ L G` sends `η(x ⊗ y)` to `η x ⊗ η y`. -/
theorem HomGeneral.pullbackTensorIsoTransport_hom_val_app_unit_tmul
    (F G : _root_.SheafOfModules.{w} (Tensor.ringSheaf (toRingedTopos Y).O)) (V : Y.Cᵒᵖ)
    (x : F.val.obj V) (y : G.val.obj V) :
    (pullbackTensorIsoTransport f.toRingedToposHom.toRingedToposModulesHom α F G).hom.val.app
        (f.u.op.obj V)
      (η (((Tensor.sheafTensor (toRingedTopos Y).O).obj F).obj G) V
        (((PresheafOfModules.sheafificationAdjunction
            (R := Stacks.Sheaves.RingedToposModules.commRingSheaf Y.J (toRingedTopos Y).O.obj
              (Tensor.ringSheaf (toRingedTopos Y).O).property) (𝟙 _)).unit.app
          (F.val ⊗ G.val)).app V
          (x ⊗ₜ[(ringPresheaf (toRingedTopos Y).O.obj).obj V] y))) =
      _root_.PresheafOfModules.Hom.app ((PresheafOfModules.sheafificationAdjunction
          (R := Tensor.ringSheaf (toRingedTopos X).O)
          (𝟙 (Tensor.ringSheaf (toRingedTopos X).O).obj)).unit.app
        (PresheafOfModules.tensorObj (O := (toRingedTopos X).O.obj) (L.obj F).val (L.obj G).val))
        (f.u.op.obj V)
        (η F V x ⊗ₜ[((toRingedTopos X).O.obj ⋙ forget₂ CommRingCat RingCat).obj
          (f.u.op.obj V)] η G V y) := by
  refine (pullbackTensorIsoTransport_hom_val_app f.toRingedToposHom.toRingedToposModulesHom α
    F G (f.u.op.obj V) _).trans ?_
  have h1 : (α.inv.app ((Functor.uncurry.obj (Tensor.sheafTensor (toRingedTopos Y).O)).obj
        (F, G))).val.app (f.u.op.obj V)
      (η (((Tensor.sheafTensor (toRingedTopos Y).O).obj F).obj G) V
        (((PresheafOfModules.sheafificationAdjunction
            (R := Stacks.Sheaves.RingedToposModules.commRingSheaf Y.J (toRingedTopos Y).O.obj
              (Tensor.ringSheaf (toRingedTopos Y).O).property) (𝟙 _)).unit.app
          (F.val ⊗ G.val)).app V
          (x ⊗ₜ[(ringPresheaf (toRingedTopos Y).O.obj).obj V] y))) =
      ((pullbackAdjPushforwardModules f.toRingedToposHom.toRingedToposModulesHom).unit.app
          (((Functor.uncurry.obj (Tensor.sheafTensor (toRingedTopos Y).O))).obj (F, G))).val.app V
        (((PresheafOfModules.sheafificationAdjunction
            (R := Stacks.Sheaves.RingedToposModules.commRingSheaf Y.J (toRingedTopos Y).O.obj
              (Tensor.ringSheaf (toRingedTopos Y).O).property) (𝟙 _)).unit.app
          (F.val ⊗ G.val)).app V
          (x ⊗ₜ[(ringPresheaf (toRingedTopos Y).O.obj).obj V] y)) :=
    hη _ V _
  rw [h1, f.pullbackTensorIso_hom_val_app_unit_tmul F G V x y]
  refine (sheafTensor_uncurry_map_val_app_unit_tmul_forget₂ (X := toRingedTopos X)
    (α.hom.app F) (α.hom.app G) (f.u.op.obj V) _ _).trans ?_
  rw [f.alpha_hom_app_val_app_unit α η hη F V x, f.alpha_hom_app_val_app_unit α η hη G V y]

omit hη in
/-- **The lax comparison of a presentation of `f_*`.** Let `adj : L ⊣ P` present `f^* ⊣ f_*`,
with `P` the direct image along the functor of sites of `f`, and `α : f^* ≅ L`. For
`𝒪_X`-modules `𝓜`, `𝓝` this is the composite

`P𝓜 ⊗ P𝓝 ⟶ P L(P𝓜 ⊗ P𝓝) ⟶ P(L P𝓜 ⊗ L P𝓝) ⟶ P(𝓜 ⊗ 𝓝)`

of the unit, Stacks 03EL read through `α`, and the two counits. -/
def HomGeneral.tensorCounitComposite
    {φ : Tensor.ringSheaf (toRingedTopos Y).O ⟶
      (f.u.sheafPushforwardContinuous RingCat.{w} Y.J X.J).obj
        (Tensor.ringSheaf (toRingedTopos X).O)}
    (adj : L ⊣ (_root_.SheafOfModules.pushforward.{w} φ))
    (M N : _root_.SheafOfModules.{w} (Tensor.ringSheaf (toRingedTopos X).O)) :
    ((Tensor.sheafTensor (toRingedTopos Y).O).obj
        ((_root_.SheafOfModules.pushforward.{w} φ).obj M)).obj
        ((_root_.SheafOfModules.pushforward.{w} φ).obj N) ⟶
      (_root_.SheafOfModules.pushforward.{w} φ).obj
        (((Tensor.sheafTensor (toRingedTopos X).O).obj M).obj N) :=
  adj.unit.app (((Tensor.sheafTensor (toRingedTopos Y).O).obj
      ((_root_.SheafOfModules.pushforward.{w} φ).obj M)).obj
        ((_root_.SheafOfModules.pushforward.{w} φ).obj N)) ≫
    (_root_.SheafOfModules.pushforward.{w} φ).map
      ((pullbackTensorIsoTransport f.toRingedToposHom.toRingedToposModulesHom α
        ((_root_.SheafOfModules.pushforward.{w} φ).obj M)
        ((_root_.SheafOfModules.pushforward.{w} φ).obj N)).hom ≫
      ((Tensor.sheafTensor (toRingedTopos X).O).obj
          (L.obj ((_root_.SheafOfModules.pushforward.{w} φ).obj M))).map
        (adj.counit.app N) ≫
      ((Tensor.sheafTensor (toRingedTopos X).O).map (adj.counit.app M)).app N)

omit [X.J.HasSheafCompose (forget CommRingCat.{w})] [Y.J.HasSheafCompose (forget CommRingCat.{w})]
  hη in
/-- **The lax comparison of a presentation of `f_*` on a pure tensor.** Let `adj : L ⊣ P` present
`f^* ⊣ f_*`, with `P` the direct image along the functor of sites `u` of `f` and `α : f^* ≅ L`
carrying the unit of `adj` to the unit of `f^* ⊣ f_*`. For `𝒪_X`-modules `𝓜`, `𝓝` the composite

`P𝓜 ⊗ P𝓝 ⟶ P L(P𝓜 ⊗ P𝓝) ⟶ P(L P𝓜 ⊗ L P𝓝) ⟶ P(𝓜 ⊗ 𝓝)`

(the unit, Stacks 03EL read through `α`, and the two counits) sends `x ⊗ y` to `x ⊗ y`: both are
local sections over `u(V)`. -/
theorem HomGeneral.tensorCounitComposite_val_app_unit_tmul
    {φ : Tensor.ringSheaf (toRingedTopos Y).O ⟶
      (f.u.sheafPushforwardContinuous RingCat.{w} Y.J X.J).obj
        (Tensor.ringSheaf (toRingedTopos X).O)}
    (adj : L ⊣ _root_.SheafOfModules.pushforward.{w} φ)
    (hadj : ∀ (F : _root_.SheafOfModules.{w} (Tensor.ringSheaf (toRingedTopos Y).O))
      (V : Y.Cᵒᵖ) (x : F.val.obj V), (α.inv.app F).val.app (f.u.op.obj V)
        ((adj.unit.app F).val.app V x) =
        ((pullbackAdjPushforwardModules f.toRingedToposHom.toRingedToposModulesHom).unit.app
          F).val.app V x)
    (M N : _root_.SheafOfModules.{w} (Tensor.ringSheaf (toRingedTopos X).O)) (V : Y.Cᵒᵖ)
    (x : ((_root_.SheafOfModules.pushforward.{w} φ).obj M).val.obj V)
    (y : ((_root_.SheafOfModules.pushforward.{w} φ).obj N).val.obj V) :
    (f.tensorCounitComposite α adj M N).val.app V
            (_root_.PresheafOfModules.Hom.app ((PresheafOfModules.sheafificationAdjunction
                (R := Tensor.ringSheaf (toRingedTopos Y).O)
                (𝟙 (Tensor.ringSheaf (toRingedTopos Y).O).obj)).unit.app
              (PresheafOfModules.tensorObj (O := (toRingedTopos Y).O.obj)
                ((_root_.SheafOfModules.pushforward.{w} φ).obj M).val
                ((_root_.SheafOfModules.pushforward.{w} φ).obj N).val)) V
              (x ⊗ₜ[((toRingedTopos Y).O.obj ⋙ forget₂ CommRingCat RingCat).obj V] y)) =
      _root_.PresheafOfModules.Hom.app ((PresheafOfModules.sheafificationAdjunction
          (R := Tensor.ringSheaf (toRingedTopos X).O)
          (𝟙 (Tensor.ringSheaf (toRingedTopos X).O).obj)).unit.app
        (PresheafOfModules.tensorObj (O := (toRingedTopos X).O.obj) M.val N.val))
        (f.u.op.obj V)
        (x ⊗ₜ[((toRingedTopos X).O.obj ⋙ forget₂ CommRingCat RingCat).obj (f.u.op.obj V)] y) := by
  change (((Tensor.sheafTensor (toRingedTopos X).O).map (adj.counit.app M)).app N).val.app
      (f.u.op.obj V)
      ((((Tensor.sheafTensor (toRingedTopos X).O).obj
          (L.obj ((_root_.SheafOfModules.pushforward.{w} φ).obj M))).map
        (adj.counit.app N)).val.app (f.u.op.obj V)
        ((pullbackTensorIsoTransport f.toRingedToposHom.toRingedToposModulesHom α
            ((_root_.SheafOfModules.pushforward.{w} φ).obj M)
            ((_root_.SheafOfModules.pushforward.{w} φ).obj N)).hom.val.app (f.u.op.obj V)
          ((adj.unit.app (((Tensor.sheafTensor (toRingedTopos Y).O).obj
              ((_root_.SheafOfModules.pushforward.{w} φ).obj M)).obj
              ((_root_.SheafOfModules.pushforward.{w} φ).obj N))).val.app V
            (((PresheafOfModules.sheafificationAdjunction
                (R := Stacks.Sheaves.RingedToposModules.commRingSheaf Y.J (toRingedTopos Y).O.obj
                  (Tensor.ringSheaf (toRingedTopos Y).O).property) (𝟙 _)).unit.app
              (((_root_.SheafOfModules.pushforward.{w} φ).obj M).val ⊗
                ((_root_.SheafOfModules.pushforward.{w} φ).obj N).val)).app V
              (x ⊗ₜ[(ringPresheaf (toRingedTopos Y).O.obj).obj V] y))))) = _
  have hK := f.pullbackTensorIsoTransport_hom_val_app_unit_tmul α
    (fun F V x => (adj.unit.app F).val.app V x) hadj
    ((_root_.SheafOfModules.pushforward.{w} φ).obj M)
    ((_root_.SheafOfModules.pushforward.{w} φ).obj N) V x y
  rw [hK]
  exact sheafTensor_map_obj_map_val_app_unit_tmul_forget₂ (X := toRingedTopos X)
    (adj.counit.app M) (adj.counit.app N) (f.u.op.obj V) _ _
    (congrArg (fun k => k.val.app V x) (adj.right_triangle_components M))
    (congrArg (fun k => k.val.app V y) (adj.right_triangle_components N))

omit [X.J.HasSheafCompose (forget CommRingCat.{w})] [Y.J.HasSheafCompose (forget CommRingCat.{w})]
  [HasWeakSheafify Y.J AddCommGrpCat.{w}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- **Any presentation of `f^* ⊣ f_*` with the direct image of the functor of sites satisfies the
unit hypothesis**: if `adj : L ⊣ f_*` and `α` is the identification of the pullback of the
morphism of ringed topoi with `L` by uniqueness of left adjoints, then `α⁻¹` carries the unit of
`adj` to the unit of the adjunction of the morphism of ringed topoi, on sections. -/
theorem HomGeneral.pullbackModulesToposIsoGeneral_trans_leftAdjointUniq_inv_app_val_app_unit
    [EssentiallySmall.{w} Y.C] [LocallySmall.{w} X.C]
    {L' : _root_.SheafOfModules.{w} (Tensor.ringSheaf (toRingedTopos Y).O) ⥤
      _root_.SheafOfModules.{w} (Tensor.ringSheaf (toRingedTopos X).O)}
    (adj : L' ⊣ f.toRingedToposSiteHom.pushforwardTopos)
    (F : _root_.SheafOfModules.{w} (Tensor.ringSheaf (toRingedTopos Y).O)) (V : Y.Cᵒᵖ)
    (x : F.val.obj V) :
    ((f.pullbackModulesToposIsoGeneral ≪≫ Adjunction.leftAdjointUniq
        f.toRingedToposSiteHom.pullbackPushforwardAdjunctionToposGeneral adj).inv.app F).val.app
        (f.u.op.obj V) ((adj.unit.app F).val.app V x) =
      ((pullbackAdjPushforwardModules f.toRingedToposHom.toRingedToposModulesHom).unit.app
        F).val.app V x := by
  have h := congrArg (fun k => k.val.app V x) (Adjunction.unit_leftAdjointUniq_hom_app adj
    f.toRingedToposSiteHom.pullbackPushforwardAdjunctionToposGeneral F)
  have e : ((f.pullbackModulesToposIsoGeneral ≪≫ Adjunction.leftAdjointUniq
        f.toRingedToposSiteHom.pullbackPushforwardAdjunctionToposGeneral adj).inv.app F).val.app
        (f.u.op.obj V) ((adj.unit.app F).val.app V x) =
      (f.pullbackModulesToposIsoGeneral.inv.app F).val.app (f.u.op.obj V)
        (((Adjunction.leftAdjointUniq adj
          f.toRingedToposSiteHom.pullbackPushforwardAdjunctionToposGeneral).hom.app F).val.app
            (f.u.op.obj V) ((adj.unit.app F).val.app V x)) := by
    rw [Iso.trans_inv, NatTrans.comp_app, Adjunction.leftAdjointUniq_inv_app]
    rfl
  refine e.trans ?_
  refine (congrArg ((f.pullbackModulesToposIsoGeneral.inv.app F).val.app (f.u.op.obj V)) h).trans
    ?_
  exact f.pullbackModulesToposIsoGeneral_inv_app_val_app_unit F V x

omit [X.J.HasSheafCompose (forget CommRingCat.{w})]
  [Y.J.HasSheafCompose (forget CommRingCat.{w})] in
/-- `AlgebraicGeometry.RingedSite.HomGeneral.tensorCounitComposite_val_app_unit_tmul` for a
presentation `adj₂ : L ⊣ P` of `f^* ⊣ f_*` whose unit agrees on sections with that of a
presentation `adj₁ : L ⊣ f_*` by the direct image of the functor of sites, the identification of
the pullback being the one given by uniqueness of left adjoints. -/
theorem HomGeneral.tensorCounitComposite_leftAdjointUniq_val_app_unit_tmul
    [EssentiallySmall.{w} Y.C] [LocallySmall.{w} X.C]
    (adj₁ : L ⊣ f.toRingedToposSiteHom.pushforwardTopos)
    {φ : Tensor.ringSheaf (toRingedTopos Y).O ⟶
      (f.u.sheafPushforwardContinuous RingCat.{w} Y.J X.J).obj
        (Tensor.ringSheaf (toRingedTopos X).O)}
    (adj₂ : L ⊣ _root_.SheafOfModules.pushforward.{w} φ)
    (h₁₂ : ∀ (F : _root_.SheafOfModules.{w} (Tensor.ringSheaf (toRingedTopos Y).O))
      (V : Y.Cᵒᵖ) (x : F.val.obj V),
      (adj₂.unit.app F).val.app V x = (adj₁.unit.app F).val.app V x)
    (M N : _root_.SheafOfModules.{w} (Tensor.ringSheaf (toRingedTopos X).O)) (V : Y.Cᵒᵖ)
    (x : ((_root_.SheafOfModules.pushforward.{w} φ).obj M).val.obj V)
    (y : ((_root_.SheafOfModules.pushforward.{w} φ).obj N).val.obj V) :
    type_of% (f.tensorCounitComposite_val_app_unit_tmul
      (f.pullbackModulesToposIsoGeneral ≪≫ Adjunction.leftAdjointUniq
        f.toRingedToposSiteHom.pullbackPushforwardAdjunctionToposGeneral adj₁)
      adj₂
      (fun F V x => (congrArg (((f.pullbackModulesToposIsoGeneral ≪≫ Adjunction.leftAdjointUniq
          f.toRingedToposSiteHom.pullbackPushforwardAdjunctionToposGeneral adj₁).inv.app F).val.app
            (f.u.op.obj V)) (h₁₂ F V x)).trans
        (f.pullbackModulesToposIsoGeneral_trans_leftAdjointUniq_inv_app_val_app_unit adj₁ F V x))
      M N V x y) :=
  f.tensorCounitComposite_val_app_unit_tmul
    (f.pullbackModulesToposIsoGeneral ≪≫ Adjunction.leftAdjointUniq
      f.toRingedToposSiteHom.pullbackPushforwardAdjunctionToposGeneral adj₁)
    adj₂
    (fun F V x => (congrArg (((f.pullbackModulesToposIsoGeneral ≪≫ Adjunction.leftAdjointUniq
        f.toRingedToposSiteHom.pullbackPushforwardAdjunctionToposGeneral adj₁).inv.app F).val.app
          (f.u.op.obj V)) (h₁₂ F V x)).trans
      (f.pullbackModulesToposIsoGeneral_trans_leftAdjointUniq_inv_app_val_app_unit adj₁ F V x))
    M N V x y

end TransportUnit

end AlgebraicGeometry.RingedSite

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The units of the two presentations of `ε^* ⊣ ε_*` agree on sections**: the unit of the
associated-module adjunction, carried back by the identification `pullbackModulesToZariskiIso` of
the pullback along the morphism of ringed topoi `ε` with the associated-module functor, is the
unit of the adjunction of `ε`. -/
theorem pullbackModulesToZariskiIso_inv_app_val_app_unit (F : S.Modules)
    (V : (S.zariskiRingedSite).Cᵒᵖ) (x : F.val.obj V) :
    ((pullbackModulesToZariskiIso B S hS).inv.app F).val.app
        ((toZariskiRingedSiteHom B S hS).u.op.obj V)
        (((associatedModuleAdjunction B S hS).unit.app F).val.app V x) =
      ((pullbackAdjPushforwardModules (toZariskiRingedToposModulesHom B S hS)).unit.app
          F).val.app V x :=
  (toZariskiRingedSiteHom B S hS).pullbackModulesToposIsoGeneral_inv_app_val_app_unit F V x

/-- The identification `pullbackModulesToZariskiIso` carries the unit of the adjunction of `ε` to
the unit of the associated-module adjunction, on sections. -/
theorem pullbackModulesToZariskiIso_hom_app_val_app_unit (F : S.Modules)
    (V : (S.zariskiRingedSite).Cᵒᵖ) (x : F.val.obj V) :
    ((pullbackModulesToZariskiIso B S hS).hom.app F).val.app
        ((toZariskiRingedSiteHom B S hS).u.op.obj V)
        (((pullbackAdjPushforwardModules (toZariskiRingedToposModulesHom B S hS)).unit.app
          F).val.app V x) =
      ((associatedModuleAdjunction B S hS).unit.app F).val.app V x := by
  refine (congrArg (((pullbackModulesToZariskiIso B S hS).hom.app F).val.app
    ((toZariskiRingedSiteHom B S hS).u.op.obj V))
    (pullbackModulesToZariskiIso_inv_app_val_app_unit B S hS F V x).symm).trans ?_
  exact congrArg (fun k => k.val.app ((toZariskiRingedSiteHom B S hS).u.op.obj V)
      (((associatedModuleAdjunction B S hS).unit.app F).val.app V x))
    ((pullbackModulesToZariskiIso B S hS).inv_hom_id_app F)

/-- **Stacks 03EL at `ε`, read through the associated-module functor, on a pure tensor**: the
comparison `(F ⊗ G)^a ⟶ F^a ⊗ G^a` sends the unit image of `x ⊗ y` to `η x ⊗ η y`, where `η` is
the unit of the associated-module adjunction.

The statement is written through `type_of%` of the instance of
`AlgebraicGeometry.RingedSite.HomGeneral.pullbackTensorIsoTransport_hom_val_app_unit_tmul` at `ε`,
so that it is that statement verbatim: restating it with the modules at the spelling of
`AlgebraicGeometry.SmallEtale.associatedModule` asks the elaborator to identify the two structure
sheaves of the small étale site, which exhausts the heartbeat budget at `whnf`. -/
theorem pullbackTensorIsoTransport_hom_val_app_unit_tmul
    (F G : _root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf S.zariskiRingedSite.toRingedTopos.O))
    (V : (S.zariskiRingedSite).Cᵒᵖ) (x : F.val.obj V) (y : G.val.obj V) :
    type_of% ((toZariskiRingedSiteHom B S hS).pullbackTensorIsoTransport_hom_val_app_unit_tmul
      (pullbackModulesToZariskiIso B S hS)
      (fun F V x => ((associatedModuleAdjunction B S hS).unit.app F).val.app V x)
      (fun F V x => pullbackModulesToZariskiIso_inv_app_val_app_unit B S hS F V x) F G V x y) :=
  (toZariskiRingedSiteHom B S hS).pullbackTensorIsoTransport_hom_val_app_unit_tmul
    (pullbackModulesToZariskiIso B S hS)
    (fun F V x => ((associatedModuleAdjunction B S hS).unit.app F).val.app V x)
    (fun F V x => pullbackModulesToZariskiIso_inv_app_val_app_unit B S hS F V x) F G V x y

/-- **The inverse of `AlgebraicGeometry.SmallEtale.restrictModuleTensorIso` on a pure tensor**:
for local sections `x` of `𝓜|_{S_Zar}` and `y` of `𝓝|_{S_Zar}` over a Zariski open `V`, the
comparison `𝓜|_{S_Zar} ⊗ 𝓝|_{S_Zar} ⟶ (𝓜 ⊗ 𝓝)|_{S_Zar}` sends `x ⊗ y` to `x ⊗ y`, the latter
a local section of `𝓜 ⊗ 𝓝` over `V` read as an étale open. -/
theorem restrictModuleTensorIso_inv_val_app_unit_tmul
    (M N : SheafOfModules.{u} (structureSheaf B S hS))
    (hM : M.IsQuasicoherentOnSite) (hN : N.IsQuasicoherentOnSite)
    (V : (S.zariskiRingedSite).Cᵒᵖ) (x : ((restrictModule B S hS).obj M).val.obj V)
    (y : ((restrictModule B S hS).obj N).val.obj V) :
    (restrictModuleTensorIso B S hS M N hM hN).inv.val.app V
        (_root_.PresheafOfModules.Hom.app ((PresheafOfModules.sheafificationAdjunction
            (R := Stacks.SheafOfModules.Tensor.ringSheaf S.zariskiRingedSite.toRingedTopos.O)
            (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf
              S.zariskiRingedSite.toRingedTopos.O).obj)).unit.app
          (PresheafOfModules.tensorObj (O := S.zariskiRingedSite.toRingedTopos.O.obj)
            ((restrictModule B S hS).obj M).val ((restrictModule B S hS).obj N).val)) V
          (x ⊗ₜ[(S.zariskiRingedSite.toRingedTopos.O.obj ⋙ forget₂ CommRingCat RingCat).obj V]
            y)) =
      _root_.PresheafOfModules.Hom.app ((PresheafOfModules.sheafificationAdjunction
          (R := Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS).toRingedTopos.O)
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS).toRingedTopos.O).obj)).unit.app
        (PresheafOfModules.tensorObj (O := (smallEtaleRingedSite B S hS).toRingedTopos.O.obj)
          M.val N.val))
        ((toZariskiRingedSiteHom B S hS).u.op.obj V)
        (x ⊗ₜ[((smallEtaleRingedSite B S hS).toRingedTopos.O.obj ⋙
          forget₂ CommRingCat RingCat).obj ((toZariskiRingedSiteHom B S hS).u.op.obj V)] y) := by
  rw [restrictModuleTensorIso_inv_eq]
  have hK := pullbackTensorIsoTransport_hom_val_app_unit_tmul B S hS
    ((restrictModule B S hS).obj M) ((restrictModule B S hS).obj N) V x y
  change ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
      (smallEtaleRingedSite B S hS).toRingedTopos.O).map
        ((associatedModuleAdjunction B S hS).counit.app M)).app N)).val.app
          ((toZariskiRingedSiteHom B S hS).u.op.obj V)
      ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        (smallEtaleRingedSite B S hS).toRingedTopos.O).obj
          ((associatedModule B S hS).obj ((restrictModule B S hS).obj M))).map
        ((associatedModuleAdjunction B S hS).counit.app N)).val.app
          ((toZariskiRingedSiteHom B S hS).u.op.obj V)
        ((Stacks.SheafOfModules.pullbackTensorIsoTransport (toZariskiRingedToposModulesHom B S hS)
            (pullbackModulesToZariskiIso B S hS) ((restrictModule B S hS).obj M)
            ((restrictModule B S hS).obj N)).hom.val.app
          ((toZariskiRingedSiteHom B S hS).u.op.obj V)
          (((associatedModuleAdjunction B S hS).unit.app
            (((Stacks.SheafOfModules.Tensor.sheafTensor S.zariskiRingedSite.toRingedTopos.O).obj
              ((restrictModule B S hS).obj M)).obj ((restrictModule B S hS).obj N))).val.app V
            (((PresheafOfModules.sheafificationAdjunction
              (R := commRingSheaf S.zariskiRingedSite.J S.zariskiRingedSite.toRingedTopos.O.obj
                (Stacks.SheafOfModules.Tensor.ringSheaf
                  S.zariskiRingedSite.toRingedTopos.O).property) (𝟙 _)).unit.app
              (((restrictModule B S hS).obj M).val ⊗ ((restrictModule B S hS).obj N).val)).app V
              (x ⊗ₜ[(ringPresheaf S.zariskiRingedSite.toRingedTopos.O.obj).obj V] y))))) = _
  rw [hK]
  exact Stacks.SheafOfModules.sheafTensor_map_obj_map_val_app_unit_tmul_forget₂
    (X := (smallEtaleRingedSite B S hS).toRingedTopos)
    ((associatedModuleAdjunction B S hS).counit.app M)
    ((associatedModuleAdjunction B S hS).counit.app N) ((toZariskiRingedSiteHom B S hS).u.op.obj V)
    _ _ (congrArg (fun k => k.val.app V x)
      ((associatedModuleAdjunction B S hS).right_triangle_components M))
    (congrArg (fun k => k.val.app V y)
      ((associatedModuleAdjunction B S hS).right_triangle_components N))

end AlgebraicGeometry.SmallEtale

end
