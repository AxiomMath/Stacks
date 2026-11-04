module

public import StacksFrontier.AlgebraicGeometry.Modules.ZariskiRingedToposHom
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorIsoTransposeCharacterization
public import StacksFrontier.AlgebraicGeometry.PullbackTensor.StalkFormula
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.Invertible
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.ChartModuleTensor

/-!
# Stacks 03EL for the Zariski morphism of ringed topoi of a morphism of schemes

Let `g : X ⟶ Y` be a morphism of schemes. Two comparisons `g^*(F ⊗ G) ≅ g^*F ⊗ g^*G` are
available for `𝒪_Y`-modules `F` and `G`: the comparison of **Stacks 03EL** for the morphism of
ringed topoi `(X_Zar, 𝒪_X) ⟶ (Y_Zar, 𝒪_Y)` (`Stacks.SheafOfModules.pullbackTensorIso`, the chain of
bijections of the modules development), and the ringed-space comparison of **Stacks 01CD**
(`Stacks.RingedSpace.comparison`, the adjoint transpose of `x ⊗ y ↦ η x ⊗ η y`), which is the one
`Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso` is. This file proves that they agree,
once the four-field pullback is identified with the ringed-space one by
`AlgebraicGeometry.Scheme.Hom.zariskiPullbackModulesIso`.

## Main results

* `Stacks.SheafOfModules.pullbackTensorIsoTransport_hom_eq_of_pullbackTensorIso_hom_app`: a
  criterion for the comparison of Stacks 03EL read through an identification `α` of pullbacks.
* `AlgebraicGeometry.Scheme.Hom.pullbackTensorIso_hom_app_eq_zariskiComparisonTransport`: **the
  comparison of Stacks 03EL for the Zariski morphism is the comparison of Stacks 01CD**, read on
  the four-field pullbacks.
* `AlgebraicGeometry.Scheme.Hom.pullbackTensorIsoTransport_zariskiPullbackModulesIso_hom`,
  `pullbackTensorIsoTransport_zariskiPullbackModulesIso`,
  `pullbackTensorIsoTransport_zariskiPullbackModulesIso_eq_moduleLimits`: the same read through
  `zariskiPullbackModulesIso`, as an equality of morphisms and of isomorphisms, the last with
  `Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso`.

## Implementation notes

The proof is the uniqueness of the comparison of a left adjoint with the tensor product:
`Stacks.SheafOfModules.eq_pullbackTensorIso_hom_app_iff` characterizes the comparison of Stacks
03EL by the pairing of its transpose, and that pairing is computed for the transported Stacks 01CD
comparison from `Stacks.RingedSpace.comparisonTranspose_unit_tmul` and the comparison of the two
units, `AlgebraicGeometry.Scheme.Hom.zariskiPullbackModulesIso_inv_app_unit`.

The modules involved carry three spellings of their structure sheaves and of their tensor
products — the ringed topos `X.zariskiRingedSite.toRingedTopos`, the ringed space
`X.toRingedSpace` and the scheme. Each crossing between two spellings is made inside one closed
term (`comparisonTranspose_val_app_unit_tmul`, `zariskiPullbackModulesIso_inv_app_unit_sections`,
`homEquiv_zariskiPullbackModulesIso_inv_app_comp_zariskiComparisonTransport`,
`zariskiComparison`): letting a rewrite or a unification problem with metavariables cross them
exhausts the heartbeat budget at `whnf`. For the same reason the ringed-space adjunction
`Stacks.RingedSpace.pullbackAdjunction` is used throughout rather than
`AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction`, its definitional equal.

## References

* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 084D](https://stacks.math.columbia.edu/tag/084D)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace MonoidalCategory
open scoped TensorProduct
open Stacks.Sheaves.RingedToposModules

universe u

namespace Stacks.SheafOfModules.Tensor

open _root_.PresheafOfModules

variable {C : Type*} [Category C] {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{u})
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- The tensor product of two morphisms of sheaves of modules, on the sheafification-unit image
of a pure tensor of local sections. -/
theorem sheafTensor_uncurry_map_val_app_unit_tmul
    {A₁ A₂ B₁ B₂ : SheafOfModules.{u} (ringSheaf R)} (f₁ : A₁ ⟶ A₂) (f₂ : B₁ ⟶ B₂) (U : Cᵒᵖ)
    (x : A₁.val.obj U) (y : B₁.val.obj U) :
    _root_.PresheafOfModules.Hom.app ((Functor.uncurry.obj (sheafTensor R)).map
        ((f₁, f₂) : ((A₁, B₁) : _ × _) ⟶ (A₂, B₂))).val U
      (_root_.PresheafOfModules.Hom.app ((PresheafOfModules.sheafificationAdjunction
          (R := ringSheaf R) (𝟙 (ringSheaf R).obj)).unit.app
        (PresheafOfModules.tensorObj (O := R.obj) A₁.val B₁.val)) U (x ⊗ₜ y)) =
      _root_.PresheafOfModules.Hom.app ((PresheafOfModules.sheafificationAdjunction
          (R := ringSheaf R) (𝟙 (ringSheaf R).obj)).unit.app
        (PresheafOfModules.tensorObj (O := R.obj) A₂.val B₂.val)) U
        (_root_.PresheafOfModules.Hom.app f₁.val U x ⊗ₜ Hom.app f₂.val U y) := by
  refine (_root_.PresheafOfModules.hom_congr_apply'
    (congrArg (fun morphism => SheafOfModules.Hom.val morphism)
      (sheafTensor_uncurry_map R f₁ f₂)) U _).trans ?_
  exact (_root_.PresheafOfModules.unit_naturality_apply (α := 𝟙 (ringSheaf R).obj)
    (_root_.PresheafOfModules.tensorHom (O := R.obj) f₁.val f₂.val) U (x ⊗ₜ y)).trans
    (congrArg _ (_root_.PresheafOfModules.tensorHom_tmul (O := R.obj) f₁.val f₂.val U x y))

end Stacks.SheafOfModules.Tensor

namespace Stacks.SheafOfModules

section TransportCriterion

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

/-- **A criterion for the transported comparison of Stacks 03EL.** If the comparison of
Stacks 03EL is a morphism `h : L(M ⊗ N) ⟶ L M ⊗ L N` read back along `α` on both sides, then the
comparison read through `α` is `h`. -/
theorem pullbackTensorIsoTransport_hom_eq_of_pullbackTensorIso_hom_app
    (M N : _root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O))
    (h : L.obj (((Tensor.sheafTensor Y.O).obj M).obj N) ⟶
      ((Tensor.sheafTensor X.O).obj (L.obj M)).obj (L.obj N))
    (hc : (pullbackTensorIso f).hom.app (M, N) =
      (Functor.whiskerLeft (Functor.uncurry.obj (Tensor.sheafTensor Y.O)) α.hom).app (M, N) ≫ h ≫
        (Functor.whiskerRight (NatTrans.prod α.inv α.inv)
          (Functor.uncurry.obj (Tensor.sheafTensor X.O))).app (M, N)) :
    (pullbackTensorIsoTransport f α M N).hom = h := by
  simp only [pullbackTensorIsoTransport, Iso.trans_hom, Iso.app_hom, Iso.symm_hom,
    Functor.mapIso_hom]
  rw [hc]
  simp only [Functor.whiskerLeft_app, Category.assoc]
  refine (Iso.inv_hom_id_app_assoc α _ _).trans ?_
  exact (congrArg (h ≫ ·) (uncurry_map_inv_comp_map_hom_app_comp_obj_map_hom
    (Tensor.sheafTensor X.O) (α.app M) (α.app N))).trans (Category.comp_id _)

end TransportCriterion

end Stacks.SheafOfModules

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- The tensor product of the two comparisons of the two pullbacks of `F` and `G`, from the
ringed-space pullbacks to the four-field ones. -/
abbrev zariskiPullbackModulesIsoInvTensor (F G : Y.Modules) :=
  (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
      X.zariskiRingedSite.toRingedTopos.O)).map
    (X := ((Stacks.RingedSpace.pullbackFunctor g.toLRSHom.toShHom).obj F,
      (Stacks.RingedSpace.pullbackFunctor g.toLRSHom.toShHom).obj G))
    (Y := (g.zariskiRingedToposModulesHom.pullbackModules.obj F,
      g.zariskiRingedToposModulesHom.pullbackModules.obj G))
    (g.zariskiPullbackModulesIso.inv.app F, g.zariskiPullbackModulesIso.inv.app G)

/-- The comparison of Stacks 01CD for `g`, read on the four-field pullbacks through the
comparison of the two pullbacks. -/
abbrev zariskiComparisonTransport (F G : Y.Modules) :
    ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
        Y.zariskiRingedSite.toRingedTopos.O)) ⋙
        g.zariskiRingedToposModulesHom.pullbackModules).obj (F, G) ⟶
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
        X.zariskiRingedSite.toRingedTopos.O))).obj
        (g.zariskiRingedToposModulesHom.pullbackModules.obj F,
          g.zariskiRingedToposModulesHom.pullbackModules.obj G) :=
  g.zariskiPullbackModulesIso.hom.app _ ≫ Stacks.RingedSpace.comparison g.toLRSHom.toShHom F G ≫
    g.zariskiPullbackModulesIsoInvTensor F G

/-- The ringed-space transpose of the comparison of Stacks 01CD read on the four-field pullbacks is
`comparisonTranspose` followed by the direct image of the comparison of the two pullbacks. -/
theorem pullbackAdjunction_homEquiv_inv_app_comp_hom_app_comp_comparison
    (F G : Y.Modules) :
    ((Stacks.RingedSpace.pullbackAdjunction g.toLRSHom.toShHom).homEquiv _ _)
        (g.zariskiPullbackModulesIso.inv.app _ ≫
          (g.zariskiPullbackModulesIso.hom.app _ ≫
            Stacks.RingedSpace.comparison g.toLRSHom.toShHom F G ≫
              g.zariskiPullbackModulesIsoInvTensor F G)) =
      Stacks.RingedSpace.comparisonTranspose g.toLRSHom.toShHom F G ≫
        (Stacks.RingedSpace.pushforwardFunctor g.toLRSHom.toShHom).map
          (g.zariskiPullbackModulesIsoInvTensor F G) := by
  refine (congrArg ((Stacks.RingedSpace.pullbackAdjunction g.toLRSHom.toShHom).homEquiv _ _)
    (Iso.inv_hom_id_app_assoc g.zariskiPullbackModulesIso _ _)).trans ?_
  refine ((Stacks.RingedSpace.pullbackAdjunction g.toLRSHom.toShHom).homEquiv_naturality_right
    _ _).trans ?_
  exact congrArg (· ≫ _) (Stacks.RingedSpace.homEquiv_comparison g.toLRSHom.toShHom F G)

/-- `homEquiv_zariskiPullbackModulesIso_inv_app_comp_zariskiComparisonTransport` with its
left-hand side at the spelling of the tensor products of the modules development. -/
theorem homEquiv_zariskiPullbackModulesIso_inv_app_comp_zariskiComparisonTransport
    (F G : Y.Modules) :
    ((Stacks.RingedSpace.pullbackAdjunction g.toLRSHom.toShHom).homEquiv
        (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
            Y.zariskiRingedSite.toRingedTopos.O))).obj (F, G))
        (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
            X.zariskiRingedSite.toRingedTopos.O))).obj
          (g.zariskiRingedToposModulesHom.pullbackModules.obj F,
            g.zariskiRingedToposModulesHom.pullbackModules.obj G)))
        (g.zariskiPullbackModulesIso.inv.app
            (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
              Y.zariskiRingedSite.toRingedTopos.O))).obj (F, G)) ≫
          g.zariskiComparisonTransport F G) =
      Stacks.RingedSpace.comparisonTranspose g.toLRSHom.toShHom F G ≫
        (Stacks.RingedSpace.pushforwardFunctor g.toLRSHom.toShHom).map
          (g.zariskiPullbackModulesIsoInvTensor F G) :=
  g.pullbackAdjunction_homEquiv_inv_app_comp_hom_app_comp_comparison F G

/-- `Stacks.RingedSpace.comparisonTranspose_unit_tmul` at the spelling of the tensor products of
the modules development. -/
theorem comparisonTranspose_val_app_unit_tmul (F G : Y.Modules) (V : Y.Opensᵒᵖ)
    (x : F.val.obj V) (y : G.val.obj V) :
    (Stacks.RingedSpace.comparisonTranspose g.toLRSHom.toShHom F G).val.app V
      (((PresheafOfModules.sheafificationAdjunction
          (R := Stacks.SheafOfModules.Tensor.ringSheaf Y.zariskiRingedSite.toRingedTopos.O)
            (𝟙 _)).unit.app (F.val ⊗ G.val)).app V
          (x ⊗ₜ[(Y.zariskiRingedSite.toRingedTopos.O.obj ⋙ forget₂ CommRingCat RingCat).obj V] y)) =
      PresheafOfModules.Hom.app ((PresheafOfModules.sheafificationAdjunction
          (R := Stacks.SheafOfModules.Tensor.ringSheaf X.zariskiRingedSite.toRingedTopos.O)
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf
            X.zariskiRingedSite.toRingedTopos.O).obj)).unit.app
        (PresheafOfModules.tensorObj (O := X.zariskiRingedSite.toRingedTopos.O.obj)
          ((Stacks.RingedSpace.pullbackFunctor g.toLRSHom.toShHom).obj F).val
          ((Stacks.RingedSpace.pullbackFunctor g.toLRSHom.toShHom).obj G).val))
        ((Opens.map g.base).op.obj V)
        (((Stacks.RingedSpace.pullbackAdjunction g.toLRSHom.toShHom).unit.app F).val.app V x ⊗ₜ
          ((Stacks.RingedSpace.pullbackAdjunction g.toLRSHom.toShHom).unit.app G).val.app V y) :=
  Stacks.RingedSpace.comparisonTranspose_unit_tmul g.toLRSHom.toShHom F G V x y

/-- `zariskiPullbackModulesIso_inv_app_unit` with both sides read as sections of the four-field
pullback over the preimage. -/
theorem zariskiPullbackModulesIso_inv_app_unit_sections (M : Y.Modules) (V : Y.Opensᵒᵖ)
    (x : M.val.obj V) :
    (g.zariskiPullbackModulesIso.inv.app M).val.app ((Opens.map g.base).op.obj V)
        (((Stacks.RingedSpace.pullbackAdjunction g.toLRSHom.toShHom).unit.app M).val.app V x) =
      (show (g.zariskiRingedToposModulesHom.pullbackModules.obj M).val.obj
          ((Opens.map g.base).op.obj V) from
        ((pullbackAdjPushforwardModules g.zariskiRingedToposModulesHom).unit.app M).val.app V x) :=
  g.zariskiPullbackModulesIso_inv_app_unit M V x

/-- The four-field transpose of the transported comparison, on the image of a pure tensor. -/
theorem zariskiComparisonTransport_transpose_unit_tmul (F G : Y.Modules) (V : Y.Opensᵒᵖ)
    (x : F.val.obj V) (y : G.val.obj V) :
    ((pullbackAdjPushforwardModules g.zariskiRingedToposModulesHom).unit.app
          (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
            Y.zariskiRingedSite.toRingedTopos.O))).obj (F, G)) ≫
        (pushforwardModules g.zariskiRingedToposModulesHom).map
          (g.zariskiComparisonTransport F G)).val.app V
        (((PresheafOfModules.sheafificationAdjunction
          (R := Stacks.SheafOfModules.Tensor.ringSheaf Y.zariskiRingedSite.toRingedTopos.O)
            (𝟙 _)).unit.app (F.val ⊗ G.val)).app V
          (x ⊗ₜ[(Y.zariskiRingedSite.toRingedTopos.O.obj ⋙ forget₂ CommRingCat RingCat).obj V] y)) =
      PresheafOfModules.Hom.app ((PresheafOfModules.sheafificationAdjunction
          (R := Stacks.SheafOfModules.Tensor.ringSheaf X.zariskiRingedSite.toRingedTopos.O)
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf
            X.zariskiRingedSite.toRingedTopos.O).obj)).unit.app
        (PresheafOfModules.tensorObj (O := X.zariskiRingedSite.toRingedTopos.O.obj)
          (g.zariskiRingedToposModulesHom.pullbackModules.obj F).val
          (g.zariskiRingedToposModulesHom.pullbackModules.obj G).val))
        ((Opens.map g.base).op.obj V)
        (((pullbackAdjPushforwardModules g.zariskiRingedToposModulesHom).unit.app F).val.app V x ⊗ₜ
          ((pullbackAdjPushforwardModules
            g.zariskiRingedToposModulesHom).unit.app G).val.app V y) := by
  refine (zariskiPullbackAdjunction_transpose_val_app g _ _ (g.zariskiComparisonTransport F G) V
    _).trans ?_
  rw [g.homEquiv_zariskiPullbackModulesIso_inv_app_comp_zariskiComparisonTransport F G]
  have hB := g.comparisonTranspose_val_app_unit_tmul F G V x y
  have hC := Stacks.SheafOfModules.Tensor.sheafTensor_uncurry_map_val_app_unit_tmul
    X.zariskiRingedSite.toRingedTopos.O
    (g.zariskiPullbackModulesIso.inv.app F) (g.zariskiPullbackModulesIso.inv.app G)
    ((Opens.map g.base).op.obj V)
    (((Stacks.RingedSpace.pullbackAdjunction g.toLRSHom.toShHom).unit.app F).val.app V x)
    (((Stacks.RingedSpace.pullbackAdjunction g.toLRSHom.toShHom).unit.app G).val.app V y)
  refine (congrArg ((g.zariskiPullbackModulesIsoInvTensor F G).val.app
    ((Opens.map g.base).op.obj V)) hB).trans (hC.trans ?_)
  exact congrArg (PresheafOfModules.Hom.app ((PresheafOfModules.sheafificationAdjunction
          (R := Stacks.SheafOfModules.Tensor.ringSheaf X.zariskiRingedSite.toRingedTopos.O)
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf
            X.zariskiRingedSite.toRingedTopos.O).obj)).unit.app
        (PresheafOfModules.tensorObj (O := X.zariskiRingedSite.toRingedTopos.O.obj)
          (g.zariskiRingedToposModulesHom.pullbackModules.obj F).val
          (g.zariskiRingedToposModulesHom.pullbackModules.obj G).val))
        ((Opens.map g.base).op.obj V))
    (congrArg₂ (TensorProduct.tmul _) (g.zariskiPullbackModulesIso_inv_app_unit_sections F V x)
      (g.zariskiPullbackModulesIso_inv_app_unit_sections G V y))

/-- The left-hand side of the characterization of Stacks 03EL at the transported comparison,
on a pair of local sections. -/
theorem pairingApp_zariskiComparisonTransport_transpose (F G : Y.Modules) (V : Y.Opensᵒᵖ)
    (x : (Sheaf.sectionsFunctor Y.zariskiRingedSite.toRingedTopos.J V).obj
      ((Stacks.SheafOfModules.Tensor.ringSheaf Y.zariskiRingedSite.toRingedTopos.O).moduleSheaf F))
    (y : (Sheaf.sectionsFunctor Y.zariskiRingedSite.toRingedTopos.J V).obj
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        Y.zariskiRingedSite.toRingedTopos.O).moduleSheaf G)) :
    Stacks.SheafOfModules.pairingApp
        (Stacks.SheafOfModules.Tensor.ringSheaf Y.zariskiRingedSite.toRingedTopos.O)
        (Stacks.SheafOfModules.pairingOfTensorHom
          (hO := (Stacks.SheafOfModules.Tensor.ringSheaf
            Y.zariskiRingedSite.toRingedTopos.O).property)
          ((PresheafOfModules.sheafificationAdjunction
              (R := Stacks.SheafOfModules.Tensor.ringSheaf Y.zariskiRingedSite.toRingedTopos.O)
                (𝟙 _)).unit.app (F.val ⊗ G.val) ≫
            ((pullbackAdjPushforwardModules g.zariskiRingedToposModulesHom).unit.app
                (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
                  Y.zariskiRingedSite.toRingedTopos.O))).obj (F, G)) ≫
              (pushforwardModules g.zariskiRingedToposModulesHom).map
                (g.zariskiComparisonTransport F G)).val)) V x y =
      PresheafOfModules.Hom.app ((PresheafOfModules.sheafificationAdjunction
          (R := Stacks.SheafOfModules.Tensor.ringSheaf X.zariskiRingedSite.toRingedTopos.O)
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf
            X.zariskiRingedSite.toRingedTopos.O).obj)).unit.app
        (PresheafOfModules.tensorObj (O := X.zariskiRingedSite.toRingedTopos.O.obj)
          (g.zariskiRingedToposModulesHom.pullbackModules.obj F).val
          (g.zariskiRingedToposModulesHom.pullbackModules.obj G).val))
        ((Opens.map g.base).op.obj V)
        (((pullbackAdjPushforwardModules g.zariskiRingedToposModulesHom).unit.app F).val.app V x ⊗ₜ
          ((pullbackAdjPushforwardModules
            g.zariskiRingedToposModulesHom).unit.app G).val.app V y) :=
  (Stacks.SheafOfModules.pairingApp_pairingOfTensorHom
      (hO := (Stacks.SheafOfModules.Tensor.ringSheaf Y.zariskiRingedSite.toRingedTopos.O).property)
      _ V x y).trans (g.zariskiComparisonTransport_transpose_unit_tmul F G V x y)

/-- **The comparison of Stacks 03EL for the Zariski morphism of a morphism of schemes is the
comparison of Stacks 01CD**, read on the four-field pullbacks through the comparison of the two
pullbacks. The proof checks the characterization
`Stacks.SheafOfModules.eq_pullbackTensorIso_hom_app_iff` on local sections: both pairings send
`(s, t)` to the tensor of the four-field unit images of `s` and `t`. -/
theorem pullbackTensorIso_hom_app_eq_zariskiComparisonTransport (F G : Y.Modules) :
    (Stacks.SheafOfModules.pullbackTensorIso g.zariskiRingedToposModulesHom).hom.app (F, G) =
      g.zariskiComparisonTransport F G := by
  refine ((Stacks.SheafOfModules.eq_pullbackTensorIso_hom_app_iff g.zariskiRingedToposModulesHom
    F G _).mpr ?_).symm
  refine Stacks.SheafOfModules.pairing_ext
    (Stacks.SheafOfModules.Tensor.ringSheaf Y.zariskiRingedSite.toRingedTopos.O) (fun V x y => ?_)
  refine (g.pairingApp_zariskiComparisonTransport_transpose F G V x y).trans ?_
  exact (g.zariskiRingedSiteHom.pairingApp_prodMap_comp_pushforward_tensorSectionPairing
    ((pullbackAdjPushforwardModules g.zariskiRingedToposModulesHom).unit.app F)
    ((pullbackAdjPushforwardModules g.zariskiRingedToposModulesHom).unit.app G) V x y).symm

/-- The comparison of Stacks 01CD for `g`, with source and target spelled with the tensor products
of the modules development. -/
abbrev zariskiComparison (F G : Y.Modules) :
    (Stacks.RingedSpace.pullbackFunctor g.toLRSHom.toShHom).obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor Y.zariskiRingedSite.toRingedTopos.O).obj F).obj
          G) ⟶
      ((Stacks.SheafOfModules.Tensor.sheafTensor X.zariskiRingedSite.toRingedTopos.O).obj
        ((Stacks.RingedSpace.pullbackFunctor g.toLRSHom.toShHom).obj F)).obj
        ((Stacks.RingedSpace.pullbackFunctor g.toLRSHom.toShHom).obj G) :=
  Stacks.RingedSpace.comparison g.toLRSHom.toShHom F G

/-- `pullbackTensorIso_hom_app_eq_zariskiComparisonTransport` with the two comparisons of the
pullbacks written as whiskerings, the shape
`Stacks.SheafOfModules.pullbackTensorIsoTransport_hom_eq_of_pullbackTensorIso_hom_app` asks for. -/
theorem pullbackTensorIso_hom_app_eq_whiskerLeft_comp_zariskiComparison (F G : Y.Modules) :
    (Stacks.SheafOfModules.pullbackTensorIso g.zariskiRingedToposModulesHom).hom.app (F, G) =
      (Functor.whiskerLeft (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
          Y.zariskiRingedSite.toRingedTopos.O)) g.zariskiPullbackModulesIso.hom).app (F, G) ≫
        g.zariskiComparison F G ≫
        (Functor.whiskerRight (NatTrans.prod g.zariskiPullbackModulesIso.inv
            g.zariskiPullbackModulesIso.inv)
          (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
            X.zariskiRingedSite.toRingedTopos.O))).app (F, G) :=
  g.pullbackTensorIso_hom_app_eq_zariskiComparisonTransport F G

/-- **Stacks 03EL for the Zariski morphism of ringed topoi of a morphism of schemes `g`, read
through the identification of its pullback with the ringed-space pullback, is the comparison of
Stacks 01CD for `g`.** -/
theorem pullbackTensorIsoTransport_zariskiPullbackModulesIso_hom (F G : Y.Modules) :
    (Stacks.SheafOfModules.pullbackTensorIsoTransport g.zariskiRingedToposModulesHom
      g.zariskiPullbackModulesIso F G).hom =
      Stacks.RingedSpace.comparison g.toLRSHom.toShHom F G :=
  Stacks.SheafOfModules.pullbackTensorIsoTransport_hom_eq_of_pullbackTensorIso_hom_app
    g.zariskiRingedToposModulesHom g.zariskiPullbackModulesIso F G
    (g.zariskiComparison F G)
    (g.pullbackTensorIso_hom_app_eq_whiskerLeft_comp_zariskiComparison F G)

/-- **Stacks 03EL for the Zariski morphism of ringed topoi of a morphism of schemes is Stacks
01CD**, as isomorphisms. -/
theorem pullbackTensorIsoTransport_zariskiPullbackModulesIso (F G : Y.Modules) :
    Stacks.SheafOfModules.pullbackTensorIsoTransport g.zariskiRingedToposModulesHom
      g.zariskiPullbackModulesIso F G =
      Stacks.RingedSpace.pullbackTensorIsoApp g.toLRSHom.toShHom F G :=
  Iso.ext (g.pullbackTensorIsoTransport_zariskiPullbackModulesIso_hom F G)

/-- `pullbackTensorIsoTransport_zariskiPullbackModulesIso` at the scheme-level spelling of
Stacks 01CD, `Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso`. -/
theorem pullbackTensorIsoTransport_zariskiPullbackModulesIso_eq_moduleLimits (F G : Y.Modules) :
    Stacks.SheafOfModules.pullbackTensorIsoTransport g.zariskiRingedToposModulesHom
      g.zariskiPullbackModulesIso F G =
      Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso g F G :=
  g.pullbackTensorIsoTransport_zariskiPullbackModulesIso F G

end AlgebraicGeometry.Scheme.Hom

end
