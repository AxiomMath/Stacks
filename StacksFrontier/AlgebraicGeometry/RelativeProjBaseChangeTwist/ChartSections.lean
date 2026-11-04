module

public import StacksFrontier.AlgebraicGeometry.RelativeProjBaseChangeTwist.ChartTwist
public import StacksFrontier.AlgebraicGeometry.TwistMapsInvertible.Multiplication

/-!
# Multiplicativity of a chart comparison, from the pullback form to local sections

A comparison `Θ : k^*B ⟶ T` of the inverse image of a module along an open immersion `k` with a
module `T`, which carries the inverse image of a product to a product in the normal form of
`Stacks.AlgebraicGeometry.TwistMulLeg` (`pbMul k mul ≫ Θ = (Θ ⊗ Θ) ≫ mulT`), carries products of
local sections to products of local sections once the restriction along `k` is identified with
the inverse image. This file proves that, with every scheme, module and morphism free, so that
it applies at the concrete charts of a relative `Proj` by substitution.

## Main results

* `Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.restrict_mul_of_pbMul`: the
  multiplication square in restriction form.
* `Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.sections_mul_of_restrict`: the square on
  the image of a pure tensor of local sections.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry
open Stacks.AlgebraicGeometry.RestrictionSections
open Stacks.RingedSpace (tensorSheaf_map_unit_tmul)
open scoped TensorProduct

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist

/-- The categorical shape of `restrict_mul_of_pbMul`, with every object and morphism free. -/
theorem restrict_square_gen {C : Type*} [Category C]
    {RT KT KTen RTen KBmn RBmn Tmn TTen : C}
    {rT : RT ⟶ KT} {cmp : KT ⟶ KTen} {w : KTen ⟶ RTen} {wInv : RTen ⟶ KTen}
    {Rinv : RTen ⟶ RT} {rmul : RT ⟶ RBmn} {rB : RBmn ⟶ KBmn} {kmul : KT ⟶ KBmn}
    {pb : KTen ⟶ KBmn} {Θmn : KBmn ⟶ Tmn} {tsmΘ : KTen ⟶ TTen} {mulT : TTen ⟶ Tmn}
    {tsmChart : RTen ⟶ TTen}
    (hR : Rinv ≫ rT ≫ cmp ≫ w = 𝟙 _) (hw : w ≫ wInv = 𝟙 _)
    (hnat : rmul ≫ rB = rT ≫ kmul) (hpb : cmp ≫ pb = kmul) (hP : pb ≫ Θmn = tsmΘ ≫ mulT)
    (htsm : tsmChart = wInv ≫ tsmΘ) :
    Rinv ≫ rmul ≫ rB ≫ Θmn = tsmChart ≫ mulT := by
  have h1 : Rinv ≫ rT ≫ cmp = wInv := by simpa [hw] using hR =≫ wInv
  rw [reassoc_of% hnat, ← hpb, Category.assoc, hP, htsm, ← h1]
  simp only [Category.assoc]

variable {X W : Scheme.{u}} (k : W ⟶ X) [IsOpenImmersion k]

/-- `restrictTensorIso`, written out: the identification of restriction with inverse image, the
Tag 01CD comparison, and the tensor product of the identifications read backwards. -/
theorem restrictTensorIso_hom_eq (Bm Bn : X.Modules) :
    (restrictTensorIso k Bm Bn).hom =
      (Scheme.Modules.restrictFunctorIsoPullback k).hom.app
          ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            ⟨(X.toRingedSpace).presheaf, (X.toRingedSpace).IsSheaf⟩)).obj (Bm, Bn)) ≫
        (Stacks.PullbackTensorIso.pullbackTensorIso k.toLRSHom.toShHom).hom.app (Bm, Bn) ≫
          ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            ⟨(W.toRingedSpace).presheaf, (W.toRingedSpace).IsSheaf⟩)).map
            (((Scheme.Modules.restrictFunctorIsoPullback k).inv.app Bm,
              (Scheme.Modules.restrictFunctorIsoPullback k).inv.app Bn) :
              (_, _) ⟶ (_, _))) := rfl

/-- The inverse of `restrictTensorIso`, followed by the written-out form of its forward map
(`restrictTensorIso_hom_eq`), is the identity. -/
theorem restrictTensorIso_inv_comp_eq (Bm Bn : X.Modules) :
    (restrictTensorIso k Bm Bn).inv ≫
        (Scheme.Modules.restrictFunctorIsoPullback k).hom.app
          ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            ⟨(X.toRingedSpace).presheaf, (X.toRingedSpace).IsSheaf⟩)).obj (Bm, Bn)) ≫
        (Stacks.PullbackTensorIso.pullbackTensorIso k.toLRSHom.toShHom).hom.app (Bm, Bn) ≫
          ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            ⟨(W.toRingedSpace).presheaf, (W.toRingedSpace).IsSheaf⟩)).map
            (((Scheme.Modules.restrictFunctorIsoPullback k).inv.app Bm,
              (Scheme.Modules.restrictFunctorIsoPullback k).inv.app Bn) :
              (_, _) ⟶ (_, _))) = 𝟙 _ :=
  (congrArg (fun z => (restrictTensorIso k Bm Bn).inv ≫ z)
    (restrictTensorIso_hom_eq k Bm Bn).symm).trans (restrictTensorIso k Bm Bn).inv_hom_id

/-- The tensor product of the inverse identifications of restriction with inverse image,
followed by the tensor product of the identifications themselves, is the identity. -/
theorem tensorSheafMap_inv_hom (Bm Bn : X.Modules) :
    ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨(W.toRingedSpace).presheaf, (W.toRingedSpace).IsSheaf⟩)).map
        (((Scheme.Modules.restrictFunctorIsoPullback k).inv.app Bm,
          (Scheme.Modules.restrictFunctorIsoPullback k).inv.app Bn) : (_, _) ⟶ (_, _))) ≫
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨(W.toRingedSpace).presheaf, (W.toRingedSpace).IsSheaf⟩)).map
          (((Scheme.Modules.restrictFunctorIsoPullback k).hom.app Bm,
            (Scheme.Modules.restrictFunctorIsoPullback k).hom.app Bn) :
            (_, _) ⟶ (_, _))) = 𝟙 _ :=
  (TwistMultTransport.tensorSheafMap_comp W.toRingedSpace _ _ _ _).symm.trans
    ((congrArg ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨(W.toRingedSpace).presheaf, (W.toRingedSpace).IsSheaf⟩)).map
        (X := ((Scheme.Modules.pullback k).obj Bm, (Scheme.Modules.pullback k).obj Bn))
        (Y := ((Scheme.Modules.pullback k).obj Bm, (Scheme.Modules.pullback k).obj Bn)))
      (Prod.ext (Iso.inv_hom_id_app (Scheme.Modules.restrictFunctorIsoPullback k) Bm)
        (Iso.inv_hom_id_app (Scheme.Modules.restrictFunctorIsoPullback k) Bn))).trans
      (TwistMultTransport.tensorSheafMap_id W.toRingedSpace _ _))

/-- **The multiplication square in restriction form**, from the pullback form. -/
theorem restrict_mul_of_pbMul {Bm Bn Bmn : X.Modules}
    (mul : (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨(X.toRingedSpace).presheaf, (X.toRingedSpace).IsSheaf⟩).obj (Bm)).obj (Bn)) ⟶ Bmn)
    {Tm Tn Tmn : W.Modules}
    (mulT : (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨(W.toRingedSpace).presheaf, (W.toRingedSpace).IsSheaf⟩).obj (Tm)).obj (Tn)) ⟶ Tmn)
    (Θm : (Scheme.Modules.pullback k).obj Bm ⟶ Tm) (Θn : (Scheme.Modules.pullback k).obj Bn ⟶ Tn)
    (Θmn : (Scheme.Modules.pullback k).obj Bmn ⟶ Tmn)
    (hP : TwistMulLeg.pbMul k mul ≫ Θmn =
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨(W.toRingedSpace).presheaf, (W.toRingedSpace).IsSheaf⟩)).map
        ((Θm, Θn) : (_, _) ⟶ (_, _))) ≫ mulT) :
    (restrictTensorIso k Bm Bn).inv ≫ (Scheme.Modules.restrictFunctor k).map mul ≫
        ((Scheme.Modules.restrictFunctorIsoPullback k).hom.app Bmn ≫ Θmn) =
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨(W.toRingedSpace).presheaf, (W.toRingedSpace).IsSheaf⟩)).map
        (((Scheme.Modules.restrictFunctorIsoPullback k).hom.app Bm ≫ Θm,
          (Scheme.Modules.restrictFunctorIsoPullback k).hom.app Bn ≫ Θn) :
          (_, _) ⟶ (_, _))) ≫ mulT :=
  restrict_square_gen (restrictTensorIso_inv_comp_eq k Bm Bn) (tensorSheafMap_inv_hom k Bm Bn)
    ((Scheme.Modules.restrictFunctorIsoPullback k).hom.naturality mul)
    (TwistMulLeg.comparison_comp_pbMul k mul) hP
    (TwistMultTransport.tensorSheafMap_comp W.toRingedSpace
      ((Scheme.Modules.restrictFunctorIsoPullback k).hom.app Bm) Θm
      ((Scheme.Modules.restrictFunctorIsoPullback k).hom.app Bn) Θn)

/-- **The multiplication square on local sections**, from the restriction form. -/
theorem sections_mul_of_restrict {Bm Bn Bmn : X.Modules}
    (mul : (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨(X.toRingedSpace).presheaf, (X.toRingedSpace).IsSheaf⟩).obj (Bm)).obj (Bn)) ⟶ Bmn)
    {Tm Tn Tmn : W.Modules}
    (mulT : (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨(W.toRingedSpace).presheaf, (W.toRingedSpace).IsSheaf⟩).obj (Tm)).obj (Tn)) ⟶ Tmn)
    (cm : (Scheme.Modules.restrictFunctor k).obj Bm ⟶ Tm)
    (cn : (Scheme.Modules.restrictFunctor k).obj Bn ⟶ Tn)
    (cmn : (Scheme.Modules.restrictFunctor k).obj Bmn ⟶ Tmn)
    (hR : (restrictTensorIso k Bm Bn).inv ≫ (Scheme.Modules.restrictFunctor k).map mul ≫ cmn =
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨(W.toRingedSpace).presheaf, (W.toRingedSpace).IsSheaf⟩)).map
        ((cm, cn) : (_, _) ⟶ (_, _))) ≫ mulT)
    (U : W.Opens) (x : Bm.val.obj (op (k ''ᵁ U))) (y : Bn.val.obj (op (k ''ᵁ U))) :
    cmn.val.app (op U) (mul.val.app (op (k ''ᵁ U))
        (PresheafOfModules.Hom.app ((PresheafOfModules.sheafificationAdjunction
          (R := Stacks.RingedSpace.structureRingSheaf (X.toRingedSpace))
          (𝟙 (Stacks.RingedSpace.structureRingSheaf (X.toRingedSpace)).obj)).unit.app
          (PresheafOfModules.tensorObj (O := (X.toRingedSpace).presheaf) (Bm).val (Bn).val))
          (op (k ''ᵁ U)) (x ⊗ₜ y))) =
      mulT.val.app (op U) (PresheafOfModules.Hom.app ((PresheafOfModules.sheafificationAdjunction
          (R := Stacks.RingedSpace.structureRingSheaf (W.toRingedSpace))
          (𝟙 (Stacks.RingedSpace.structureRingSheaf (W.toRingedSpace)).obj)).unit.app
          (PresheafOfModules.tensorObj (O := (W.toRingedSpace).presheaf) (Tm).val (Tn).val))
          (op U)
        (cm.val.app (op U) x ⊗ₜ cn.val.app (op U) y)) := by
  set z := PresheafOfModules.Hom.app ((PresheafOfModules.sheafificationAdjunction
    (R := Stacks.RingedSpace.structureRingSheaf (X.toRingedSpace))
    (𝟙 (Stacks.RingedSpace.structureRingSheaf (X.toRingedSpace)).obj)).unit.app
    (PresheafOfModules.tensorObj (O := (X.toRingedSpace).presheaf) (Bm).val (Bn).val))
    (op (k ''ᵁ U)) (x ⊗ₜ y)
  have h := congrArg
    (fun φ => φ.val.app (op U) ((restrictTensorIso k Bm Bn).hom.val.app (op U) z)) hR
  have hinv : (restrictTensorIso k Bm Bn).inv.val.app (op U)
      ((restrictTensorIso k Bm Bn).hom.val.app (op U) z) = z :=
    congrArg (fun φ => φ.val.app (op U) z) (restrictTensorIso k Bm Bn).hom_inv_id
  refine Eq.trans ?_ (h.trans ?_)
  · exact (congrArg (fun z => cmn.val.app (op U)
      (((Scheme.Modules.restrictFunctor k).map mul).val.app (op U) z)) hinv).symm
  · refine Eq.trans (congrArg (fun z => (((Functor.uncurry.obj
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨(W.toRingedSpace).presheaf, (W.toRingedSpace).IsSheaf⟩)).map
          ((cm, cn) : (_, _) ⟶ (_, _))) ≫ mulT).val.app
      (op U) z) (restrictTensorIso_hom_unit_tmul k Bm Bn U x y)) ?_
    exact congrArg (fun z => mulT.val.app (op U) z)
      (tensorSheaf_map_unit_tmul W.toRingedSpace cm cn (op U) x y)

end Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist

end
