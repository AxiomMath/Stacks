module

public import StacksFrontier.Deformation.ToposThickening.DerivedExtensionOfScalarsComp
public import StacksFrontier.Deformation.ToposThickening.SquareZeroReductionSequence
public import StacksFrontier.Deformation.ToposThickening.IdealPartInclBaseChangeAux

/-!
# The inclusion of the ideal part under a change of thickening

Let `g : O ⟶ O'` and `f' : O' ⟶ O₀` be morphisms of sheaves of commutative rings on a site, with
composite `f = g ≫ f'`, and let `ι : I₀|_O ⟶ O`, `ι' : I₀'|_{O'} ⟶ O'` be ideal inclusions along
`f` and `f'` together with a morphism `u₀ : I₀ ⟶ I₀'` of `O₀`-modules compatible with `g`
(`ι(i)` maps to `ι'(u₀ i)` under `g`). For an `O`-module `M`, the inclusion of the ideal part
`((O₀ ⊗_O M) ⊗_{O₀} I₀)|_O ⟶ M` along `f`, followed by the unit `M ⟶ (O' ⊗_O M)|_O` along `g`,
equals the base change `(O₀ ⊗_O M) ⊗ I₀ ⟶ (O₀ ⊗_{O'} (O' ⊗_O M)) ⊗ I₀'` of the ideal parts followed
by the inclusion of the ideal part along `f'` at `O' ⊗_O M`, read over `O`.

This is the square through which the reduction sequences of `O` and of `O'` are compared in the
proof of Stacks 0DLL, where `O` and `O'` are two thickenings of `O₀`.

## Main results

* `Deformation.ComplexLift.idealPartIncl_app_comp_unit`: the compatibility above.

## Implementation notes

Both sides are morphisms out of `((O₀ ⊗_O M) ⊗_{O₀} I₀)|_O`; precomposing with the projection
formula `M ⊗_O I₀|_O ≅ ((O₀ ⊗_O M) ⊗_{O₀} I₀)|_O` turns them into morphisms out of a sheaf tensor
product, which are determined on pure tensors `m ⊗ i`
(`Stacks.SheafOfModules.FlatSquareZero.tensorSheaf_hom_ext`). On `m ⊗ i` the left side is
`η_g(ι(i) • m) = ι(i) • η_g(m)`. On the right, `m ⊗ i ↦ η_f(m) ⊗ i ↦ η_{f'}(η_g(m)) ⊗ u₀(i)` (the
comparison of the extensions of scalars carries `η_f` to `η_{f'} ∘ η_g`,
`Deformation.ComplexLift.extendRestrictAdjunction_unit_comp_extensionOfScalarsCompIso_inv`), and
the inclusion along `f'` sends this to `ι'(u₀ i) • η_g(m) = g(ι(i)) • η_g(m)`. The section formulas
used are those of `StacksFrontier/Deformation/ToposThickening/IdealPartInclBaseChangeAux.lean`.

## References

* [Stacks Project, Tag 0DLL](https://stacks.math.columbia.edu/tag/0DLL)
* [Stacks Project, Tag 0DIZ](https://stacks.math.columbia.edu/tag/0DIZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v' u u'

namespace Deformation.ComplexLift

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {O O' O₀ : Sheaf J CommRingCat.{u}} {f : O ⟶ O₀} {f' : O' ⟶ O₀} (g : O ⟶ O')
  (hg : g ≫ f' = f)
variable {I₀ I₀' : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀)}
  (ι : restrictIdeal f I₀ ⟶ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O))
  (ι' : restrictIdeal f' I₀' ⟶ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O'))
  (u₀ : I₀ ⟶ I₀')

include hg in
/-- **The inclusion of the ideal part under a change of thickening.** The inclusion of the ideal
part along `f`, followed by the unit along `g`, is the base change `h ⊗ u₀` of the ideal parts
followed by the inclusion of the ideal part along `f'` (read over `O`), provided the ideal
inclusions are compatible with `g` and `u₀` (`hu`). On sections both send `η_f(m) ⊗ i` to
`ι(i) • η_g(m)`. -/
theorem idealPartIncl_app_comp_unit
    (hu : ι ≫ Stacks.SheafOfModules.ChangeOfRings.unitToRestrictScalarsUnit (ringSheafMapOf J g) =
      (SheafOfModules.restrictScalars.{u} (ringSheafMapOf J f)).map u₀ ≫
        (restrictScalarsCompIsoOf g hg).inv.app I₀' ≫
        (SheafOfModules.restrictScalars.{u} (ringSheafMapOf J g)).map ι')
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) :
    (idealPartIncl f ι).app M ≫ (extendRestrictAdjunction g).unit.app M =
      (SheafOfModules.restrictScalars.{u} (ringSheafMapOf J f)).map
          ((tensorRight O₀ I₀).map ((extensionOfScalarsCompIso g hg).inv.app M) ≫
            ((Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', u, u, u} O₀).obj
              ((extensionOfScalars f').obj ((extensionOfScalars g).obj M))).map u₀) ≫
        (restrictScalarsCompIsoOf g hg).inv.app _ ≫
        (SheafOfModules.restrictScalars.{u} (ringSheafMapOf J g)).map
          ((idealPartIncl f' ι').app ((extensionOfScalars g).obj M)) := by
  apply (cancel_epi ((idealTensorRightIso f I₀).hom.app M)).mp
  apply Stacks.SheafOfModules.FlatSquareZero.tensorSheaf_hom_ext O M (restrictIdeal f I₀)
  intro U m i
  let N := (extensionOfScalars g).obj M
  let ηg := (extendRestrictAdjunction g).unit.app M
  let ηf := (extendRestrictAdjunction f).unit.app M
  let pt := pureTensorClass O M (restrictIdeal f I₀) U m i
  let r : (Stacks.SheafOfModules.Tensor.ringSheaf O).obj.obj U := ι.val.app U i
  let r' : (Stacks.SheafOfModules.Tensor.ringSheaf O').obj.obj U := ι'.val.app U (u₀.val.app U i)
  let n : N.val.obj U := ηg.val.app U m
  have hLa : ((idealPartIncl f ι).app M).val.app U
      (((idealTensorRightIso f I₀).hom.app M).val.app U pt) = r • m :=
    (congrArg (fun y => ((idealAction ι).app M).val.app U y)
      (congrArg (fun k => k.val.app U pt) ((idealTensorRightIso f I₀).hom_inv_id_app M))).trans
      (idealAction_app_pureTensorClass ι M U m i)
  have hL : (((idealTensorRightIso f I₀).hom.app M ≫ (idealPartIncl f ι).app M ≫ ηg).val.app U)
      pt = r • (ηg.val.app U m) :=
    (congrArg (fun y => (ηg.val.app U) y) hLa).trans ((ηg.val.app U).hom.map_smul r m)
  have hR3 : ((extensionOfScalarsCompIso g hg).inv.app M).val.app U (ηf.val.app U m) =
      ((extendRestrictAdjunction f').unit.app N).val.app U (ηg.val.app U m) :=
    (congrArg (fun k => k.val.app U m)
      (extendRestrictAdjunction_unit_comp_extensionOfScalarsCompIso_inv g hg M)).trans
      (restrictScalarsCompIsoOf_hom_app_val_app g hg _ U _)
  have hR2 := Stacks.SheafOfModules.FlatSquareZero.tensorRight_map_tmul O₀ I₀
    ((extensionOfScalarsCompIso g hg).inv.app M) U (ηf.val.app U m) i
  have hR4 := Stacks.SheafOfModules.FlatSquareZero.tensorLeft_map_tmul O₀
    ((extensionOfScalars f').obj N) u₀ U
    (((extendRestrictAdjunction f').unit.app N).val.app U (ηg.val.app U m)) i
  have hR6 := idealPartIncl_app_pureTensorClass_unit ι' N U (ηg.val.app U m) (u₀.val.app U i)
  have hR : (((idealTensorRightIso f I₀).hom.app M ≫
      (SheafOfModules.restrictScalars.{u} (ringSheafMapOf J f)).map
          ((tensorRight O₀ I₀).map ((extensionOfScalarsCompIso g hg).inv.app M) ≫
            ((Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', u, u, u} O₀).obj
              ((extensionOfScalars f').obj N)).map u₀) ≫
        (restrictScalarsCompIsoOf g hg).inv.app _ ≫
        (SheafOfModules.restrictScalars.{u} (ringSheafMapOf J g)).map
          ((idealPartIncl f' ι').app N)).val.app U) pt = (show N.val.obj U from r' • n) := by
    let A := (tensorRight O₀ I₀).map ((extensionOfScalarsCompIso g hg).inv.app M)
    let B := ((Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', u, u, u} O₀).obj
      ((extensionOfScalars f').obj N)).map u₀
    let Rc := (restrictScalarsCompIsoOf g hg).inv.app
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', u, u, u} O₀).obj
        ((extensionOfScalars f').obj N)).obj I₀')
    let P := (idealPartIncl f' ι').app N
    refine Eq.trans (congrArg (fun y => P.val.app U (Rc.val.app U (B.val.app U (A.val.app U y))))
      (idealTensorRightIso_hom_app_pureTensorClass f I₀ M U m i)) ?_
    refine Eq.trans (congrArg (fun y => P.val.app U (Rc.val.app U (B.val.app U y))) hR2) ?_
    refine Eq.trans (congrArg (fun y => P.val.app U (Rc.val.app U (B.val.app U
      (pureTensorClass O₀ ((extensionOfScalars f').obj N) I₀ U y i)))) hR3) ?_
    refine Eq.trans (congrArg (fun y => P.val.app U (Rc.val.app U y)) hR4) ?_
    refine Eq.trans (congrArg (fun y => P.val.app U y)
      (restrictScalarsCompIsoOf_inv_app_val_app g hg _ U _)) ?_
    exact hR6
  have hui := congrArg (fun k => k.val.app U i) hu
  have hgr : (ringSheafMapOf J g).hom.app U r = r' :=
    (Stacks.SheafOfModules.ChangeOfRings.unitToRestrictScalarsUnit_val_app
      (ringSheafMapOf J g) U r).symm.trans (hui.trans (congrArg (fun y => ι'.val.app U y)
        (restrictScalarsCompIsoOf_inv_app_val_app g hg I₀' U (u₀.val.app U i))))
  have hfin : r • (ηg.val.app U m) = (show N.val.obj U from r' • n) :=
    (show r • (ηg.val.app U m) = (show N.val.obj U from ((ringSheafMapOf J g).hom.app U r) • n)
      from rfl).trans (congrArg (fun s => (show N.val.obj U from s • n)) hgr)
  exact hL.trans (hfin.trans hR.symm)

end Deformation.ComplexLift

end
