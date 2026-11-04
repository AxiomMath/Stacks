module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackModulesCompIsoUnit
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorChainSections
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorMateMonoidal

/-!
# The compositor of Stacks 03D8 against the pairings at the bottom of the chain of Tag 03EL

The comparison of **Tag 03EL** is the preimage of the identity under the chain of bijections of that
tag, and the bottom of the chain — steps 4, 5 and 6 traversed backwards from the identity — is a
*pairing* of the two inverse images which sends a pair of local sections to the pure tensor of their
images under the unit of extension of scalars of Stacks 03CZ
(`Stacks.SheafOfModules.pairingApp_pullbackTensorBottom`).

This file proves the identity between those pairings for a composite `ψ ∘ φ` and for its two
factors: the pairing at the bottom of the chain for `φ`, taken at the two inverse images along `φ`
of the units for `ψ` and followed by the compositor of **Stacks 03D8** on the tensor product, is the
pairing at the bottom of the chain for `ψ ∘ φ`. It is the compositor analogue of
`Stacks.SheafOfModules.prodMap_mate_comp_pullbackTensorBottomPairing`, and like that one it reduces
factor by factor to a single identity about units — here
`Stacks.SheafOfModules.extendScalarsUnitSheafHom_comp_pullbackModulesCompAdjIso`.

## Main definitions

* `Stacks.SheafOfModules.compTensorHom`: the compositor on the tensor product of the two pullbacks.
* `Stacks.SheafOfModules.compTensorSheafHom`: the same on underlying sheaves of sets, with both
  endpoints ascribed as the bottom of the chain of Tag 03EL spells them.

## Main results

* `Stacks.SheafOfModules.extendScalarsUnitSheafHom_comp_pullbackModulesCompAdjIso_inv`: the
  compositor read in the direction the chain uses — the two units of Stacks 03CZ followed by the
  compositor are the unit for the composite.
* `Stacks.SheafOfModules.prodMap_comp_pullbackTensorBottomPairing`: **the pairing identity for the
  compositor.**

## Implementation notes

Every step is a declaration of its own with both of its sides written out, for the reason recorded
in the implementation notes of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorMateMonoidal`: the heartbeat budget is
per declaration, and a composite of two of these steps assembled inside one proof exhausts it at
`whnf` even though each step costs a fraction of a second on its own.

## References

* [Stacks Project, Tag 03CZ](https://stacks.math.columbia.edu/tag/03CZ)
* [Stacks Project, Tag 03D8](https://stacks.math.columbia.edu/tag/03D8)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry CategoryTheory.Sheaf
open AlgebraicGeometry.SheafOfModules Stacks.Sheaves.RingedToposModules
open Stacks.PresheafOfModules.ChangeOfRings
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward
open scoped TensorProduct

namespace Stacks.SheafOfModules

universe w w' w'' v u v' u' v'' u''

section CompPairing

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  {Z : RingedTopos.{v'', u'', w''}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{w''} RingCat.{w''})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [Z.J.HasSheafCompose (forget RingCat.{w''})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [Z.J.HasSheafCompose (forget AddCommGrpCat.{w''})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
  (φ : AlgebraicGeometry.RingedToposHom X Y) (ψ : AlgebraicGeometry.RingedToposHom Y Z)
  (A : SheafOfModules.{w''} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O))

/-- **The compositor of Stacks 03D8 read in the direction the chain of Tag 03EL uses.** The inverse
image along `φ` of the unit of extension of scalars for `ψ`, followed by the unit for `φ` at `ψ^*A`
and then by the compositor, is the unit for the composite.

This is `Stacks.SheafOfModules.extendScalarsUnitSheafHom_comp_pullbackModulesCompAdjIso` with the
compositor inverted, which is where the chain meets it: the chain produces the two units in turn and
the comparison of the two targets is the *inverse* of the compositor. -/
theorem extendScalarsUnitSheafHom_comp_pullbackModulesCompAdjIso_inv :
    φ.toToposHom.inverseImage.map (extendScalarsUnitSheafHom ψ.toModulesHom A) ≫
        extendScalarsUnitSheafHom φ.toModulesHom ((ψ.toModulesHom.pullbackModules).obj A) ≫
          (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).map
            ((pullbackModulesCompAdjIso φ ψ).inv.app A) =
      extendScalarsUnitSheafHom (ψ.comp φ).toModulesHom A :=
  (congrArg (fun m ↦ m ≫ (Sheaf.moduleSheafFunctor
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).map
      ((pullbackModulesCompAdjIso φ ψ).inv.app A))
    (extendScalarsUnitSheafHom_comp_pullbackModulesCompAdjIso φ ψ A).symm).trans
    ((Category.assoc _ _ _).trans
      ((congrArg (fun m ↦ extendScalarsUnitSheafHom (ψ.comp φ).toModulesHom A ≫ m)
          (((Sheaf.moduleSheafFunctor
                (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).map_comp _ _).symm.trans
            ((congrArg (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).map
                ((pullbackModulesCompAdjIso φ ψ).hom_inv_id_app A)).trans
              ((Sheaf.moduleSheafFunctor
                (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).map_id _)))).trans
        (Category.comp_id _)))

/-- The compositor of Stacks 03D8 against the units of Stacks 03CZ, on a local section: the three
morphisms applied in turn. -/
private lemma sectionsFunctor_map_extendScalarsUnit_comp_compAdjIso (W : X.Cᵒᵖ)
    (x : ((inverseImageModules (ψ.comp φ).toModulesHom.toToposHom
      (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)).obj A).val.obj W) :
    ((pullbackModulesCompAdjIso φ ψ).inv.app A).val.app W
        (((extendRestrictScalarsAdjunction X.J (fSharpCommRing φ.toModulesHom)
              (inverseImageRingSheaf φ.toToposHom
                (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).property
              (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property).unit.app
            ((inverseImageModules φ.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj
              ((ψ.toModulesHom.pullbackModules).obj A))).val.app W
          ((Sheaf.sectionsFunctor X.J W).map
            (φ.toToposHom.inverseImage.map (extendScalarsUnitSheafHom ψ.toModulesHom A)) x)) =
      ((extendRestrictScalarsAdjunction X.J (fSharpCommRing (ψ.comp φ).toModulesHom)
            (inverseImageRingSheaf (ψ.comp φ).toModulesHom.toToposHom
              (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)).property
            (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property).unit.app
          ((inverseImageModules (ψ.comp φ).toModulesHom.toToposHom
            (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)).obj A)).val.app W x :=
  congrArg (fun m ↦ (Sheaf.sectionsFunctor X.J W).map m x)
    (extendScalarsUnitSheafHom_comp_pullbackModulesCompAdjIso_inv φ ψ A)

variable (B : SheafOfModules.{w''} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O))

/-- **The compositor of Stacks 03D8 on the tensor product of the two pullbacks.**

Declared at the spelling of the bifunctor — the one its own `Functor.map` produces — for the reason
recorded for `Stacks.SheafOfModules.mateTensorHom`: ascribing the spelling
`Stacks.SheafOfModules.pullbackTensorTarget` here exhausts the elaborator's budget at `whnf` before
the body is looked at. -/
def compTensorHom :
    ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O))).obj
        ((φ.toModulesHom.pullbackModules).obj ((ψ.toModulesHom.pullbackModules).obj A),
          (φ.toModulesHom.pullbackModules).obj ((ψ.toModulesHom.pullbackModules).obj B)) ⟶
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O))).obj
        (((ψ.comp φ).toModulesHom.pullbackModules).obj A,
          ((ψ.comp φ).toModulesHom.pullbackModules).obj B) :=
  ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O))).map
    (((pullbackModulesCompAdjIso φ ψ).inv.app A, (pullbackModulesCompAdjIso φ ψ).inv.app B) :
      (((φ.toModulesHom.pullbackModules).obj ((ψ.toModulesHom.pullbackModules).obj A),
          (φ.toModulesHom.pullbackModules).obj
            ((ψ.toModulesHom.pullbackModules).obj B)) : _ × _) ⟶
        (((ψ.comp φ).toModulesHom.pullbackModules).obj A,
          ((ψ.comp φ).toModulesHom.pullbackModules).obj B))

/-- **The compositor on the tensor product of the two pullbacks, on a pure tensor**: it carries the
sheafification-unit image of `y ⊗ₜ z` to the unit image of the pure tensor of the two values of the
compositor. This is the naturality of the sheafification unit. -/
lemma compTensorHom_val_app_unit_tmul (V : X.Cᵒᵖ)
    (y : ((φ.toModulesHom.pullbackModules).obj
      ((ψ.toModulesHom.pullbackModules).obj A)).val.obj V)
    (z : ((φ.toModulesHom.pullbackModules).obj
      ((ψ.toModulesHom.pullbackModules).obj B)).val.obj V) :
    (compTensorHom φ ψ A B).val.app V
        (((PresheafOfModules.sheafificationAdjunction
            (R := commRingSheaf X.J X.O.obj
              (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property) (𝟙 _)).unit.app
            (((φ.toModulesHom.pullbackModules).obj
                ((ψ.toModulesHom.pullbackModules).obj A)).val ⊗
              ((φ.toModulesHom.pullbackModules).obj
                ((ψ.toModulesHom.pullbackModules).obj B)).val)).app V
          (y ⊗ₜ[(ringPresheaf X.O.obj).obj V] z)) =
      ((PresheafOfModules.sheafificationAdjunction
          (R := commRingSheaf X.J X.O.obj
            (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property) (𝟙 _)).unit.app
          ((((ψ.comp φ).toModulesHom.pullbackModules).obj A).val ⊗
            (((ψ.comp φ).toModulesHom.pullbackModules).obj B).val)).app V
        (((pullbackModulesCompAdjIso φ ψ).inv.app A).val.app V y
          ⊗ₜ[(ringPresheaf X.O.obj).obj V]
          ((pullbackModulesCompAdjIso φ ψ).inv.app B).val.app V z) := by
  unfold compTensorHom
  rw [Stacks.SheafOfModules.Tensor.sheafTensor_uncurry_map]
  exact TensorSheafification.sheafification_map_val_app_unit X.O.obj
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property
    (PresheafOfModules.tensorHom (O := X.O.obj)
      (SheafOfModules.Hom.val ((pullbackModulesCompAdjIso φ ψ).inv.app A))
      (SheafOfModules.Hom.val ((pullbackModulesCompAdjIso φ ψ).inv.app B))) V
    (y ⊗ₜ[(ringPresheaf X.O.obj).obj V] z)

/-- **The compositor on the tensor product of the two pullbacks, on underlying sheaves of sets, with
both endpoints ascribed as the bottom of the chain of Tag 03EL spells them.** As for
`Stacks.SheafOfModules.mateTensorSheafHom`, the bottom of the chain lands in the underlying sheaf of
sets of a restriction of scalars — to `φ⁻¹O_D` on one side and to `(ψ ∘ φ)⁻¹O_E` on the other — and
that sheaf of sets does not depend on which ring is restricted to nor on which spelling of the
tensor product is used, but the combinations are not syntactically equal. -/
def compTensorSheafHom :
    Sheaf.moduleSheaf (inverseImageRingSheaf φ.toToposHom
        (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
        ((SheafOfModules.restrictScalars φ.toModulesHom.fSharpInverseImage).obj
          (pullbackTensorTarget φ.toModulesHom ((ψ.toModulesHom.pullbackModules).obj A)
            ((ψ.toModulesHom.pullbackModules).obj B))) ⟶
      Sheaf.moduleSheaf (inverseImageRingSheaf (ψ.comp φ).toModulesHom.toToposHom
          (Stacks.SheafOfModules.Tensor.ringSheaf Z.O))
        ((SheafOfModules.restrictScalars (ψ.comp φ).toModulesHom.fSharpInverseImage).obj
          (pullbackTensorTarget (ψ.comp φ).toModulesHom A B)) :=
  (Sheaf.moduleSheafFunctor (inverseImageRingSheaf φ.toToposHom
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).map
    ((SheafOfModules.restrictScalars φ.toModulesHom.fSharpInverseImage).map
      (compTensorHom φ ψ A B))

/-- **The left-hand side of the pairing identity on a pair of local sections**: the two inverse
images along `φ` of the units for `ψ`, followed by the pairing at the bottom of the chain for `φ`
and then by the compositor, carry a pair of sections to the unit image of the pure tensor of the
two values of the compositor at the two units for `φ`. -/
private lemma sectionsFunctor_map_prodMap_comp_pullbackTensorBottomPairing (W : X.Cᵒᵖ)
    (x : ((inverseImageModules (ψ.comp φ).toModulesHom.toToposHom
      (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)).obj A).val.obj W)
    (s : ((inverseImageModules (ψ.comp φ).toModulesHom.toToposHom
      (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)).obj B).val.obj W) :
    (Sheaf.sectionsFunctor X.J W).map
        (prod.map (φ.toToposHom.inverseImage.map (extendScalarsUnitSheafHom ψ.toModulesHom A))
            (φ.toToposHom.inverseImage.map (extendScalarsUnitSheafHom ψ.toModulesHom B)) ≫
          ((pullbackTensorStep4 φ.toModulesHom ((ψ.toModulesHom.pullbackModules).obj A)
                ((ψ.toModulesHom.pullbackModules).obj B)
                (pullbackTensorTarget φ.toModulesHom ((ψ.toModulesHom.pullbackModules).obj A)
                  ((ψ.toModulesHom.pullbackModules).obj B))).symm
              (pullbackTensorBottomHom φ.toModulesHom
                ((ψ.toModulesHom.pullbackModules).obj A)
                ((ψ.toModulesHom.pullbackModules).obj B))).1 ≫
            compTensorSheafHom φ ψ A B)
        (Functor.prodObjMk (P := Sheaf.sectionsFunctor.{w} X.J W) x s) =
      ((PresheafOfModules.sheafificationAdjunction
          (R := commRingSheaf X.J X.O.obj
            (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property) (𝟙 _)).unit.app
          ((((ψ.comp φ).toModulesHom.pullbackModules).obj A).val ⊗
            (((ψ.comp φ).toModulesHom.pullbackModules).obj B).val)).app W
        (((pullbackModulesCompAdjIso φ ψ).inv.app A).val.app W
            (((extendRestrictScalarsAdjunction X.J (fSharpCommRing φ.toModulesHom)
                  (inverseImageRingSheaf φ.toToposHom
                    (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).property
                  (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property).unit.app
                ((inverseImageModules φ.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj
                  ((ψ.toModulesHom.pullbackModules).obj A))).val.app W
              ((Sheaf.sectionsFunctor X.J W).map
                (φ.toToposHom.inverseImage.map
                  (extendScalarsUnitSheafHom ψ.toModulesHom A)) x))
          ⊗ₜ[(ringPresheaf X.O.obj).obj W]
          ((pullbackModulesCompAdjIso φ ψ).inv.app B).val.app W
            (((extendRestrictScalarsAdjunction X.J (fSharpCommRing φ.toModulesHom)
                  (inverseImageRingSheaf φ.toToposHom
                    (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).property
                  (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property).unit.app
                ((inverseImageModules φ.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj
                  ((ψ.toModulesHom.pullbackModules).obj B))).val.app W
              ((Sheaf.sectionsFunctor X.J W).map
                (φ.toToposHom.inverseImage.map
                  (extendScalarsUnitSheafHom ψ.toModulesHom B)) s))) :=
  ((Sheaf.sectionsFunctor X.J W).map_comp_apply
      (prod.map (φ.toToposHom.inverseImage.map (extendScalarsUnitSheafHom ψ.toModulesHom A))
        (φ.toToposHom.inverseImage.map (extendScalarsUnitSheafHom ψ.toModulesHom B)))
      (((pullbackTensorStep4 φ.toModulesHom ((ψ.toModulesHom.pullbackModules).obj A)
              ((ψ.toModulesHom.pullbackModules).obj B)
              (pullbackTensorTarget φ.toModulesHom ((ψ.toModulesHom.pullbackModules).obj A)
                ((ψ.toModulesHom.pullbackModules).obj B))).symm
            (pullbackTensorBottomHom φ.toModulesHom ((ψ.toModulesHom.pullbackModules).obj A)
              ((ψ.toModulesHom.pullbackModules).obj B))).1 ≫
        compTensorSheafHom φ ψ A B) _).trans
    ((congrArg ((Sheaf.sectionsFunctor X.J W).map
          (((pullbackTensorStep4 φ.toModulesHom ((ψ.toModulesHom.pullbackModules).obj A)
                  ((ψ.toModulesHom.pullbackModules).obj B)
                  (pullbackTensorTarget φ.toModulesHom
                    ((ψ.toModulesHom.pullbackModules).obj A)
                    ((ψ.toModulesHom.pullbackModules).obj B))).symm
                (pullbackTensorBottomHom φ.toModulesHom
                  ((ψ.toModulesHom.pullbackModules).obj A)
                  ((ψ.toModulesHom.pullbackModules).obj B))).1 ≫
            compTensorSheafHom φ ψ A B))
        (Limits.map_prodMap_prodObjMk (P := Sheaf.sectionsFunctor.{w} X.J W)
          (φ.toToposHom.inverseImage.map (extendScalarsUnitSheafHom ψ.toModulesHom A))
          (φ.toToposHom.inverseImage.map (extendScalarsUnitSheafHom ψ.toModulesHom B)) x s)).trans
      (((Sheaf.sectionsFunctor X.J W).map_comp_apply _ (compTensorSheafHom φ ψ A B) _).trans
        ((congrArg ((Sheaf.sectionsFunctor X.J W).map (compTensorSheafHom φ ψ A B))
            (pairingApp_pullbackTensorBottom φ.toModulesHom
              ((ψ.toModulesHom.pullbackModules).obj A)
              ((ψ.toModulesHom.pullbackModules).obj B) W _ _)).trans
          ((sectionsFunctor_map_moduleSheafFunctor_map'
              (inverseImageRingSheaf φ.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
              ((SheafOfModules.restrictScalars φ.toModulesHom.fSharpInverseImage).map
                (compTensorHom φ ψ A B)) W _).trans
            (compTensorHom_val_app_unit_tmul φ ψ A B W _ _)))))

/-- **The pairing identity for the compositor of Stacks 03D8: the two inverse images along `φ` of
the units of Stacks 03CZ for `ψ`, followed by the pairing at the bottom of the chain of Tag 03EL for
`φ` and then by the compositor on the tensor product of the two pullbacks, are the pairing at the
bottom of the chain for `ψ ∘ φ`.**

Both sides are pairings of the underlying sheaves of sets of the two inverse images along the
composite, so they agree as soon as they agree on every pair of local sections; there the left-hand
side is the pure tensor of the two compositor values at the units for `φ` and the right-hand side is
the pure tensor of the two units for the composite, and the two agree factor by factor by
`Stacks.SheafOfModules.extendScalarsUnitSheafHom_comp_pullbackModulesCompAdjIso`.

This is the compositor analogue of
`Stacks.SheafOfModules.prodMap_mate_comp_pullbackTensorBottomPairing`, and the whole mathematical
content of the monoidality of the compositor. -/
theorem prodMap_comp_pullbackTensorBottomPairing :
    prod.map (φ.toToposHom.inverseImage.map (extendScalarsUnitSheafHom ψ.toModulesHom A))
          (φ.toToposHom.inverseImage.map (extendScalarsUnitSheafHom ψ.toModulesHom B)) ≫
        ((pullbackTensorStep4 φ.toModulesHom ((ψ.toModulesHom.pullbackModules).obj A)
              ((ψ.toModulesHom.pullbackModules).obj B)
              (pullbackTensorTarget φ.toModulesHom ((ψ.toModulesHom.pullbackModules).obj A)
                ((ψ.toModulesHom.pullbackModules).obj B))).symm
            (pullbackTensorBottomHom φ.toModulesHom ((ψ.toModulesHom.pullbackModules).obj A)
              ((ψ.toModulesHom.pullbackModules).obj B))).1 ≫
          compTensorSheafHom φ ψ A B =
      ((pullbackTensorStep4 (ψ.comp φ).toModulesHom A B
            (pullbackTensorTarget (ψ.comp φ).toModulesHom A B)).symm
          (pullbackTensorBottomHom (ψ.comp φ).toModulesHom A B)).1 :=
  hom_ext_prod' fun W x s ↦
    (sectionsFunctor_map_prodMap_comp_pullbackTensorBottomPairing φ ψ A B W x s).trans
      (by
        rw [sectionsFunctor_map_extendScalarsUnit_comp_compAdjIso φ ψ A W x,
          sectionsFunctor_map_extendScalarsUnit_comp_compAdjIso φ ψ B W s]
        exact (pairingApp_pullbackTensorBottom (ψ.comp φ).toModulesHom A B W x s).symm)

end CompPairing

end Stacks.SheafOfModules

end
