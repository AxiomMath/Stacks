module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorStep1Apply
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorStep2Apply
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackModulesOfIsoStructureMap
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorBilinEquivPairingApp
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorChainApply
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorStepTargetApply
public import StacksFrontier.CategoryTheory.Sites.Modules.InternalHomAndFlatness.InternalHomEvaluationRestriction
public import StacksFrontier.CategoryTheory.Sites.Modules.InternalHomAndFlatness.TensorRestrictionComparisonSections
public import StacksFrontier.CategoryTheory.Sites.Modules.LocalizationRingedSites.TensorTransport
public import StacksFrontier.CategoryTheory.Sites.Modules.InternalHomAndFlatness.PullbackInternalHomCompMap
public import StacksFrontier.CategoryTheory.Sites.Modules.LocalizationRingedSites.PullbackToposSquare
public import StacksFrontier.CategoryTheory.Sites.Modules.LocalizationRingedSites.LocalizationFsharpIso
public import StacksFrontier.CategoryTheory.Sites.Modules.LocalizationRingedSites.PullbackRestrictionUnit
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackPairingTranspose
public import StacksFrontier.CategoryTheory.Sites.Modules.LocalizationRingedSites.IsoStructureMap
import StacksCore.Tactic.StacksAttribute

/-!
# The comparison of Stacks 03EL at a localization morphism is the mate of Stacks 0E8H

Let `(C, O)` be a ringed site and `U` an object of `C`. Restriction of sheaves of modules to the
slice site over `U` carries two comparisons of tensor products, built in completely different
ways:

* the comparison of **Stacks 03EL** for the localization morphism of ringed topoi
  `π : (Sh(C/U), O|_U) ⟶ (Sh(C), O)`, which is `Stacks.SheafOfModules.pullbackTensorIso` and is
  defined by the six-step chain of bijections `Stacks.SheafOfModules.pullbackTensorHomEquiv`;
* the mate of **Stacks 0E8H** under the tensor--internal-Hom correspondence of Stacks 03EO,
  which is `Stacks.SheafOfModules.ExtensionByZero.tensorRestrictionComparison`.

This file identifies them, through the identification of Stacks 04IX
`AlgebraicGeometry.RingedSite.localizationPullbackToposIsoRestriction` of the pullback along `π`
with restriction.

## Why this identification is what Stacks 0GN2 needs

It is the one input of the localization square of Stacks 04J0 for the canonical map of
Stacks 0GMX that the development does not already have. The square is reached by feeding
`Stacks.SheafOfModules.InternalHom.toposPullbackInternalHomMap_compOf` the same composite twice,
once as `f` after `j_U` and once as `j_V` after `f_V`; what the resulting identity has to be
solved for is the restriction of the canonical map of `f`, and solving needs the canonical map of
each *localization* to be invertible. By `tensorEvaluation_injective` together with
`Stacks.SheafOfModules.ExtensionByZero.tensorEvaluation_internalHomRestrictionNatIso`, that
invertibility reduces to exactly the identification proved here, Stacks 0E8H being an
isomorphism.

The route through mates is circular and is not taken: `CategoryTheory.mateEquiv` is a genuine
bijection, and the mate of a tensor comparison under the correspondence of Stacks 03EO is the
canonical map of Stacks 0GMX by construction, so identifying the two comparisons by taking mates
reduces the statement to itself.

## Main results

* `Stacks.SheafOfModules.localizationPullbackTensorIso_hom_app`: the comparison of Stacks 03EL at
  the localization morphism, read through Stacks 04IX, is the mate of Stacks 0E8H.
* `Stacks.SheafOfModules.localizationPullbackTensorIso_inv_app`: the same identity for the
  inverse comparison, which is the direction the canonical map of Stacks 0GMX is built from.

## References

* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 03EO](https://stacks.math.columbia.edu/tag/03EO)
* [Stacks Project, Tag 04IX](https://stacks.math.columbia.edu/tag/04IX)
* [Stacks Project, Tag 0E8H](https://stacks.math.columbia.edu/tag/0E8H)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CategoryTheory.Sheaf
open Stacks.Sheaves.RingedToposModules
open scoped TensorProduct
open Stacks.SheafOfModules.Tensor (sheafTensor)

namespace Stacks.SheafOfModules

universe u

open Stacks.SheafOfModules.InternalHom

section Localization

variable (X : RingedSite.{u, u, u}) (U : X.C)
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [(X.J.over U).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.HasSheafCompose (forget RingCat.{u})]
  [(X.J.over U).HasSheafCompose (forget RingCat.{u})]
  [X.J.HasSheafCompose (forget CommRingCat.{u})]
  [(X.J.over U).HasSheafCompose (forget CommRingCat.{u})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [(X.J.over U).HasSheafCompose (forget AddCommGrpCat.{u})]
  [HasWeakSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify (X.J.over U) AddCommGrpCat.{u}]
  [(X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
  (A F : _root_.SheafOfModules.{u} (Tensor.ringSheaf X.O))

local instance scalarUnitMap_localization_isIso
    (T : _root_.SheafOfModules.{u} (Tensor.ringSheaf X.O)) :
    IsIso (scalarUnitMap (X.localizationMorphism U) T) :=
  scalarUnitMap_isIso (X.localizationMorphism U) T

/-- The native scalar unit followed by restriction is the identity. -/
theorem scalarUnitMap_localization_comp_restriction
    (T : _root_.SheafOfModules.{u} (Tensor.ringSheaf X.O)) :
    scalarUnitMap (X.localizationMorphism U) T ≫
      (X.localizationModuleForgetTarget U).map
        ((X.localizationPullbackIsoRestriction U).hom.app T) = 𝟙 _ :=
  X.map_unit_comp_localizationPullbackIsoRestriction U T

/-- The native comparison is the inverse of the scalar unit, with the unit kept folded. -/
theorem inv_scalarUnitMap_localization
    (T : _root_.SheafOfModules.{u} (Tensor.ringSheaf X.O)) :
    inv (scalarUnitMap (X.localizationMorphism U) T) =
      (X.localizationModuleForgetTarget U).map
        ((X.localizationPullbackIsoRestriction U).hom.app T) :=
  IsIso.inv_eq_of_hom_inv_id (scalarUnitMap_localization_comp_restriction X U T)

/-- The restriction of a tensor pairing, after the scalar units are canceled, on sections. -/
theorem localization_tensorTranspose_sections
    (T : _root_.SheafOfModules.{u} (Tensor.ringSheaf X.O))
    (t : A.val ⊗ F.val ⟶ T.val) (W : (X.over U).Cᵒᵖ)
    (a : ((X.localizationMorphism U).pullbackModules.obj A).val.obj W)
    (b : ((X.localizationMorphism U).pullbackModules.obj F).val.obj W) :
    (sectionsFunctor (X.over U).J W).map
      ((X.localizationMorphism U).toToposHom.inverseImage.map
          (pairingOfTensorHom (hO := (Tensor.ringSheaf X.O).property) t) ≫
        (scalarUnitMap (X.localizationMorphism U) T ≫
          (X.localizationModuleForgetTarget U).map
            ((X.localizationPullbackIsoRestriction U).hom.app T)))
      (Functor.prodObjMk
        (P := (X.localizationMorphism U).toToposHom.inverseImage ⋙
          sectionsFunctor (X.over U).J W)
        ((sectionsFunctor (X.over U).J W).map
          (inv (scalarUnitMap (X.localizationMorphism U) A)) a)
        ((sectionsFunctor (X.over U).J W).map
          (inv (scalarUnitMap (X.localizationMorphism U) F)) b)) =
      t.app (Opposite.op (Opposite.unop W).left)
        ((((X.localizationPullbackIsoRestriction U).hom.app A).val.app W) a ⊗ₜ[((X.O.obj ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj
            (Opposite.op (Opposite.unop W).left))]
          (((X.localizationPullbackIsoRestriction U).hom.app F).val.app W) b) := by
  let S := sectionsFunctor (X.over U).J W
  let L := (X.localizationMorphism U).toToposHom.inverseImage
  let p := L.map (pairingOfTensorHom (A := A) (B := F) (N := T)
    (hO := (Tensor.ringSheaf X.O).property) t)
  let v := Functor.prodObjMk (P := L ⋙ S)
    (A := moduleSheaf (Tensor.ringSheaf X.O) A)
    (B := moduleSheaf (Tensor.ringSheaf X.O) F)
    (S.map (inv (scalarUnitMap (X.localizationMorphism U) A)) a)
    (S.map (inv (scalarUnitMap (X.localizationMorphism U) F)) b)
  refine (S.map_comp_apply p _ v).trans ?_
  refine (congrArg (fun m ↦ S.map m (S.map p v))
    (scalarUnitMap_localization_comp_restriction X U T)).trans ?_
  refine (S.map_id_apply _ (S.map p v)).trans ?_
  have ha := congrArg (fun m ↦ S.map m a) (inv_scalarUnitMap_localization X U A)
  have hb := congrArg (fun m ↦ S.map m b) (inv_scalarUnitMap_localization X U F)
  refine (congrArg₂ (fun x y ↦ S.map p (Functor.prodObjMk (P := L ⋙ S)
    (A := moduleSheaf (Tensor.ringSheaf X.O) A)
    (B := moduleSheaf (Tensor.ringSheaf X.O) F) x y)) ha hb).trans ?_
  exact pairingApp_pairingOfTensorHom (hO := (Tensor.ringSheaf X.O).property) t
    (Opposite.op (Opposite.unop W).left) _ _

/-- **The comparison of Stacks 03EL at a localization morphism is the mate of Stacks 0E8H.**
Read through the identification of Stacks 04IX of the pullback along the localization with
restriction to the slice site, the comparison `π^*(A ⊗_O F) ⟶ π^*A ⊗_{O|_U} π^*F` of Stacks 03EL
followed by the transport of its two factors is the comparison
`A|_U ⊗_{O|_U} F|_U ⟶ (A ⊗_O F)|_U` of Stacks 0E8H's mate, read backwards. -/
theorem localizationPullbackTensorIso_hom_app :
    (X.localizationPullbackIsoRestriction U).hom.app
        (((sheafTensor X.O).obj A).obj F) =
      (Stacks.SheafOfModules.pullbackTensorIso
            (X.localizationMorphism U)).hom.app (A, F) ≫
        (tensorTransportFirst X U A ((X.localizationPullbackIsoRestriction U).hom.app A)
            ((X.localizationMorphism U).pullbackModules.obj F) ≫
          tensorTransportSecond X U A F
            ((X.localizationPullbackIsoRestriction U).hom.app F)) ≫
          (ExtensionByZero.tensorRestrictionComparison X U F).natTrans.app A := by
  -- The comparison of Stacks 03EL is the chain applied to the identity
  -- (`Stacks.SheafOfModules.pullbackTensorIso_hom_app`, an equality by `rfl`), so precomposing
  -- with it is the inverse chain by naturality in the sheaf of values.
  refine Eq.trans ?_ ((congrArg
      (fun m ↦ (Stacks.SheafOfModules.pullbackTensorHomEquiv
        (X.localizationMorphism U) A F _).symm m) (Category.id_comp _).symm).trans
    (Stacks.SheafOfModules.pullbackTensorHomEquiv_symm_naturality
      (X.localizationMorphism U) A F (𝟙 _) _))
  refine ((Stacks.SheafOfModules.pullbackTensorHomEquiv
    (X.localizationMorphism U) A F _).eq_symm_apply).2 ?_
  refine (Stacks.SheafOfModules.pullbackTensorHomEquiv_eq_iff_pairingApp_unit
    (X.localizationMorphism U) A F _ _ _).2 ?_
  intro W a b
  refine (ExtensionByZero.transport_comp_tensorRestrictionComparison_val_app_unit_tmul_tensorTransportComp
    X U F A ((X.localizationPullbackIsoRestriction U).hom.app A)
    ((X.localizationPullbackIsoRestriction U).hom.app F) W a b).trans ?_
  refine Eq.trans ?_ (pairingApp_pullbackTensorBilinEquiv_tensorTranspose
    (X.localizationMorphism U) A F (((sheafTensor X.O).obj A).obj F)
    ((_root_.SheafOfModules.overFunctor (Tensor.ringSheaf X.O) U).obj
      (((sheafTensor X.O).obj A).obj F))
    ((PresheafOfModules.sheafificationAdjunction
      (R := Tensor.ringSheaf X.O) (𝟙 _)).unit.app (A.val ⊗ F.val))
    ((X.localizationPullbackIsoRestriction U).hom.app (((sheafTensor X.O).obj A).obj F))
    W a b).symm
  exact (localization_tensorTranspose_sections X U A F
    (((sheafTensor X.O).obj A).obj F)
    ((PresheafOfModules.sheafificationAdjunction
      (R := Tensor.ringSheaf X.O) (𝟙 _)).unit.app (A.val ⊗ F.val)) W a b).symm

/-- **The inverse comparison of Stacks 03EL at a localization morphism is the mate of
Stacks 0E8H.** This is the direction the canonical map of Stacks 0GMX is built from, since
`toposPullbackEvaluation` is `(pullbackTensorIso _).inv.app _` followed by a pullback.

The two directions differ by cancelling the comparison of Stacks 03EL against its inverse, which
is `Stacks.SheafOfModules.InternalHom.cancelWhisker`: the junction between the curried tensor
product of Stacks 0GMW and the bifunctor of Stacks 03EL sits at an explicit argument of that
abstract lemma, where it is free, rather than inside a hand-written statement, where it costs the
elaborator's whole budget. -/
theorem localizationPullbackTensorIso_inv_app :
    (Stacks.SheafOfModules.pullbackTensorIso
            (X.localizationMorphism U)).inv.app (A, F) ≫
        (X.localizationPullbackIsoRestriction U).hom.app
          (((sheafTensor X.O).obj A).obj F) =
      (tensorTransportFirst X U A ((X.localizationPullbackIsoRestriction U).hom.app A)
            ((X.localizationMorphism U).pullbackModules.obj F) ≫
          tensorTransportSecond X U A F
            ((X.localizationPullbackIsoRestriction U).hom.app F)) ≫
        (ExtensionByZero.tensorRestrictionComparison X U F).natTrans.app A :=
  cancelWhisker
    ((Stacks.SheafOfModules.pullbackTensorIso
      (X.localizationMorphism U)).inv_hom_id_app (A, F))
    (localizationPullbackTensorIso_hom_app X U A F)

end Localization

end Stacks.SheafOfModules

end
