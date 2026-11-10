module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleRestrictModuleTensorSections
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeIdEtaleChartTensor
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.Algebra
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.ZariskiReadingAdjunction

/-!
# The Zariski reading of a tensor product, on pure tensors

Let `U` be an object of the big fppf site with underlying scheme `T`. The Zariski reading of an
`𝒪`-module on the small étale site of the algebraic space `yoneda.obj U` is its direct image along
`AlgebraicGeometry.Space.selfOpensFunctor`: the inclusion of the Zariski opens of `T` into the
small étale site of `T`, followed by the inverse of the comparison of Stacks 04M0. This file
builds the comparison `𝓟|_T ⊗ 𝓠|_T ⟶ (𝓟 ⊗ 𝓠)|_T` of the reading with tensor products and
computes its two halves on pure tensors.

## Main results

* `Stacks.SheafOfModules.tensorCounitComposite_reindex_val_app_unit_tmul`: the lax comparison
  of the inverse of a reindexing along an equivalence of sites (its unit, Stacks 03EL at the
  reindexing, its two counits) sends `x ⊗ y` to `x ⊗ y`;
  `Stacks.SheafOfModules.isIso_tensorCounitComposite_reindex`: it is an isomorphism.
* `AlgebraicGeometry.Space.representedSmallEtaleModuleInverseTensorHom` and
  `representedSmallEtaleModuleInverseTensorHom_val_app_unit_tmul`: that comparison at the
  equivalence of Stacks 04M0, on pure tensors.
* `AlgebraicGeometry.Space.zariskiReadingTensor_comp_val_app_unit_tmul`: a composite of the
  identifications of the reading with the Zariski restriction, the inverse of
  `AlgebraicGeometry.SmallEtale.restrictModuleTensorIso`, and the restriction of a middle map `t`
  sends `x ⊗ y` to `x ⊗ y` as soon as `t` does.
* `AlgebraicGeometry.Space.zariskiReadingTensorHom`: **the comparison
  `𝓟|_T ⊗ 𝓠|_T ⟶ (𝓟 ⊗ 𝓠)|_T` of the reading with tensor products**, for quasi-coherent modules;
  `isIso_zariskiReadingTensorHom`: it is an isomorphism;
  `zariskiReadingTensorHom_val_app_unit_tmul`: it sends `x ⊗ y` to `x ⊗ y`.

## Implementation notes

The étale-site half of the comparison is
`AlgebraicGeometry.RingedSite.HomGeneral.tensorCounitComposite` at the reindexing, with the
structure map of the reindexing spelled `Stacks.SheafOfModules.reindexBackSharp` of the
structure sheaf of rings of the small étale site of `T`. Its value on a pure tensor is stated
over the structure sheaf of the algebraic space; the generic statement is over the transported
structure sheaf `Stacks.SheafOfModules.reindexCommRing`, and the two are bridged by the `rfl`
lemmas `tensorSheafUnit_reindexCommRing_app_tmul` and
`sheafificationUnit_representedSmallEtaleModuleEquivalence_inverse_tmul`. The generic statement
is instantiated before the morphism is passed
(`Stacks.SheafOfModules.val_app_unit_tmul_of_eq_tensorCounitComposite_reindex`), so that its
instance arguments are fixed when the morphism is unified.

The composite of the four pieces mixes morphisms of `Scheme.Modules` (whose morphisms are
`AlgebraicGeometry.Scheme.Modules.Hom`) with morphisms of sheaves of modules over the ring sheaf
of the Zariski ringed site. Its value on a pure tensor can only be computed from the composite
as `zariskiReadingTensor_comp_val_app_unit_tmul` elaborates it; a definition elaborating the same
composite separately produces a term whose comparison with that one exhausts the heartbeat budget.
So `zariskiReadingTensorHom` is the composite chosen through
`exists_zariskiReadingTensorHom`, whose witness is assigned by unification from the statement of
`zariskiReadingTensor_comp_val_app_unit_tmul`; it is determined by its values on pure tensors.

**No `@[stacks]` attribute.** Tags 03EL, 03DU and 04M0 are registered on the declarations this
file composes.

## References

* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open Stacks.Sheaves.RingedToposModules Stacks.PresheafOfModules.ChangeOfRings
open scoped TensorProduct

namespace Stacks.SheafOfModules

section Reindex

universe u v w

variable {C : Type u} [Category.{v} C] {C' : Type u} [Category.{v} C']
  {J : GrothendieckTopology C} (J' : GrothendieckTopology C')
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J'.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  (e : C' ≌ C) [e.functor.IsContinuous J' J] [e.inverse.IsContinuous J J']
  (O : Sheaf J CommRingCat.{w})
  [hmos : _root_.IsMorphismOfSites.{w} e.inverse J J']
  [J.HasSheafCompose (forget RingCat.{w})] [J'.HasSheafCompose (forget RingCat.{w})]
  [J.HasSheafCompose (forget AddCommGrpCat.{w})] [J'.HasSheafCompose (forget AddCommGrpCat.{w})]
  [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J' AddCommGrpCat.{w}] [J'.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [EssentiallySmall.{w} C] [LocallySmall.{w} C']

/-- **The lax comparison of the inverse of the reindexing on pure tensors**: it sends `x ⊗ y` to
`x ⊗ y`. -/
theorem tensorCounitComposite_reindex_val_app_unit_tmul
    (P Q : _root_.SheafOfModules.{w} (Tensor.ringSheaf (reindexCommRing J' e O)))
    (V : Cᵒᵖ)
    (x : ((reindexEquivalence.{w, w, u, v, u, v} e (Tensor.ringSheaf O)).inverse.obj P).val.obj V)
    (y : ((reindexEquivalence.{w, w, u, v, u, v} e (Tensor.ringSheaf O)).inverse.obj Q).val.obj V) :
    ((reindexRingedSiteHom J' e O).tensorCounitComposite (pullbackModulesReindexIso J' e O)
      (φ := reindexBackSharp e (Tensor.ringSheaf O))
      (reindexEquivalence.{w, w, u, v, u, v} e (Tensor.ringSheaf O)).toAdjunction P Q).val.app V
        (_root_.PresheafOfModules.Hom.app ((PresheafOfModules.sheafificationAdjunction
            (R := Tensor.ringSheaf O) (𝟙 (Tensor.ringSheaf O).obj)).unit.app
          (PresheafOfModules.tensorObj (O := O.obj)
            ((reindexEquivalence.{w, w, u, v, u, v} e (Tensor.ringSheaf O)).inverse.obj P).val
            ((reindexEquivalence.{w, w, u, v, u, v} e (Tensor.ringSheaf O)).inverse.obj Q).val)) V
          (x ⊗ₜ[(O.obj ⋙ forget₂ CommRingCat RingCat).obj V] y)) =
      _root_.PresheafOfModules.Hom.app ((PresheafOfModules.sheafificationAdjunction
          (R := Tensor.ringSheaf (reindexCommRing J' e O))
          (𝟙 (Tensor.ringSheaf (reindexCommRing J' e O)).obj)).unit.app
        (PresheafOfModules.tensorObj (O := (reindexCommRing J' e O).obj) P.val Q.val))
        (e.inverse.op.obj V)
        (x ⊗ₜ[((reindexCommRing J' e O).obj ⋙ forget₂ CommRingCat RingCat).obj
          (e.inverse.op.obj V)] y) :=
  (reindexRingedSiteHom J' e O).tensorCounitComposite_val_app_unit_tmul
      (pullbackModulesReindexIso J' e O)
      (φ := reindexBackSharp e (Tensor.ringSheaf O))
      (reindexEquivalence.{w, w, u, v, u, v} e (Tensor.ringSheaf O)).toAdjunction
      (fun F V x => (reindexRingedSiteHom J' e O)
        |>.pullbackModulesToposIsoGeneral_trans_leftAdjointUniq_inv_app_val_app_unit
          (reindexEquivalence.{w, w, u, v, u, v} e (Tensor.ringSheaf O)).toAdjunction F V x)
      P Q V x y

/-- `Stacks.SheafOfModules.tensorCounitComposite_reindex_val_app_unit_tmul` for any morphism `t`
equal to the lax comparison, its source and target spelled through the inverse of the reindexing
equivalence. -/
theorem val_app_unit_tmul_of_eq_tensorCounitComposite_reindex
    (P Q : _root_.SheafOfModules.{w} (Tensor.ringSheaf (reindexCommRing J' e O)))
    (t : ((Tensor.sheafTensor O).obj ((reindexEquivalence.{w, w, u, v, u, v} (J' := J') e
        (Tensor.ringSheaf O)).inverse.obj P)).obj
        ((reindexEquivalence.{w, w, u, v, u, v} (J' := J') e (Tensor.ringSheaf O)).inverse.obj Q) ⟶
      (reindexEquivalence.{w, w, u, v, u, v} (J' := J') e (Tensor.ringSheaf O)).inverse.obj
        (((Tensor.sheafTensor (reindexCommRing J' e O)).obj P).obj Q))
    (ht : t = (reindexRingedSiteHom J' e O).tensorCounitComposite (pullbackModulesReindexIso J' e O)
      (φ := reindexBackSharp e (Tensor.ringSheaf O))
      (reindexEquivalence.{w, w, u, v, u, v} e (Tensor.ringSheaf O)).toAdjunction P Q)
    (V : Cᵒᵖ)
    (x : ((reindexEquivalence.{w, w, u, v, u, v} (J' := J') e (Tensor.ringSheaf O)).inverse.obj
      P).val.obj V)
    (y : ((reindexEquivalence.{w, w, u, v, u, v} (J' := J') e (Tensor.ringSheaf O)).inverse.obj
      Q).val.obj V) :
    t.val.app V
        (_root_.PresheafOfModules.Hom.app ((PresheafOfModules.sheafificationAdjunction
            (R := Tensor.ringSheaf O) (𝟙 (Tensor.ringSheaf O).obj)).unit.app
          (PresheafOfModules.tensorObj (O := O.obj)
            ((reindexEquivalence.{w, w, u, v, u, v} (J' := J') e (Tensor.ringSheaf O)).inverse.obj
              P).val
            ((reindexEquivalence.{w, w, u, v, u, v} (J' := J') e (Tensor.ringSheaf O)).inverse.obj
              Q).val)) V
          (x ⊗ₜ[(O.obj ⋙ forget₂ CommRingCat RingCat).obj V] y)) =
      _root_.PresheafOfModules.Hom.app ((PresheafOfModules.sheafificationAdjunction
          (R := Tensor.ringSheaf (reindexCommRing J' e O))
          (𝟙 (Tensor.ringSheaf (reindexCommRing J' e O)).obj)).unit.app
        (PresheafOfModules.tensorObj (O := (reindexCommRing J' e O).obj) P.val Q.val))
        (e.inverse.op.obj V)
        (x ⊗ₜ[((reindexCommRing J' e O).obj ⋙ forget₂ CommRingCat RingCat).obj
          (e.inverse.op.obj V)] y) := by
  subst ht
  exact tensorCounitComposite_reindex_val_app_unit_tmul J' e O P Q V x y

/-- **The lax comparison of the inverse of the reindexing is an isomorphism**: its unit and its
two counits are those of an equivalence, and Stacks 03EL is an isomorphism. -/
theorem isIso_tensorCounitComposite_reindex
    (P Q : _root_.SheafOfModules.{w} (Tensor.ringSheaf (reindexCommRing J' e O))) :
    IsIso ((reindexRingedSiteHom J' e O).tensorCounitComposite (pullbackModulesReindexIso J' e O)
      (φ := reindexBackSharp e (Tensor.ringSheaf O))
      (reindexEquivalence.{w, w, u, v, u, v} e (Tensor.ringSheaf O)).toAdjunction P Q) := by
  have hu : ∀ X, IsIso ((reindexEquivalence.{w, w, u, v, u, v} (J' := J') e
      (Tensor.ringSheaf O)).toAdjunction.unit.app X) := fun X => by
    rw [Equivalence.toAdjunction_unit]
    infer_instance
  have hc : ∀ X, IsIso ((reindexEquivalence.{w, w, u, v, u, v} (J' := J') e
      (Tensor.ringSheaf O)).toAdjunction.counit.app X) := fun X => by
    rw [Equivalence.toAdjunction_counit]
    infer_instance
  unfold AlgebraicGeometry.RingedSite.HomGeneral.tensorCounitComposite
  refine IsIso.comp_isIso' (hu _) (@Functor.map_isIso _ _ _ _ _ _ _ _ ?_)
  refine IsIso.comp_isIso' (Iso.isIso_hom _) (IsIso.comp_isIso' ?_ ?_)
  · exact @Functor.map_isIso _ _ _ _ _ _ _ _ (hc Q)
  · exact @NatIso.isIso_app_of_isIso _ _ _ _ _ _ _ (@Functor.map_isIso _ _ _ _ _ _ _ _ (hc P)) _

end Reindex

end Stacks.SheafOfModules

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (U : BigFppfOver B S hS)

/-- **The inverse of the comparison of Stacks 04M0 preserves quasi-coherence**: for a
quasi-coherent `𝒪`-module `𝓟` on the small étale site of `yoneda.obj U`, the module it is read as
on the small étale site of the scheme underlying `U` is quasi-coherent. -/
theorem isQuasicoherentOnSite_representedSmallEtaleModuleEquivalence_inverse_obj
    (P : Modules.{u, u} B S hS (yoneda.obj U)
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U))
    (hP : P.IsQuasicoherentOnSite) :
    ((representedSmallEtaleModuleEquivalence B S hS U).inverse.obj P).IsQuasicoherentOnSite :=
  (isQuasicoherentOnSite_representedSmallEtaleModule_iff B S hS U
      ((representedSmallEtaleModuleEquivalence B S hS U).inverse.obj P)).1
    (SheafOfModules.IsQuasicoherentOnSite.of_iso
      ((representedSmallEtaleModuleEquivalence B S hS U).counitIso.app P).symm hP)

/-- **The lax comparison of the inverse of the comparison of Stacks 04M0 with tensor products**:
`E⁻¹𝓟 ⊗ E⁻¹𝓠 ⟶ E⁻¹(𝓟 ⊗ 𝓠)` on the small étale site of the scheme underlying `U`, for the
equivalence `E` of `AlgebraicGeometry.Space.representedSmallEtaleModuleEquivalence`. It is
`AlgebraicGeometry.RingedSite.HomGeneral.tensorCounitComposite` at the reindexing: the unit of
`E`, Stacks 03EL at the reindexing, and the two counits of `E`. -/
def representedSmallEtaleModuleInverseTensorHom
    (P Q : Modules.{u, u} B S hS (yoneda.obj U)
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U)) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor
    (representedSchemeCommRingStructureSheaf B S hS U)).obj
        ((representedSmallEtaleModuleEquivalence B S hS U).inverse.obj P)).obj
        ((representedSmallEtaleModuleEquivalence B S hS U).inverse.obj Q) ⟶
      (representedSmallEtaleModuleEquivalence B S hS U).inverse.obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
          (structureSheaf B S hS (yoneda.obj U)
            (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U))).obj P).obj Q) :=
  (Stacks.SheafOfModules.reindexRingedSiteHom (SmallEtale.topology B S hS (yoneda.obj U))
      (representedSmallEtaleEquivalence B S hS U)
      (representedSchemeCommRingStructureSheaf B S hS U)).tensorCounitComposite
    (Stacks.SheafOfModules.pullbackModulesReindexIso (SmallEtale.topology B S hS (yoneda.obj U))
      (representedSmallEtaleEquivalence B S hS U)
      (representedSchemeCommRingStructureSheaf B S hS U))
    (φ := Stacks.SheafOfModules.reindexBackSharp (representedSmallEtaleEquivalence B S hS U)
      (representedSchemeStructureSheaf B S hS U))
    (representedSmallEtaleModuleEquivalence B S hS U).toAdjunction P Q

/-- The map exhibiting the tensor product of two `𝒪`-modules on the small étale site of
`yoneda.obj U` as a sheafification, on a pure tensor, is the same whether the structure sheaf is
spelled as the structure sheaf of the algebraic space or as the structure sheaf of the scheme
underlying `U` transported along the comparison of Stacks 04M0: the two are equal by `rfl`. -/
theorem tensorSheafUnit_reindexCommRing_app_tmul
    (P Q : Modules.{u, u} B S hS (yoneda.obj U)
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U))
    (W : (SmallEtale B S hS (yoneda.obj U))ᵒᵖ) (a : P.val.obj W) (b : Q.val.obj W) :
    (PresheafOfModules.tensorSheafUnit (Osharp := Stacks.SheafOfModules.reindexCommRing
      (SmallEtale.topology B S hS (yoneda.obj U)) (representedSmallEtaleEquivalence B S hS U)
      (representedSchemeCommRingStructureSheaf B S hS U)) P Q).app W (a ⊗ₜ b) =
    (PresheafOfModules.tensorSheafUnit (Osharp := (structureSheaf B S hS (yoneda.obj U)
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U))) P Q).app W (a ⊗ₜ b) := rfl

/-- The map exhibiting a tensor product on the small étale site of the scheme underlying `U` as
a sheafification, on a pure tensor of sections of two modules read through the inverse of the
comparison of Stacks 04M0, is the same whether that inverse is spelled as
`AlgebraicGeometry.Space.representedSmallEtaleModuleEquivalence` or as the reindexing
equivalence it is defined to be. -/
theorem sheafificationUnit_representedSmallEtaleModuleEquivalence_inverse_tmul
    (P Q : Modules.{u, u} B S hS (yoneda.obj U)
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U))
    (W : (_root_.AlgebraicGeometry.SmallEtale (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj U) U.left.property)ᵒᵖ)
    (a : ((representedSmallEtaleModuleEquivalence B S hS U).inverse.obj P).val.obj W)
    (b : ((representedSmallEtaleModuleEquivalence B S hS U).inverse.obj Q).val.obj W) :
    _root_.PresheafOfModules.Hom.app ((PresheafOfModules.sheafificationAdjunction
        (R := Stacks.SheafOfModules.Tensor.ringSheaf
        (representedSchemeCommRingStructureSheaf B S hS U))
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf
          (representedSchemeCommRingStructureSheaf B S hS U)).obj)).unit.app
      (PresheafOfModules.tensorObj (O := (representedSchemeCommRingStructureSheaf B S hS U).obj)
        ((representedSmallEtaleModuleEquivalence B S hS U).inverse.obj P).val
        ((representedSmallEtaleModuleEquivalence B S hS U).inverse.obj Q).val)) W
      (a ⊗ₜ[((representedSchemeCommRingStructureSheaf B S hS U).obj ⋙
        forget₂ CommRingCat RingCat).obj W] b) =
    _root_.PresheafOfModules.Hom.app ((PresheafOfModules.sheafificationAdjunction
        (R := Stacks.SheafOfModules.Tensor.ringSheaf
        (representedSchemeCommRingStructureSheaf B S hS U))
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf
          (representedSchemeCommRingStructureSheaf B S hS U)).obj)).unit.app
      (PresheafOfModules.tensorObj (O := (representedSchemeCommRingStructureSheaf B S hS U).obj)
        ((Stacks.SheafOfModules.reindexEquivalence.{u, u, u + 1, u, u + 1, u}
          (J' := SmallEtale.topology B S hS (yoneda.obj U))
          (representedSmallEtaleEquivalence B S hS U)
          (Stacks.SheafOfModules.Tensor.ringSheaf
            (representedSchemeCommRingStructureSheaf B S hS U))).inverse.obj P).val
        ((Stacks.SheafOfModules.reindexEquivalence.{u, u, u + 1, u, u + 1, u}
          (J' := SmallEtale.topology B S hS (yoneda.obj U))
          (representedSmallEtaleEquivalence B S hS U)
          (Stacks.SheafOfModules.Tensor.ringSheaf
            (representedSchemeCommRingStructureSheaf B S hS U))).inverse.obj Q).val)) W
      (a ⊗ₜ[((representedSchemeCommRingStructureSheaf B S hS U).obj ⋙
        forget₂ CommRingCat RingCat).obj W] b) := rfl

/-- **The lax comparison of the inverse of the comparison of Stacks 04M0 on pure tensors**: it
sends `a ⊗ b` to `a ⊗ b`, a local section over the étale scheme `W` being a local section over the
corresponding object of the small étale site of `yoneda.obj U`. -/
theorem representedSmallEtaleModuleInverseTensorHom_val_app_unit_tmul
    (P Q : Modules.{u, u} B S hS (yoneda.obj U)
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U))
    (W : (_root_.AlgebraicGeometry.SmallEtale (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj U) U.left.property)ᵒᵖ)
    (a : ((representedSmallEtaleModuleEquivalence B S hS U).inverse.obj P).val.obj W)
    (b : ((representedSmallEtaleModuleEquivalence B S hS U).inverse.obj Q).val.obj W) :
    (representedSmallEtaleModuleInverseTensorHom B S hS U P Q).val.app W
        (_root_.PresheafOfModules.Hom.app ((PresheafOfModules.sheafificationAdjunction
            (R := Stacks.SheafOfModules.Tensor.ringSheaf
              (representedSchemeCommRingStructureSheaf B S hS U))
            (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf
              (representedSchemeCommRingStructureSheaf B S hS U)).obj)).unit.app
          (PresheafOfModules.tensorObj (O := (representedSchemeCommRingStructureSheaf B S hS U).obj)
            ((representedSmallEtaleModuleEquivalence B S hS U).inverse.obj P).val
            ((representedSmallEtaleModuleEquivalence B S hS U).inverse.obj Q).val)) W
          (a ⊗ₜ[((representedSchemeCommRingStructureSheaf B S hS U).obj ⋙
            forget₂ CommRingCat RingCat).obj W] b)) =
      (PresheafOfModules.tensorSheafUnit (Osharp := (structureSheaf B S hS (yoneda.obj U)
          (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U))) P Q).app
        ((representedSmallEtaleEquivalence B S hS U).inverse.op.obj W)
        ((a : P.val.obj ((representedSmallEtaleEquivalence B S hS U).inverse.op.obj W)) ⊗ₜ
          (b : Q.val.obj ((representedSmallEtaleEquivalence B S hS U).inverse.op.obj W))) := by
  -- instantiate the generic statement with its instance arguments fixed before `t` is passed
  have h₀ := Stacks.SheafOfModules.val_app_unit_tmul_of_eq_tensorCounitComposite_reindex
    (SmallEtale.topology B S hS (yoneda.obj U)) (representedSmallEtaleEquivalence B S hS U)
    (representedSchemeCommRingStructureSheaf B S hS U) P Q
  have h := h₀ (representedSmallEtaleModuleInverseTensorHom B S hS U P Q) rfl W a b
  refine Eq.trans ?_ (tensorSheafUnit_reindexCommRing_app_tmul B S hS U P Q
    ((representedSmallEtaleEquivalence B S hS U).inverse.op.obj W) a b)
  rw [sheafificationUnit_representedSmallEtaleModuleEquivalence_inverse_tmul]
  exact h

/-- The value on a pure tensor of the composite of the identifications of the Zariski reading
with the Zariski restriction (`AlgebraicGeometry.Space.selfOpensPushforwardIso`), the inverse of
`AlgebraicGeometry.SmallEtale.restrictModuleTensorIso`, and the Zariski restriction of a map
`t : E⁻¹𝓟 ⊗ E⁻¹𝓠 ⟶ E⁻¹(𝓟 ⊗ 𝓠)` that sends `a ⊗ b` to `a ⊗ b`: it sends `x ⊗ y` to `x ⊗ y`. -/
theorem zariskiReadingTensor_comp_val_app_unit_tmul
    (P Q : Modules.{u, u} B S hS (yoneda.obj U)
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U))
    (hP' : ((representedSmallEtaleModuleEquivalence B S hS U).inverse.obj P).IsQuasicoherentOnSite)
    (hQ' : ((representedSmallEtaleModuleEquivalence B S hS U).inverse.obj Q).IsQuasicoherentOnSite)
    (t : ((Stacks.SheafOfModules.Tensor.sheafTensor
    (representedSchemeCommRingStructureSheaf B S hS U)).obj
    ((representedSmallEtaleModuleEquivalence B S hS U).inverse.obj P)).obj
        ((representedSmallEtaleModuleEquivalence B S hS U).inverse.obj Q) ⟶
      (representedSmallEtaleModuleEquivalence B S hS U).inverse.obj
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        (structureSheaf B S hS (yoneda.obj U)
          (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U))).obj P).obj Q))
    (ht : ∀ (W : (_root_.AlgebraicGeometry.SmallEtale (associatedBigEtaleSite B)
    ((BigFppfOver.toScheme B S hS).obj U)
        U.left.property)ᵒᵖ)
          (a : ((representedSmallEtaleModuleEquivalence B S hS U).inverse.obj P).val.obj W)
          (b : ((representedSmallEtaleModuleEquivalence B S hS U).inverse.obj Q).val.obj W),
      t.val.app W (_root_.PresheafOfModules.Hom.app ((PresheafOfModules.sheafificationAdjunction
            (R := Stacks.SheafOfModules.Tensor.ringSheaf
            (representedSchemeCommRingStructureSheaf B S hS U))
            (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf
            (representedSchemeCommRingStructureSheaf B S hS U)).obj)).unit.app
          (PresheafOfModules.tensorObj (O := (representedSchemeCommRingStructureSheaf B S hS U).obj)
            ((representedSmallEtaleModuleEquivalence B S hS U).inverse.obj P).val
            ((representedSmallEtaleModuleEquivalence B S hS U).inverse.obj Q).val)) W
          (a ⊗ₜ[((representedSchemeCommRingStructureSheaf B S hS U).obj ⋙ forget₂
          CommRingCat RingCat).obj W] b)) =
        (PresheafOfModules.tensorSheafUnit (Osharp := (structureSheaf B S hS (yoneda.obj U)
          (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U))) P Q).app
          ((representedSmallEtaleEquivalence B S hS U).inverse.op.obj W)
          ((a : P.val.obj ((representedSmallEtaleEquivalence B S hS U).inverse.op.obj W)) ⊗ₜ
            (b : Q.val.obj ((representedSmallEtaleEquivalence B S hS U).inverse.op.obj W))))
    (V : (((BigFppfOver.toScheme B S hS).obj U).zariskiRingedSite).Cᵒᵖ)
    (x : ((SheafOfModules.pushforward.{u} (selfOpensStructureMap B S hS U)).obj P).val.obj V)
    (y : ((SheafOfModules.pushforward.{u} (selfOpensStructureMap B S hS U)).obj Q).val.obj V) :
    (((Functor.uncurry.obj
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ((BigFppfOver.toScheme B S hS).obj U).zariskiRingedSite.toRingedTopos.O)).mapIso
      (Iso.prod (selfOpensPushforwardIso B S hS U P).symm
        (selfOpensPushforwardIso B S hS U Q).symm)).hom ≫
      (_root_.AlgebraicGeometry.SmallEtale.restrictModuleTensorIso (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj U) U.left.property
        ((representedSmallEtaleModuleEquivalence B S hS U).inverse.obj P)
        ((representedSmallEtaleModuleEquivalence B S hS U).inverse.obj Q) hP' hQ').inv ≫
      (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj U) U.left.property).map t ≫
      (selfOpensPushforwardIso B S hS U
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        (structureSheaf B S hS (yoneda.obj U)
          (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U))).obj P).obj Q)).hom).val.app V
        (_root_.PresheafOfModules.Hom.app ((PresheafOfModules.sheafificationAdjunction
            (R := Stacks.SheafOfModules.Tensor.ringSheaf
            ((BigFppfOver.toScheme B S hS).obj U).zariskiRingedSite.toRingedTopos.O)
            (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf
              ((BigFppfOver.toScheme B S hS).obj
                U).zariskiRingedSite.toRingedTopos.O).obj)).unit.app
          (PresheafOfModules.tensorObj
          (O := ((BigFppfOver.toScheme B S hS).obj U).zariskiRingedSite.toRingedTopos.O.obj)
            ((SheafOfModules.pushforward.{u} (selfOpensStructureMap B S hS U)).obj P).val
            ((SheafOfModules.pushforward.{u} (selfOpensStructureMap B S hS U)).obj Q).val)) V
          (x ⊗ₜ[(((BigFppfOver.toScheme B S hS).obj U).zariskiRingedSite.toRingedTopos.O.obj ⋙
          forget₂ CommRingCat RingCat).obj V]
            y)) =
      (PresheafOfModules.tensorSheafUnit (Osharp := (structureSheaf B S hS (yoneda.obj U)
          (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U))) P Q).app
        ((selfOpensFunctor B S hS U).op.obj V)
        ((x : P.val.obj ((selfOpensFunctor B S hS U).op.obj V)) ⊗ₜ
          (y : Q.val.obj ((selfOpensFunctor B S hS U).op.obj V))) := by
  have h1 := Stacks.SheafOfModules.sheafTensor_uncurry_map_val_app_unit_tmul_forget₂
    (X := ((BigFppfOver.toScheme B S hS).obj U).zariskiRingedSite.toRingedTopos)
    (selfOpensPushforwardIso B S hS U P).inv (selfOpensPushforwardIso B S hS U Q).inv V x y
  have h2 := _root_.AlgebraicGeometry.SmallEtale.restrictModuleTensorIso_inv_val_app_unit_tmul
    (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj U) U.left.property
    ((representedSmallEtaleModuleEquivalence B S hS U).inverse.obj P)
    ((representedSmallEtaleModuleEquivalence B S hS U).inverse.obj Q)
    hP' hQ' V ((selfOpensPushforwardIso B S hS U P).inv.val.app V x)
    ((selfOpensPushforwardIso B S hS U Q).inv.val.app V y)
  change (selfOpensPushforwardIso B S hS U
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
      (structureSheaf B S hS (yoneda.obj U)
          (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U))).obj P).obj Q)).hom.val.app V
      (t.val.app ((_root_.AlgebraicGeometry.SmallEtale.opensToSmallEtale (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj U)
        U.left.property).op.obj V)
        ((_root_.AlgebraicGeometry.SmallEtale.restrictModuleTensorIso (associatedBigEtaleSite B)
          ((BigFppfOver.toScheme B S hS).obj U) U.left.property
          ((representedSmallEtaleModuleEquivalence B S hS U).inverse.obj P)
          ((representedSmallEtaleModuleEquivalence B S hS U).inverse.obj Q) hP' hQ').inv.val.app V
          (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
              ((BigFppfOver.toScheme B S hS).obj U).zariskiRingedSite.toRingedTopos.O)).map
              (((selfOpensPushforwardIso B S hS U P).inv,
                (selfOpensPushforwardIso B S hS U Q).inv) : (_, _) ⟶ (_, _))).val.app V
            (_root_.PresheafOfModules.Hom.app ((PresheafOfModules.sheafificationAdjunction
            (R := Stacks.SheafOfModules.Tensor.ringSheaf
            ((BigFppfOver.toScheme B S hS).obj U).zariskiRingedSite.toRingedTopos.O)
            (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf
              ((BigFppfOver.toScheme B S hS).obj
                U).zariskiRingedSite.toRingedTopos.O).obj)).unit.app
          (PresheafOfModules.tensorObj
          (O := ((BigFppfOver.toScheme B S hS).obj U).zariskiRingedSite.toRingedTopos.O.obj)
            ((SheafOfModules.pushforward.{u} (selfOpensStructureMap B S hS U)).obj P).val
            ((SheafOfModules.pushforward.{u} (selfOpensStructureMap B S hS U)).obj Q).val)) V
          (x ⊗ₜ[(((BigFppfOver.toScheme B S hS).obj U).zariskiRingedSite.toRingedTopos.O.obj ⋙
          forget₂ CommRingCat RingCat).obj V]
            y))))) = _
  let F := fun z => (selfOpensPushforwardIso B S hS U
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
      (structureSheaf B S hS (yoneda.obj U)
          (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U))).obj P).obj Q)).hom.val.app V
      (t.val.app ((_root_.AlgebraicGeometry.SmallEtale.opensToSmallEtale (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj U)
        U.left.property).op.obj V) z)
  refine (congrArg (fun z => F ((_root_.AlgebraicGeometry.SmallEtale.restrictModuleTensorIso
    (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj U) U.left.property
    ((representedSmallEtaleModuleEquivalence B S hS U).inverse.obj P)
    ((representedSmallEtaleModuleEquivalence B S hS U).inverse.obj Q) hP' hQ').inv.val.app V z))
    h1).trans ((congrArg F h2).trans ?_)
  exact ht _ _ _


/-- **The comparison of the Zariski reading with tensor products exists**: for quasi-coherent
`𝒪`-modules `𝓟`, `𝓠` on the small étale site of `yoneda.obj U` there is an isomorphism
`𝓟|_T ⊗ 𝓠|_T ⟶ (𝓟 ⊗ 𝓠)|_T` on the Zariski site of the scheme `T` of `U` sending `x ⊗ y` to
`x ⊗ y`. It is the composite of
`AlgebraicGeometry.Space.zariskiReadingTensor_comp_val_app_unit_tmul` with the lax comparison
`AlgebraicGeometry.Space.representedSmallEtaleModuleInverseTensorHom`. -/
theorem exists_zariskiReadingTensorHom
    (P Q : Modules.{u, u} B S hS (yoneda.obj U)
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U))
    (hP : P.IsQuasicoherentOnSite) (hQ : Q.IsQuasicoherentOnSite) :
    ∃ c : ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ((BigFppfOver.toScheme B S hS).obj U).zariskiRingedSite.toRingedTopos.O).obj
      ((SheafOfModules.pushforward.{u} (selfOpensStructureMap B S hS U)).obj P)).obj
      ((SheafOfModules.pushforward.{u} (selfOpensStructureMap B S hS U)).obj Q) ⟶
      (SheafOfModules.pushforward.{u} (selfOpensStructureMap B S hS U)).obj
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
      (structureSheaf B S hS (yoneda.obj U)
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U))).obj P).obj Q), IsIso c ∧
      ∀ (V : (((BigFppfOver.toScheme B S hS).obj U).zariskiRingedSite).Cᵒᵖ)
        (x : ((SheafOfModules.pushforward.{u} (selfOpensStructureMap B S hS U)).obj P).val.obj V)
        (y : ((SheafOfModules.pushforward.{u} (selfOpensStructureMap B S hS U)).obj Q).val.obj V),
        c.val.app V
            (_root_.PresheafOfModules.Hom.app ((PresheafOfModules.sheafificationAdjunction
                (R := Stacks.SheafOfModules.Tensor.ringSheaf
                ((BigFppfOver.toScheme B S hS).obj U).zariskiRingedSite.toRingedTopos.O)
                (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf
                ((BigFppfOver.toScheme B S hS).obj
                  U).zariskiRingedSite.toRingedTopos.O).obj)).unit.app
              (PresheafOfModules.tensorObj
              (O := ((BigFppfOver.toScheme B S hS).obj U).zariskiRingedSite.toRingedTopos.O.obj)
              ((SheafOfModules.pushforward.{u} (selfOpensStructureMap B S hS U)).obj P).val
              ((SheafOfModules.pushforward.{u} (selfOpensStructureMap B S hS U)).obj Q).val)) V
              (x ⊗ₜ[(((BigFppfOver.toScheme B S hS).obj U).zariskiRingedSite.toRingedTopos.O.obj ⋙
              forget₂ CommRingCat RingCat).obj V] y)) =
          (PresheafOfModules.tensorSheafUnit (Osharp := (structureSheaf B S hS (yoneda.obj U)
          (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U))) P Q).app
            ((selfOpensFunctor B S hS U).op.obj V)
            ((x : P.val.obj ((selfOpensFunctor B S hS U).op.obj V)) ⊗ₜ
              (y : Q.val.obj ((selfOpensFunctor B S hS U).op.obj V))) := by
  refine ⟨_, ?_, fun V x y => zariskiReadingTensor_comp_val_app_unit_tmul B S hS U P Q
    (isQuasicoherentOnSite_representedSmallEtaleModuleEquivalence_inverse_obj B S hS U P hP)
    (isQuasicoherentOnSite_representedSmallEtaleModuleEquivalence_inverse_obj B S hS U Q hQ)
    (representedSmallEtaleModuleInverseTensorHom B S hS U P Q)
    (representedSmallEtaleModuleInverseTensorHom_val_app_unit_tmul B S hS U P Q) V x y⟩
  have hm : IsIso (representedSmallEtaleModuleInverseTensorHom B S hS U P Q) :=
    Stacks.SheafOfModules.isIso_tensorCounitComposite_reindex
      (SmallEtale.topology B S hS (yoneda.obj U)) (representedSmallEtaleEquivalence B S hS U)
      (representedSchemeCommRingStructureSheaf B S hS U) P Q
  exact IsIso.comp_isIso' (Iso.isIso_hom _) (IsIso.comp_isIso' (Iso.isIso_inv _)
    (IsIso.comp_isIso' (((_root_.AlgebraicGeometry.SmallEtale.restrictModule
    (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj U) U.left.property).mapIso
        (@asIso _ _ _ _ (representedSmallEtaleModuleInverseTensorHom B S hS U P Q) hm)).isIso_hom)
      (Iso.isIso_hom _)))

/-- **The comparison of the Zariski reading with tensor products**: for quasi-coherent
`𝒪`-modules `𝓟`, `𝓠` on the small étale site of the algebraic space `yoneda.obj U`, the
isomorphism `𝓟|_T ⊗ 𝓠|_T ⟶ (𝓟 ⊗ 𝓠)|_T` on the Zariski site of the scheme `T` of `U` sending
`x ⊗ y` to `x ⊗ y`, where `(-)|_T` is the direct image along
`AlgebraicGeometry.Space.selfOpensFunctor`. It is determined by its values on pure tensors
(`AlgebraicGeometry.Space.zariskiReadingTensorHom_val_app_unit_tmul`), which generate. -/
def zariskiReadingTensorHom
    (P Q : Modules.{u, u} B S hS (yoneda.obj U)
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U))
    (hP : P.IsQuasicoherentOnSite) (hQ : Q.IsQuasicoherentOnSite) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
    ((BigFppfOver.toScheme B S hS).obj U).zariskiRingedSite.toRingedTopos.O).obj
    ((SheafOfModules.pushforward.{u} (selfOpensStructureMap B S hS U)).obj P)).obj
    ((SheafOfModules.pushforward.{u} (selfOpensStructureMap B S hS U)).obj Q) ⟶
    (SheafOfModules.pushforward.{u} (selfOpensStructureMap B S hS U)).obj
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
    (structureSheaf B S hS (yoneda.obj U)
    (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U))).obj P).obj Q) :=
  (exists_zariskiReadingTensorHom B S hS U P Q hP hQ).choose

/-- The comparison of the Zariski reading with tensor products is an isomorphism. -/
instance isIso_zariskiReadingTensorHom
    (P Q : Modules.{u, u} B S hS (yoneda.obj U)
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U))
    (hP : P.IsQuasicoherentOnSite) (hQ : Q.IsQuasicoherentOnSite) :
    IsIso (zariskiReadingTensorHom B S hS U P Q hP hQ) :=
  (exists_zariskiReadingTensorHom B S hS U P Q hP hQ).choose_spec.1

/-- **The comparison of the Zariski reading with tensor products on pure tensors**: it sends
`x ⊗ y` to `x ⊗ y`, a local section over the Zariski open `V` being a local section over the
corresponding étale chart. -/
theorem zariskiReadingTensorHom_val_app_unit_tmul
    (P Q : Modules.{u, u} B S hS (yoneda.obj U)
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U))
    (hP : P.IsQuasicoherentOnSite) (hQ : Q.IsQuasicoherentOnSite)
    (V : (((BigFppfOver.toScheme B S hS).obj U).zariskiRingedSite).Cᵒᵖ)
    (x : ((SheafOfModules.pushforward.{u} (selfOpensStructureMap B S hS U)).obj P).val.obj V)
    (y : ((SheafOfModules.pushforward.{u} (selfOpensStructureMap B S hS U)).obj Q).val.obj V) :
    (zariskiReadingTensorHom B S hS U P Q hP hQ).val.app V
        (_root_.PresheafOfModules.Hom.app ((PresheafOfModules.sheafificationAdjunction
            (R := Stacks.SheafOfModules.Tensor.ringSheaf
            ((BigFppfOver.toScheme B S hS).obj U).zariskiRingedSite.toRingedTopos.O)
            (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf
            ((BigFppfOver.toScheme B S hS).obj U).zariskiRingedSite.toRingedTopos.O).obj)).unit.app
          (PresheafOfModules.tensorObj
          (O := ((BigFppfOver.toScheme B S hS).obj U).zariskiRingedSite.toRingedTopos.O.obj)
          ((SheafOfModules.pushforward.{u} (selfOpensStructureMap B S hS U)).obj P).val
          ((SheafOfModules.pushforward.{u} (selfOpensStructureMap B S hS U)).obj Q).val)) V
          (x ⊗ₜ[(((BigFppfOver.toScheme B S hS).obj U).zariskiRingedSite.toRingedTopos.O.obj ⋙
          forget₂ CommRingCat RingCat).obj V] y)) =
      (PresheafOfModules.tensorSheafUnit (Osharp := (structureSheaf B S hS (yoneda.obj U)
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U))) P Q).app
        ((selfOpensFunctor B S hS U).op.obj V)
        ((x : P.val.obj ((selfOpensFunctor B S hS U).op.obj V)) ⊗ₜ
          (y : Q.val.obj ((selfOpensFunctor B S hS U).op.obj V))) :=
  (exists_zariskiReadingTensorHom B S hS U P Q hP hQ).choose_spec.2 V x y

end AlgebraicGeometry.Space


end
