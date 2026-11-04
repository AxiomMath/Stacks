module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorSectionsSite
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SliceExteriorAlgebra

/-!
# The tensorator of restriction to a slice site, on local sections

`Stacks.SheafOfModules.SliceRestriction.overFunctorMonoidal` makes restriction of sheaves of
modules to the slice site `(C/U, J.over U)` a monoidal functor for the monoidal structure of
Tag 01CA, by transporting a monoidal structure obtained from the localization of presheaves of
modules along sheafification. This file computes its tensorator on local sections: it carries the
pure tensor `a ⊗ b` of two local sections, formed on the slice site, to the pure tensor of the same
two sections formed on `C`. Restriction to a slice only reindexes the sections, and the
computation shows that the localized tensorator cancels.

## Main results

* `Stacks.SliceRestrictionTensorSections.delta_overFunctorMonoidal_eq`: the oplax tensorator of
  `overFunctorMonoidal` is the comparison of restriction with sheafification followed by the
  sheafification of a morphism of presheaves of modules.
* `Stacks.SliceRestrictionTensorSections.mu_overFunctorMonoidal_shSec_tmul`: **the tensorator of
  `overFunctorMonoidal` on a local pure tensor**.

## Implementation notes

The computation follows `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorSectionsSite`,
which carries it out for the inverse image along a continuous functor of sites, with the lifting
isomorphism there replaced by `Stacks.SheafOfModules.SliceRestriction.sliceSheafifyIso`. That
isomorphism is the inverse of the morphism adjoint to the restricted sheafification unit, so its
value on a unit image is read off `SheafOfModules.sheafificationHomEquiv_symm_app`.

## References

* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 03EH](https://stacks.math.columbia.edu/tag/03EH)
-/

@[expose] public section

open CategoryTheory MonoidalCategory Functor PresheafOfModules
open Stacks.SheafOfModules.TensorSheafification
open Stacks.SheafOfModules.SliceRestriction Stacks.PullbackTensorSectionsSite

open scoped TensorProduct

universe u

namespace Stacks.SliceRestrictionTensorSections

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  (𝒪 : Cᵒᵖ ⥤ CommRingCat.{u}) (h𝒪 : Presheaf.IsSheaf J (structureRingPresheaf 𝒪)) (U : C)
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]
  [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify (J.over U) AddCommGrpCat.{u}]

section Localized

attribute [local instance] Stacks.SheafOfModules.monoidalCategory
attribute [local instance] Stacks.SheafOfModules.sheafifyFunctor_monoidal
attribute [local instance] sliceCompSheafifyMonoidal

/-- Restriction to the slice site commutes with sheafification, at a presheaf of modules: the
component of `Stacks.SheafOfModules.SliceRestriction.sliceSheafifyIso`. -/
noncomputable def lift (P : PresheafOfModules.{u} (structureRingPresheaf 𝒪)) :
    (overFunctor 𝒪 h𝒪 U).obj ((Stacks.SheafOfModules.sheafifyFunctor 𝒪 h𝒪).obj P) ≅
      (sliceSheafify 𝒪 h𝒪 U).obj ((sliceFunctor 𝒪 U).obj P) :=
  (sliceSheafifyIso 𝒪 h𝒪 U).app P

/-- The oplax tensorator of restriction of presheaves of modules followed by sheafification. -/
noncomputable def sliceDelta (P Q : PresheafOfModules.{u} (structureRingPresheaf 𝒪)) :
    (sliceSheafify 𝒪 h𝒪 U).obj ((sliceFunctor 𝒪 U).obj (P ⊗ Q)) ⟶
      (sliceSheafify 𝒪 h𝒪 U).obj ((sliceFunctor 𝒪 U).obj P) ⊗
        (sliceSheafify 𝒪 h𝒪 U).obj ((sliceFunctor 𝒪 U).obj Q) :=
  Functor.OplaxMonoidal.δ (self := (sliceCompSheafifyMonoidal 𝒪 h𝒪 U).toOplaxMonoidal)
    (sliceFunctor 𝒪 U ⋙ sliceSheafify 𝒪 h𝒪 U) P Q

/-- The oplax tensorator of the presheaf-level restriction. -/
noncomputable def preDelta (P Q : PresheafOfModules.{u} (structureRingPresheaf 𝒪)) :
    (sliceFunctor 𝒪 U).obj (P ⊗ Q) ⟶ (sliceFunctor 𝒪 U).obj P ⊗ (sliceFunctor 𝒪 U).obj Q :=
  Functor.OplaxMonoidal.δ (sliceFunctor 𝒪 U) P Q

omit [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}] in
/-- `sliceDelta` is the sheafification of `preDelta` followed by the oplax tensorator `shDelta` of
sheafification on the slice site. -/
theorem sliceDelta_eq (P Q : PresheafOfModules.{u} (structureRingPresheaf 𝒪)) :
    sliceDelta 𝒪 h𝒪 U P Q =
      (sliceSheafify 𝒪 h𝒪 U).map (preDelta 𝒪 U P Q) ≫
        shDelta (sliceRingPresheaf 𝒪 U) (isSheaf_sliceRingPresheaf 𝒪 h𝒪 U)
          ((sliceFunctor 𝒪 U).obj P) ((sliceFunctor 𝒪 U).obj Q) :=
  rfl

/-- The tensorator of `overFunctorMonoidalLocalized` at a pair of sheafified presheaves, expressed
through `sliceSheafifyIso` and the tensorators of `sliceFunctor 𝒪 U ⋙ sliceSheafify 𝒪 h𝒪 U` and
of sheafification. -/
theorem overFunctorMonoidalLocalized_mu (P Q : PresheafOfModules.{u} (structureRingPresheaf 𝒪)) :
    Functor.LaxMonoidal.μ (self := (overFunctorMonoidalLocalized 𝒪 h𝒪 U).toLaxMonoidal)
        (overFunctor 𝒪 h𝒪 U)
        ((Stacks.SheafOfModules.sheafifyFunctor 𝒪 h𝒪).obj P)
        ((Stacks.SheafOfModules.sheafifyFunctor 𝒪 h𝒪).obj Q) =
      (((sliceSheafifyIso 𝒪 h𝒪 U).hom.app P ⊗ₘ (sliceSheafifyIso 𝒪 h𝒪 U).hom.app Q) ≫
          Functor.LaxMonoidal.μ (self := (sliceCompSheafifyMonoidal 𝒪 h𝒪 U).toLaxMonoidal)
            (sliceFunctor 𝒪 U ⋙ sliceSheafify 𝒪 h𝒪 U) P Q) ≫
        (sliceSheafifyIso 𝒪 h𝒪 U).inv.app (P ⊗ Q) ≫
          (overFunctor 𝒪 h𝒪 U).map
            (Functor.OplaxMonoidal.δ (Stacks.SheafOfModules.sheafifyFunctor 𝒪 h𝒪) P Q) :=
  Localization.Monoidal.functorMonoidalOfComp_μ
    (Stacks.SheafOfModules.sheafifyFunctor 𝒪 h𝒪) (Stacks.SheafOfModules.localIso (J := J) 𝒪)
    (overFunctor 𝒪 h𝒪 U) (sliceFunctor 𝒪 U ⋙ sliceSheafify 𝒪 h𝒪 U) P Q

private theorem map_shDelta_comp_delta_aux
    (P Q : PresheafOfModules.{u} (structureRingPresheaf 𝒪)) :
    (overFunctor 𝒪 h𝒪 U).map
            (Functor.OplaxMonoidal.δ (Stacks.SheafOfModules.sheafifyFunctor 𝒪 h𝒪) P Q) ≫
        Functor.OplaxMonoidal.δ (self := (overFunctorMonoidalLocalized 𝒪 h𝒪 U).toOplaxMonoidal)
          (overFunctor 𝒪 h𝒪 U) ((Stacks.SheafOfModules.sheafifyFunctor 𝒪 h𝒪).obj P)
            ((Stacks.SheafOfModules.sheafifyFunctor 𝒪 h𝒪).obj Q) =
      (sliceSheafifyIso 𝒪 h𝒪 U).hom.app (P ⊗ Q) ≫
        Functor.OplaxMonoidal.δ (self := (sliceCompSheafifyMonoidal 𝒪 h𝒪 U).toOplaxMonoidal)
            (sliceFunctor 𝒪 U ⋙ sliceSheafify 𝒪 h𝒪 U) P Q ≫
          ((sliceSheafifyIso 𝒪 h𝒪 U).inv.app P ⊗ₘ (sliceSheafifyIso 𝒪 h𝒪 U).inv.app Q) := by
  refine eq_of_comp_id_comp (k := Functor.LaxMonoidal.μ
      (self := (overFunctorMonoidalLocalized 𝒪 h𝒪 U).toLaxMonoidal) (overFunctor 𝒪 h𝒪 U)
        ((Stacks.SheafOfModules.sheafifyFunctor 𝒪 h𝒪).obj P)
        ((Stacks.SheafOfModules.sheafifyFunctor 𝒪 h𝒪).obj Q) ≫
      (overFunctor 𝒪 h𝒪 U).map
        (Functor.LaxMonoidal.μ (Stacks.SheafOfModules.sheafifyFunctor 𝒪 h𝒪) P Q)) ?_ ?_
  · rw [Category.assoc, ← Category.assoc
        (Functor.OplaxMonoidal.δ (self := (overFunctorMonoidalLocalized 𝒪 h𝒪 U).toOplaxMonoidal)
          (overFunctor 𝒪 h𝒪 U) ((Stacks.SheafOfModules.sheafifyFunctor 𝒪 h𝒪).obj P)
            ((Stacks.SheafOfModules.sheafifyFunctor 𝒪 h𝒪).obj Q)),
      Functor.Monoidal.δ_μ, Category.id_comp]
    exact Functor.Monoidal.map_δ_μ (Stacks.SheafOfModules.sheafifyFunctor 𝒪 h𝒪)
      (overFunctor 𝒪 h𝒪 U) P Q
  · rw [overFunctorMonoidalLocalized_mu]
    simp only [Category.assoc, Functor.Monoidal.map_δ_μ_assoc, Iso.inv_hom_id_app_assoc,
      Functor.Monoidal.μ_δ_assoc, MonoidalCategory.tensorHom_comp_tensorHom, Iso.hom_inv_id_app,
      MonoidalCategory.id_tensorHom_id]
    rfl

/-- **The localization tensorator cancels, at a pair of sheafified presheaves.** -/
theorem map_shDelta_comp_delta (P Q : PresheafOfModules.{u} (structureRingPresheaf 𝒪)) :
    (overFunctor 𝒪 h𝒪 U).map (shDelta 𝒪 h𝒪 P Q) ≫
        Functor.OplaxMonoidal.δ (self := (overFunctorMonoidalLocalized 𝒪 h𝒪 U).toOplaxMonoidal)
          (overFunctor 𝒪 h𝒪 U) ((Stacks.SheafOfModules.sheafifyFunctor 𝒪 h𝒪).obj P)
            ((Stacks.SheafOfModules.sheafifyFunctor 𝒪 h𝒪).obj Q) =
      (lift 𝒪 h𝒪 U (P ⊗ Q)).hom ≫
        sliceDelta 𝒪 h𝒪 U P Q ≫ ((lift 𝒪 h𝒪 U P).inv ⊗ₘ (lift 𝒪 h𝒪 U Q).inv) :=
  map_shDelta_comp_delta_aux 𝒪 h𝒪 U P Q

/-- **The localization tensorator cancels, at an arbitrary pair of sheaves of modules.** -/
theorem map_tensorComparisonIso_inv_comp_delta
    (A B : SheafOfModules.{u} (structureSheaf 𝒪 h𝒪)) :
    (overFunctor 𝒪 h𝒪 U).map (tensorComparisonIso 𝒪 h𝒪 A B).inv ≫
        Functor.OplaxMonoidal.δ (self := (overFunctorMonoidalLocalized 𝒪 h𝒪 U).toOplaxMonoidal)
          (overFunctor 𝒪 h𝒪 U) A B =
      (lift 𝒪 h𝒪 U (valp 𝒪 h𝒪 A ⊗ valp 𝒪 h𝒪 B)).hom ≫
        sliceDelta 𝒪 h𝒪 U (valp 𝒪 h𝒪 A) (valp 𝒪 h𝒪 B) ≫
          (((lift 𝒪 h𝒪 U (valp 𝒪 h𝒪 A)).inv ≫
              (overFunctor 𝒪 h𝒪 U).map (valIso 𝒪 h𝒪 A).hom) ⊗ₘ
            ((lift 𝒪 h𝒪 U (valp 𝒪 h𝒪 B)).inv ≫
              (overFunctor 𝒪 h𝒪 U).map (valIso 𝒪 h𝒪 B).hom)) := by
  rw [tensorComparisonIso_inv, Functor.map_comp, Category.assoc,
    ← Functor.OplaxMonoidal.δ_natural, ← Category.assoc, map_shDelta_comp_delta,
    Category.assoc, Category.assoc, MonoidalCategory.tensorHom_comp_tensorHom]

/-- **The canonical map from the restriction of the underlying presheaf of a sheaf of modules into
the underlying presheaf of its restriction**: the sheafification unit on the slice site followed
by the comparison of restriction with sheafification. -/
noncomputable def overLeg (A : SheafOfModules.{u} (structureSheaf 𝒪 h𝒪)) :
    (sliceFunctor 𝒪 U).obj (valp 𝒪 h𝒪 A) ⟶
      valp (sliceRingPresheaf 𝒪 U) (isSheaf_sliceRingPresheaf 𝒪 h𝒪 U)
        ((overFunctor 𝒪 h𝒪 U).obj A) :=
  shUnitHom (sliceRingPresheaf 𝒪 U) (isSheaf_sliceRingPresheaf 𝒪 h𝒪 U)
      ((sliceFunctor 𝒪 U).obj (valp 𝒪 h𝒪 A)) ≫
    valHom (sliceRingPresheaf 𝒪 U) (isSheaf_sliceRingPresheaf 𝒪 h𝒪 U)
      ((lift 𝒪 h𝒪 U (valp 𝒪 h𝒪 A)).inv ≫ (overFunctor 𝒪 h𝒪 U).map (valIso 𝒪 h𝒪 A).hom)

omit [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}] in
/-- The sheafification of the presheaf-level oplax tensorator, followed by the comparison of the
localized tensor product with the tensor product sheaf and by the sheafification of a tensor
product of morphisms, is a single sheafification. -/
theorem map_preDelta_comp (P Q : PresheafOfModules.{u} (structureRingPresheaf 𝒪))
    {M N : SheafOfModules.{u} (sliceStructureSheaf 𝒪 h𝒪 U)}
    (gA : (sliceSheafify 𝒪 h𝒪 U).obj ((sliceFunctor 𝒪 U).obj P) ⟶ M)
    (gB : (sliceSheafify 𝒪 h𝒪 U).obj ((sliceFunctor 𝒪 U).obj Q) ⟶ N) :
    (sliceSheafify 𝒪 h𝒪 U).map (preDelta 𝒪 U P Q) ≫
        (shDelta (sliceRingPresheaf 𝒪 U) (isSheaf_sliceRingPresheaf 𝒪 h𝒪 U)
            ((sliceFunctor 𝒪 U).obj P) ((sliceFunctor 𝒪 U).obj Q) ≫
          (tensorComparisonIso (sliceRingPresheaf 𝒪 U) (isSheaf_sliceRingPresheaf 𝒪 h𝒪 U)
              ((sliceSheafify 𝒪 h𝒪 U).obj ((sliceFunctor 𝒪 U).obj P))
              ((sliceSheafify 𝒪 h𝒪 U).obj ((sliceFunctor 𝒪 U).obj Q))).hom ≫
            (sliceSheafify 𝒪 h𝒪 U).map
              (valHom (sliceRingPresheaf 𝒪 U) (isSheaf_sliceRingPresheaf 𝒪 h𝒪 U) gA ⊗ₘ
                valHom (sliceRingPresheaf 𝒪 U) (isSheaf_sliceRingPresheaf 𝒪 h𝒪 U) gB)) =
      (sliceSheafify 𝒪 h𝒪 U).map (preDelta 𝒪 U P Q ≫
        ((shUnitHom (sliceRingPresheaf 𝒪 U) (isSheaf_sliceRingPresheaf 𝒪 h𝒪 U)
              ((sliceFunctor 𝒪 U).obj P) ≫
            valHom (sliceRingPresheaf 𝒪 U) (isSheaf_sliceRingPresheaf 𝒪 h𝒪 U) gA) ⊗ₘ
          (shUnitHom (sliceRingPresheaf 𝒪 U) (isSheaf_sliceRingPresheaf 𝒪 h𝒪 U)
              ((sliceFunctor 𝒪 U).obj Q) ≫
            valHom (sliceRingPresheaf 𝒪 U) (isSheaf_sliceRingPresheaf 𝒪 h𝒪 U) gB))) := by
  rw [← Category.assoc (shDelta (sliceRingPresheaf 𝒪 U) (isSheaf_sliceRingPresheaf 𝒪 h𝒪 U)
      ((sliceFunctor 𝒪 U).obj P) ((sliceFunctor 𝒪 U).obj Q)),
    shDelta_comp_tensorComparisonIso_hom, ← Functor.map_comp,
    MonoidalCategory.tensorHom_comp_tensorHom, ← Functor.map_comp]

end Localized


section Strict

attribute [local instance] Stacks.SheafOfModules.Strict.monoidalCategory

/-- **The oplax tensorator of `overFunctorMonoidal`** is the tensorator of the localized monoidal
structure conjugated by `tensorComparisonIso`. -/
theorem delta_overFunctorMonoidal (A B : SheafOfModules.{u} (structureSheaf 𝒪 h𝒪)) :
    Functor.OplaxMonoidal.δ (self := (overFunctorMonoidal 𝒪 h𝒪 U).toOplaxMonoidal)
        (overFunctor 𝒪 h𝒪 U) A B =
      (overFunctor 𝒪 h𝒪 U).map (tensorComparisonIso 𝒪 h𝒪 A B).inv ≫
        (Functor.OplaxMonoidal.δ (self := (overFunctorMonoidalLocalized 𝒪 h𝒪 U).toOplaxMonoidal)
            (overFunctor 𝒪 h𝒪 U) A B ≫
          (tensorComparisonIso (sliceRingPresheaf 𝒪 U) (isSheaf_sliceRingPresheaf 𝒪 h𝒪 U)
            ((overFunctor 𝒪 h𝒪 U).obj A) ((overFunctor 𝒪 h𝒪 U).obj B)).hom) := by
  have h : Functor.OplaxMonoidal.δ (self := (overFunctorMonoidal 𝒪 h𝒪 U).toOplaxMonoidal)
        (overFunctor 𝒪 h𝒪 U) A B =
      (overFunctor 𝒪 h𝒪 U).map (tensorComparisonIso 𝒪 h𝒪 A B).inv ≫
        (Functor.OplaxMonoidal.δ (self := (overFunctorMonoidalLocalized 𝒪 h𝒪 U).toOplaxMonoidal)
            (overFunctor 𝒪 h𝒪 U) A B ≫
          Functor.OplaxMonoidal.δ
            (self := (fromLocalizedMonoidalMonoidal (sliceRingPresheaf 𝒪 U)
              (isSheaf_sliceRingPresheaf 𝒪 h𝒪 U)).toOplaxMonoidal)
            (fromLocalizedMonoidal (sliceRingPresheaf 𝒪 U) (isSheaf_sliceRingPresheaf 𝒪 h𝒪 U))
            ((overFunctor 𝒪 h𝒪 U).obj A) ((overFunctor 𝒪 h𝒪 U).obj B)) := rfl
  rw [h, delta_fromLoc]
  rfl

/-- **The oplax tensorator of `overFunctorMonoidal`, computed**: the comparison of restriction
with sheafification followed by the sheafification of the presheaf-level oplax tensorator and of
the tensor product of the two canonical maps `overLeg`. -/
theorem delta_overFunctorMonoidal_eq (A B : SheafOfModules.{u} (structureSheaf 𝒪 h𝒪)) :
    Functor.OplaxMonoidal.δ (self := (overFunctorMonoidal 𝒪 h𝒪 U).toOplaxMonoidal)
        (overFunctor 𝒪 h𝒪 U) A B =
      (lift 𝒪 h𝒪 U (valp 𝒪 h𝒪 A ⊗ valp 𝒪 h𝒪 B)).hom ≫
        (sliceSheafify 𝒪 h𝒪 U).map
          (preDelta 𝒪 U (valp 𝒪 h𝒪 A) (valp 𝒪 h𝒪 B) ≫
            (overLeg 𝒪 h𝒪 U A ⊗ₘ overLeg 𝒪 h𝒪 U B)) := by
  rw [delta_overFunctorMonoidal, ← Category.assoc, map_tensorComparisonIso_inv_comp_delta,
    Category.assoc, Category.assoc, tensorComparisonIso_naturality, sliceDelta_eq,
    Category.assoc]
  exact congrArg (fun z => (lift 𝒪 h𝒪 U (valp 𝒪 h𝒪 A ⊗ valp 𝒪 h𝒪 B)).hom ≫ z)
    (map_preDelta_comp 𝒪 h𝒪 U (valp 𝒪 h𝒪 A) (valp 𝒪 h𝒪 B) _ _)

end Strict


section Sections

/-- **The comparison of restriction with sheafification, inverted, on a unit image**: it carries
the slice sheafification unit image of a local section to the sheafification unit image of the same
section over the underlying object of `C`. -/
theorem lift_inv_shSec (P : PresheafOfModules.{u} (structureRingPresheaf 𝒪)) (V : (Over U)ᵒᵖ)
    (m : P.obj (Opposite.op V.unop.left)) :
    (lift 𝒪 h𝒪 U P).inv.val.app V
        (shSec (sliceRingPresheaf 𝒪 U) (isSheaf_sliceRingPresheaf 𝒪 h𝒪 U)
          ((sliceFunctor 𝒪 U).obj P) V m) =
      shSec 𝒪 h𝒪 P (Opposite.op V.unop.left) m := by
  have h : (lift 𝒪 h𝒪 U P).inv = (sliceComparison 𝒪 h𝒪 U).app P := rfl
  rw [h, sliceComparison_app]
  have : Presheaf.IsLocallyInjective (J.over U) (𝟙 (sliceStructureSheaf 𝒪 h𝒪 U).obj) :=
    Presheaf.isLocallyInjective_of_injective _ _ (fun _ => Function.injective_id)
  have : Presheaf.IsLocallySurjective (J.over U) (𝟙 (sliceStructureSheaf 𝒪 h𝒪 U).obj) :=
    Presheaf.isLocallySurjective_of_surjective _ _ (fun _ => Function.surjective_id)
  exact @SheafOfModules.sheafificationHomEquiv_symm_app _ _ _ _ _ _ ‹_› ‹_› _ _ _ _
    (sliceUnit 𝒪 h𝒪 U P) V m

/-- The comparison of restriction with sheafification on a unit image. -/
theorem lift_hom_shSec (P : PresheafOfModules.{u} (structureRingPresheaf 𝒪)) (V : (Over U)ᵒᵖ)
    (m : P.obj (Opposite.op V.unop.left)) :
    (lift 𝒪 h𝒪 U P).hom.val.app V (shSec 𝒪 h𝒪 P (Opposite.op V.unop.left) m) =
      shSec (sliceRingPresheaf 𝒪 U) (isSheaf_sliceRingPresheaf 𝒪 h𝒪 U)
        ((sliceFunctor 𝒪 U).obj P) V m := by
  rw [← lift_inv_shSec 𝒪 h𝒪 U P V m]
  exact SheafOfModules.hom_congr_app_apply (lift 𝒪 h𝒪 U P).inv_hom_id V _

/-- **The canonical map `overLeg` is the identity on local sections.** -/
theorem overLeg_app (A : SheafOfModules.{u} (structureSheaf 𝒪 h𝒪)) (V : (Over U)ᵒᵖ)
    (x : (valp 𝒪 h𝒪 A).obj (Opposite.op V.unop.left)) :
    Hom.app (overLeg 𝒪 h𝒪 U A) V x = x := by
  refine Eq.trans (SheafOfModules.comp_val_app_apply (lift 𝒪 h𝒪 U (valp 𝒪 h𝒪 A)).inv
    ((overFunctor 𝒪 h𝒪 U).map (valIso 𝒪 h𝒪 A).hom) V
    (shSec (sliceRingPresheaf 𝒪 U) (isSheaf_sliceRingPresheaf 𝒪 h𝒪 U)
      ((sliceFunctor 𝒪 U).obj (valp 𝒪 h𝒪 A)) V x)) ?_
  rw [lift_inv_shSec]
  exact valIso_hom_shSec 𝒪 h𝒪 A (Opposite.op V.unop.left) x

end Sections


section StrictSections

attribute [local instance] Stacks.SheafOfModules.Strict.monoidalCategory

/-- **The oplax tensorator of `overFunctorMonoidal` on a local pure tensor**: it carries the pure
tensor of two sections over the underlying object of `V`, formed on `C`, to the pure tensor of
the same two sections formed on the slice site. -/
theorem delta_overFunctorMonoidal_shSec_tmul (A B : SheafOfModules.{u} (structureSheaf 𝒪 h𝒪))
    (V : (Over U)ᵒᵖ) (a : (valp 𝒪 h𝒪 A).obj (Opposite.op V.unop.left))
    (b : (valp 𝒪 h𝒪 B).obj (Opposite.op V.unop.left)) :
    (Functor.OplaxMonoidal.δ (self := (overFunctorMonoidal 𝒪 h𝒪 U).toOplaxMonoidal)
          (overFunctor 𝒪 h𝒪 U) A B).val.app V
        (shSec 𝒪 h𝒪 (valp 𝒪 h𝒪 A ⊗ valp 𝒪 h𝒪 B) (Opposite.op V.unop.left) (a ⊗ₜ b)) =
      shSec (sliceRingPresheaf 𝒪 U) (isSheaf_sliceRingPresheaf 𝒪 h𝒪 U)
        (valp (sliceRingPresheaf 𝒪 U) (isSheaf_sliceRingPresheaf 𝒪 h𝒪 U)
            ((overFunctor 𝒪 h𝒪 U).obj A) ⊗
          valp (sliceRingPresheaf 𝒪 U) (isSheaf_sliceRingPresheaf 𝒪 h𝒪 U)
            ((overFunctor 𝒪 h𝒪 U).obj B)) V (a ⊗ₜ b) := by
  refine Eq.trans (SheafOfModules.hom_congr_app_apply
    (delta_overFunctorMonoidal_eq 𝒪 h𝒪 U A B) V
    (shSec 𝒪 h𝒪 (valp 𝒪 h𝒪 A ⊗ valp 𝒪 h𝒪 B) (Opposite.op V.unop.left) (a ⊗ₜ b))) ?_
  refine Eq.trans (SheafOfModules.comp_val_app_apply
    (lift 𝒪 h𝒪 U (valp 𝒪 h𝒪 A ⊗ valp 𝒪 h𝒪 B)).hom
    ((sliceSheafify 𝒪 h𝒪 U).map
      (preDelta 𝒪 U (valp 𝒪 h𝒪 A) (valp 𝒪 h𝒪 B) ≫
        (overLeg 𝒪 h𝒪 U A ⊗ₘ overLeg 𝒪 h𝒪 U B))) V
    (shSec 𝒪 h𝒪 (valp 𝒪 h𝒪 A ⊗ valp 𝒪 h𝒪 B) (Opposite.op V.unop.left) (a ⊗ₜ b))) ?_
  refine Eq.trans (congrArg (fun z => ((sliceSheafify 𝒪 h𝒪 U).map
      (preDelta 𝒪 U (valp 𝒪 h𝒪 A) (valp 𝒪 h𝒪 B) ≫
        (overLeg 𝒪 h𝒪 U A ⊗ₘ overLeg 𝒪 h𝒪 U B))).val.app V z)
    (lift_hom_shSec 𝒪 h𝒪 U (valp 𝒪 h𝒪 A ⊗ valp 𝒪 h𝒪 B) V (a ⊗ₜ b))) ?_
  refine Eq.trans (map_shSec (sliceRingPresheaf 𝒪 U) (isSheaf_sliceRingPresheaf 𝒪 h𝒪 U)
    (preDelta 𝒪 U (valp 𝒪 h𝒪 A) (valp 𝒪 h𝒪 B) ≫
      (overLeg 𝒪 h𝒪 U A ⊗ₘ overLeg 𝒪 h𝒪 U B)) V (a ⊗ₜ b)) ?_
  refine congrArg (shSec (sliceRingPresheaf 𝒪 U) (isSheaf_sliceRingPresheaf 𝒪 h𝒪 U) _ V) ?_
  refine Eq.trans (PresheafOfModules.comp_app_apply
    (preDelta 𝒪 U (valp 𝒪 h𝒪 A) (valp 𝒪 h𝒪 B))
    (overLeg 𝒪 h𝒪 U A ⊗ₘ overLeg 𝒪 h𝒪 U B) V (a ⊗ₜ b)) ?_
  exact (presheafTensorHom_tmul (sliceRingPresheaf 𝒪 U) (overLeg 𝒪 h𝒪 U A)
    (overLeg 𝒪 h𝒪 U B) V a b).trans
    (congrArg₂ _ (overLeg_app 𝒪 h𝒪 U A V a) (overLeg_app 𝒪 h𝒪 U B V b))

/-- **The tensorator of `overFunctorMonoidal` on a local pure tensor**: restriction to the slice
site carries the pure tensor `a ⊗ b` formed on the slice to the pure tensor formed on `C`. -/
theorem mu_overFunctorMonoidal_shSec_tmul (A B : SheafOfModules.{u} (structureSheaf 𝒪 h𝒪))
    (V : (Over U)ᵒᵖ) (a : (valp 𝒪 h𝒪 A).obj (Opposite.op V.unop.left))
    (b : (valp 𝒪 h𝒪 B).obj (Opposite.op V.unop.left)) :
    (Functor.LaxMonoidal.μ (self := (overFunctorMonoidal 𝒪 h𝒪 U).toLaxMonoidal)
          (overFunctor 𝒪 h𝒪 U) A B).val.app V
        (shSec (sliceRingPresheaf 𝒪 U) (isSheaf_sliceRingPresheaf 𝒪 h𝒪 U)
          (valp (sliceRingPresheaf 𝒪 U) (isSheaf_sliceRingPresheaf 𝒪 h𝒪 U)
              ((overFunctor 𝒪 h𝒪 U).obj A) ⊗
            valp (sliceRingPresheaf 𝒪 U) (isSheaf_sliceRingPresheaf 𝒪 h𝒪 U)
              ((overFunctor 𝒪 h𝒪 U).obj B)) V (a ⊗ₜ b)) =
      shSec 𝒪 h𝒪 (valp 𝒪 h𝒪 A ⊗ valp 𝒪 h𝒪 B) (Opposite.op V.unop.left) (a ⊗ₜ b) := by
  rw [← delta_overFunctorMonoidal_shSec_tmul 𝒪 h𝒪 U A B V a b]
  exact SheafOfModules.hom_congr_app_apply
    (Functor.Monoidal.δ_μ (self := overFunctorMonoidal 𝒪 h𝒪 U) (overFunctor 𝒪 h𝒪 U) A B) V _

end StrictSections

end Stacks.SliceRestrictionTensorSections

end
