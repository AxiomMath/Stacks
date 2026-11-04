module

public import StacksFrontier.CategoryTheory.Abelian.ExtMapFunctorial
public import StacksFrontier.Deformation.ToposThickening.Helpers.ObstructionClassIsoNaturality
public import StacksFrontier.Deformation.ToposThickening.Helpers.ObstructionCompatibilityPushforward
public import StacksFrontier.Deformation.ToposThickening.FlatThickeningFlatLifts

/-!
# The descended obstruction classes along a morphism of the targets of two thickenings

Let `i₁ : X ⟶ Y₁` and `i₂ : X ⟶ Y₂` be first order thickenings of one ringed topos and let
`j : Y₂ ⟶ Y₁` be a morphism of their targets
(`Deformation.ToposThickening.ThickeningTargetMorphism`),
with `Ψ₀ = ρ^*j_*` on modules over the bases. Write `Φₖ = iₖ_*` for the direct images of modules,
which are equivalences, so that an obstruction class of Stacks 08MF on `Yₖ` of the shape
`o(ΦₖF, ΦₖJₖ ⊗ ΦₖF, c)` descends to `Ext²_X(F, Jₖ ⊗ F)`
(`Deformation.ToposThickening.extDescentAddEquiv`).

Given an isomorphism `E : Ψ₀ ∘ Φ₂ ≅ Φ₁`, a map `λ : J₁ ⟶ J₂` of `O_X`-modules and isomorphisms
`eₖ : ΦₖJₖ ≅ ℐₖ` with the square ideals, this file shows that the descended class of the second
thickening is the descended class of the first pushed forward along `λ ⊗ F`, as soon as the
actions are compatible: `(e₁⁻¹ ⊗ 1) ≫ t₁ ≫ Φ₁(λ ⊗ F)` agrees with
`(1 ⊗ E⁻¹) ≫ θ ≫ Ψ₀((e₂⁻¹ ⊗ 1) ≫ t₂) ≫ E`, where `tₖ : ΦₖJ ⊗ ΦₖF ≅ Φₖ(J ⊗ F)` and
`θ : ℐ₁ ⊗ Ψ₀M ⟶ Ψ₀(ℐ₂ ⊗ M)` are the canonical maps. This is the functoriality of obstruction
classes along a morphism of thickenings used in the proof of Stacks 0CYF, read on `X`.

## Main results

* `Deformation.ToposThickening.mapExactFunctor_extDescentAddEquiv_symm`.
* `ThickeningTargetMorphism.extDescentAddEquiv_symm_existenceObstructionClass_eq_comp`.

This module is a helper and carries no `@[stacks]` attribute.

## References

* [Stacks Project, Tag 0CYC](https://stacks.math.columbia.edu/tag/0CYC)
* [Stacks Project, Tag 0CYF](https://stacks.math.columbia.edu/tag/0CYF)
* [Stacks Project, Tag 08MF](https://stacks.math.columbia.edu/tag/08MF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry (RingedTopos RingedToposHom)
open Stacks.Sheaves.ToposPushforward (pushforwardCommRingFunctor pushforwardModuleFunctor)

universe v u v₁ u₁ v₂ u₂ w e e'

namespace Deformation.ToposThickening

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

variable {X : RingedTopos.{v, u, w}} {Y₁ : RingedTopos.{v₁, u₁, w}} {Y₂ : RingedTopos.{v₂, u₂, w}}
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y₁.J.HasSheafCompose (forget RingCat.{w})]
  [Y₂.J.HasSheafCompose (forget RingCat.{w})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y₁.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y₂.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y₁.J.HasSheafCompose (forget AddCommGrpCat.{w})] [Y₂.J.HasSheafCompose (forget
      AddCommGrpCat.{w})]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify X.J AddCommGrpCat.{w}]
  [Y₁.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify Y₁.J AddCommGrpCat.{w}]
  [Y₂.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify Y₂.J AddCommGrpCat.{w}]
  [HasSheafify Y₁.J AddCommGrpCat.{w}] [HasSheafify Y₂.J AddCommGrpCat.{w}]
  {i₁ : RingedToposHom X Y₁} {i₂ : RingedToposHom X Y₂}

section Descent

variable {Y : RingedTopos.{v₁, u₁, w}} [Y.J.HasSheafCompose (forget RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify Y.J AddCommGrpCat.{w}]
  {i : RingedToposHom X Y} (hi : FirstOrderThickening i)
  [HasExt.{e} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i)))]
  [HasExt.{e'} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
  [EnoughInjectives (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]

/-- **The direct image of a descended class**: `i_*` of the class descended from
`o ∈ Ext^n(i_*F, i_*J ⊗ i_*F)` is `o` followed by `i_*J ⊗ i_*F ≅ i_*(J ⊗ F)`. -/
theorem mapExactFunctor_extDescentAddEquiv_symm
    (F J : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) {n : ℕ}
    (o : Abelian.Ext.{e} ((thickenedModulesFunctor i).obj F)
      (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i)).flip.obj
        ((thickenedModulesFunctor i).obj F)).obj ((thickenedModulesFunctor i).obj J)) n) :
    haveI := isEquivalence_thickenedModulesFunctor hi
    haveI : (thickenedModulesFunctor i).Additive :=
      Functor.additive_of_preserves_binary_products _
    ((extDescentAddEquiv hi F J n).symm o).mapExactFunctor (thickenedModulesFunctor i) =
      o.comp (Abelian.Ext.mk₀ (pushforwardModuleTensorIso hi F J).hom) (add_zero n) := by
  have := isEquivalence_thickenedModulesFunctor hi
  have : (thickenedModulesFunctor i).Additive := Functor.additive_of_preserves_binary_products _
  obtain ⟨x, rfl⟩ := (extDescentAddEquiv hi F J n).surjective o
  rw [AddEquiv.symm_apply_apply, extDescentAddEquiv_apply]
  have hm : (Abelian.Ext.mk₀ (C := SheafOfModules.{w}
        (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing
            i))) (pushforwardModuleTensorIso hi F J).inv).comp
      (Abelian.Ext.mk₀ (C := SheafOfModules.{w}
        (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing
            i))) (pushforwardModuleTensorIso hi F J).hom)
        (zero_add 0) =
        Abelian.Ext.mk₀ (C := SheafOfModules.{w}
          (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i))) (𝟙 _) :=
    (Abelian.Ext.mk₀_comp_mk₀ _ _).trans (congrArg _ (Iso.inv_hom_id _))
  exact Eq.symm ((Abelian.Ext.comp_assoc_of_third_deg_zero _ _ _ _).trans
    ((congrArg (fun z => (x.mapExactFunctor (thickenedModulesFunctor i)).comp z (add_zero n))
        hm).trans
      (Abelian.Ext.comp_mk₀_id _)))

end Descent

namespace ThickeningTargetMorphism

variable (D : ThickeningTargetMorphism i₁ i₂) (hi₁ : FirstOrderThickening i₁)
  (hi₂ : FirstOrderThickening i₂) (hj : FirstOrderThickening D.j)
  [HasExt.{e} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i₁)))]
  [HasExt.{e} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i₂)))]
  [HasExt.{e} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y₁.O))]
  [HasExt.{e} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y₂.O))]
  [HasExt.{e'} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
  [EnoughInjectives (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]

include hj in
/-- **The descended obstruction classes of two thickenings related by a morphism of their
targets**: for `E : Ψ₀ ∘ Φ₂ ≅ Φ₁`, `λ : J₁ ⟶ J₂` and `eₖ : ΦₖJₖ ≅ ℐₖ` whose actions are
compatible (`hkey`), the class `o(Φ₂F, Φ₂J₂ ⊗ Φ₂F, e₂⁻¹ ⊗ 1)` descended to `X` is the descended
class `o(Φ₁F, Φ₁J₁ ⊗ Φ₁F, e₁⁻¹ ⊗ 1)` pushed forward along `λ ⊗ F`. -/
theorem extDescentAddEquiv_symm_existenceObstructionClass_eq_comp
    (E : thickenedModulesFunctor i₂ ⋙ D.basePushforward ≅ thickenedModulesFunctor i₁)
    (F J₁ J₂ : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (lam : J₁ ⟶ J₂)
    (e₁ : (thickenedModulesFunctor i₁).obj J₁ ≅ hi₁.I)
    (e₂ : (thickenedModulesFunctor i₂).obj J₂ ≅ hi₂.I)
    (hkey : ((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i₁)).flip.obj
          ((thickenedModulesFunctor i₁).obj F)).map e₁.inv ≫
        (pushforwardModuleTensorIso hi₁ F J₁).hom ≫
          (thickenedModulesFunctor i₁).map
            (((Stacks.SheafOfModules.Tensor.sheafTensor X.O).flip.obj F).map lam) =
      ((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i₁)).obj hi₁.I).map (E.inv.app F) ≫
        D.idealTensorMap hi₁ hi₂ ((thickenedModulesFunctor i₂).obj F) ≫
          D.basePushforward.map
            (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i₂)).flip.obj
                ((thickenedModulesFunctor i₂).obj F)).map e₂.inv ≫
              (pushforwardModuleTensorIso hi₂ F J₂).hom) ≫
          E.hom.app (((Stacks.SheafOfModules.Tensor.sheafTensor X.O).flip.obj F).obj J₂)) :
    (extDescentAddEquiv hi₂ F J₂ 2).symm
        (existenceObstructionClass hi₂ ((thickenedModulesFunctor i₂).obj F) _
          (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i₂)).flip.obj
            ((thickenedModulesFunctor i₂).obj F)).map e₂.inv)) =
      ((extDescentAddEquiv hi₁ F J₁ 2).symm
        (existenceObstructionClass hi₁ ((thickenedModulesFunctor i₁).obj F) _
          (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i₁)).flip.obj
            ((thickenedModulesFunctor i₁).obj F)).map e₁.inv))).comp
        (Abelian.Ext.mk₀ (((Stacks.SheafOfModules.Tensor.sheafTensor X.O).flip.obj F).map lam))
        (add_zero 2) := by
  have := isEquivalence_thickenedModulesFunctor hi₁
  have := isEquivalence_thickenedModulesFunctor hi₂
  have : (thickenedModulesFunctor i₁).Additive := Functor.additive_of_preserves_binary_products _
  have : (thickenedModulesFunctor i₂).Additive := Functor.additive_of_preserves_binary_products _
  have := (D.basePushforward_exact hj).1
  have := (D.basePushforward_exact hj).2
  have : D.basePushforward.Additive := Functor.additive_of_preserves_binary_products _
  refine (CategoryTheory.Functor.mapExt_bijective_of_preservesInjectiveObjects
    (thickenedModulesFunctor i₁) F
    (((Stacks.SheafOfModules.Tensor.sheafTensor X.O).flip.obj F).obj J₂) 2).1 ?_
  simp only [Functor.mapExtAddHom_apply]
  -- the second side
  have hR : (((extDescentAddEquiv hi₁ F J₁ 2).symm (existenceObstructionClass hi₁
      ((thickenedModulesFunctor i₁).obj F) _ (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing
      i₁)).flip.obj ((thickenedModulesFunctor
          i₁).obj F)).map e₁.inv))).comp (Abelian.Ext.mk₀
              (((Stacks.SheafOfModules.Tensor.sheafTensor X.O).flip.obj F).map lam))
        (add_zero 2)).mapExactFunctor (thickenedModulesFunctor i₁) =
      existenceObstructionClass hi₁ ((thickenedModulesFunctor i₁).obj F) _
        ((((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i₁)).flip.obj
            ((thickenedModulesFunctor i₁).obj
            F)).map e₁.inv) ≫ (pushforwardModuleTensorIso hi₁ F J₁).hom ≫ (thickenedModulesFunctor
                i₁).map (((Stacks.SheafOfModules.Tensor.sheafTensor X.O).flip.obj F).map lam)) := by
    rw [Abelian.Ext.mapExactFunctor_comp, Abelian.Ext.mapExactFunctor_mk₀,
      mapExactFunctor_extDescentAddEquiv_symm hi₁ F J₁ (existenceObstructionClass hi₁
          ((thickenedModulesFunctor i₁).obj F) _ (((Stacks.SheafOfModules.Tensor.sheafTensor
          (baseRing i₁)).flip.obj ((thickenedModulesFunctor i₁).obj F)).map e₁.inv)),
      Abelian.Ext.comp_assoc_of_third_deg_zero, Abelian.Ext.mk₀_comp_mk₀,
      existenceObstructionClass_comp i₁ hi₁]
  -- the first side
  have hE := Stacks.ExtFunctorial.mk₀_comp_mapExactFunctor E.hom F 2
    ((extDescentAddEquiv hi₂ F J₂ 2).symm (existenceObstructionClass hi₂ ((thickenedModulesFunctor
        i₂).obj F) _ (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing
        i₂)).flip.obj ((thickenedModulesFunctor i₂).obj F)).map e₂.inv)))
  have hcomp := Stacks.ExtFunctorial.mapExactFunctor_comp_functor (thickenedModulesFunctor
      i₂) D.basePushforward F 2
    ((extDescentAddEquiv hi₂ F J₂ 2).symm (existenceObstructionClass hi₂ ((thickenedModulesFunctor
        i₂).obj F) _ (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing
        i₂)).flip.obj ((thickenedModulesFunctor i₂).obj F)).map e₂.inv)))
  have hbase := D.baseExtMap_existenceObstructionClass hi₁ hi₂ hj ((thickenedModulesFunctor i₂).obj
      F)
    (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i₂)).flip.obj ((thickenedModulesFunctor
        i₂).obj F)).obj
      ((thickenedModulesFunctor i₂).obj J₂))
    (D.basePushforward.obj
      (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i₂)).flip.obj ((thickenedModulesFunctor
          i₂).obj F)).obj
        ((thickenedModulesFunctor i₂).obj J₂)))
    (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i₂)).flip.obj ((thickenedModulesFunctor
        i₂).obj F)).map e₂.inv) (D.idealTensorMap hi₁ hi₂ ((thickenedModulesFunctor i₂).obj F) ≫
            D.basePushforward.map (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing
            i₂)).flip.obj ((thickenedModulesFunctor i₂).obj F)).map e₂.inv)) (𝟙 _)
    (Category.comp_id _)
  rw [Abelian.Ext.comp_mk₀_id, baseExtMap_apply] at hbase
  have hL : ((extDescentAddEquiv hi₂ F J₂ 2).symm (existenceObstructionClass hi₂
      ((thickenedModulesFunctor i₂).obj F) _ (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing
      i₂)).flip.obj ((thickenedModulesFunctor
          i₂).obj F)).map e₂.inv))).mapExactFunctor (thickenedModulesFunctor i₁) =
      (Abelian.Ext.mk₀ (E.inv.app F)).comp
        ((((extDescentAddEquiv hi₂ F J₂ 2).symm (existenceObstructionClass hi₂
            ((thickenedModulesFunctor i₂).obj F) _ (((Stacks.SheafOfModules.Tensor.sheafTensor
            (baseRing i₂)).flip.obj ((thickenedModulesFunctor
            i₂).obj F)).map e₂.inv))).mapExactFunctor (thickenedModulesFunctor i₂ ⋙
                D.basePushforward)).comp
          (Abelian.Ext.mk₀ (E.hom.app _)) (add_zero 2)) (zero_add 2) := by
    rw [← hE, Abelian.Ext.mk₀_comp_mk₀_assoc, Iso.inv_hom_id_app, Abelian.Ext.mk₀_id_comp]
  have hL2 : ((extDescentAddEquiv hi₂ F J₂ 2).symm (existenceObstructionClass hi₂
      ((thickenedModulesFunctor i₂).obj F) _ (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing
      i₂)).flip.obj ((thickenedModulesFunctor
          i₂).obj F)).map e₂.inv))).mapExactFunctor (thickenedModulesFunctor i₂ ⋙
              D.basePushforward) =
      (existenceObstructionClass hi₁ (D.basePushforward.obj ((thickenedModulesFunctor i₂).obj F)) _
        (D.idealTensorMap hi₁ hi₂ ((thickenedModulesFunctor i₂).obj F) ≫ D.basePushforward.map
            (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i₂)).flip.obj
            ((thickenedModulesFunctor i₂).obj F)).map e₂.inv))).comp
        (Abelian.Ext.mk₀ (D.basePushforward.map (pushforwardModuleTensorIso hi₂ F J₂).hom))
        (add_zero 2) := by
    rw [← hcomp, mapExactFunctor_extDescentAddEquiv_symm hi₂ F J₂ (existenceObstructionClass hi₂
        ((thickenedModulesFunctor i₂).obj F) _ (((Stacks.SheafOfModules.Tensor.sheafTensor
        (baseRing i₂)).flip.obj ((thickenedModulesFunctor i₂).obj F)).map e₂.inv)),
      Abelian.Ext.mapExactFunctor_comp, Abelian.Ext.mapExactFunctor_mk₀, hbase]
  have hL3 : (Abelian.Ext.mk₀ (E.inv.app F)).comp
      (((existenceObstructionClass hi₁ (D.basePushforward.obj ((thickenedModulesFunctor i₂).obj F))
          _
        (D.idealTensorMap hi₁ hi₂ ((thickenedModulesFunctor i₂).obj F) ≫ D.basePushforward.map
            (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i₂)).flip.obj
            ((thickenedModulesFunctor i₂).obj F)).map e₂.inv))).comp
        (Abelian.Ext.mk₀ (D.basePushforward.map (pushforwardModuleTensorIso hi₂ F J₂).hom))
        (add_zero 2)).comp (Abelian.Ext.mk₀ (E.hom.app _)) (add_zero 2)) (zero_add 2) =
      existenceObstructionClass hi₁ ((thickenedModulesFunctor i₁).obj F) _
        (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing i₁)).obj hi₁.I).map (E.inv.app F) ≫
          D.idealTensorMap hi₁ hi₂ ((thickenedModulesFunctor i₂).obj
              F) ≫ D.basePushforward.map (((Stacks.SheafOfModules.Tensor.sheafTensor (baseRing
              i₂)).flip.obj ((thickenedModulesFunctor i₂).obj F)).map e₂.inv) ≫
          D.basePushforward.map (pushforwardModuleTensorIso hi₂ F J₂).hom ≫
          E.hom.app (((Stacks.SheafOfModules.Tensor.sheafTensor X.O).flip.obj F).obj J₂)) := by
    rw [Abelian.Ext.comp_assoc_of_third_deg_zero, Abelian.Ext.mk₀_comp_mk₀,
      ← existenceObstructionClass_comp i₁ hi₁]
    refine (existenceObstructionClass_of_iso hi₁ (E.app F).symm _ _).symm.trans ?_
    congr 1
  rw [hL, hL2, hL3, hR]
  congr 1
  rw [hkey]
  refine congrArg (fun m => _ ≫ _ ≫ m) ?_
  exact ((congrArg (· ≫ E.hom.app _) (D.basePushforward.map_comp _ _)).trans
    (Category.assoc _ _ _)).symm

end ThickeningTargetMorphism

end Deformation.ToposThickening

end
