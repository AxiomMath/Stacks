module

public import StacksFrontier.AlgebraicGeometry.Quot.ProperFlatChartProblem
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.EtaleRestrictionInverseImageGlobalSection
public import StacksFrontier.AlgebraicGeometry.Spaces.BaseRingTensorModuleSections

/-!
# Global sections along the identifications of `problemOnChart`

Let `x = (X → Spec A)` be an object of `Spaces'_{fp, flat, proper}` over an affine chart and `D`
a square-zero thickening `Spec A ⊂ Spec A'` of Situation 07YX. The extension problem
`AlgebraicGeometry.Space.ProperFlatLift.problemOnChart x hx D` is the problem of `x` along `D`,
posed over the closed subspace `Z ⊆ Spec A'` cut out by `Spec A`, moved to `Spec A` along
`ρ : Spec A ≅ Z` through `(f ≫ ρ)⁻¹𝒪' ≅ f⁻¹(𝒪'|_{Spec A})`
(`AlgebraicGeometry.Space.inverseImageRestrictionIsoOfCompIso`). This file computes that
identification on inverse images of global sections, on underlying sheaves of sets.

## Main results

* `globalSectionMap_comp_forget_map_inverseImageRestrictionIsoOfCompIso_hom`: a global section
  of `F` pulled back along `g ≫ ρ` is carried to the inverse image along `g` of its restriction
  along `ρ`.
* `counitIso_hom_val_app_baseRingTensorSection`: the section `1 ⊗ m` of `𝒪_X ⊗_R M`, read on the
  model, is the section `1 ⊗ m` of the base-ring tensor module on the model.

## References

* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Remark 0D1P](https://stacks.math.columbia.edu/tag/0D1P)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf

attribute [local instance] MorphismOfTopoi.preservesFiniteLimits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X Y Z : AlgebraicSpaces B S hS} (g : X ⟶ Y) (ρ : Y ≅ Z)

/-- `(g ≫ ρ)⁻¹F ≅ g⁻¹(F|_Y)` on underlying sheaves of sets: the composition law of inverse
images followed by `g⁻¹` of the comparison of Stacks 03LQ. -/
theorem forget_map_inverseImageRestrictionIsoOfCompIso_hom
    (F : Sheaf (SmallEtale.topology B S hS Z.1) CommRingCat.{u}) :
    (sheafCompose (SmallEtale.topology B S hS X.1) (forget CommRingCat.{u})).map
      (inverseImageRestrictionIsoOfCompIso g ρ F).hom =
      (smallEtaleRingedToposHom_compInverseImageIso B S hS g ρ.hom).inv.app _ ≫
        (smallEtaleRingedToposHom B S hS g).toToposHom.inverseImage.map
          ((smallToposMorphismTypeU_inverseImageIso B S hS ρ.hom
            (isEtale_hom_of_iso B S hS ρ)).hom.app _) := by
  have hc : (sheafCompose (SmallEtale.topology B S hS X.1) (forget CommRingCat.{u})).map
      ((smallEtaleRingedToposHom_compInverseImageRingIso B S hS g ρ.hom).inv.app F) =
      (smallEtaleRingedToposHom_compInverseImageIso B S hS g ρ.hom).inv.app _ := by
    rw [smallEtaleRingedToposHom_compInverseImageRingIso, Iso.trans_inv, NatTrans.comp_app,
      Functor.map_comp]
    exact (congrArg (_ ≫ ·)
      (Stacks.Sheaves.ToposPushforward.forget_map_inverseImageCommRingComp_inv
        (smallEtaleRingedToposHom B S hS ρ.hom).toToposHom
        (smallEtaleRingedToposHom B S hS g).toToposHom F)).trans (Category.comp_id _)
  have hr := Stacks.Sheaves.ToposPullback.inverseImageCommRingRestrictionIso_hom_forget
    (SmallEtale.topology B S hS Y.1) (SmallEtale.topology B S hS Z.1)
    (smallEtalePostcomp B S hS ρ.hom (isEtale_hom_of_iso B S hS ρ))
    (smallEtaleRingedToposHom B S hS ρ.hom).toToposHom
    (smallToposMorphismTypeU_inverseImageIso B S hS ρ.hom (isEtale_hom_of_iso B S hS ρ)) F
  have hm := Stacks.Sheaves.ToposPushforward.inverseImageCommRingFunctor_map_forget
    (smallEtaleRingedToposHom B S hS g).toToposHom (isoInverseImageRestrictionIso ρ F).hom
  refine ((sheafCompose (SmallEtale.topology B S hS X.1)
    (forget CommRingCat.{u})).map_comp _ _).trans ?_
  refine (congrArg (· ≫ _) hc).trans (congrArg (_ ≫ ·) (hm.trans ?_))
  exact congrArg (smallEtaleRingedToposHom B S hS g).toToposHom.inverseImage.map hr

/-- `(g ≫ ρ)⁻¹F ≅ g⁻¹(F|_Y)` on inverse images of global sections: a global section `τ` of
`F`, pulled back along `g ≫ ρ`, is carried to the inverse image along `g` of the restriction of
`τ` along `ρ`, on underlying sheaves of sets. -/
theorem globalSectionMap_comp_forget_map_inverseImageRestrictionIsoOfCompIso_hom
    (F : Sheaf (SmallEtale.topology B S hS Z.1) CommRingCat.{u})
    (τ : ⊤_ _ ⟶ (sheafCompose (SmallEtale.topology B S hS Z.1) (forget CommRingCat.{u})).obj F) :
    (smallEtaleRingedToposHom B S hS (g ≫ ρ.hom)).toToposHom.inverseImage.globalSectionMap τ ≫
        (sheafCompose (SmallEtale.topology B S hS X.1) (forget CommRingCat.{u})).map
          (inverseImageRestrictionIsoOfCompIso g ρ F).hom =
      (smallEtaleRingedToposHom B S hS g).toToposHom.inverseImage.globalSectionMap
        ((smallEtaleSetRestriction B S hS ρ.hom (isEtale_hom_of_iso B S hS ρ)).globalSectionMap
          τ) := by
  have h1 := Functor.globalSectionMap_comp_inv_app
    (F := (smallEtaleRingedToposHom B S hS ρ.hom).toToposHom.inverseImage)
    (G := (smallEtaleRingedToposHom B S hS g).toToposHom.inverseImage)
    (smallEtaleRingedToposHom_compInverseImageIso B S hS g ρ.hom) τ
  have h2 := globalSectionMap_comp_smallToposMorphismTypeU_inverseImageIso_hom_app B S hS ρ.hom
    (isEtale_hom_of_iso B S hS ρ) τ
  refine (congrArg (_ ≫ ·) (forget_map_inverseImageRestrictionIsoOfCompIso_hom g ρ F)).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ _) h1).trans ?_
  refine (Functor.globalSectionMap_comp _ _ _).trans ?_
  exact congrArg (smallEtaleRingedToposHom B S hS g).toToposHom.inverseImage.globalSectionMap h2

section Model

open Stacks.Cohomology.SiteModules

variable (X : AlgebraicSpaces B S hS) {R : Type u} [CommRing R]
  (φ : R →+* modelGlobalFunctions B S hS X)

/-- The section `1 ⊗ m` of `𝒪_X ⊗_R M`, read on the model: over an object `U` of the model,
the value at `1` of the section `1 ⊗ m` of `AlgebraicGeometry.Space.baseRingTensorModule`,
carried by the counit of the Comparison Lemma, is the section `1 ⊗ m` of the base-ring tensor
module on the model. -/
theorem counitIso_hom_val_app_baseRingTensorSection (M : ModuleCat.{u} R) (m : M)
    (U : (SmallModel.{u} (SmallEtale B S hS X.1))ᵒᵖ) :
    ((smallEtaleModelModulesEquiv B S hS X).counitIso.hom.app
        ((baseRingTensorFunctor.{u, u, u, u} φ).obj M)).val.app U
        ((baseRingTensorSection B S hS X φ M m).val.app
          (Opposite.op ((smallEtaleModelEquiv B S hS X).inverse.obj U.unop))
          (1 : chartRing B S hS X.1 X.2 ((smallEtaleModelEquiv B S hS X).inverse.obj U.unop))) =
      ((baseRingTensorUnit.{u, u, u, u} φ M).hom m).eval U := by
  have h₀ : (baseRingTensorSection B S hS X φ M m).val.app
        (Opposite.op ((smallEtaleModelEquiv B S hS X).inverse.obj U.unop))
        (1 : chartRing B S hS X.1 X.2 ((smallEtaleModelEquiv B S hS X).inverse.obj U.unop)) =
      (((baseRingTensorModuleAdjunction B S hS X φ).unit.app M).hom m).val U := by
    have h := modelSectionsHomEquiv_symm_val B S hS X φ ((baseRingTensorModule B S hS X φ).obj M)
      (baseRingTensorSection B S hS X φ M m) U
    have hs : (modelSectionsHomEquiv B S hS X φ ((baseRingTensorModule B S hS X φ).obj M)).symm
        (baseRingTensorSection B S hS X φ M m) =
        ((baseRingTensorModuleAdjunction B S hS X φ).unit.app M).hom m :=
      Equiv.symm_apply_apply _ _
    exact h.symm.trans (congrArg (fun s => s.val U) hs)
  have h₂ := Adjunction.comp_unit_app (baseRingTensorAdjunction.{u, u, u, u} φ)
    (smallEtaleModelModulesEquiv B S hS X).symm.toAdjunction M
  have h₃ : (smallEtaleModelModulesEquiv B S hS X).symm.toAdjunction.unit.app
      ((baseRingTensorFunctor.{u, u, u, u} φ).obj M) ≫
      (smallEtaleModelModulesEquiv B S hS X).counitIso.hom.app
        ((baseRingTensorFunctor.{u, u, u, u} φ).obj M) = 𝟙 _ :=
    (smallEtaleModelModulesEquiv B S hS X).counitIso.inv_hom_id_app _
  refine (congrArg _ h₀).trans ?_
  show ((smallEtaleModelModulesEquiv B S hS X).counitIso.hom.app _).val.app U
    (((((baseRingTensorAdjunction.{u, u, u, u} φ).comp
      (smallEtaleModelModulesEquiv B S hS X).symm.toAdjunction).unit.app M).hom m).1 U) = _
  rw [h₂]
  exact congrArg
    (fun t => t.val.app U ((((baseRingTensorAdjunction.{u, u, u, u} φ).unit.app M).hom m).1 U)) h₃

end Model

end AlgebraicGeometry.Space
