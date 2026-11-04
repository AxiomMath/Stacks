module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedTensorHom.RingedSiteHom
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedToposSiteHomOfRingedSite

/-!
# Direct image along the morphism of constant ringed sites is the étale direct image

For a morphism of schemes `f : X ⟶ Y` and a commutative ring `Λ`, the direct image of sheaves of
modules along the morphism of constant ringed sites `Stacks.EtaleCohomology.etaleRingedSiteHom`
is, read through the identifications `Stacks.EtaleCohomology.etaleModulesEquivalence` of sheaves
of `Λ̲`-modules with sheaves of `Λ`-modules, the direct image `f_*` of sheaves of `Λ`-modules on
small étale sites, `Stacks.EtaleCohomology.etaleModuleDirectImage`.

## Main results

* `Stacks.EtaleCohomology.etaleRingedSiteFSharp_constantRingedSiteRingMap`: the structure map of
  the morphism of ringed sites is compatible with the two maps out of the constant presheaf of
  rings.
* `Stacks.EtaleCohomology.etaleRingedPushforwardIso`: the comparison of direct images.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u r

namespace Stacks.EtaleCohomology

variable (Λ : Type r) [CommRing Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- **The structure map of the morphism of constant ringed sites carries the constant `a` to the
constant `a`**, read through the maps out of the constant presheaf of rings. -/
theorem etaleRingedSiteFSharp_constantRingedSiteRingMap (V : (AsSmall.{max (u + 1) r} Y.Etale)ᵒᵖ)
    (a : ULift.{max (u + 1) r} Λ) :
    ((etaleRingedSiteFSharp.{u, r} Λ f).hom.app V).hom
        (((Stacks.ConstantRingModules.constantRingedSiteRingMap (etaleSmallModelTopology.{u, r} Y)
          (ULift.{max (u + 1) r} Λ)).app V).hom a) =
      ((Stacks.ConstantRingModules.constantRingedSiteRingMap (etaleSmallModelTopology.{u, r} X)
          (ULift.{max (u + 1) r} Λ)).app
            ((etaleSmallModelBaseChange.{u, r} f).op.obj V)).hom a := by
  rw [constantRingedSiteRingMap_app_apply, constantRingedSiteRingMap_app_apply]
  exact congrArg (fun φ => (φ.app V).hom a) (etaleRingedSiteFSharp_toSheafify.{u, r} Λ f)

/-- The sections over an étale `Y`-scheme `V` of the direct image of a sheaf of `Λ̲`-modules `M`
along the morphism of constant ringed sites, read as a `Λ`-module. -/
abbrev etaleRingedPushforwardSections (M : EtaleRingedModules.{u, r} Λ X) (V : Y.Etaleᵒᵖ) :
    ModuleCat.{max (u + 1) r} Λ :=
  ((etaleModulesEquivalence.{u, r} Λ Y).inverse.obj
    ((etaleRingedSiteHom.{u, r} Λ f).toRingedToposSiteHom.pushforwardTopos.obj M)).obj.obj V

/-- The sections over an étale `Y`-scheme `V` of the étale direct image of the sheaf of
`Λ`-modules underlying a sheaf of `Λ̲`-modules `M`. -/
abbrev etaleDirectImageSections (M : EtaleRingedModules.{u, r} Λ X) (V : Y.Etaleᵒᵖ) :
    ModuleCat.{max (u + 1) r} Λ :=
  ((etaleModuleDirectImage.{u, r} Λ f).obj
    ((etaleModulesEquivalence.{u, r} Λ X).inverse.obj M)).obj.obj V

/-- The actions of `Λ` on the two modules of sections agree. -/
theorem etaleRingedPushforward_smul (M : EtaleRingedModules.{u, r} Λ X) (V : Y.Etaleᵒᵖ) (a : Λ)
    (x : etaleRingedPushforwardSections.{u, r} Λ f M V) :
    (a • x : etaleRingedPushforwardSections.{u, r} Λ f M V) =
      (a • (show etaleDirectImageSections.{u, r} Λ f M V from x) :
        etaleDirectImageSections.{u, r} Λ f M V) := by
  have h := etaleRingedSiteFSharp_constantRingedSiteRingMap.{u, r} Λ f (op (AsSmall.up.obj V.unop))
    (ULift.up a)
  exact congrArg
    (fun (s : (Stacks.SheafOfModules.Tensor.ringSheaf (etaleRingedSite.{u, r} Λ X).O).obj.obj
        (op ((AsSmall.up : X.Etale ⥤ AsSmall.{max (u + 1) r} X.Etale).obj
          ((smallEtaleBaseChange f).obj V.unop)))) =>
      s • (show M.val.obj (op ((AsSmall.up : X.Etale ⥤ AsSmall.{max (u + 1) r} X.Etale).obj
        ((smallEtaleBaseChange f).obj V.unop))) from x)) h

/-- The two `Λ`-modules of sections agree: they are the sections of `M` over the base change of
`V`, with the same action of `Λ`. -/
def etaleRingedPushforwardSectionsLinear (M : EtaleRingedModules.{u, r} Λ X) (V : Y.Etaleᵒᵖ) :
    etaleRingedPushforwardSections.{u, r} Λ f M V →ₗ[Λ] etaleDirectImageSections.{u, r} Λ f M V
    where
  toFun x := x
  map_add' _ _ := rfl
  map_smul' a x := etaleRingedPushforward_smul.{u, r} Λ f M V a x

/-- The inverse of `etaleRingedPushforwardSectionsLinear`. -/
def etaleDirectImageSectionsLinear (M : EtaleRingedModules.{u, r} Λ X) (V : Y.Etaleᵒᵖ) :
    etaleDirectImageSections.{u, r} Λ f M V →ₗ[Λ] etaleRingedPushforwardSections.{u, r} Λ f M V
    where
  toFun x := x
  map_add' _ _ := rfl
  map_smul' a x := (etaleRingedPushforward_smul.{u, r} Λ f M V a x).symm

/-- The component at a sheaf of modules `M` and an étale `Y`-scheme `V` of
`etaleRingedPushforwardIso`. -/
def etaleRingedPushforwardIsoApp (M : EtaleRingedModules.{u, r} Λ X) (V : Y.Etaleᵒᵖ) :
    etaleRingedPushforwardSections.{u, r} Λ f M V ≅ etaleDirectImageSections.{u, r} Λ f M V where
  hom := ModuleCat.homEquiv.symm (etaleRingedPushforwardSectionsLinear.{u, r} Λ f M V)
  inv := ModuleCat.homEquiv.symm (etaleDirectImageSectionsLinear.{u, r} Λ f M V)
  hom_inv_id := rfl
  inv_hom_id := rfl

/-- **Direct image along the morphism of constant ringed sites is the étale direct image**:
`Ψ_Y⁻¹ ∘ f_* ≅ f_* ∘ Ψ_X⁻¹`, for the identifications `Ψ` of sheaves of `Λ̲`-modules with sheaves
of `Λ`-modules. -/
def etaleRingedPushforwardIso :
    (etaleRingedSiteHom.{u, r} Λ f).toRingedToposSiteHom.pushforwardTopos ⋙
        (etaleModulesEquivalence.{u, r} Λ Y).inverse ≅
      (etaleModulesEquivalence.{u, r} Λ X).inverse ⋙ etaleModuleDirectImage.{u, r} Λ f :=
  NatIso.ofComponents
    (fun M => ObjectProperty.isoMk _
      (NatIso.ofComponents (fun V => etaleRingedPushforwardIsoApp.{u, r} Λ f M V)
        (fun _ => by ext; rfl)))
    (fun _ => by ext; rfl)

end Stacks.EtaleCohomology

end
