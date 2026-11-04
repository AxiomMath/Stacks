module
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GlobalSectionsClosed.InverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleDerivedFunctors
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmallEtaleBaseChange

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.AbelianTensor.InverseImageMonoidal
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ModuleTensor.Monoidal
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleInverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleInverseImageUnconditional

/-!
# Inverse image of étale sheaves of `Λ`-modules is a monoidal functor

Let `Λ` be a commutative ring and `f : X ⟶ Y` a morphism of schemes. For the tensor product of
étale sheaves of `Λ`-modules, `Stacks.EtaleCohomology.etaleModuleMonoidalCategory`, this file
shows:

* the direct image `f_*` is lax monoidal (`etaleModuleDirectImageLaxMonoidal`);
* the inverse image `f⁻¹` is a strong monoidal functor (`etaleModuleInverseImageMonoidal`), whose
  oplax structure is the mate of that lax structure, so that
  `etaleModuleInverseImageTensorIso Λ f M N : f⁻¹(M ⊗_Λ N) ≅ f⁻¹M ⊗_Λ f⁻¹N`.

## Implementation notes

This is the site-level statement of `StacksFrontier.CategoryTheory.Sites.SheafPushforwardMonoidal`
for the base change functor `smallEtaleBaseChange f` of small étale sites, exactly as for abelian
étale sheaves (`Stacks.EtaleCohomology.etaleAbelianInverseImageMonoidal`). Its inputs are: the
sheafification of `Λ`-module presheaves on a small étale site is monoidal
(`isMonoidal_W_smallEtale_module`), the comma categories computing the left Kan extension along
base change are filtered (`isFiltered_costructuredArrow_smallEtaleBaseChange`), and the tensor
product of `Λ`-modules commutes with colimits in each variable.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal
open AlgebraicGeometry

universe u r

namespace Stacks.EtaleCohomology

attribute [local instance] etaleModuleMonoidalCategory isMonoidal_W_smallEtale_module

variable (Λ : Type r) [CommRing Λ]

/-- Tensoring `Λ`-modules commutes with colimits of diagrams of the size of the comma categories
of base change, in each variable. -/
instance preservesColimit₂_smallEtaleBaseChange_module {X Y : Scheme.{u}} (f : X ⟶ Y)
    (V : X.Etaleᵒᵖ) (P Q : Y.Etaleᵒᵖ ⥤ ModuleCat.{max (u + 1) r} Λ) :
    PreservesColimit₂ (CostructuredArrow.proj (smallEtaleBaseChange f).op V ⋙ P)
      (CostructuredArrow.proj (smallEtaleBaseChange f).op V ⋙ Q)
      (curriedTensor (ModuleCat.{max (u + 1) r} Λ)) := by
  have hl (M : ModuleCat.{max (u + 1) r} Λ) :
      PreservesColimitsOfSize.{u, u + 1} ((curriedTensor (ModuleCat.{max (u + 1) r} Λ)).obj M) :=
    have : PreservesColimitsOfSize.{max (u + 1) r, max (u + 1) r}
        ((curriedTensor (ModuleCat.{max (u + 1) r} Λ)).obj M) :=
      preservesColimits_tensorLeft_etaleCoefficients.{u, r} Λ M
    preservesColimitsOfSize_of_univLE.{max (u + 1) r, max (u + 1) r, u, u + 1} _
  have hr (M : ModuleCat.{max (u + 1) r} Λ) :
      PreservesColimitsOfSize.{u, u + 1}
        ((curriedTensor (ModuleCat.{max (u + 1) r} Λ)).flip.obj M) :=
    have : PreservesColimitsOfSize.{max (u + 1) r, max (u + 1) r}
        ((curriedTensor (ModuleCat.{max (u + 1) r} Λ)).flip.obj M) :=
      preservesColimits_tensorRight_etaleCoefficients.{u, r} Λ M
    preservesColimitsOfSize_of_univLE.{max (u + 1) r, max (u + 1) r, u, u + 1} _
  infer_instance

section

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- **The direct image of étale sheaves of `Λ`-modules is lax monoidal**: the tensorator
`f_*M ⊗ f_*N ⟶ f_*(M ⊗ N)` is the morphism out of the sheafification of the sectionwise tensor
product induced by the sheafification unit of `M ⊗ N`. -/
@[instance_reducible]
noncomputable def etaleModuleDirectImageLaxMonoidal :
    (etaleModuleDirectImage.{u, r} Λ f).LaxMonoidal :=
  Stacks.SheafPushforwardMonoidal.pushforwardLaxMonoidal Y.smallEtaleTopology X.smallEtaleTopology
    (ModuleCat.{max (u + 1) r} Λ) (smallEtaleBaseChange f)

/-- **The inverse image of étale sheaves of `Λ`-modules is a monoidal functor.** Its oplax
structure is the mate of the lax structure `etaleModuleDirectImageLaxMonoidal` of the direct
image, and it is strong. -/
@[instance_reducible]
noncomputable def etaleModuleInverseImageMonoidal :
    (etaleModuleInverseImage.{u, r} Λ f).Monoidal :=
  Stacks.SheafPushforwardMonoidal.pullbackMonoidal Y.smallEtaleTopology X.smallEtaleTopology
    (ModuleCat.{max (u + 1) r} Λ) (smallEtaleBaseChange f)
    (etaleModuleInverseImageAdj.{u, r} Λ f)

attribute [local instance] etaleModuleDirectImageLaxMonoidal etaleModuleInverseImageMonoidal

/-- The adjunction between inverse and direct image of étale sheaves of `Λ`-modules is
compatible with the monoidal structure of the inverse image and the lax monoidal structure of the
direct image. -/
instance isMonoidal_etaleModuleInverseImageAdj :
    (etaleModuleInverseImageAdj.{u, r} Λ f).IsMonoidal :=
  Stacks.SheafPushforwardMonoidal.isMonoidal_pullbackMonoidal Y.smallEtaleTopology
    X.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ) (smallEtaleBaseChange f)
    (etaleModuleInverseImageAdj.{u, r} Λ f)

/-- **The inverse image of étale sheaves of `Λ`-modules commutes with the tensor product**:
`f⁻¹(M ⊗_Λ N) ≅ f⁻¹M ⊗_Λ f⁻¹N`, the inverse of the tensorator of the monoidal structure
`etaleModuleInverseImageMonoidal`, whose forward direction is the comparison morphism `δ`. -/
noncomputable def etaleModuleInverseImageTensorIso (M N : EtaleModules.{u, r} Λ Y) :
    (etaleModuleInverseImage.{u, r} Λ f).obj (M ⊗ N) ≅
      (etaleModuleInverseImage.{u, r} Λ f).obj M ⊗ (etaleModuleInverseImage.{u, r} Λ f).obj N :=
  (Functor.Monoidal.μIso (etaleModuleInverseImage.{u, r} Λ f) M N).symm

lemma etaleModuleInverseImageTensorIso_hom (M N : EtaleModules.{u, r} Λ Y) :
    (etaleModuleInverseImageTensorIso.{u, r} Λ f M N).hom =
      δ (etaleModuleInverseImage.{u, r} Λ f) M N :=
  rfl

/-- Naturality of `etaleModuleInverseImageTensorIso` in the first variable, in the form
`CochainComplex.KFlatBifunctor.derivedTransportIso` consumes. -/
lemma etaleModuleInverseImageTensorIso_hom_natural_left {M M' : EtaleModules.{u, r} Λ Y}
    (φ : M ⟶ M') (N : EtaleModules.{u, r} Λ Y) :
    (etaleModuleInverseImage.{u, r} Λ f).map (((etaleModuleTensor Λ Y).map φ).app N) ≫
        (etaleModuleInverseImageTensorIso.{u, r} Λ f M' N).hom =
      (etaleModuleInverseImageTensorIso.{u, r} Λ f M N).hom ≫
        ((etaleModuleTensor Λ X).map ((etaleModuleInverseImage.{u, r} Λ f).map φ)).app
          ((etaleModuleInverseImage.{u, r} Λ f).obj N) :=
  (Functor.OplaxMonoidal.δ_natural_left (etaleModuleInverseImage.{u, r} Λ f) φ N).symm

/-- Naturality of `etaleModuleInverseImageTensorIso` in the second variable, in the form
`CochainComplex.KFlatBifunctor.derivedTransportIso` consumes. -/
lemma etaleModuleInverseImageTensorIso_hom_natural_right (M : EtaleModules.{u, r} Λ Y)
    {N N' : EtaleModules.{u, r} Λ Y} (ψ : N ⟶ N') :
    (etaleModuleInverseImage.{u, r} Λ f).map (((etaleModuleTensor Λ Y).obj M).map ψ) ≫
        (etaleModuleInverseImageTensorIso.{u, r} Λ f M N').hom =
      (etaleModuleInverseImageTensorIso.{u, r} Λ f M N).hom ≫
        ((etaleModuleTensor Λ X).obj ((etaleModuleInverseImage.{u, r} Λ f).obj M)).map
          ((etaleModuleInverseImage.{u, r} Λ f).map ψ) :=
  (Functor.OplaxMonoidal.δ_natural_right (etaleModuleInverseImage.{u, r} Λ f) M ψ).symm

end

end Stacks.EtaleCohomology

end
