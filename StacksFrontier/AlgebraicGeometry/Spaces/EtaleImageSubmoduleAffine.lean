module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiImageSubsheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartSurjectivityFromDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.AlgebraSheafImageQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleFiniteTypeQuotient
import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiLocallySurjective

/-!
# The image submodule of a morphism of quasi-coherent modules on an algebraic space

Let `F` be an algebraic space and `φ : G ⟶ M` a morphism of `𝒪_F`-modules on the small étale
site.  The submodule `Stacks.SheafOfModules.ImageSubsheaf.imageSubmodule φ ⊆ M` of sections lying
locally in the range of `φ` is the image of `φ`.  When `G` and `M` are quasi-coherent it is
quasi-coherent, it is of finite type when `G` is, and over every affine étale chart its sections
are exactly the range of `φ` there: the image of a quasi-coherent module is computed sectionwise on
affine charts.

## Main results

* `AlgebraicGeometry.Space.toImageSubmodule`: the factorization of `φ` through its image
  submodule, an epimorphism.
* `AlgebraicGeometry.Space.isQuasicoherentOnSite_imageSubmodule`: the image submodule of a
  morphism of quasi-coherent modules is quasi-coherent.
* `AlgebraicGeometry.Space.isFiniteTypeOnSite_imageSubmodule`: it is of finite type when the
  source is.
* `AlgebraicGeometry.Space.mem_imageSubmodule_iff_of_isAffine`: **over an affine étale chart its
  sections are the range of `φ`.**

## References

* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
* [Stacks Project, Tag 0829](https://stacks.math.columbia.edu/tag/0829)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.SheafOfModules.ImageSubsheaf

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hF : IsAlgebraicSpace B S hS F}
    {G M : Modules.{u, u} B S hS F hF}

/-- The factorization of a morphism of `𝒪_F`-modules through its image submodule. -/
noncomputable def toImageSubmodule (φ : G ⟶ M) : G ⟶ (imageSubmodule φ).toSheafOfModules :=
  Stacks.SheafOfModules.sheafFactorThruSubmodule φ (imageSubmodule φ)
    (fun _ m => apply_mem_imageSubmodule φ m)

/-- The factorization through the image submodule, followed by its inclusion, is `φ`. -/
@[reassoc (attr := simp)]
theorem toImageSubmodule_ι (φ : G ⟶ M) : toImageSubmodule φ ≫ (imageSubmodule φ).ι = φ :=
  Stacks.SheafOfModules.sheafFactorThruSubmodule_ι _ _ _

/-- The factorization through the image submodule is an epimorphism. -/
instance epi_toImageSubmodule (φ : G ⟶ M) : Epi (toImageSubmodule φ) := by
  refine Stacks.SheafOfModules.EpiMono.epi_of_isLocallySurjective _ ⟨fun {U} s => ?_⟩
  refine GrothendieckTopology.superset_covering _ (fun V g hg => ?_) s.2
  obtain ⟨m, hm⟩ := (mem_rangeSubmodule_obj_iff φ _ _).1 hg
  exact ⟨m, Subtype.ext hm⟩

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian in
/-- **The image submodule of a morphism of quasi-coherent `𝒪_F`-modules is quasi-coherent.** -/
theorem isQuasicoherentOnSite_imageSubmodule (φ : G ⟶ M) (hG : G.IsQuasicoherentOnSite)
    (hM : M.IsQuasicoherentOnSite) :
    (imageSubmodule φ).toSheafOfModules.IsQuasicoherentOnSite :=
  have : StrongEpi (toImageSubmodule φ) := strongEpi_of_epi _
  SheafOfModules.IsQuasicoherentOnSite.of_iso
    (image.isoStrongEpiMono (toImageSubmodule φ) (imageSubmodule φ).ι
      (toImageSubmodule_ι φ)).symm
    (isQuasicoherentOnSite_image_unconditional B S hS F hF φ hG hM)

/-- The image submodule of a morphism out of an `𝒪_F`-module of finite type is of finite type. -/
theorem isFiniteTypeOnSite_imageSubmodule (φ : G ⟶ M)
    (hG : SheafOfModules.IsFiniteTypeOnSite G) :
    SheafOfModules.IsFiniteTypeOnSite (imageSubmodule φ).toSheafOfModules :=
  isFiniteTypeOnSite_of_epi B S hS F hF (toImageSubmodule φ) hG

/-- Over an affine étale chart the factorization of a morphism of quasi-coherent modules through
its image submodule is surjective on sections. -/
theorem surjective_toImageSubmodule_app (φ : G ⟶ M) (hG : G.IsQuasicoherentOnSite)
    (hM : M.IsQuasicoherentOnSite) (W : SmallEtale B S hS F)
    (hW : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj W)) :
    Function.Surjective ((toImageSubmodule φ).val.app (op W)) :=
  surjective_val_app_of_epi_of_isQuasicoherentOnSite _ inferInstance hG
    (isQuasicoherentOnSite_imageSubmodule φ hG hM) W hW

/-- **Over an affine étale chart, the sections of the image submodule of a morphism of
quasi-coherent `𝒪_F`-modules are the range of the morphism.** -/
theorem mem_imageSubmodule_iff_of_isAffine (φ : G ⟶ M) (hG : G.IsQuasicoherentOnSite)
    (hM : M.IsQuasicoherentOnSite) (W : SmallEtale B S hS F)
    (hW : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj W))
    (x : M.val.obj (op W)) :
    x ∈ (imageSubmodule φ).obj (op W) ↔ ∃ y, φ.val.app (op W) y = x := by
  refine ⟨fun hx => ?_, fun ⟨y, hy⟩ => hy ▸ apply_mem_imageSubmodule φ y⟩
  obtain ⟨y, hy⟩ := surjective_toImageSubmodule_app φ hG hM W hW ⟨x, hx⟩
  exact ⟨y, congrArg Subtype.val hy⟩

end AlgebraicGeometry.Space

end
