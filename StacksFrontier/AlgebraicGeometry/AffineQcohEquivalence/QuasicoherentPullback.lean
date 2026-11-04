module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposModuleAdjunction
public import StacksFrontier.AlgebraicGeometry.AffineQcohEquivalence.Basic
public import StacksFrontier.AlgebraicGeometry.QcohOverAlgebra.RestrictScalars
public import StacksFrontier.AlgebraicGeometry.ChangeOfRingsTensor.Basic
public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentPullbackScheme
public import StacksFrontier.CategoryTheory.Sites.Modules.TensorProduct.Basic

/-!
# The quasi-inverse of Stacks Tag 01SB preserves quasi-coherence

Let `f : X ⟶ S` be an affine morphism of schemes, let `A = f_* 𝒪_X` and let
`Stacks.AlgebraicGeometry.AffineQcohEquivalence.pullbackModules f` be the left adjoint of the
direct image over `A`, the quasi-inverse of Stacks Tag 01SB. This file proves that this
quasi-inverse carries quasi-coherent `A`-modules to quasi-coherent `𝒪_X`-modules, which is the
first of the three hypotheses of
`Stacks.AlgebraicGeometry.AffineQcohEquivalence.isEquivalence_affineQuasicoherentPushforward`.

## Main definitions

* `Stacks.AlgebraicGeometry.AffineQcohEquivalence.extendScalarsPushforwardRing`: extension of
  scalars along `𝒪_S ⟶ f_* 𝒪_X`, with `f_* 𝒪_X` spelled as
  `Stacks.AlgebraicGeometry.AffineQcohPushforward.pushforwardRing`.
* `Stacks.AlgebraicGeometry.AffineQcohEquivalence.restrictScalarsPushforwardRing`: restriction of
  scalars along `𝒪_S ⟶ f_* 𝒪_X`, with the same spelling.
* `Stacks.AlgebraicGeometry.AffineQcohEquivalence.extendRestrictScalarsPushforwardRingAdjunction`:
  the adjunction between them.

## Main results

* `Stacks.AlgebraicGeometry.AffineQcohEquivalence.pullbackExtendScalarsIso`: the quasi-inverse
  of Tag 01SB precomposed with extension of scalars is the ordinary pullback of `𝒪_S`-modules.
* `Stacks.AlgebraicGeometry.AffineQcohEquivalence.isQuasicoherent_restrictScalars_extendScalars`:
  extension of scalars along `𝒪_S ⟶ f_* 𝒪_X`, read back as a functor to `𝒪_S`-modules,
  preserves quasi-coherence when `f` is affine.
* `Stacks.AlgebraicGeometry.AffineQcohEquivalence.isQuasicoherent_extendScalars`: the same
  statement read over `f_* 𝒪_X` rather than over `𝒪_S`.
* `Stacks.AlgebraicGeometry.AffineQcohEquivalence.isQuasicoherent_pullbackModules`: **the first
  of the three hypotheses of Stacks Tag 01SB**, namely that the quasi-inverse preserves
  quasi-coherence.

## References

* [Stacks Project, Tag 01SB](https://stacks.math.columbia.edu/tag/01SB)
* [Stacks Project, Tag 01CE](https://stacks.math.columbia.edu/tag/01CE)
* [Stacks Project, Tag 01BG](https://stacks.math.columbia.edu/tag/01BG)
* [Stacks Project, Tag 0H88](https://stacks.math.columbia.edu/tag/0H88)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry
open Stacks.Sheaves.ModuleAdjunction

universe u

noncomputable section

namespace Stacks.AlgebraicGeometry.AffineQcohEquivalence

open Stacks.AlgebraicGeometry.AffineQcohPushforward

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-! ### Extension and restriction of scalars along `𝒪_S ⟶ f_* 𝒪_X` -/

/-- Extension of scalars along `𝒪_S ⟶ f_* 𝒪_X`, with the target sheaf of rings spelled as
`Stacks.AlgebraicGeometry.AffineQcohPushforward.pushforwardRing`. -/
def extendScalarsPushforwardRing :
    SheafOfModules.{u} S.ringCatSheaf ⥤
      SheafOfModules.{u} (pushforwardRing f.base X.ringCatSheaf) :=
  extendScalars f.toRingCatSheafHom

/-- Restriction of scalars along `𝒪_S ⟶ f_* 𝒪_X`, with the source sheaf of rings spelled as
`Stacks.AlgebraicGeometry.AffineQcohPushforward.pushforwardRing`. -/
def restrictScalarsPushforwardRing :
    SheafOfModules.{u} (pushforwardRing f.base X.ringCatSheaf) ⥤
      SheafOfModules.{u} S.ringCatSheaf :=
  SheafOfModules.restrictScalars f.toRingCatSheafHom

/-- Extension of scalars along `𝒪_S ⟶ f_* 𝒪_X` is left adjoint to restriction of scalars. -/
def extendRestrictScalarsPushforwardRingAdjunction :
    extendScalarsPushforwardRing f ⊣ restrictScalarsPushforwardRing f :=
  extendRestrictScalarsAdjunction f.toRingCatSheafHom

/-- Restriction of scalars along `𝒪_S ⟶ f_* 𝒪_X` preserves zero morphisms. -/
instance preservesZeroMorphisms_restrictScalarsPushforwardRing :
    (restrictScalarsPushforwardRing f).PreservesZeroMorphisms :=
  ⟨fun _ _ ↦ rfl⟩

/-- Restriction of scalars along `𝒪_S ⟶ f_* 𝒪_X` preserves finite limits. -/
instance preservesFiniteLimits_restrictScalarsPushforwardRing :
    PreservesFiniteLimits (restrictScalarsPushforwardRing f) :=
  QcohOverAlgebra.preservesFiniteLimits_restrictScalars.{u} f.toRingCatSheafHom

/-- The counit of extension and restriction of scalars along `𝒪_S ⟶ f_* 𝒪_X` is an
epimorphism. -/
instance epi_extendRestrictScalarsPushforwardRingAdjunction_counit
    (G : SheafOfModules.{u} (pushforwardRing f.base X.ringCatSheaf)) :
    Epi ((extendRestrictScalarsPushforwardRingAdjunction f).counit.app G) := by
  have hsplit : IsSplitEpi ((restrictScalarsPushforwardRing f).map
      ((extendRestrictScalarsPushforwardRingAdjunction f).counit.app G)) :=
    ⟨⟨_, (extendRestrictScalarsPushforwardRingAdjunction f).right_triangle_components G⟩⟩
  have hreflects : (restrictScalarsPushforwardRing f).ReflectsEpimorphisms :=
    QcohOverAlgebra.reflectsEpimorphisms_restrictScalars.{u} f.toRingCatSheafHom
  exact (restrictScalarsPushforwardRing f).epi_of_epi_map hsplit.epi

/-! ### The quasi-inverse of Tag 01SB on an extension of scalars -/

/-- The quasi-inverse of Stacks Tag 01SB precomposed with extension of scalars along
`𝒪_S ⟶ f_* 𝒪_X` is the ordinary pullback of `𝒪_S`-modules. -/
def pullbackExtendScalarsIso :
    Scheme.Modules.pullback f ≅
      extendScalarsPushforwardRing f ⋙ pullbackModules f :=
  Adjunction.leftAdjointUniq (Scheme.Modules.pullbackPushforwardAdjunction f)
    ((extendRestrictScalarsPushforwardRingAdjunction f).comp
      (pullbackPushforwardAdjunction f))

/-- The quasi-inverse of Stacks Tag 01SB carries the extension of scalars of a quasi-coherent
`𝒪_S`-module to a quasi-coherent `𝒪_X`-module. -/
theorem isQuasicoherent_pullbackModules_extendScalars (F : S.Modules)
    (hF : F.IsQuasicoherent) :
    ((pullbackModules f).obj
      ((extendScalarsPushforwardRing f).obj F)).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    ((pullbackExtendScalarsIso f).app F)
    (Stacks.Modules.isQuasicoherent_pullback f F hF)

/-! ### Extension of scalars along `𝒪_S ⟶ f_* 𝒪_X` preserves quasi-coherence -/

/-- For an affine morphism `f : X ⟶ S`, extension of scalars along `𝒪_S ⟶ f_* 𝒪_X` read back as
a functor to `𝒪_S`-modules preserves quasi-coherence. -/
theorem isQuasicoherent_restrictScalars_extendScalars [IsAffineHom f] (F : S.Modules)
    (hF : F.IsQuasicoherent) :
    ((restrictScalarsPushforwardRing f).obj
      ((extendScalarsPushforwardRing f).obj F)).IsQuasicoherent := by
  have h₁ : Presheaf.IsSheaf (Opens.grothendieckTopology S.carrier)
      (Stacks.PresheafOfModules.ChangeOfRings.ringPresheaf S.presheaf) := S.ringCatSheaf.2
  have h₂ : Presheaf.IsSheaf (Opens.grothendieckTopology S.carrier)
      (Stacks.PresheafOfModules.ChangeOfRings.ringPresheaf ((Opens.map f.base).op ⋙ X.presheaf)) :=
    (pushforwardRing f.base X.ringCatSheaf).2
  have hA : ((restrictScalarsPushforwardRing f).obj
      (SheafOfModules.unit (pushforwardRing f.base X.ringCatSheaf))).IsQuasicoherent :=
    isQuasicoherent_restrictScalars_pushforwardRing f
  have ebridge : extendScalarsPushforwardRing f ≅
      Stacks.Sheaves.RingedToposModules.extendScalars
        (Opens.grothendieckTopology S.carrier) f.c h₁ h₂ :=
    Adjunction.leftAdjointUniq (extendRestrictScalarsPushforwardRingAdjunction f)
      (Stacks.Sheaves.RingedToposModules.extendRestrictScalarsAdjunction
        (Opens.grothendieckTopology S.carrier) f.c h₁ h₂)
  have etensor := Stacks.Sheaves.ChangeOfRings.extendScalarsCompRestrictScalarsIso
    (Opens.grothendieckTopology S.carrier) f.c h₁ h₂
  have hten : (((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, u, u, u}
      ⟨S.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ S.presheaf (forget₂ CommRingCat RingCat)
        h₁⟩).obj ((restrictScalarsPushforwardRing f).obj
          (SheafOfModules.unit (pushforwardRing f.base X.ringCatSheaf)))).obj
            F).IsQuasicoherent := by
    show (((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨S.toRingedSpace.presheaf, S.toRingedSpace.IsSheaf⟩).obj _).obj F).IsQuasicoherent
    exact @AlgebraicGeometry.tensorSheaf_isQuasicoherent _ _ F hA hF
  exact (SheafOfModules.isQuasicoherent S.ringCatSheaf).prop_of_iso
    ((((restrictScalarsPushforwardRing f).mapIso (ebridge.app F)) ≪≫
      etensor.app F).symm) hten

/-- For an affine morphism, the extension of scalars of a quasi-coherent `𝒪_S`-module along
`𝒪_S ⟶ f_* 𝒪_X` is quasi-coherent as an `f_* 𝒪_X`-module. -/
theorem isQuasicoherent_extendScalars [IsAffineHom f] (F : S.Modules)
    (hF : F.IsQuasicoherent) :
    ((extendScalarsPushforwardRing f).obj F).IsQuasicoherent :=
  QcohLimits.isQuasicoherent_of_restrictScalars_pushforwardRing f _
    (isQuasicoherent_restrictScalars_extendScalars f F hF)

/-! ### The first hypothesis of Tag 01SB, and the reduction it leaves -/

/-- **The first of the three hypotheses of Stacks Tag 01SB.**  For an affine morphism
`f : X ⟶ S`, the quasi-inverse `𝒢 ↦ f^*𝒢 ⊗_{f^*f_*𝒪_X} 𝒪_X` of Stacks Tag 01SB carries
quasi-coherent `f_* 𝒪_X`-modules to quasi-coherent `𝒪_X`-modules. -/
theorem isQuasicoherent_pullbackModules [IsAffineHom f]
    (G : SheafOfModules.{u} (pushforwardRing f.base X.ringCatSheaf))
    (hG : G.IsQuasicoherent) :
    ((pullbackModules f).obj G).IsQuasicoherent := by
  have hsmall : PreservesColimitsOfSize.{0, 0} (pullbackModules f) :=
    preservesSmallestColimits_of_preservesColimits.{u, u} _
  set ε := (extendRestrictScalarsPushforwardRingAdjunction f).counit.app G
  have hRsG : ((restrictScalarsPushforwardRing f).obj G).IsQuasicoherent :=
    have := hG
    QcohOverAlgebra.isQuasicoherent_restrictScalars_pushforwardModules f G
  have hRsERsG : ((restrictScalarsPushforwardRing f).obj
      ((extendScalarsPushforwardRing f).obj
        ((restrictScalarsPushforwardRing f).obj G))).IsQuasicoherent :=
    isQuasicoherent_restrictScalars_extendScalars f _ hRsG
  have hRsK : ((restrictScalarsPushforwardRing f).obj (kernel ε)).IsQuasicoherent := by
    have hker : (kernel ((restrictScalarsPushforwardRing f).map ε)).IsQuasicoherent :=
      @QcohLimits.isQuasicoherent_kernel S _ _
        ((restrictScalarsPushforwardRing f).map ε) hRsERsG hRsG
    exact (SheafOfModules.isQuasicoherent S.ringCatSheaf).prop_of_iso
      (asIso (kernelComparison ε (restrictScalarsPushforwardRing f))).symm hker
  have hcoker := isCokernelEpiComp (Abelian.epiIsCokernelOfKernel _ (kernelIsKernel ε))
    (g := (extendRestrictScalarsPushforwardRingAdjunction f).counit.app (kernel ε))
    (h := (extendRestrictScalarsPushforwardRingAdjunction f).counit.app (kernel ε) ≫
      kernel.ι ε) rfl
  refine QuasicoherentColimits.isQuasicoherent_of_isColimit (fun k ↦ ?_)
    (isColimitOfPreserves (pullbackModules f) hcoker)
  obtain _ | _ := k
  · exact isQuasicoherent_pullbackModules_extendScalars f _ hRsK
  · exact isQuasicoherent_pullbackModules_extendScalars f _ hRsG

end Stacks.AlgebraicGeometry.AffineQcohEquivalence

end

end
