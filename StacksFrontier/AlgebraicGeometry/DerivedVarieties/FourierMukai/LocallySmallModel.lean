module

public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.FourierMukai.LeftAdjointLocallySmall
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.FourierMukai.QuasiCoherent
public import StacksFrontier.AlgebraicGeometry.Duality.CompactGeneration.StandardModel
public import StacksFrontier.Homology.DerivedCategory.Bridge.Pullback
public import StacksFrontier.Homology.DerivedCategory.Bridge.Pushforward
public import StacksFrontier.Homology.DerivedCategory.Bridge.Tensor

/-!
# Fourier-Mukai transforms at the standard and at the locally small model

The Fourier-Mukai functor `AlgebraicGeometry.fourierMukai` is built at the standard model
`HasDerivedCategory.standard` of the derived categories, while the right adjoint of derived direct
image ([Stacks, Tag 0A9E]) and the duality statements built on it live at the locally small model
`AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`. This file identifies the two Fourier-Mukai
functors across the comparison `AlgebraicGeometry.Scheme.Modules.derivedModelEquiv` of the two
models: each of the three factors — derived pullback, derived tensor product with the kernel, and
derived direct image — commutes with the comparison
(`StacksDraft.DerivedModel.schemeDerivedPullbackStandardModelEquivIso`,
`AlgebraicGeometry.Scheme.Modules.derivedTensorProductFunctorStandardIso`,
`StacksDraft.DerivedModel.schemeDerivedPushforwardStandardIso`).

## Main definitions

* `AlgebraicGeometry.fourierMukaiModelEquivIso` — `Φ_K ⋙ e_Y ≅ e_X ⋙ Φ_{e K}` on `D(𝒪)`.
* `AlgebraicGeometry.quasiCoherentFourierMukaiModelEquivIso` — the same on `D_QCoh`.

## Implementation notes

No `HasDerivedCategory` instance is installed: every object at the standard model is written with
`HasDerivedCategory.standard` explicitly, and every object at the locally small model with the
global instance.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe u

namespace AlgebraicGeometry

variable {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)

/-- **The Fourier-Mukai functor commutes with the comparison of models.** For a kernel `K` at the
standard model, `Φ_K` followed by the comparison `e_Y` of the two models of `D(𝒪_Y)` is the
comparison `e_X` followed by the Fourier-Mukai functor of `e K` at the locally small model. -/
def fourierMukaiModelEquivIso
    (K : @DerivedCategory (pullback f g).Modules _ _ (HasDerivedCategory.standard _)) :
    fourierMukai f g K ⋙ (Scheme.Modules.derivedModelEquiv Y).functor ≅
      (Scheme.Modules.derivedModelEquiv X).functor ⋙
        Stacks.Duality.derivedPullback (pullback.fst f g) ⋙
          (Stacks.Duality.derivedTensor (pullback f g)).flip.obj
            ((Scheme.Modules.derivedModelEquiv (pullback f g)).functor.obj K) ⋙
          Stacks.Duality.derivedPushforward (pullback.snd f g) := by
  let eP := Scheme.Modules.derivedModelEquiv (pullback f g)
  let τ := Scheme.Modules.derivedTensorProductFunctorStandardIso (pullback f g)
  let T : @DerivedCategory (pullback f g).Modules _ _ (HasDerivedCategory.standard _) ⥤
      @DerivedCategory (pullback f g).Modules _ _ (HasDerivedCategory.standard _) :=
    (@Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor _ _ _ (pullback f g).sheaf _ _
      (HasDerivedCategory.standard _) _ _ _).flip.obj K
  let eT : T ⋙ eP.functor ≅ eP.functor ⋙
      (Stacks.Duality.derivedTensor (pullback f g)).flip.obj (eP.functor.obj K) :=
    NatIso.ofComponents (fun A => (τ.app A).app K)
      (fun {A A'} φ => NatTrans.congr_app (τ.hom.naturality φ) K)
  exact Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _
        (StacksDraft.DerivedModel.schemeDerivedPushforwardStandardIso (pullback.snd f g)) ≪≫
      (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight eT _ ≪≫
      Functor.associator _ _ _) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (StacksDraft.DerivedModel.schemeDerivedPullbackStandardModelEquivIso (pullback.fst f g)) _ ≪≫
    Functor.associator _ _ _

variable [QuasiCompact f] [QuasiSeparated f] [CompactSpace Y]

/-- **The Fourier-Mukai functor on `D_QCoh` commutes with the comparison of models.** For a
kernel `K` with quasi-coherent cohomology at the standard model, the restriction
`Φ_K : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)` followed by the comparison of the two models of
`D_QCoh(𝒪_Y)` is the comparison for `X` followed by the Fourier-Mukai transform
`Stacks.Duality.fourierMukaiLocallySmall` of the transported kernel. -/
def quasiCoherentFourierMukaiModelEquivIso
    (K : @DerivedCategory (pullback f g).Modules _ _ (HasDerivedCategory.standard _))
    (hK : ∀ j : ℤ, ((@DerivedCategory.homologyFunctor (pullback f g).Modules _ _
      (HasDerivedCategory.standard _) j).obj K).IsQuasicoherent) :
    quasiCoherentFourierMukai f g K hK ⋙
        (Stacks.Duality.StandardModel.quasiCoherentModelEquiv Y).functor ≅
      (Stacks.Duality.StandardModel.quasiCoherentModelEquiv X).functor ⋙
        Stacks.Duality.fourierMukaiLocallySmall f g
          ((Stacks.Duality.StandardModel.quasiCoherentModelEquiv (pullback f g)).functor.obj
            ⟨K, hK⟩) := by
  let KL := (Stacks.Duality.StandardModel.quasiCoherentModelEquiv (pullback f g)).functor.obj
    ⟨K, hK⟩
  let Φ' : Stacks.Duality.quasiCoherentDerivedCategory X ⥤
      Stacks.Duality.quasiCoherentDerivedCategory Y :=
    Stacks.Duality.quasiCoherentDerivedPullback' (pullback.fst f g) ⋙
      (Stacks.Duality.quasiCoherentDerivedTensor (pullback f g)).flip.obj KL ⋙
      Stacks.Duality.quasiCoherentDerivedPushforward (pullback.snd f g)
        (Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs _)
  let tL : (Stacks.Duality.quasiCoherentDerivedTensor (pullback f g)).flip.obj KL ⋙
        ObjectProperty.ι _ ≅
      ObjectProperty.ι _ ⋙ (Stacks.Duality.derivedTensor (pullback f g)).flip.obj KL.obj :=
    NatIso.ofComponents (fun _ => Iso.refl _) (fun φ => by
      simp only [Functor.comp_map, ObjectProperty.ι_map, Functor.flip_obj_map,
        Stacks.Duality.quasiCoherentDerivedTensor_map_app_hom, Iso.refl_hom]
      exact (Category.comp_id _).trans (Category.id_comp _).symm)
  let iso₁ : quasiCoherentFourierMukai f g K hK ⋙
        (Stacks.Duality.StandardModel.quasiCoherentModelEquiv Y).functor ≅
      (Stacks.Duality.StandardModel.quasiCoherentModelEquiv X).functor ⋙ Φ' :=
    ((ObjectProperty.fullyFaithfulι _).whiskeringRight _).preimageIso
      (Functor.isoWhiskerLeft (ObjectProperty.ι _) (fourierMukaiModelEquivIso f g K) ≪≫
        (Functor.isoWhiskerLeft
          ((Stacks.Duality.StandardModel.quasiCoherentModelEquiv X).functor ⋙
            Stacks.Duality.quasiCoherentDerivedPullback' (pullback.fst f g))
          (Functor.isoWhiskerRight tL
            (Stacks.Duality.derivedPushforward (pullback.snd f g)))).symm)
  let iso₂ : Φ' ≅ Stacks.Duality.fourierMukaiLocallySmall f g KL :=
    Functor.isoWhiskerLeft _ (Functor.isoWhiskerRight
      (((flipFunctor _ _ _).mapIso
        (Stacks.Duality.quasiCoherentDerivedTensorIsoCurriedTensor (pullback f g))).app KL) _)
  exact iso₁ ≪≫ Functor.isoWhiskerLeft _ iso₂

end AlgebraicGeometry

end
