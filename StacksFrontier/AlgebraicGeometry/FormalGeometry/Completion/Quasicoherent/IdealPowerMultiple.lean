module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.IdealPowerQuasicoherent
public import StacksFrontier.CategoryTheory.Sites.Modules.TensorProduct.Basic

/-!
# Quasi-coherence of the ideal-power subsheaf

Let `X` be a scheme, `I` a quasi-coherent ideal sheaf on `X`, `n` a natural number and `F` a
quasi-coherent sheaf of modules on `X`. The subsheaf `I ^ n F` of `F` is the image of the
multiplication map `(I ^ n) ⊗ F ⟶ F`, and is therefore quasi-coherent.

## Main results

* `Stacks.Algebraization.isQuasicoherent_image`: the image of a morphism of quasi-coherent sheaves
  of modules is quasi-coherent.
* `Stacks.Algebraization.idealPowerMultiple_isQuasicoherent`: the subsheaf `I ^ n F` of a
  quasi-coherent sheaf of modules is quasi-coherent.

## References

* [Stacks Project, Tag 02O9](https://stacks.math.columbia.edu/tag/02O9)
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TensorProduct
open TopologicalSpace

universe u

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

namespace Stacks.Algebraization

attribute [local instance] sectionsModuleΓ sectionsModuleΓSheaf sectionsSMulCommClassΓ
  monoSubmoduleι

/-- The module structure on `Γ(M, U)` over the ring `X.ringCatSheaf.obj.obj (op U)` of sections
of the structure sheaf. -/
local instance sectionsModuleΓPresheaf {X : Scheme.{u}} (M : X.Modules) (U : X.Opens) :
    Module (X.ringCatSheaf.obj.obj (op U)) Γ(M, U) :=
  inferInstanceAs (Module Γ(X, U) Γ(M, U))

/-- The image of a morphism of quasi-coherent sheaves of modules is quasi-coherent. -/
public lemma isQuasicoherent_image {X : Scheme.{u}} {M N : X.Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] (f : M ⟶ N) :
    (image (C := X.Modules) f).IsQuasicoherent := by
  exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso (Abelian.imageIsoImage f)
    (by dsimp [Abelian.image]; infer_instance)

/-- The subsheaf `I ^ n F` of a quasi-coherent sheaf of modules `F` is quasi-coherent. -/
public lemma idealPowerMultiple_isQuasicoherent {X : Scheme.{u}}
    (I : X.IdealSheafData) (n : ℕ) (F : X.Modules) [F.IsQuasicoherent] :
    (idealPowerMultiple I n F).toSheafOfModules.IsQuasicoherent := by
  let J := kernelSubmodule
    (SheafOfModules.unitToPushforwardObjUnit (I ^ n).subschemeι.toRingCatSheafHom)
  have hJ : J.toSheafOfModules.IsQuasicoherent := idealKernel_isQuasicoherent (I ^ n)
  let P := idealPowerMultiple I n F
  have hgen (U : X.affineOpens) :
      I.ideal U ^ n • (⊤ : Submodule Γ(X, U) Γ(F, U)) ≤ P.toSubmodule.obj (op U.1) :=
    (idealPowerMultiple_le_iff I n F P).mp le_rfl U
  have hmul (U : (Opens X)ᵒᵖ) (a : J.toSheafOfModules.val.obj U) (m : F.val.obj U) :
      (show X.presheaf.obj U from a.1) • m ∈ P.toSubmodule.obj U := by
    apply mem_submodule_of_affine P U.unop
    intro V i
    have ha := J.toSubmodule.map_mem i.op a.property
    change (X.presheaf.map i.op).hom a.1 ∈ J.toSubmodule.obj (op V.1) at ha
    dsimp only [J] at ha
    rw [kernelSubmodule_obj_affine, Scheme.IdealSheafData.ideal_pow] at ha
    exact Eq.mpr (congrArg (· ∈ P.toSubmodule.obj (op V.1)) (F.val.map_smul i.op a.1 m))
      (hgen V (Submodule.smul_mem_smul ha Submodule.mem_top))
  let a := idealAction J F
  let K := kernelSubmodule (cokernel.π (C := X.Modules) a)
  have hPK : P ≤ K := by
    refine (idealPowerMultiple_le_iff I n F K).2 fun U ↦ Submodule.smul_le.mpr fun r hr m _ ↦ ?_
    have hrJ : r ∈ J.toSubmodule.obj (op U.1) := by
      dsimp only [J]
      rwa [kernelSubmodule_obj_affine, Scheme.IdealSheafData.ideal_pow]
    let t := Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection X.toRingedSpace
      J.toSheafOfModules F (op U.1) (⟨r, hrJ⟩ ⊗ₜ[Γ(X, U)] m)
    have ht : a.val.app (op U.1) t = r • m := idealAction_tmul J F _ ⟨r, hrJ⟩ m
    have hz := congrArg (fun f ↦ (f.val.app (op U.1)).hom t)
      (cokernel.condition (C := X.Modules) a)
    change (cokernel.π (C := X.Modules) a).val.app (op U.1)
      (a.val.app (op U.1) t) = 0 at hz
    dsimp only [K]
    rw [kernelSubmodule_toSubmodule_obj]
    rwa [ht] at hz
  let fac : MonoFactorisation a :=
    { I := P.toSheafOfModules
      m := P.ι
      m_mono := monoSubmoduleι P
      e := idealActionLift J F P hmul
      fac := idealActionLift_fac J F P hmul }
  let l := (Abelian.imageStrongEpiMonoFactorisation a).toMonoIsImage.lift fac
  have hl : l ≫ fac.m = (Abelian.imageStrongEpiMonoFactorisation a).m :=
    (Abelian.imageStrongEpiMonoFactorisation a).toMonoIsImage.lift_fac fac
  let k : K.toSheafOfModules ⟶ P.toSheafOfModules :=
    (kernelSubmoduleIso (cokernel.π (C := X.Modules) a)).hom ≫ l
  have hk : k ≫ P.ι = K.ι :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun g ↦ (kernelSubmoduleIso (cokernel.π (C := X.Modules) a)).hom ≫ g) hl).trans
        (kernel.lift_ι (C := X.Modules) _ _ _))
  have hKP : K ≤ P := by
    intro U m hm
    have he := congrArg (fun f ↦ (f.val.app U).hom ⟨m, hm⟩) hk
    change ((k.val.app U).hom ⟨m, hm⟩).1 = m at he
    exact he ▸ ((k.val.app U).hom ⟨m, hm⟩).property
  show P.toSheafOfModules.IsQuasicoherent
  rw [le_antisymm hPK hKP]
  exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    ((Abelian.imageIsoImage a).symm ≪≫
      (kernelSubmoduleIso (cokernel.π (C := X.Modules) a)).symm)
    (@isQuasicoherent_image X _ F
      (@AlgebraicGeometry.tensorSheaf_isQuasicoherent _ J.toSheafOfModules F hJ ‹_›) ‹_› a)

end Stacks.Algebraization

end

end
