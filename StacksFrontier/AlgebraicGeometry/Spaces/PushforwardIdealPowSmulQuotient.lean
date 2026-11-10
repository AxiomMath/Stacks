module

public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleAffinePushforwardExactness
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardChartComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.PushforwardTensorPairing

/-!
# `π_*(ℐᵃ𝒬)` as a quotient of a finite locally free module

Let `π : Y ⟶ X` be an affine morphism of algebraic spaces, `ℐ ⊆ 𝒪_Y` a quasi-coherent sheaf of
ideals such that `π_*ℐ` is a quotient of a finite locally free `𝒪_X`-module, and let
`ρ : 𝒬 ⟶ ℐⁿ⁺¹` be an epimorphism of quasi-coherent `𝒪_Y`-modules whose kernel is killed by
`ℐᵃ⁺¹`.  Then `π_*(ℐᵃ⁺¹𝒬)` is a quotient of a finite locally free `𝒪_X`-module.

The action `π_*ℐᵃ⁺¹ ⊗ π_*𝒬 ⟶ π_*(ℐᵃ⁺¹𝒬)` is an epimorphism
(`AlgebraicGeometry.Space.epi_idealPowSmulPairing`) which kills `π_*ℐᵃ⁺¹ ⊗ π_*(ker ρ)`; the tensor
product being right exact (Stacks 05NB) and `π_*` exact on quasi-coherent modules, it factors
through `π_*ℐᵃ⁺¹ ⊗ π_*ℐⁿ⁺¹`, and both factors are quotients of finite locally free modules
(`AlgebraicGeometry.Space.exists_isFiniteLocallyFreeOnSite_epi_bcPushforward_idealSheafPow`).

This is how the extended generators of the converse of Stacks 0GV1 are fed to the trace: the
module `ℐᵃ⁺¹𝒬` is the source of a map to `π^!ℱ` whose kernel issues, invisible on `j(V)`, are
absorbed by the factor `ℐᵃ⁺¹`.

## Main results

* `AlgebraicGeometry.Space.isColimit_cokernelCofork_bcPushforward`: the direct image along an
  affine morphism keeps the cokernel of a short exact sequence of quasi-coherent modules.
* `AlgebraicGeometry.Space.exists_isFiniteLocallyFreeOnSite_epi_bcPushforward_idealPowModule`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

open scoped TensorProduct

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS} (π : Y ⟶ X)
    (hrep : yoneda.relativelyRepresentable π.hom)

/-- The abelian structure on modules, pinned at the universes in use. -/
noncomputable local instance (priority := high) abelianModules_pushforwardIdealPowSmulQuotient
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F) :
    Abelian (Modules.{u, u} B S hS F hF) :=
  SheafOfModules.instAbelian _

/-- The direct image along small-chart base change, as a functor between categories of
`AlgebraicGeometry.Space.Modules`. -/
abbrev bcPushforwardFunctor : Modules.{u, u} B S hS Y.1 Y.2 ⥤ Modules.{u, u} B S hS X.1 X.2 :=
  smallBaseChangeModulePushforward.{u, u} B S hS π hrep

/-- The direct image along small-chart base change is additive, being isomorphic to the direct
image `AlgebraicGeometry.Space.modulePushforward`. -/
instance additive_bcPushforwardFunctor : (bcPushforwardFunctor B S hS π hrep).Additive :=
  Functor.additive_of_iso (modulePushforwardChartIso B S hS π hrep)

/-- **The direct image along an affine morphism keeps the cokernel of a short exact sequence of
quasi-coherent modules**, in the small-chart base-change spelling of the direct image. -/
def isColimit_cokernelCofork_bcPushforward (hπ : IsAffineHom B S hS π.hom)
    {K Q D : Modules.{u, u} B S hS Y.1 Y.2} (ι : K ⟶ Q) (ρ : Q ⟶ D) (w : ι ≫ ρ = 0)
    (hι : IsLimit (KernelFork.ofι ι w)) [Epi ρ] (hQ : Q.IsQuasicoherentOnSite)
    (hD : D.IsQuasicoherentOnSite) :
    IsColimit (CokernelCofork.ofπ ((bcPushforwardFunctor B S hS π hrep).map ρ)
      (by rw [← Functor.map_comp, w, Functor.map_zero]) :
        CokernelCofork ((bcPushforwardFunctor B S hS π hrep).map ι)) := by
  let SC := ShortComplex.mk ι ρ w
  haveI : PreservesLimits (modulePushforward B S hS π) :=
    (modulePullbackAdjunction B S hS π).rightAdjoint_preservesLimits
  have hfk := KernelFork.mapIsLimit _ hι (modulePushforward B S hS π)
  have hSE' : (SC.map (modulePushforward B S hS π)).ShortExact :=
    { exact := ShortComplex.exact_of_f_is_kernel _ hfk
      mono_f := mono_of_isLimit_fork hfk
      epi_g := epi_modulePushforward_map_of_isAffineHom π hπ hQ hD ρ }
  have hSE'' : (SC.map (bcPushforwardFunctor B S hS π hrep)).ShortExact :=
    ShortComplex.shortExact_of_iso
      (SC.mapNatIso (modulePushforwardChartIso B S hS π hrep)) hSE'
  exact hSE''.gIsCokernel

variable (I : (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS Y.1 Y.2).O)).Submodule)

/-- **The action of `π_*ℐᵃ` on `π_*` of a module vanishes on the direct image of a submodule
killed by `ℐᵃ`.** -/
theorem tensorSheafRight_map_comp_idealPowSmulPairing_eq_zero (a : ℕ)
    {K Q : Modules.{u, u} B S hS Y.1 Y.2} (g : K ⟶ Q)
    (hkill : ∀ (W : (smallEtaleRingedSite B S hS Y.1 Y.2).Cᵒᵖ)
      (r : (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O).obj.obj
        W), r ∈ (SheafOfModules.idealSheafPow I a).obj W →
        ∀ k : K.val.obj W, r • (g.val.app W).hom k = 0) :
    (Stacks.SheafOfModules.TensorLocalProperties.tensorSheafRight
        (smallEtaleRingedSite B S hS X.1 X.2).J (smallEtaleRingedSite B S hS X.1 X.2).O
        (bcPushforward B S hS π hrep (SheafOfModules.idealSheafPow I a).toSheafOfModules)).map
          ((bcPushforwardFunctor B S hS π hrep).map g) ≫
      idealPowSmulPairing B S hS π hrep I a Q = 0 := by
  refine modulesTensor_hom_eq_zero B S hS _ fun V x y => ?_
  have h1 := tensorSheafRight_map_tmul B S hS
    (bcPushforward B S hS π hrep (SheafOfModules.idealSheafPow I a).toSheafOfModules)
    ((bcPushforwardFunctor B S hS π hrep).map g) V x y
  change ((idealPowSmulPairing B S hS π hrep I a Q).val.app V).hom
    ((((((Stacks.SheafOfModules.Tensor.sheafTensor (smallEtaleRingedSite B S hS X.1 X.2).O).obj
      _).map ((bcPushforwardFunctor B S hS π hrep).map g)).val.app V).hom
        (modulesTensorTmul B S hS x y))) = 0
  rw [h1]
  refine (pushforwardTensorPairing_tmul B S hS π hrep _ _ _ _ _ _ _ _ _).trans ?_
  refine idealPowSmulSection_ext B S hS ?_
  exact hkill _ _ (submoduleSection B S hS x).2 _

/-- **`π_*(ℐᵃ⁺¹𝒬)` is a quotient of a finite locally free module** when `π` is affine, `π_*ℐ`
is a quotient of a finite locally free module, and `𝒬` surjects onto `ℐⁿ⁺¹` with kernel killed
by `ℐᵃ⁺¹`. -/
theorem exists_isFiniteLocallyFreeOnSite_epi_bcPushforward_idealPowModule
    (hπ : IsAffineHom B S hS π.hom) (hI : I.toSheafOfModules.IsQuasicoherentOnSite)
    (E : Modules.{u, u} B S hS X.1 X.2) (hE : SheafOfModules.IsFiniteLocallyFreeOnSite E)
    (e : E ⟶ bcPushforward B S hS π hrep I.toSheafOfModules) (he : Epi e) (n a : ℕ)
    {Q : Modules.{u, u} B S hS Y.1 Y.2} (hQ : Q.IsQuasicoherentOnSite)
    (ρ : Q ⟶ (SheafOfModules.idealSheafPow I (n + 1)).toSheafOfModules) [Epi ρ]
    (hkill : ∀ (W : (smallEtaleRingedSite B S hS Y.1 Y.2).Cᵒᵖ)
      (r : (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O).obj.obj
        W), r ∈ (SheafOfModules.idealSheafPow I (a + 1)).obj W →
        ∀ k : Q.val.obj W, (ρ.val.app W).hom k = 0 → r • k = 0) :
    ∃ (P : Modules.{u, u} B S hS X.1 X.2) (_ : SheafOfModules.IsFiniteLocallyFreeOnSite P)
      (p : P ⟶ bcPushforward B S hS π hrep (idealPowModule I (a + 1) Q)), Epi p := by
  have hD : (SheafOfModules.idealSheafPow I (n + 1)).toSheafOfModules.IsQuasicoherentOnSite := by
    have h1 : SheafOfModules.idealSheafPow I (n + 1) =
        idealPowSubmodule I (n + 1) (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS Y.1 Y.2).O)) :=
      Eq.trans (idealSheafPow_eq_idealPow B S hS Y I (n + 1))
        (Stacks.Sites.idealSmul_top_eq.{u, u + 1, u} _).symm
    rw [h1]
    exact isQuasicoherentOnSite_idealPowSubmodule B S hS Y.1 Y.2 I _
      (SheafOfModules.isQuasicoherentOnSite_unit _) hI (n + 1)
  let hcolim := isColimit_cokernelCofork_bcPushforward B S hS π hrep hπ (kernel.ι ρ) ρ
    (kernel.condition ρ) (kernelIsKernel ρ) hQ hD
  let T := Stacks.SheafOfModules.TensorLocalProperties.tensorSheafRight
    (smallEtaleRingedSite B S hS X.1 X.2).J (smallEtaleRingedSite B S hS X.1 X.2).O
    (bcPushforward B S hS π hrep (SheafOfModules.idealSheafPow I (a + 1)).toSheafOfModules)
  have : PreservesColimitsOfSize.{0, 0} T := preservesColimitsOfSize_shrink.{0, u, 0, u} _
  have hT := CokernelCofork.mapIsColimit _ hcolim T
  have hzero : T.map ((bcPushforwardFunctor B S hS π hrep).map (kernel.ι ρ)) ≫
      idealPowSmulPairing B S hS π hrep I (a + 1) Q = 0 :=
    tensorSheafRight_map_comp_idealPowSmulPairing_eq_zero B S hS π hrep I (a + 1) (kernel.ι ρ)
      fun W r hr k => hkill W r hr _
        (congrArg (fun φ => (φ.val.app W).hom k) (kernel.condition ρ))
  obtain ⟨μ, hμ⟩ := CokernelCofork.IsColimit.desc' hT
    (idealPowSmulPairing B S hS π hrep I (a + 1) Q) hzero
  have hepi : Epi (idealPowSmulPairing B S hS π hrep I (a + 1) Q) :=
    epi_idealPowSmulPairing B S hS π hrep I hπ hI (a + 1) Q hQ
  have hμepi : Epi μ := by
    have h' := hμ ▸ hepi
    exact @epi_of_epi _ _ _ _ _ _ μ h'
  have hgen := exists_isFiniteLocallyFreeOnSite_epi_bcPushforward_idealSheafPow
    B S hS π hrep I hπ hI E hE e he
  obtain ⟨P₁, hP₁, p₁, hp₁⟩ := hgen a
  obtain ⟨P₂, hP₂, p₂, hp₂⟩ := hgen n
  have : PreservesColimitsOfSize.{0, 0}
      (Stacks.SheafOfModules.TensorLocalProperties.tensorSheafLeft
        (smallEtaleRingedSite B S hS X.1 X.2).J (smallEtaleRingedSite B S hS X.1 X.2).O P₂) :=
    preservesColimitsOfSize_shrink.{0, u, 0, u} _
  have h₁ : Epi (((Stacks.SheafOfModules.Tensor.sheafTensor
      (smallEtaleRingedSite B S hS X.1 X.2).O).map p₁).app P₂) :=
    (Stacks.SheafOfModules.TensorLocalProperties.tensorSheafLeft
      (smallEtaleRingedSite B S hS X.1 X.2).J (smallEtaleRingedSite B S hS X.1 X.2).O P₂).map_epi p₁
  have h₂ : Epi (T.map p₂) := T.map_epi p₂
  refine ⟨modulesTensor B S hS X P₁ P₂,
    Stacks.SheafOfModules.TensorLocalProperties.tensorSheaf_isFiniteLocallyFreeOnSite
      (smallEtaleRingedSite B S hS X.1 X.2) P₁ P₂ hP₁ hP₂,
    (((Stacks.SheafOfModules.Tensor.sheafTensor (smallEtaleRingedSite B S hS X.1 X.2).O).map
      p₁).app P₂ ≫ T.map p₂) ≫ μ, ?_⟩
  exact @epi_comp _ _ _ _ _ _ (@epi_comp _ _ _ _ _ _ h₁ _ h₂) _ hμepi

end AlgebraicGeometry.Space

end
