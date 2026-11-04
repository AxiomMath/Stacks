module

public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiTwistReading
public import StacksFrontier.AlgebraicGeometry.Spaces.AmpleSchemeFibreTwistStalk
public import StacksFrontier.AlgebraicGeometry.Spaces.InvertibleQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackQuasicoherentFromChartDiagrams
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleUnit
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerCoherence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleRankOne

/-!
# The twist `𝒪 ⊗ ℒ^{⊗ d}`, read on a scheme over an algebraic space

For an invertible `𝒪_X`-module `ℒ` and a morphism `p : h_U ⟶ X` from (the space of) a scheme,
the restriction of `p^*(𝒪_X ⊗ ℒ^{⊗ d})` to the Zariski site of `U` is the `d`-th tensor power of
the restriction `ℒ_U` of `ℒ` (`d ≥ 1`), in the spelling `Stacks.Ample.tensorPowModule` of the
ampleness theory of schemes.  This is how the sections of `ℒ_y^{⊗ d}` on the fibre `X_y` chosen in
the proof of Stacks 0D3A are read as sections of the twist that Stacks 0D39 lifts.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open Stacks.SheafOfModules.Tensor (ringSheaf)

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] modulesMonoidalCategory

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **`p^*(𝒪_X ⊗ ℒ^{⊗ (d+1)})` read on `U` is `ℒ_U^{⊗ (d+1)}`.** -/
theorem nonempty_restrictToChartScheme_unit_tensor_tensorPow_iso {X : AlgebraicSpaces B S hS}
    (L : Modules.{u, u} B S hS X.1 X.2)
    [Stacks.SheafOfModules.IsInvertible (structureSheaf B S hS X.1 X.2).obj
      (structureRingPresheaf_isSheaf B S hS X.1 X.2) L]
    (U : BigFppfOver B S hS) (p : yoneda.obj U ⟶ X.1)
    [Stacks.Ample.IsInvertibleModule ((BigFppfOver.toScheme B S hS).obj U)
      (baseChangeModule B S hS L U p)] (d : ℕ) :
    Nonempty (restrictToChartSchemeModules B S hS (representedAlgebraicSpace B S hS U).1
        (representedAlgebraicSpace B S hS U).2
        ((modulePullback B S hS (ObjectProperty.homMk p :
          representedAlgebraicSpace B S hS U ⟶ X)).obj
            (SheafOfModules.unit (ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O) ⊗
              tensorPow B S hS L (d + 1))) (idEtaleChart B S hS U) ≅
      Stacks.Ample.tensorPowModule ((BigFppfOver.toScheme B S hS).obj U)
        (baseChangeModule B S hS L U p) ((d + 1 : ℕ) : ℤ)) := by
  let P : representedAlgebraicSpace B S hS U ⟶ X := ObjectProperty.homMk p
  have hL : L.IsQuasicoherentOnSite := isQuasicoherentOnSite_of_isInvertible B S hS X L
    (Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ L ‹_›)
  have hpL := isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS P L hL
  have hpO := isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS P
    (SheafOfModules.unit (ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))
    inferInstance
  have : Stacks.Ample.IsInvertibleModule ((BigFppfOver.toScheme B S hS).obj U)
      (zariskiModule U ((modulePullback B S hS P).obj L)) :=
    ‹Stacks.Ample.IsInvertibleModule _ (baseChangeModule B S hS L U p)›
  have e₁ := (zariskiFunctor U).mapIso (modulePullbackTensorPowIso P
    (SheafOfModules.unit (ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)) L (d + 1))
  have e₂ := zariskiModuleTwistPowSuccIso U _ _ hpO hpL d
  have e₃ := Stacks.RelativeVeryAmple.tensorModulesMapIso ((BigFppfOver.toScheme B S hS).obj U)
    (baseChangeUnitModuleIso X U p)
    (Iso.refl (Stacks.Ample.tensorPowModule ((BigFppfOver.toScheme B S hS).obj U)
      (baseChangeModule B S hS L U p) ((d + 1 : ℕ) : ℤ)))
  have e₄ := Stacks.Algebraization.unitTensorModulesIso ((BigFppfOver.toScheme B S hS).obj U)
    (Stacks.Ample.tensorPowModule ((BigFppfOver.toScheme B S hS).obj U)
      (baseChangeModule B S hS L U p) ((d + 1 : ℕ) : ℤ))
  exact ⟨e₁ ≪≫ e₂ ≪≫ e₃ ≪≫ e₄⟩

section Invertible

variable {X : AlgebraicSpaces B S hS}

/-- The tensor product of two invertible `𝒪_X`-modules is invertible (Stacks 01CT (1)). -/
theorem isInvertible_modulesTensorObj (M N : Modules.{u, u} B S hS X.1 X.2)
    [Stacks.SheafOfModules.IsInvertible (structureSheaf B S hS X.1 X.2).obj
      (structureRingPresheaf_isSheaf B S hS X.1 X.2) M]
    [Stacks.SheafOfModules.IsInvertible (structureSheaf B S hS X.1 X.2).obj
      (structureRingPresheaf_isSheaf B S hS X.1 X.2) N] :
    Stacks.SheafOfModules.IsInvertible (structureSheaf B S hS X.1 X.2).obj
      (structureRingPresheaf_isSheaf B S hS X.1 X.2) (M ⊗ N : Modules.{u, u} B S hS X.1 X.2) :=
  have := Stacks.SheafOfModules.isInvertible_tensorSheaf (structureSheaf B S hS X.1 X.2).obj
    (structureRingPresheaf_isSheaf B S hS X.1 X.2) M N
  Stacks.SheafOfModules.isInvertible_of_iso _ _ (modulesTensorObjIso B S hS X.1 X.2 M N).symm

/-- The structure sheaf is an invertible `𝒪_X`-module. -/
theorem isInvertible_modulesTensorUnit :
    Stacks.SheafOfModules.IsInvertible (structureSheaf B S hS X.1 X.2).obj
      (structureRingPresheaf_isSheaf B S hS X.1 X.2) (𝟙_ (Modules.{u, u} B S hS X.1 X.2)) := by
  have e : (𝟙_ (Modules.{u, u} B S hS X.1 X.2)) ⊗ 𝟙_ (Modules.{u, u} B S hS X.1 X.2) ≅
      𝟙_ (Modules.{u, u} B S hS X.1 X.2) := λ_ _
  exact (Stacks.SheafOfModules.isInvertible_iff_exists_tensor_iso_unit _).mpr
    ⟨𝟙_ (Modules.{u, u} B S hS X.1 X.2), ⟨(modulesTensorObjIso B S hS X.1 X.2 _ _).symm ≪≫ e⟩⟩

/-- The tensor powers of an invertible `𝒪_X`-module are invertible. -/
theorem isInvertible_tensorPow (L : Modules.{u, u} B S hS X.1 X.2)
    [Stacks.SheafOfModules.IsInvertible (structureSheaf B S hS X.1 X.2).obj
      (structureRingPresheaf_isSheaf B S hS X.1 X.2) L] :
    ∀ d : ℕ, Stacks.SheafOfModules.IsInvertible (structureSheaf B S hS X.1 X.2).obj
      (structureRingPresheaf_isSheaf B S hS X.1 X.2) (tensorPow B S hS L d)
  | 0 => isInvertible_modulesTensorUnit
  | 1 => ‹_›
  | d + 2 => by
    have := isInvertible_tensorPow L (d + 1)
    exact isInvertible_modulesTensorObj (tensorPow B S hS L (d + 1)) L

/-- **The twist `𝒪_X ⊗ ℒ^{⊗ d}` of an invertible module is invertible.** -/
theorem isInvertible_unit_tensor_tensorPow (L : Modules.{u, u} B S hS X.1 X.2)
    [Stacks.SheafOfModules.IsInvertible (structureSheaf B S hS X.1 X.2).obj
      (structureRingPresheaf_isSheaf B S hS X.1 X.2) L] (d : ℕ) :
    Stacks.SheafOfModules.IsInvertible (structureSheaf B S hS X.1 X.2).obj
      (structureRingPresheaf_isSheaf B S hS X.1 X.2)
      (SheafOfModules.unit (ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O) ⊗
        tensorPow B S hS L d : Modules.{u, u} B S hS X.1 X.2) := by
  have := isInvertible_tensorPow L d
  have : Stacks.SheafOfModules.IsInvertible (structureSheaf B S hS X.1 X.2).obj
      (structureRingPresheaf_isSheaf B S hS X.1 X.2)
      (SheafOfModules.unit (ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)) :=
    isInvertible_modulesTensorUnit
  exact isInvertible_modulesTensorObj _ (tensorPow B S hS L d)

end Invertible

end AlgebraicGeometry.Space

end
