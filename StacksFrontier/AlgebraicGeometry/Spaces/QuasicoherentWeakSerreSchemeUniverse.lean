module

public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentWeakSerre
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentWeakSerreUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.SliceAssociatedModuleEssSurjFromChart
import all StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentWeakSerre

/-!
# Additions to `StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentWeakSerre`

Declarations supplementing `StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentWeakSerre`, kept
in their own module.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 5000] SheafOfModules.instAbelian

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-- **The extension clause of Stacks 03M1 at the universe of the schemes.**  The middle term of a
short exact sequence of `𝒪_F`-modules whose outer terms are quasi-coherent is quasi-coherent. -/
instance isClosedUnderExtensions_quasicoherentSheaves_smallEtale :
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS F hF).O))).IsClosedUnderExtensions where
  prop_X₂_of_shortExact {T} hT h₁ h₃ := by
    have : T.X₁.IsQuasicoherentOnSite := h₁
    have : T.X₃.IsQuasicoherentOnSite := h₃
    exact isQuasicoherent_middle_of_shortExact T hT
      (isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS F hF)
      (fun U hU => surjective_g_val_app_of_shortExact_of_h03DW T hT
        (fun q hq hk W hW =>
          surjective_val_app_of_epi_of_kernel_isCartesian_unconditional B S hS (X := ⟨F, hF⟩)
            q hq hk W hW)
        (isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS F hF T.X₁ h₁) U hU)

/- The weak Serre class of quasi-coherent `𝒪_F`-modules at the universe of the schemes is
`AlgebraicGeometry.Space.quasicoherentSheaves_isWeakSerreClass_schemeUniverse`
(`StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentWeakSerreUnconditional`); it is made an
instance here. -/
attribute [instance] quasicoherentSheaves_isWeakSerreClass_schemeUniverse

end AlgebraicGeometry.Space

end
