module

public import StacksFrontier.AlgebraicGeometry.FibreProductAffineChart.ChartBoxSectionGeneration

/-!
# The chart base change of a differential operator, as a term

Let `a : X ⟶ S` and `b : Y ⟶ S` be morphisms of schemes, let `F`, `F'` be quasi-coherent
`𝒪_X`-modules, let `G` be a quasi-coherent `𝒪_Y`-module and let `D : F ⟶ F'` be a differential
operator of order at most `k` on `X/S`. Over the opens of an affine chart of `X ×_S Y` the base
change of `D` is the operator `D ⊗ id` of Tag 0G37, transported along the identification of the
sections of `F ⊠ G` on the chart with `Γ(Spec A, F) ⊗_R Γ(Spec B, G)`. This file defines that
operator and computes its action on the section of `F ⊠ G` attached to a pair of local sections.

## Main definitions

* `Stacks.FibreProductAffineChart.Chart.boxOp`: the base change of `D` over the opens of a chart,
  together with its order bound.

## Main results

* `Stacks.FibreProductAffineChart.Chart.boxOp_tmul`: read through the chart identification,
  `Chart.boxOp` carries `s ⊗ t` to `D s ⊗ t`.
* `Stacks.FibreProductAffineChart.Chart.apply_externalTensorSection_boxOp`: `Chart.boxOp`
  carries the section of `F ⊠ G` attached to a section `s` of `F` over an open containing the
  chart's first factor and a section `t` of `G` over an open containing its second factor to the
  section attached to `D s` and `t`.

## References

* [Stacks Project, Tag 0G37](https://stacks.math.columbia.edu/tag/0G37)
* [Stacks Project, Tag 0G45](https://stacks.math.columbia.edu/tag/0G45)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct TopologicalSpace
open CommRingCat
open Stacks.Tag01VSPullbackTensor

universe u

attribute [local instance] Stacks.AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback

namespace Stacks.FibreProductAffineChart

open _root_.AlgebraicGeometry

attribute [local instance] Algebra.TensorProduct.rightAlgebra

namespace Chart

variable {X Y S : Scheme.{u}} {a : X ⟶ S} {b : Y ⟶ S} (c : Chart a b)

attribute [local instance] leftModuleAlg leftModuleBase leftTower
attribute [local instance] rightModuleAlg rightModuleBase rightTower
attribute [local instance] Stacks.TensorProductPushout.rightModule
  Stacks.TensorProductPushout.rightModule_isScalarTower
  Stacks.TensorProductPushout.smulCommClass_right
  Stacks.TensorProductPushout.pushoutModule
  Stacks.TensorProductPushout.pushoutModule_isScalarTower
attribute [local instance] boxModuleAlg boxModuleBase boxTower

variable (F F' : X.Modules) (G : Y.Modules)
  [F.IsQuasicoherent] [F'.IsQuasicoherent] [G.IsQuasicoherent] (k : ℕ)
  (D : DiffOp.GlobalOp F F')
  (hD : DiffOp.IsGlobalDiffOpOfOrder a.relativeStructureSheafMap k D)

/-- **The base change of a differential operator over the opens of an affine chart.** The operator
`D ⊗ id` on `Γ(Spec A, F) ⊗_R Γ(Spec B, G)`, together with its order bound, read through the
identification of the differential operators of order at most `k` on `X ×_S Y / Y` over the opens
of the chart with the differential operators of order at most `k` relative to `B ⟶ A ⊗_R B` on
those sections. -/
def boxOp :
    {E : DiffOp.RawOp (externalTensorProduct a b F G) (externalTensorProduct a b F' G)
        c.ι.opensRange //
      DiffOp.IsDiffOpOfOrder (pullback.snd a b).relativeStructureSheafMap k E} :=
  letI := c.algebraLeft
  letI := c.algebraRight
  (c.boxDiffOpTensorEquiv (ofHom_algebraMap_left c) (ofHom_algebraMap_right c) F G F' k).symm
    ⟨LinearMap.IsDifferentialOperatorOfOrderLE.rTensorB
        (Stacks.TensorProductPushout.pushoutModule_algebraMap_apply
          ↑Γ(S, c.base) ↑Γ(X, c.left) ↑Γ(Y, c.right))
        (Stacks.TensorProductPushout.pushoutModule_smul_tmul_tmul
          ↑Γ(S, c.base) ↑Γ(X, c.left) ↑Γ(Y, c.right) _ _)
        (Stacks.TensorProductPushout.pushoutModule_smul_tmul_tmul
          ↑Γ(S, c.base) ↑Γ(X, c.left) ↑Γ(Y, c.right) _ _)
        (c.leftDiffOpEquiv (ofHom_algebraMap_left c) F F' k
          ⟨D.restrict c.fromSpecLeft.opensRange, hD c.fromSpecLeft.opensRange⟩).1,
      LinearMap.IsDifferentialOperatorOfOrderLE.order_rTensorB
        (c.leftDiffOpEquiv (ofHom_algebraMap_left c) F F' k
          ⟨D.restrict c.fromSpecLeft.opensRange, hD c.fromSpecLeft.opensRange⟩).2
        (Stacks.TensorProductPushout.pushoutModule_algebraMap_apply
          ↑Γ(S, c.base) ↑Γ(X, c.left) ↑Γ(Y, c.right))
        (Stacks.TensorProductPushout.pushoutModule_smul_tmul_tmul
          ↑Γ(S, c.base) ↑Γ(X, c.left) ↑Γ(Y, c.right) _ _)
        (Stacks.TensorProductPushout.pushoutModule_smul_tmul_tmul
          ↑Γ(S, c.base) ↑Γ(X, c.left) ↑Γ(Y, c.right) _ _)⟩

/-- **`Stacks.FibreProductAffineChart.Chart.boxOp` on pure tensors.** Read through the
identification of the sections of `F ⊠ G` on the chart with `Γ(Spec A, F) ⊗_R Γ(Spec B, G)`, the
base change of `D` carries `s ⊗ t` to `D s ⊗ t`. -/
theorem boxOp_tmul :
    letI := c.algebraLeft
    letI := c.algebraRight
    ∀ (s : Γ((Scheme.Modules.pullback c.fromSpecLeft).obj F, ⊤))
      (t : Γ((Scheme.Modules.pullback c.fromSpecRight).obj G, ⊤)),
      (c.boxDiffOpTensorEquiv (ofHom_algebraMap_left c) (ofHom_algebraMap_right c) F G F' k
          (c.boxOp F F' G k D hD)).1 (s ⊗ₜ[Γ(S, c.base)] t) =
        (c.leftDiffOpEquiv (ofHom_algebraMap_left c) F F' k
            ⟨D.restrict c.fromSpecLeft.opensRange, hD c.fromSpecLeft.opensRange⟩).1 s
          ⊗ₜ[Γ(S, c.base)] t := by
  let := c.algebraLeft
  let := c.algebraRight
  intro s t
  simp only [boxOp, Equiv.apply_symm_apply]
  exact LinearMap.IsDifferentialOperatorOfOrderLE.rTensorB_tmul _ _ _ _ s t

/-- **`Stacks.FibreProductAffineChart.Chart.boxOp` on the section attached to a pair of local
sections.** For opens `U'` of `X` and `V'` of `Y` containing the chart's two factors, over an open
`W` of `X ×_S Y` contained in the chart and in `pr₁⁻¹U' ⊓ pr₂⁻¹V'`, the base change of `D` carries
the section of `F ⊠ G` attached to `s` and `t` to the section of `F' ⊠ G` attached to `D s` and
`t`. -/
theorem apply_externalTensorSection_boxOp {U' : X.Opens} {V' : Y.Opens} (hU : c.left ≤ U')
    (hV : c.right ≤ V') (s : Γ(F, U')) (t : Γ(G, V')) (W : (pullback a b).Opens)
    (hW : W ≤ c.ι.opensRange) (hW₁ : W ≤ pullback.fst a b ⁻¹ᵁ U')
    (hW₂ : W ≤ pullback.snd a b ⁻¹ᵁ V') :
    (c.boxOp F F' G k D hD).1 (Over.mk (homOfLE hW))
        (externalTensorSection a b F G s t W hW₁ hW₂) =
      externalTensorSection a b F' G (D (op U') s) t W hW₁ hW₂ := by
  let := c.algebraLeft
  let := c.algebraRight
  exact c.apply_externalTensorSection (ofHom_algebraMap_left c) (ofHom_algebraMap_right c)
    F F' G k D hD (c.boxOp F F' G k D hD) (c.boxOp_tmul F F' G k D hD) U' V'
    (top_unique (c.preimage_fromSpecLeft_left.ge.trans (Scheme.Hom.preimage_mono _ hU)))
    (top_unique (c.preimage_fromSpecRight_right.ge.trans (Scheme.Hom.preimage_mono _ hV)))
    s t W hW hW₁ hW₂

end Chart

end Stacks.FibreProductAffineChart

end
