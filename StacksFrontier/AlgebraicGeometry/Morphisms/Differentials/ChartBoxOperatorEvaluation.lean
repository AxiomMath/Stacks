module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.ChartBoxProductOperator

/-!
# Evaluating the chart identification of differential operators on the sections of a chart

Let `a : X ⟶ S` and `b : Y ⟶ S` be morphisms of schemes and let `c` be an affine chart of the
fibre product `X ×_S Y`, with `R = Γ(S, W)`, `A = Γ(X, U)`, `B = Γ(Y, V)`.
`Stacks.FibreProductAffineChart.Chart.boxDiffOpEquiv` identifies the differential operators of
order at most `k` on `X ×_S Y / Y` defined over the opens of the chart with the differential
operators of order at most `k` relative to `B ⟶ A ⊗_R B` on the sections of the inverse images on
the chart. This file records what that identification *is*: the linear map attached to an
operator is the operator's own action on the sections over the chart, read through the comparison
of the restriction along the chart with the inverse image along it.

## Main results

* `Stacks.FibreProductAffineChart.Chart.boxDiffOpEquiv_apply_coe_apply`: the linear map attached
  to a differential operator on a chart is the operator's action at the image of the chart,
  conjugated by `AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback`.

## References

* [Stacks Project, Tag 0G44](https://stacks.math.columbia.edu/tag/0G44)
* [Stacks Project, Tag 0G45](https://stacks.math.columbia.edu/tag/0G45)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct TopologicalSpace
open CommRingCat

universe u

attribute [local instance] Stacks.AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback

namespace Stacks.FibreProductAffineChart

open _root_.AlgebraicGeometry RingHomClass

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

variable [Algebra Γ(S, c.base) Γ(X, c.left)] [Algebra Γ(S, c.base) Γ(Y, c.right)]
  (hl : ofHom (algebraMap Γ(S, c.base) Γ(X, c.left)) = c.leftHom)
  (hr : ofHom (algebraMap Γ(S, c.base) Γ(Y, c.right)) = c.rightHom)

/-- The operator on the sections over a chart attached to a differential operator on
`X ×_S Y / Y` is the operator's action on those sections, read through the comparison of the
restriction along the chart with the inverse image along it. -/
theorem boxDiffOpEquiv_apply_coe_apply (M M' : (pullback a b).Modules) [M.IsQuasicoherent]
    (k : ℕ)
    (D : {D : DiffOp.RawOp M M' c.ι.opensRange //
      DiffOp.IsDiffOpOfOrder (pullback.snd a b).relativeStructureSheafMap k D})
    (x : Γ((Scheme.Modules.pullback ((c.specIso hl hr).inv ≫ c.ι)).obj M, ⊤))
    (hV : ((c.specIso hl hr).inv ≫ c.ι) ''ᵁ ⊤ ≤ c.ι.opensRange) :
    (c.boxDiffOpEquiv hl hr M M' k D).1 x =
      Scheme.Modules.Hom.app
        ((Scheme.Modules.restrictFunctorIsoPullback
          ((c.specIso hl hr).inv ≫ c.ι)).app M').hom ⊤
        (D.1 (Over.mk (homOfLE hV))
          (Scheme.Modules.Hom.app
            ((Scheme.Modules.restrictFunctorIsoPullback
              ((c.specIso hl hr).inv ≫ c.ι)).app M).inv ⊤ x)) :=
  ((AffineDiffOp.globalDiffOpEquiv (R := Γ(Y, c.right))
      ((Scheme.Modules.pullback ((c.specIso hl hr).inv ≫ c.ι)).obj M)
      ((Scheme.Modules.pullback ((c.specIso hl hr).inv ≫ c.ι)).obj M') k).2
    (Equiv.subtypeEquivRight (c.boxOrder_iff hl hr M M' k)
      (diffOpEquivGlobalDiffOpPullback ((c.specIso hl hr).inv ≫ c.ι) (pullback.snd a b)
        M M' k
        (Equiv.subtypeEquiv
          (DiffOp.RawOp.congrBase
            (Scheme.Hom.opensRange_comp_of_isIso (c.specIso hl hr).inv c.ι).symm)
          (fun D ↦ (DiffOp.RawOp.isDiffOpOfOrder_congrBase _ k _ D).symm) D))) x).trans
    ((diffOpEquivGlobalDiffOpPullback_coe_apply ((c.specIso hl hr).inv ≫ c.ι)
        (pullback.snd a b) M M' k _ ⊤ x).trans
      (congrArg
        (fun T : Γ(M, ((c.specIso hl hr).inv ≫ c.ι) ''ᵁ ⊤) →+
            Γ(M', ((c.specIso hl hr).inv ≫ c.ι) ''ᵁ ⊤) ↦
          Scheme.Modules.Hom.app
            ((Scheme.Modules.restrictFunctorIsoPullback
              ((c.specIso hl hr).inv ≫ c.ι)).app M').hom ⊤
            (T (Scheme.Modules.Hom.app
              ((Scheme.Modules.restrictFunctorIsoPullback
                ((c.specIso hl hr).inv ≫ c.ι)).app M).inv ⊤ x)))
        (DiffOp.RawOp.congrBase_apply
          (Scheme.Hom.opensRange_comp_of_isIso (c.specIso hl hr).inv c.ι).symm D.1
          (imageOver ((c.specIso hl hr).inv ≫ c.ι) ⊤) hV)))

end Chart

end Stacks.FibreProductAffineChart

end
