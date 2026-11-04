module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.ChartBoxOperatorEvaluation

/-!
# Evaluating the tensor-product form of the chart identification of differential operators

Let `a : X ⟶ S` and `b : Y ⟶ S` be morphisms of schemes and let `c` be an affine chart of the
fibre product `X ×_S Y`, with `R = Γ(S, W)`, `A = Γ(X, U)`, `B = Γ(Y, V)`.
`Stacks.FibreProductAffineChart.Chart.boxDiffOpTensorEquiv` identifies the differential operators
of order at most `k` on `X ×_S Y / Y` over the opens of the chart with the differential operators
of order at most `k` relative to `B ⟶ A ⊗_R B` on `Γ(Spec A, F) ⊗_R Γ(Spec B, G)`. The operator
it attaches to `E` is the operator `Stacks.FibreProductAffineChart.Chart.boxDiffOpEquiv` attaches
to `E`, conjugated by the identification of the sections of `F ⊠ G` on the chart with that tensor
product.

## Main results

* `Stacks.DifferentialOperator.orderEquivConj_coe`: the operator attached to `D` by the bijection
  of operators induced by two linear equivalences is `D` conjugated by them.
* `Stacks.DifferentialOperator.conj_eq_comp`: that conjugate as a composite of three linear maps
  over the ring of scalars of the order predicate.
* `Stacks.FibreProductAffineChart.Chart.boxDiffOpTensorEquiv_coe` and
  `Stacks.FibreProductAffineChart.Chart.boxDiffOpTensorEquiv_coe_apply`: the operator on
  `Γ(Spec A, F) ⊗_R Γ(Spec B, G)` attached to a differential operator on a chart, as the operator
  on the sections of the chart conjugated by
  `Stacks.FibreProductAffineChart.Chart.boxSectionsEquiv`, and the same read on an element.

## References

* [Stacks Project, Tag 0G44](https://stacks.math.columbia.edu/tag/0G44)
* [Stacks Project, Tag 0G45](https://stacks.math.columbia.edu/tag/0G45)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct TopologicalSpace
open CommRingCat

universe u

namespace Stacks.DifferentialOperator

variable {R S M M' N N' : Type*} [CommSemiring R] [Semiring S] [Algebra R S]
  [AddCommMonoid M] [Module R M] [Module S M] [IsScalarTower R S M]
  [AddCommGroup M'] [Module R M'] [Module S M'] [IsScalarTower R S M']
  [AddCommMonoid N] [Module R N] [Module S N] [IsScalarTower R S N]
  [AddCommGroup N'] [Module R N'] [Module S N'] [IsScalarTower R S N']

/-- The differential operator attached to `D` by the bijection of operators of order at most `k`
induced by two linear equivalences is `D` conjugated by them. -/
theorem orderEquivConj_coe (e : M ≃ₗ[S] N) (e' : M' ≃ₗ[S] N') (k : ℕ)
    (D : {D : M →ₗ[R] M' // D.IsDifferentialOperatorOfOrderLE S k}) :
    ((orderEquivConj e e' k D).1 : N →ₗ[R] N') = conj e e' D.1 := rfl

/-- The conjugate of an operator by two linear equivalences, as a composite of three linear maps
over the ring of scalars of the order predicate. -/
theorem conj_eq_comp (e : M ≃ₗ[S] N) (e' : M' ≃ₗ[S] N') (D : M →ₗ[R] M') :
    conj e e' D = e'.toLinearMap.restrictScalars R ∘ₗ
      (D ∘ₗ e.symm.toLinearMap.restrictScalars R) := rfl

/-- The restriction of scalars of a linear equivalence acts as the equivalence. -/
theorem restrictScalars_toLinearMap_apply (e : M ≃ₗ[S] N) (m : M) :
    e.toLinearMap.restrictScalars R m = e m :=
  (LinearMap.restrictScalars_apply R e.toLinearMap m).trans
    (congrFun (LinearEquiv.coe_coe e) m)

end Stacks.DifferentialOperator

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
  (F : X.Modules) (G : Y.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent]
  (F' : X.Modules) [F'.IsQuasicoherent] (k : ℕ)

/-- `Stacks.FibreProductAffineChart.Chart.boxDiffOpTensorEquiv` is the chart identification of
differential operators followed by conjugation along the identification of the sections of a box
product on the chart. -/
theorem boxDiffOpTensorEquiv_eq :
    c.boxDiffOpTensorEquiv hl hr F G F' k =
      (c.boxDiffOpEquiv hl hr (externalTensorProduct a b F G)
          (externalTensorProduct a b F' G) k).trans
        (Stacks.DifferentialOperator.orderEquivConj (c.boxSectionsEquiv hl hr F G)
          (c.boxSectionsEquiv hl hr F' G) k) := rfl

variable (E : {E : DiffOp.RawOp (externalTensorProduct a b F G)
    (externalTensorProduct a b F' G) c.ι.opensRange //
  DiffOp.IsDiffOpOfOrder (pullback.snd a b).relativeStructureSheafMap k E})

/-- The operator on `Γ(Spec A, F) ⊗_R Γ(Spec B, G)` attached to a differential operator on a
chart is the operator on the sections of `F ⊠ G` over the chart attached to the same differential
operator, conjugated by the identification of those sections with the tensor product. -/
theorem boxDiffOpTensorEquiv_coe :
    (c.boxDiffOpTensorEquiv hl hr F G F' k E).1 =
      Stacks.DifferentialOperator.conj (c.boxSectionsEquiv hl hr F G)
        (c.boxSectionsEquiv hl hr F' G)
        (c.boxDiffOpEquiv hl hr (externalTensorProduct a b F G)
          (externalTensorProduct a b F' G) k E).1 :=
  (congrArg (fun q ↦ (q E).1) (c.boxDiffOpTensorEquiv_eq hl hr F G F' k)).trans
    ((congrArg Subtype.val (Equiv.trans_apply
        (c.boxDiffOpEquiv hl hr (externalTensorProduct a b F G)
          (externalTensorProduct a b F' G) k)
        (Stacks.DifferentialOperator.orderEquivConj (c.boxSectionsEquiv hl hr F G)
          (c.boxSectionsEquiv hl hr F' G) k) E)).trans
      (Stacks.DifferentialOperator.orderEquivConj_coe (c.boxSectionsEquiv hl hr F G)
        (c.boxSectionsEquiv hl hr F' G) k _))

/-- The operator on `Γ(Spec A, F) ⊗_R Γ(Spec B, G)` attached to a differential operator on a
chart, written as a composite of three linear maps over `B`. -/
theorem boxDiffOpTensorEquiv_coe_comp :
    (c.boxDiffOpTensorEquiv hl hr F G F' k E).1 =
      (c.boxSectionsEquiv hl hr F' G).toLinearMap.restrictScalars Γ(Y, c.right) ∘ₗ
        ((c.boxDiffOpEquiv hl hr (externalTensorProduct a b F G)
            (externalTensorProduct a b F' G) k E).1 ∘ₗ
          (c.boxSectionsEquiv hl hr F G).symm.toLinearMap.restrictScalars Γ(Y, c.right)) :=
  (c.boxDiffOpTensorEquiv_coe hl hr F G F' k E).trans
    (Stacks.DifferentialOperator.conj_eq_comp (c.boxSectionsEquiv hl hr F G)
      (c.boxSectionsEquiv hl hr F' G)
      (c.boxDiffOpEquiv hl hr (externalTensorProduct a b F G)
        (externalTensorProduct a b F' G) k E).1)

/-- The operator on `Γ(Spec A, F) ⊗_R Γ(Spec B, G)` attached to a differential operator on a
chart, evaluated at `z`, is the operator on the sections of `F ⊠ G` over the chart evaluated at the
section corresponding to `z`, carried back to the tensor product. -/
theorem boxDiffOpTensorEquiv_coe_apply
    (z : Γ((Scheme.Modules.pullback c.fromSpecLeft).obj F, ⊤) ⊗[Γ(S, c.base)]
      Γ((Scheme.Modules.pullback c.fromSpecRight).obj G, ⊤)) :
    (c.boxDiffOpTensorEquiv hl hr F G F' k E).1 z =
      c.boxSectionsEquiv hl hr F' G
        ((c.boxDiffOpEquiv hl hr (externalTensorProduct a b F G)
          (externalTensorProduct a b F' G) k E).1
          ((c.boxSectionsEquiv hl hr F G).symm z)) :=
  (LinearMap.congr_fun (c.boxDiffOpTensorEquiv_coe_comp hl hr F G F' k E) z).trans
    ((LinearMap.comp_apply
        ((c.boxSectionsEquiv hl hr F' G).toLinearMap.restrictScalars Γ(Y, c.right))
        ((c.boxDiffOpEquiv hl hr (externalTensorProduct a b F G)
            (externalTensorProduct a b F' G) k E).1 ∘ₗ
          (c.boxSectionsEquiv hl hr F G).symm.toLinearMap.restrictScalars Γ(Y, c.right))
        z).trans
      ((Stacks.DifferentialOperator.restrictScalars_toLinearMap_apply
          (R := Γ(Y, c.right)) (c.boxSectionsEquiv hl hr F' G) _).trans
        (congrArg (fun y ↦ c.boxSectionsEquiv hl hr F' G y)
          ((LinearMap.comp_apply
              (c.boxDiffOpEquiv hl hr (externalTensorProduct a b F G)
                (externalTensorProduct a b F' G) k E).1
              ((c.boxSectionsEquiv hl hr F G).symm.toLinearMap.restrictScalars
                Γ(Y, c.right)) z).trans
            (congrArg
              (fun y ↦ (c.boxDiffOpEquiv hl hr (externalTensorProduct a b F G)
                (externalTensorProduct a b F' G) k E).1 y)
              (Stacks.DifferentialOperator.restrictScalars_toLinearMap_apply
                (R := Γ(Y, c.right)) (c.boxSectionsEquiv hl hr F G).symm z))))))

end Chart

end Stacks.FibreProductAffineChart

end
