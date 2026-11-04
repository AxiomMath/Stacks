module

public import StacksFrontier.AlgebraicGeometry.FibreProductAffineChart.BoxProductSections
public import StacksFrontier.AlgebraicGeometry.FibreProductAffineChart.CancellationPureTensors

/-!
# Pure tensors of sections of a box product on an affine chart

Let `a : X ⟶ S` and `b : Y ⟶ S`, let `F` and `G` be quasi-coherent modules on `X` and on `Y`, and
let `Spec (A ⊗_R B) ⟶ X ×_S Y` be an affine chart of the fibre product coming from open immersions
`Spec A ⟶ X` and `Spec B ⟶ Y` over `Spec R ⟶ S`. The sections of `F ⊠ G` on the chart are, as a
module over `R`, the tensor product `Γ(Spec A, F) ⊗_R Γ(Spec B, G)`, and this file evaluates that
identification on pure tensors: the section which the chart isomorphism matches with
`(1 ⊗ s) ⊗ (1 ⊗ t)` is the one matched with `s ⊗ t`.

## Main results

* `Stacks.FibreProductAffineChart.chartExternalTensorSectionsBaseIso_hom_inv_one_tmul`: the
  section corresponding to `(1 ⊗ s) ⊗ (1 ⊗ t)` over `A ⊗_R B` corresponds to `s ⊗ t` over `R`.
* `Stacks.FibreProductAffineChart.chartExternalTensorSectionsBaseIso_inv_tmul`: the inverse
  statement, that `s ⊗ t` over `R` is carried to the section corresponding to `(1 ⊗ s) ⊗ (1 ⊗ t)`.

## Implementation notes

Both identifications factor through `Stacks.FibreProductAffineChart.chartExternalTensorSectionsIso`
followed by `Stacks.TensorProductPushout.extendScalarsCancelIso`, and only the second factor moves
a pure tensor; so the rules below are the pure-tensor rules of the cancellation transported along
the first factor, which is left as an isomorphism because no description of the sections of a box
product in terms of sections of `F` and of `G` is available yet.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TensorProduct
open AlgebraicGeometry CommRingCat RingHomClass

namespace Stacks.FibreProductAffineChart

universe u

variable {X Y S : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S)
  (R A B : Type u) [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
  (u : Spec (.of A) ⟶ X) (v : Spec (.of B) ⟶ Y) (w : Spec (.of R) ⟶ S)
  (hu : Spec.map (ofHom (algebraMap R A)) ≫ w = u ≫ a)
  (hv : Spec.map (ofHom (algebraMap R B)) ≫ w = v ≫ b)
  (F : X.Modules) (G : Y.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent]

attribute [local instance] Algebra.TensorProduct.rightAlgebra

open scoped ChangeOfRings in
/-- **Pure tensors of sections of a box product on an affine chart.** The section of `F ⊠ G` on
`Spec (A ⊗_R B)` that the chart isomorphism matches with the pure tensor `(1 ⊗ s) ⊗ (1 ⊗ t)` of
base-changed sections is the one that the isomorphism over the base ring matches with `s ⊗ t`. -/
theorem chartExternalTensorSectionsBaseIso_hom_inv_one_tmul
    (s : moduleSpecΓFunctor.obj ((Scheme.Modules.pullback u).obj F))
    (t : moduleSpecΓFunctor.obj ((Scheme.Modules.pullback v).obj G)) :
    (chartExternalTensorSectionsBaseIso a b R A B u v w hu hv F G).hom
        ((chartExternalTensorSectionsIso a b R A B u v w hu hv F G).inv
          (((1 : A ⊗[R] B) ⊗ₜ[A, algebraMap A (A ⊗[R] B)] s) ⊗ₜ[A ⊗[R] B]
            ((1 : A ⊗[R] B) ⊗ₜ[B, algebraMap B (A ⊗[R] B)] t)))
      = (s ⊗ₜ[R] t :
          ↑(MonoidalCategory.tensorObj
            ((ModuleCat.restrictScalars (algebraMap R A)).obj
              (moduleSpecΓFunctor.obj ((Scheme.Modules.pullback u).obj F)))
            ((ModuleCat.restrictScalars (algebraMap R B)).obj
              (moduleSpecΓFunctor.obj ((Scheme.Modules.pullback v).obj G))))) :=
  (congrArg (fun y => (Stacks.TensorProductPushout.extendScalarsCancelIso R A B
        (moduleSpecΓFunctor.obj ((Scheme.Modules.pullback u).obj F))
        (moduleSpecΓFunctor.obj ((Scheme.Modules.pullback v).obj G))).hom y)
      (Iso.inv_hom_id_apply (chartExternalTensorSectionsIso a b R A B u v w hu hv F G) _)).trans
    (Stacks.TensorProductPushout.extendScalarsCancelIso_hom_one_tmul R A B _ _ s t)

open scoped ChangeOfRings in
/-- The inverse of the identification of the sections of `F ⊠ G` on an affine chart with
`Γ(Spec A, F) ⊗_R Γ(Spec B, G)` carries `s ⊗ t` to the section that the chart isomorphism matches
with `(1 ⊗ s) ⊗ (1 ⊗ t)`. -/
theorem chartExternalTensorSectionsBaseIso_inv_tmul
    (s : moduleSpecΓFunctor.obj ((Scheme.Modules.pullback u).obj F))
    (t : moduleSpecΓFunctor.obj ((Scheme.Modules.pullback v).obj G)) :
    (chartExternalTensorSectionsBaseIso a b R A B u v w hu hv F G).inv
        (s ⊗ₜ[R] t :
          ↑(MonoidalCategory.tensorObj
            ((ModuleCat.restrictScalars (algebraMap R A)).obj
              (moduleSpecΓFunctor.obj ((Scheme.Modules.pullback u).obj F)))
            ((ModuleCat.restrictScalars (algebraMap R B)).obj
              (moduleSpecΓFunctor.obj ((Scheme.Modules.pullback v).obj G)))))
      = (chartExternalTensorSectionsIso a b R A B u v w hu hv F G).inv
          (((1 : A ⊗[R] B) ⊗ₜ[A, algebraMap A (A ⊗[R] B)] s) ⊗ₜ[A ⊗[R] B]
            ((1 : A ⊗[R] B) ⊗ₜ[B, algebraMap B (A ⊗[R] B)] t)) :=
  congrArg (fun y => (chartExternalTensorSectionsIso a b R A B u v w hu hv F G).inv y)
    (Stacks.TensorProductPushout.extendScalarsCancelIso_inv_tmul R A B _ _ s t)

end Stacks.FibreProductAffineChart

end
