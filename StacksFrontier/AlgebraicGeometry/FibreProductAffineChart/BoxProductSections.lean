module

public import StacksFrontier.AlgebraicGeometry.ExternalTensorPullback.Basic
public import StacksFrontier.AlgebraicGeometry.FibreProductAffineChart.Basic
public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentPullbackScheme
public import StacksFrontier.AlgebraicGeometry.PullbackSections.Affine
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.AffineTilde
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.TildeTensorSections
public import StacksFrontier.LinearAlgebra.TensorProduct.BaseChangeCancellation

/-!
# Sections of a box product on an affine chart of a fibre product

Let `a : X ⟶ S` and `b : Y ⟶ S`, let `F` be a quasi-coherent `𝒪_X`-module and `G` a
quasi-coherent `𝒪_Y`-module, and let `F ⊠ G = p^*F ⊗ q^*G` be their external tensor product on
`X ×_S Y`. On an affine chart `Spec (A ⊗_R B) ⟶ X ×_S Y` coming from open immersions
`Spec A ⟶ X`, `Spec B ⟶ Y` over `Spec R ⟶ S`, the module of sections of `F ⊠ G` is the tensor
product over `A ⊗_R B` of the two base changes
`(A ⊗_R B) ⊗_A Γ(Spec A, F|_{Spec A})` and `(A ⊗_R B) ⊗_B Γ(Spec B, G|_{Spec B})`, and hence, as a
module over `R`, the tensor product `Γ(Spec A, F|_{Spec A}) ⊗_R Γ(Spec B, G|_{Spec B})`.

## Main definitions

* `Stacks.FibreProductAffineChart.chartPullbackExternalTensorIso`: the sheaf-level step, that the
  pullback of `F ⊠ G` along the chart is the tensor product on `Spec (A ⊗_R B)` of the two base
  changes of `F|_{Spec A}` and `G|_{Spec B}`.
* `Stacks.FibreProductAffineChart.tensorPullbackSectionsIso`: the sections, on `Spec T`, of a
  tensor product of two pullbacks along `Spec φ` and `Spec ψ`.
* `Stacks.FibreProductAffineChart.chartExternalTensorSectionsIso`: the two combined, which is the
  statement above.
* `Stacks.FibreProductAffineChart.chartExternalTensorSectionsBaseIso`: the same sections, as a
  module over `R`, identified with `Γ(Spec A, F|_{Spec A}) ⊗_R Γ(Spec B, G|_{Spec B})`.

## Main results

* `Stacks.FibreProductAffineChart.lift_affineChart`: an affine chart is the morphism into the
  fibre product induced by its two components, which is what lets the pullback of an external
  tensor product along it be computed.

## Implementation notes

The sheaf-level step is `Stacks.Tag01VSPullbackTensor.pullbackLift_externalTensorProductIso`
(Tag 01CD) at the two components of the chart, whose identifications with `Spec` of the two
algebra maps into `A ⊗_R B` are
`Stacks.FibreProductAffineChart.affineChart_fst` and `affineChart_snd`.

The sections step is `AlgebraicGeometry.TildeTensor.gammaTensorEquiv` (the tensor half of
Tag 01I8 on global sections) followed by `AlgebraicGeometry.quasicoherentPullbackSectionsIso`
(the affine base-change description of the sections of a pullback) in each factor. It is stated
with the ring of the chart as a *bundled* `CommRingCat` variable `T`, and as an isomorphism in
`ModuleCat T` rather than as a `LinearEquiv`. Both are forced: `Module ↑(CommRingCat.of A) Γ(M, U)`
is not found by instance search when `A` is a type variable carrying its own `CommRing` instance,
even though `Module ↑T Γ(M, U)` is found for a `CommRingCat` variable `T`, so a `LinearEquiv`
phrased at `CommRingCat.of (A ⊗[R] B)` cannot be elaborated. An isomorphism of `ModuleCat T`
objects carries no `Module` instance in its type and so is immune.

The last step is the purely algebraic cancellation
`((A ⊗_R B) ⊗_A M) ⊗_{A ⊗_R B} ((A ⊗_R B) ⊗_B N) ≅ M ⊗_R N`, which is
`Stacks.TensorProductPushout.extendScalarsCancelIso`. It is only `R`-linear, so the sections are
restricted to `R` along `R ⟶ A ⊗_R B` before it is applied; both restrictions are
`ModuleCat.restrictScalars`, which agrees with the base changes already in play because
`ModuleCat.extendScalars` and `ModuleCat.restrictScalars` both take the module structure over the
source ring through `Module.compHom`.

## References

* [Stacks Project, Tag 01I8](https://stacks.math.columbia.edu/tag/01I8)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 0G46](https://stacks.math.columbia.edu/tag/0G46)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TensorProduct
open AlgebraicGeometry CommRingCat RingHomClass
open Stacks.Tag01VSPullbackTensor

namespace Stacks.FibreProductAffineChart

universe u

variable {X Y S : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S)
  (R A B : Type u) [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
  (u : Spec (.of A) ⟶ X) (v : Spec (.of B) ⟶ Y) (w : Spec (.of R) ⟶ S)
  (hu : Spec.map (ofHom (algebraMap R A)) ≫ w = u ≫ a)
  (hv : Spec.map (ofHom (algebraMap R B)) ≫ w = v ≫ b)

/-- The algebra map `A ⟶ A ⊗_R B`. -/
abbrev chartInclLeft : CommRingCat.of A ⟶ CommRingCat.of (A ⊗[R] B) :=
  ofHom (algebraMap A (A ⊗[R] B))

/-- The algebra map `B ⟶ A ⊗_R B`. -/
abbrev chartInclRight : CommRingCat.of B ⟶ CommRingCat.of (A ⊗[R] B) :=
  ofHom (R := B) (S := A ⊗[R] B) (toRingHom Algebra.TensorProduct.includeRight)

/-- The two components of an affine chart agree over the base. -/
theorem affineChart_comp_comm :
    (affineChart a b R A B u v w hu hv ≫ pullback.fst a b) ≫ a =
      (affineChart a b R A B u v w hu hv ≫ pullback.snd a b) ≫ b := by
  rw [Category.assoc, Category.assoc, pullback.condition]

/-- An affine chart is the morphism into the fibre product induced by its two components. -/
theorem lift_affineChart :
    pullback.lift (affineChart a b R A B u v w hu hv ≫ pullback.fst a b)
      (affineChart a b R A B u v w hu hv ≫ pullback.snd a b)
      (affineChart_comp_comm a b R A B u v w hu hv) = affineChart a b R A B u v w hu hv :=
  pullback.hom_ext (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)

variable (F : X.Modules) (G : Y.Modules)

/-- The pullback of a box product along an affine chart is the tensor product, on
`Spec (A ⊗_R B)`, of the base changes along `A ⟶ A ⊗_R B` and `B ⟶ A ⊗_R B` of the pullbacks of
`F` to `Spec A` and of `G` to `Spec B`. -/
def chartPullbackExternalTensorIso :
    (Scheme.Modules.pullback (affineChart a b R A B u v w hu hv)).obj
        (externalTensorProduct a b F G) ≅
      (((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨(((Spec (CommRingCat.of (A ⊗[R] B))).toRingedSpace)).presheaf,
            (((Spec (CommRingCat.of (A ⊗[R] B))).toRingedSpace)).IsSheaf⟩).obj
          (((Scheme.Modules.pullback (Spec.map (chartInclLeft R A B))).obj
            ((Scheme.Modules.pullback u).obj F)))).obj
        (((Scheme.Modules.pullback (Spec.map (chartInclRight R A B))).obj
          ((Scheme.Modules.pullback v).obj G)))) :=
  (Scheme.Modules.pullbackCongr (lift_affineChart a b R A B u v w hu hv).symm).app _ ≪≫
    pullbackLift_externalTensorProductIso a b _ _ _ F G ≪≫
    tensorSheafMapIso
      (pullbackCompCongrIso _ u (affineChart_fst a b R A B u v w hu hv).symm F).symm
      (pullbackCompCongrIso _ v (affineChart_snd a b R A B u v w hu hv).symm G).symm

/-! ### Sections of a tensor product of two pullbacks on an affine scheme -/

section Aux

variable {A' B' T : CommRingCat.{u}} (φ : A' ⟶ T) (ψ : B' ⟶ T)
  (P : (Spec A').Modules) (Q : (Spec B').Modules) [P.IsQuasicoherent] [Q.IsQuasicoherent]

/-- The global sections on `Spec T` of the tensor product of the pullbacks of two quasi-coherent
modules along `Spec φ : Spec T ⟶ Spec A'` and `Spec ψ : Spec T ⟶ Spec B'`: the tensor product
over `T` of the two base-changed modules of sections. -/
def tensorPullbackSectionsIso :
    moduleSpecΓFunctor.obj (TildeTensor.modTensor
        ((Scheme.Modules.pullback (Spec.map φ)).obj P)
        ((Scheme.Modules.pullback (Spec.map ψ)).obj Q)) ≅
      MonoidalCategory.tensorObj
        ((ModuleCat.extendScalars φ.hom).obj (moduleSpecΓFunctor.obj P))
        ((ModuleCat.extendScalars ψ.hom).obj (moduleSpecΓFunctor.obj Q)) :=
  (TildeTensor.gammaTensorEquiv _ _).symm.toModuleIso ≪≫
    MonoidalCategory.tensorIso (quasicoherentPullbackSectionsIso A' T φ P).symm
      (quasicoherentPullbackSectionsIso B' T ψ Q).symm

end Aux

/-! ### Sections of a box product on an affine chart -/

/-- **Sections of a box product on an affine chart of a fibre product.** For quasi-coherent `F`
on `X` and `G` on `Y`, the module of sections of `F ⊠ G` on the affine chart
`Spec (A ⊗_R B) ⟶ X ×_S Y` is the tensor product over `A ⊗_R B` of the base changes of the module
of sections of `F` on `Spec A` and of the module of sections of `G` on `Spec B`. -/
def chartExternalTensorSectionsIso [F.IsQuasicoherent] [G.IsQuasicoherent] :
    moduleSpecΓFunctor.obj ((Scheme.Modules.pullback (affineChart a b R A B u v w hu hv)).obj
        (externalTensorProduct a b F G)) ≅
      MonoidalCategory.tensorObj
        ((ModuleCat.extendScalars (chartInclLeft R A B).hom).obj
          (moduleSpecΓFunctor.obj ((Scheme.Modules.pullback u).obj F)))
        ((ModuleCat.extendScalars (chartInclRight R A B).hom).obj
          (moduleSpecΓFunctor.obj ((Scheme.Modules.pullback v).obj G))) :=
  moduleSpecΓFunctor.mapIso (chartPullbackExternalTensorIso a b R A B u v w hu hv F G) ≪≫
    tensorPullbackSectionsIso (chartInclLeft R A B) (chartInclRight R A B)
      ((Scheme.Modules.pullback u).obj F) ((Scheme.Modules.pullback v).obj G)

/-- **Sections of a box product on an affine chart, over the base ring.** For quasi-coherent `F`
on `X` and `G` on `Y`, the module of sections of `F ⊠ G` on the affine chart
`Spec (A ⊗_R B) ⟶ X ×_S Y` is, as a module over `R`, the tensor product over `R` of the module of
sections of `F` on `Spec A` and of the module of sections of `G` on `Spec B`. -/
def chartExternalTensorSectionsBaseIso [F.IsQuasicoherent] [G.IsQuasicoherent] :
    (ModuleCat.restrictScalars (algebraMap R (A ⊗[R] B))).obj
        (moduleSpecΓFunctor.obj ((Scheme.Modules.pullback (affineChart a b R A B u v w hu hv)).obj
          (externalTensorProduct a b F G))) ≅
      MonoidalCategory.tensorObj
        ((ModuleCat.restrictScalars (algebraMap R A)).obj
          (moduleSpecΓFunctor.obj ((Scheme.Modules.pullback u).obj F)))
        ((ModuleCat.restrictScalars (algebraMap R B)).obj
          (moduleSpecΓFunctor.obj ((Scheme.Modules.pullback v).obj G))) :=
  (ModuleCat.restrictScalars (algebraMap R (A ⊗[R] B))).mapIso
      (chartExternalTensorSectionsIso a b R A B u v w hu hv F G) ≪≫
    Stacks.TensorProductPushout.extendScalarsCancelIso R A B _ _

end Stacks.FibreProductAffineChart

end
