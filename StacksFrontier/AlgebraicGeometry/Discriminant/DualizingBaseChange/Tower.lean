module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Different.DualizingModulesQuasi.BaseChange

/-!
# Base change of a relative dualizing module along a tower

Let `A → A₁ → A₂` be a tower of rings and `A → B` a quasi-finite map with a chosen finite-open
factorization. Extending scalars first to `A₁` and then to `A₂` produces the relative dualizing
module of `A₂ ⊗[A₁] (A₁ ⊗[A] B)`, while extending scalars directly to `A₂` produces that of
`A₂ ⊗[A] B`. The two are identified by the cancellation isomorphism of iterated tensor
products, and under that identification the two base change maps out of the original dualizing
module agree.

## Main definitions

* `Stacks.Discriminant.dualizingModule.baseChangeTowerEquiv` is the identification of the
  iterated scalar extension of a relative dualizing module with the direct one, packaged
  together with its formula on pure tensors.

## Main results

* `Stacks.Discriminant.dualizingModule.baseChange_comp`: the composite of the two base change
  maps of a tower is the direct base change map.

## Implementation notes

The identification is built as a tensor product of two semilinear equivalences over the
cancellation isomorphism of intermediate algebras: one on the dual factor and one on the
coefficient ring. Scalar compatibility of the second is checked by induction on tensors, since
the cancellation isomorphism is only an algebra map after unfolding.

## References

* [Stacks Project, Tag 0BVC](https://stacks.math.columbia.edu/tag/0BVC)
-/

@[expose] public section

open scoped TensorProduct

universe u v w x y

namespace Stacks.Discriminant

namespace dualizingModule

attribute [local instance] algebraDualModule

/-- The canonical additive identification of the relative dualizing module of an iterated
scalar extension with that of the direct one. It is characterized by its effect on pure
tensors, and the underlying identification of intermediate algebras is the cancellation
isomorphism `A₂ ⊗[A₁] (A₁ ⊗[A] B') ≃ₐ[A₂] A₂ ⊗[A] B'`. -/
noncomputable def baseChangeTowerEquiv
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    (F : FiniteOpenFactorization.{u, v, w} A B)
    (A₁ : Type x) [CommRing A₁] [Algebra A A₁]
    (A₂ : Type y) [CommRing A₂] [Algebra A A₂] [Algebra A₁ A₂]
    [IsScalarTower A A₁ A₂] :
    {e : dualizingModule
          (FiniteOpenFactorization.baseChange
            (FiniteOpenFactorization.baseChange F A₁) A₂) ≃+
        dualizingModule
          (FiniteOpenFactorization.baseChange F A₂) //
      ∀ (f : Module.Dual A₂
            (FiniteOpenFactorization.baseChange
              (FiniteOpenFactorization.baseChange F A₁) A₂).middle)
          (b : A₂ ⊗[A₁] (A₁ ⊗[A] B)),
        e (dualizingModule.tmul
            (FiniteOpenFactorization.baseChange
              (FiniteOpenFactorization.baseChange F A₁) A₂)
            f b) =
          dualizingModule.tmul
            (FiniteOpenFactorization.baseChange F A₂)
            (f.comp (Algebra.TensorProduct.cancelBaseChange
              A A₁ A₂ A₂ F.middle).symm.toLinearMap)
            (Algebra.TensorProduct.cancelBaseChange A A₁ A₂ A₂ B b)} := by
  let cM := Algebra.TensorProduct.cancelBaseChange A A₁ A₂ A₂ F.middle
  let cB := Algebra.TensorProduct.cancelBaseChange A A₁ A₂ A₂ B
  let Fiter := FiniteOpenFactorization.baseChange
      (FiniteOpenFactorization.baseChange F A₁) A₂
  let Fdirect := FiniteOpenFactorization.baseChange F A₂
  let F₁ := FiniteOpenFactorization.baseChange F A₁
  letI : CommRing F₁.middle := F₁.commRingMiddle
  letI : Algebra A₁ F₁.middle := F₁.algebraMiddle
  letI : Algebra F₁.middle (A₁ ⊗[A] B) := F₁.algebraTarget
  letI : IsScalarTower A₁ F₁.middle (A₁ ⊗[A] B) := F₁.scalarTower
  let cM' : Fiter.middle ≃ₐ[A₂] Fdirect.middle := cM
  letI : CommRing (A₂ ⊗[A₁] (A₁ ⊗[A] F.middle)) := Fiter.commRingMiddle
  letI : Algebra A₂ (A₂ ⊗[A₁] (A₁ ⊗[A] F.middle)) := Fiter.algebraMiddle
  letI : Algebra (A₂ ⊗[A₁] (A₁ ⊗[A] F.middle))
      (A₂ ⊗[A₁] (A₁ ⊗[A] B)) := Fiter.algebraTarget
  letI : IsScalarTower A₂ (A₂ ⊗[A₁] (A₁ ⊗[A] F.middle))
      (A₂ ⊗[A₁] (A₁ ⊗[A] B)) := Fiter.scalarTower
  letI : CommRing (A₂ ⊗[A] F.middle) := Fdirect.commRingMiddle
  letI : Algebra A₂ (A₂ ⊗[A] F.middle) := Fdirect.algebraMiddle
  letI : Algebra (A₂ ⊗[A] F.middle) (A₂ ⊗[A] B) := Fdirect.algebraTarget
  letI : IsScalarTower A₂ (A₂ ⊗[A] F.middle) (A₂ ⊗[A] B) := Fdirect.scalarTower
  letI : RingHomInvPair cM'.toRingHom cM'.symm.toRingHom := by
    constructor <;> ext x <;> simp
  letI : RingHomInvPair cM'.symm.toRingHom cM'.toRingHom := by
    constructor <;> ext x <;> simp
  letI : Module Fiter.middle (Module.Dual A₂ Fiter.middle) :=
    algebraDualModule A₂ Fiter.middle
  letI : Module Fdirect.middle (Module.Dual A₂ Fdirect.middle) :=
    algebraDualModule A₂ Fdirect.middle
  letI : Algebra B (A₁ ⊗[A] B) := Algebra.TensorProduct.rightAlgebra
  letI : Module B (dualizingModule
      (FiniteOpenFactorization.baseChange F A₁)) :=
    Module.compHom _ (algebraMap B (A₁ ⊗[A] B))
  letI : Algebra (A₁ ⊗[A] B) (A₂ ⊗[A₁] (A₁ ⊗[A] B)) :=
    Algebra.TensorProduct.rightAlgebra
  letI : Module (A₁ ⊗[A] B) (dualizingModule
      (FiniteOpenFactorization.baseChange
        (FiniteOpenFactorization.baseChange F A₁) A₂)) :=
    Module.compHom _ (algebraMap (A₁ ⊗[A] B) (A₂ ⊗[A₁] (A₁ ⊗[A] B)))
  letI : Algebra B (A₂ ⊗[A] B) := Algebra.TensorProduct.rightAlgebra
  letI : Module B (dualizingModule
      (FiniteOpenFactorization.baseChange F A₂)) :=
    Module.compHom _ (algebraMap B (A₂ ⊗[A] B))
  let eDual : Module.Dual A₂
      Fiter.middle
      ≃ₛₗ[cM'.toRingHom]
      Module.Dual A₂ Fdirect.middle := {
    toFun := fun f => f.comp cM'.symm.toLinearMap
    invFun := fun f => f.comp cM'.toLinearMap
    left_inv := by intro f; ext x; simp
    right_inv := by intro f; ext x; simp
    map_add' := by intro f g; ext x; rfl
    map_smul' := by
      intro r f
      ext x
      simp [algebraDualModule_smul_apply] }
  let eCoeff :
      (A₂ ⊗[A₁] (A₁ ⊗[A] B)) ≃ₛₗ[cM'.toRingHom]
        (A₂ ⊗[A] B) := {
    toFun := cB
    invFun := cB.symm
    left_inv := cB.left_inv
    right_inv := cB.right_inv
    map_add' := cB.map_add
    map_smul' := by
      intro r b
      change cB (algebraMap _ _ r * b) = algebraMap _ _ (cM' r) * cB b
      have hscalarRaw (r : A₂ ⊗[A₁] (A₁ ⊗[A] F.middle)) :
          cB (algebraMap _ _ r) = algebraMap _ _ (cM r) := by
        induction r using TensorProduct.induction_on with
        | zero =>
          simp
        | tmul a₂ z =>
          induction z using TensorProduct.induction_on with
          | zero =>
            simp
          | tmul a₁ m =>
            have hinner :
                IsScalarTower.toAlgHom A₁ F₁.middle (A₁ ⊗[A] B)
                    (a₁ ⊗ₜ[A] m) = a₁ ⊗ₜ[A] algebraMap F.middle B m := by
              change (Algebra.TensorProduct.map (AlgHom.id A A₁)
                  (IsScalarTower.toAlgHom A F.middle B)) (a₁ ⊗ₜ[A] m) = _
              simp [Algebra.TensorProduct.map_tmul]
            change cB
                ((Algebra.TensorProduct.map (AlgHom.id A₁ A₂)
                    (IsScalarTower.toAlgHom A₁ F₁.middle (A₁ ⊗[A] B)))
                  (a₂ ⊗ₜ[A₁] (a₁ ⊗ₜ[A] m))) =
              (Algebra.TensorProduct.map (AlgHom.id A A₂)
                  (IsScalarTower.toAlgHom A F.middle B))
                (cM (a₂ ⊗ₜ[A₁] (a₁ ⊗ₜ[A] m)))
            have hmap := Algebra.TensorProduct.map_tmul (AlgHom.id A₁ A₂)
              (IsScalarTower.toAlgHom A₁ F₁.middle (A₁ ⊗[A] B)) a₂
              (a₁ ⊗ₜ[A] m)
            rw [hmap, AlgHom.id_apply, hinner]
            simp [cB, cM, Algebra.TensorProduct.map_tmul,
              Algebra.TensorProduct.cancelBaseChange_tmul]
          | add z₁ z₂ hz₁ hz₂ =>
            rw [TensorProduct.tmul_add]
            simp only [map_add, hz₁, hz₂]
        | add r₁ r₂ hr₁ hr₂ =>
          simp only [map_add, hr₁, hr₂]
      have hscalar (r : Fiter.middle) :
          cB (algebraMap _ _ r) = algebraMap _ _ (cM' r) :=
        hscalarRaw r
      rw [map_mul, hscalar]
  }
  let e := TensorProduct.congr eDual eCoeff
  refine ⟨e.toAddEquiv, ?_⟩
  intro f b
  change TensorProduct.congr eDual eCoeff
      (f ⊗ₜ[Fiter.middle] b) = _
  exact TensorProduct.congr_tmul eDual eCoeff f b

/-- Successive base change maps agree with direct base change after the
canonical identification of the iterated tensor product with the direct one. -/
@[stacks 0BVC "composition of base changes"]
theorem baseChange_comp
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    (F : FiniteOpenFactorization.{u, v, w} A B)
    (A₁ : Type x) [CommRing A₁] [Algebra A A₁]
    (A₂ : Type y) [CommRing A₂] [Algebra A A₂] [Algebra A₁ A₂]
    [IsScalarTower A A₁ A₂]
    (ω : dualizingModule F) :
    (baseChangeTowerEquiv F A₁ A₂).1
        (dualizingModule.baseChange
          (FiniteOpenFactorization.baseChange F A₁) A₂
          (dualizingModule.baseChange F A₁ ω)) =
      dualizingModule.baseChange F A₂ ω := by
  -- The compatibility follows on pure tensors from the defining formula for
  -- base change and the tensor cancellation equivalence.
  let : Module F.middle (Module.Dual A F.middle) := algebraDualModule A F.middle
  dsimp [dualizingModule] at ω
  let F₁ := FiniteOpenFactorization.baseChange F A₁
  let Fiter := FiniteOpenFactorization.baseChange F₁ A₂
  let Fdirect := FiniteOpenFactorization.baseChange F A₂
  let : CommRing F₁.middle := F₁.commRingMiddle
  let : Algebra A₁ F₁.middle := F₁.algebraMiddle
  let : Algebra F₁.middle (A₁ ⊗[A] B) := F₁.algebraTarget
  let : IsScalarTower A₁ F₁.middle (A₁ ⊗[A] B) := F₁.scalarTower
  let : CommRing Fiter.middle := Fiter.commRingMiddle
  let : Algebra A₂ Fiter.middle := Fiter.algebraMiddle
  let : Algebra Fiter.middle (A₂ ⊗[A₁] (A₁ ⊗[A] B)) := Fiter.algebraTarget
  let : IsScalarTower A₂ Fiter.middle (A₂ ⊗[A₁] (A₁ ⊗[A] B)) := Fiter.scalarTower
  let : CommRing Fdirect.middle := Fdirect.commRingMiddle
  let : Algebra A₂ Fdirect.middle := Fdirect.algebraMiddle
  let : Algebra Fdirect.middle (A₂ ⊗[A] B) := Fdirect.algebraTarget
  let : IsScalarTower A₂ Fdirect.middle (A₂ ⊗[A] B) := Fdirect.scalarTower
  let : Module F₁.middle (Module.Dual A₁ F₁.middle) :=
    algebraDualModule A₁ F₁.middle
  let : Module Fiter.middle (Module.Dual A₂ Fiter.middle) :=
    algebraDualModule A₂ Fiter.middle
  let : Module Fdirect.middle (Module.Dual A₂ Fdirect.middle) :=
    algebraDualModule A₂ Fdirect.middle
  let : Algebra B (A₁ ⊗[A] B) := Algebra.TensorProduct.rightAlgebra
  let : Module B (dualizingModule F₁) :=
    Module.compHom _ (algebraMap B (A₁ ⊗[A] B))
  let : Algebra (A₁ ⊗[A] B) (A₂ ⊗[A₁] (A₁ ⊗[A] B)) :=
    Algebra.TensorProduct.rightAlgebra
  let : Module (A₁ ⊗[A] B) (dualizingModule Fiter) :=
    Module.compHom _ (algebraMap (A₁ ⊗[A] B) (A₂ ⊗[A₁] (A₁ ⊗[A] B)))
  let : Algebra B (A₂ ⊗[A] B) := Algebra.TensorProduct.rightAlgebra
  let : Module B (dualizingModule Fdirect) :=
    Module.compHom _ (algebraMap B (A₂ ⊗[A] B))
  induction ω using TensorProduct.induction_on with
  | zero =>
    show (baseChangeTowerEquiv F A₁ A₂).1
      (dualizingModule.baseChange
        (FiniteOpenFactorization.baseChange F A₁) A₂
          (dualizingModule.baseChange F A₁ (0 : dualizingModule F))) =
      dualizingModule.baseChange F A₂ (0 : dualizingModule F)
    rw [map_zero, map_zero, map_zero]
    exact (map_zero (dualizingModule.baseChange F A₂)).symm
  | tmul f b =>
    show (baseChangeTowerEquiv F A₁ A₂).1
        (dualizingModule.baseChange
          (FiniteOpenFactorization.baseChange F A₁) A₂
          (dualizingModule.baseChange F A₁
            (dualizingModule.tmul F f b))) =
      dualizingModule.baseChange F A₂
        (dualizingModule.tmul F f b)
    rw [dualizingModule.baseChange_tmul (F := F) (A₁ := A₁) f b,
      dualizingModule.baseChange_tmul (F := F) (A₁ := A₂) f b,
      dualizingModule.baseChange_tmul (F := F₁) (A₁ := A₂)
        (f.baseChange A₁) (1 ⊗ₜ[A] b)]
    let cM' : Fiter.middle ≃ₐ[A₂] Fdirect.middle :=
      Algebra.TensorProduct.cancelBaseChange A A₁ A₂ A₂ F.middle
    let cB := Algebra.TensorProduct.cancelBaseChange A A₁ A₂ A₂ B
    have hcM :
        (Algebra.TensorProduct.cancelBaseChange A A₁ A₂ A₂ F.middle).toLinearMap =
          TensorProduct.AlgebraTensorModule.cancelBaseChange A A₁ A₂ A₂ F.middle := by
      rfl
    have hdual :
        ((f.baseChange A₁).baseChange A₂).comp cM'.symm.toLinearMap =
          f.baseChange A₂ := by
      apply LinearMap.ext
      intro z
      rw [Module.Dual.baseChange_baseChange]
      have hcancel (z : Fdirect.middle) :
          TensorProduct.AlgebraTensorModule.cancelBaseChange A A₁ A₂ A₂ F.middle
              (cM'.symm z) = z :=
        (LinearMap.congr_fun hcM (cM'.symm z)).symm.trans (cM'.apply_symm_apply z)
      show (f.baseChange A₂)
          ((TensorProduct.AlgebraTensorModule.cancelBaseChange A A₁ A₂ A₂ F.middle)
            (cM'.symm z)) = (f.baseChange A₂) z
      rw [hcancel]
    calc
      (baseChangeTowerEquiv F A₁ A₂).1
          (dualizingModule.tmul Fiter
            ((f.baseChange A₁).baseChange A₂) (1 ⊗ₜ[A₁] (1 ⊗ₜ[A] b))) =
        dualizingModule.tmul Fdirect
          (((f.baseChange A₁).baseChange A₂).comp cM'.symm.toLinearMap)
          (cB (1 ⊗ₜ[A₁] (1 ⊗ₜ[A] b))) :=
        (baseChangeTowerEquiv F A₁ A₂).2
          ((f.baseChange A₁).baseChange A₂) (1 ⊗ₜ[A₁] (1 ⊗ₜ[A] b))
      _ = dualizingModule.tmul Fdirect (f.baseChange A₂) (1 ⊗ₜ[A] b) := by
        rw [hdual]
        simp [cB, Algebra.TensorProduct.cancelBaseChange_tmul]
  | add x y hx hy =>
    change dualizingModule F at x
    change dualizingModule F at y
    calc
      (baseChangeTowerEquiv F A₁ A₂).1
          (dualizingModule.baseChange F₁ A₂
            (dualizingModule.baseChange F A₁ (x + y))) =
        (baseChangeTowerEquiv F A₁ A₂).1
          (dualizingModule.baseChange F₁ A₂
            (dualizingModule.baseChange F A₁ x +
              dualizingModule.baseChange F A₁ y)) := by
          rw [(dualizingModule.baseChange F A₁).map_add x y]
      _ = (baseChangeTowerEquiv F A₁ A₂).1
          (dualizingModule.baseChange F₁ A₂
            (dualizingModule.baseChange F A₁ x) +
              dualizingModule.baseChange F₁ A₂
                (dualizingModule.baseChange F A₁ y)) := by
          rw [(dualizingModule.baseChange F₁ A₂).map_add]
      _ = (baseChangeTowerEquiv F A₁ A₂).1
          (dualizingModule.baseChange F₁ A₂
            (dualizingModule.baseChange F A₁ x)) +
            (baseChangeTowerEquiv F A₁ A₂).1
              (dualizingModule.baseChange F₁ A₂
                (dualizingModule.baseChange F A₁ y)) :=
          (baseChangeTowerEquiv F A₁ A₂).1.map_add _ _
      _ = dualizingModule.baseChange F A₂ x +
            dualizingModule.baseChange F A₂ y := by rw [hx, hy]
      _ = dualizingModule.baseChange F A₂ (x + y) :=
          ((dualizingModule.baseChange F A₂).map_add x y).symm

end dualizingModule

end Stacks.Discriminant
