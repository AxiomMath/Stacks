module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Different.DualizingModulesQuasi.BaseChange

/-!
# Flat base change for relative dualizing modules

For a flat extension `A → A₁` of a Noetherian base ring, the canonical base change map on the
relative dualizing module of a quasi-finite algebra exhibits the new dualizing module as the
scalar extension of the original one. In other words, forming the relative dualizing module
commutes with flat base change.

## Main results

* `Stacks.Discriminant.dualizingModule_isBaseChange_of_flat` states that the canonical map
  exhibits the new dualizing module as the scalar extension of the original one.

## Implementation notes

The quasi-finite algebra is represented by a finite-open factorization. `IsBaseChange` asserts
precisely that the map induced from the displayed base change map is an isomorphism of modules
over the base-changed algebra. Noetherianity of the base ensures that the finite intermediate
algebra is finitely presented as a module, which is what makes the dual commute with the flat
base change.

The proof assembles the comparison out of four canonical equivalences — commuting the two
tensor factors on each side, cancelling a base change over the intermediate algebra, and
transporting the dual — and then checks the resulting equivalence against the base change map
on pure tensors.

## References

* [Stacks Project, Tag 0BT3](https://stacks.math.columbia.edu/tag/0BT3)
-/

@[expose] public section

open scoped TensorProduct

universe u v w x

namespace Stacks.Discriminant

/-- **Stacks Project, Tag 0BT3.** Flat base change identifies the scalar extension of
the relative dualizing module with the relative dualizing module after base change. -/
@[stacks 0BT3]
theorem dualizingModule_isBaseChange_of_flat
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [IsNoetherianRing A]
    (F : FiniteOpenFactorization.{u, v, w} A B)
    (A₁ : Type x) [CommRing A₁] [Algebra A A₁] [Module.Flat A A₁] :
    letI : Algebra B (A₁ ⊗[A] B) := Algebra.TensorProduct.rightAlgebra
    letI : Module B
        (dualizingModule (FiniteOpenFactorization.baseChange F A₁)) :=
      Module.compHom _ (algebraMap B (A₁ ⊗[A] B))
    letI : IsScalarTower B (A₁ ⊗[A] B)
        (dualizingModule (FiniteOpenFactorization.baseChange F A₁)) :=
      IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
    IsBaseChange (A₁ ⊗[A] B) (dualizingModule.baseChange F A₁) := by
  -- Every instance is introduced before the abbreviation that uses it: `Module.Dual A₁ C₁`
  -- elaborated under a globally-found `Algebra A₁ C₁` while `algebraDualModule A₁ C₁` was then
  -- given the factorization's own, and the two are reconciled only by a transparency override.
  let C := F.middle
  let _ : CommRing C := F.commRingMiddle
  let _ : Algebra A C := F.algebraMiddle
  let _ : Algebra C B := F.algebraTarget
  let _ : IsScalarTower A C B := F.scalarTower
  let _ : Module.Finite A C := F.finite_middle
  let _ : Module.FinitePresentation A C := Module.finitePresentation_of_finite A C
  let F₁ := FiniteOpenFactorization.baseChange F A₁
  let C₁ := A₁ ⊗[A] C
  let B₁ := A₁ ⊗[A] B
  let E := Module.Dual A C
  let E₁ := Module.Dual A₁ C₁
  let _ : Module C E := algebraDualModule A C
  let _ : Algebra C C₁ := Algebra.TensorProduct.rightAlgebra
  let _ : Algebra C₁ B₁ := F₁.algebraTarget
  let _ : Algebra B B₁ := Algebra.TensorProduct.rightAlgebra
  let _ : Algebra C B₁ := Algebra.compHom B₁ (algebraMap C B)
  let _ : Module C B₁ := Module.compHom B₁ (algebraMap C B)
  let _ : Module C₁ E₁ := algebraDualModule A₁ C₁
  let _ : Module C E₁ := Module.compHom E₁ (algebraMap C C₁)
  let _ : IsScalarTower C C₁ E₁ :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  let _ : IsScalarTower A₁ C₁ B₁ :=
    FiniteOpenFactorization.baseChange_scalarTower F A₁
  let _ : IsScalarTower C B B₁ :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let _ : IsScalarTower C C₁ B₁ := IsScalarTower.of_algebraMap_eq (fun c => by
    show algebraMap C₁ B₁ (algebraMap C C₁ c) =
      algebraMap B B₁ (algebraMap C B c)
    show Algebra.TensorProduct.map (AlgHom.id A A₁)
        (IsScalarTower.toAlgHom A C B) (1 ⊗ₜ[A] c) = _
    rw [Algebra.TensorProduct.map_tmul]
    simp only [AlgHom.id_apply]
    show algebraMap B B₁ (algebraMap C B c) = _
    rfl)
  let _ : Module B (E ⊗[C] B) :=
    (TensorProduct.comm C E B).toAddEquiv.module B
  let _ : Module B₁ (E₁ ⊗[C₁] B₁) :=
    (TensorProduct.comm C₁ E₁ B₁).toAddEquiv.module B₁
  let _ : Module B (dualizingModule F) :=
    (TensorProduct.comm C E B).toAddEquiv.module B
  let _ : Module B₁ (dualizingModule (FiniteOpenFactorization.baseChange F A₁)) :=
    (TensorProduct.comm C₁ E₁ B₁).toAddEquiv.module B₁
  let _ : Module B (dualizingModule (FiniteOpenFactorization.baseChange F A₁)) :=
    Module.compHom _ (algebraMap B B₁)
  let hTower : IsScalarTower B B₁
      (dualizingModule (FiniteOpenFactorization.baseChange F A₁)) :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  let _ : IsScalarTower B B₁
      (dualizingModule (FiniteOpenFactorization.baseChange F A₁)) := hTower
  let hE := dualizingModule.dual_baseChange_isBaseChange_overTensor (R := A) (M := C) (S := A₁)
  let eComm : E ⊗[C] B ≃ₗ[B] B ⊗[C] E :=
    (TensorProduct.comm C E B).toAddEquiv.linearEquiv B
  let eCommTarget : E₁ ⊗[C₁] B₁ ≃ₗ[B₁] B₁ ⊗[C₁] E₁ :=
    (TensorProduct.comm C₁ E₁ B₁).toAddEquiv.linearEquiv B₁
  let eTensor' : B₁ ⊗[B] (E ⊗[C] B) ≃ₗ[B₁]
      B₁ ⊗[B] (B ⊗[C] E) :=
    TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl B₁ B₁) eComm
  let eCancel :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange C B B₁ B₁ E
  let eSource := eTensor'.trans eCancel
  let eCancelC :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange C C₁ B₁ B₁ E
  let eLift : B₁ ⊗[C₁] (C₁ ⊗[C] E) ≃ₗ[B₁] B₁ ⊗[C₁] E₁ :=
    TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl B₁ B₁) hE.equiv
  let eMiddle := eCancelC.symm.trans eLift
  let e : B₁ ⊗[B] dualizingModule F ≃ₗ[B₁]
      dualizingModule (FiniteOpenFactorization.baseChange F A₁) :=
    eSource.trans (eMiddle.trans eCommTarget.symm)
  refine @IsBaseChange.of_equiv B _ _ B₁ _ _ _ _ _ _ _ _ hTower
    (f := dualizingModule.baseChange F A₁) e ?_
  intro x
  dsimp only [dualizingModule] at x ⊢
  induction x using TensorProduct.induction_on with
  | zero =>
    calc
      e 0 = 0 := map_zero e
      _ = dualizingModule.baseChange F A₁ 0 :=
        (map_zero (dualizingModule.baseChange F A₁)).symm
  | add x y hx hy =>
    -- `rw [TensorProduct.tmul_add]` cannot abstract the sum here, because the `+` of the goal
    -- and the `+` of the lemma are two instances identified only definitionally; splitting the
    -- tensor is therefore done as a term, where the check happens at elaboration.
    have hsplit : e (1 ⊗ₜ[B] (x + y)) = e (1 ⊗ₜ[B] x) + e (1 ⊗ₜ[B] y) :=
      (congrArg e (TensorProduct.tmul_add (1 : B₁) x y)).trans (map_add e _ _)
    have hsum : dualizingModule.baseChange F A₁ x + dualizingModule.baseChange F A₁ y =
        dualizingModule.baseChange F A₁ (x + y) :=
      (map_add (dualizingModule.baseChange F A₁) x y).symm
    exact hsplit.trans ((congrArg₂ (· + ·) hx hy).trans hsum)
  | tmul f b =>
    show e (1 ⊗ₜ[B] dualizingModule.tmul F f b) =
      dualizingModule.baseChange F A₁
        (dualizingModule.tmul F f b)
    rw [dualizingModule.baseChange_tmul]
    have h1 : eTensor' (1 ⊗ₜ[B] (f ⊗ₜ[C] b)) =
        1 ⊗ₜ[B] (b ⊗ₜ[C] f) := by
      show (1 : B₁) ⊗ₜ[B] eComm (f ⊗ₜ[C] b) = _
      rfl
    have h2 : eCancel (1 ⊗ₜ[B] (b ⊗ₜ[C] f)) =
        (algebraMap B B₁ b) ⊗ₜ[C] f := by
      simp [eCancel, TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul,
        Algebra.smul_def]
    have h3 : eCancelC.symm ((algebraMap B B₁ b) ⊗ₜ[C] f) =
        (algebraMap B B₁ b) ⊗ₜ[C₁] (1 ⊗ₜ[C] f) := by
      simp [eCancelC, TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul]
    have h4 : eLift ((algebraMap B B₁ b) ⊗ₜ[C₁] (1 ⊗ₜ[C] f)) =
        (algebraMap B B₁ b) ⊗ₜ[C₁] (Module.Dual.baseChange A₁ f) := by
      show (algebraMap B B₁ b) ⊗ₜ[C₁] hE.equiv (1 ⊗ₜ[C] f) = _
      rw [IsBaseChange.equiv_tmul]
      rw [one_smul, dualizingModule.dualBaseChangeRestrictScalars]
      rfl
    have h5 : eCommTarget.symm
        ((algebraMap B B₁ b) ⊗ₜ[C₁] (Module.Dual.baseChange A₁ f)) =
        (Module.Dual.baseChange A₁ f) ⊗ₜ[C₁] (algebraMap B B₁ b) := rfl
    show eCommTarget.symm
      (eLift (eCancelC.symm (eCancel
        (eTensor' (1 ⊗ₜ[B] (f ⊗ₜ[C] b)))))) = _
    rw [h1, h2, h3, h4, h5]
    rw [Algebra.TensorProduct.right_algebraMap_apply]
    rfl

end Stacks.Discriminant
