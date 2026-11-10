module

public import StacksFrontier.AlgebraicGeometry.Different.DualizingModulesQuasi.FlatAlgebraBaseChange.TargetAway

/-!
# Arbitrary base change for the dualizing module: the finite projective case

This part proves that `Stacks.Discriminant.dualizingModule.baseChangeLinearMap` is bijective
for an arbitrary finite open factorization of a finite projective algebra
(`baseChangeLinearMap_bijective_of_finite_projective_target`), by identifying its dualizing
module with the dual `Hom_A(B, A)` through the dual adjunction along the middle ring, and using
that this dual commutes with arbitrary base change.
It also identifies the base change of the factorization `targetAwayFactorization F e` with the
corresponding factorization of the base-changed algebra (`targetAwayBaseChangeAlgEquiv`,
`targetAwayBaseChangeDualizingEquiv`).

## References

* [Stacks Project, Tag 0BVF](https://stacks.math.columbia.edu/tag/0BVF)
* [Stacks Project, Tag 0BVB](https://stacks.math.columbia.edu/tag/0BVB)
* [Stacks Project, Tag 0BT3](https://stacks.math.columbia.edu/tag/0BT3)
-/

@[expose] public section


open scoped TensorProduct

universe u v w x y

namespace Stacks.Discriminant

namespace dualizingModule

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]

open Topology CategoryTheory Opposite AlgebraicGeometry

private theorem linearMap_eq_of_one_tmul
    {R S M N : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]
    [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module S N]
    (f g : S ⊗[R] M →ₗ[S] N)
    (h : ∀ m, f (1 ⊗ₜ[R] m) = g (1 ⊗ₜ[R] m)) : f = g := by
  ext z
  induction z using TensorProduct.inductionOn with
  | add z z' hz hz' => simp [hz, hz']
  | tmul s m =>
      rw [TensorProduct.tmul_eq_smul_one_tmul]
      simp [h]

private def dualRestrictLinear_bridge
    {R F C : Type*} [CommRing R] [CommRing F] [CommRing C]
    [Algebra R F] [Algebra R C] (r : F →ₐ[R] C) :
    letI : Module C (Module.Dual R C) := algebraDualModule R C
    letI : Module F (Module.Dual R C) := Module.compHom _ r.toRingHom
    letI : Module F (Module.Dual R F) := algebraDualModule R F
    Module.Dual R C →ₗ[F] Module.Dual R F := by
  letI : Module C (Module.Dual R C) := algebraDualModule R C
  letI : Module F (Module.Dual R C) := Module.compHom _ r.toRingHom
  letI : Module F (Module.Dual R F) := algebraDualModule R F
  refine { toFun := fun φ => φ.comp r.toLinearMap, map_add' := ?_, map_smul' := ?_ }
  · intro φ ψ; ext z; rfl
  · intro c φ
    ext z
    rw [algebraDualModule_smul_apply]
    change φ (r c * r z) = φ (r (c * z))
    exact congrArg φ (map_mul r c z).symm

private noncomputable def dualAdjunction_bridge
    {R F C : Type*} [CommRing R] [CommRing F] [CommRing C]
    [Algebra R F] [Algebra R C] [Algebra F C] [IsScalarTower R F C] :
    letI : Module C (Module.Dual R C) := algebraDualModule R C
    letI : Module F (Module.Dual R F) := algebraDualModule R F
    letI : Module C (C →ₗ[F] Module.Dual R F) := dualHomModule
    Module.Dual R C ≃ₗ[C] (C →ₗ[F] Module.Dual R F) := by
  letI : Module C (Module.Dual R C) := algebraDualModule R C
  letI : Module F (Module.Dual R F) := algebraDualModule R F
  letI : Module C (C →ₗ[F] Module.Dual R F) := dualHomModule
  let adj (φ : Module.Dual R C) : C →ₗ[F] Module.Dual R F :=
    { toFun := fun c =>
        { toFun := fun a => φ (c * algebraMap F C a)
          map_add' := by intro a b; simp [map_add, mul_add]
          map_smul' := by
            intro a x
            simp only [Algebra.smul_def]
            change φ (c * algebraMap F C (algebraMap R F a * x)) =
              algebraMap R R a * φ (c * algebraMap F C x)
            rw [map_mul (algebraMap F C)]
            rw [← IsScalarTower.algebraMap_apply R F C a]
            calc
              φ (c * (algebraMap R C a * algebraMap F C x)) =
                  φ (algebraMap R C a * (c * algebraMap F C x)) := by congr 1; ring
              _ = algebraMap R R a * φ (c * algebraMap F C x) := by
                  simpa [Algebra.smul_def] using φ.map_smul a (c * algebraMap F C x) }
      map_add' := by intro c d; ext x; simp [map_add, add_mul]
      map_smul' := by
        intro b c
        ext x
        simp only [Algebra.smul_def]
        change φ ((algebraMap F C b * c) * algebraMap F C x) =
          φ (c * algebraMap F C (b * x))
        simp only [map_mul]
        congr 1; ring }
  let unadj (ψ : C →ₗ[F] Module.Dual R F) : Module.Dual R C :=
    { toFun := fun c => ψ c 1
      map_add' := by intro c d; exact congrArg (fun f : Module.Dual R F => f 1) (ψ.map_add c d)
      map_smul' := by
        intro a c
        simp only [Algebra.smul_def]
        have hs := congrArg (fun f : Module.Dual R F => f 1) (ψ.map_smul (algebraMap R F a) c)
        rw [Algebra.smul_def, ← IsScalarTower.algebraMap_apply R F C a,
          algebraDualModule_smul_apply] at hs
        change ψ (algebraMap R C a * c) 1 = algebraMap R R a * ψ c 1
        have hA : ψ c (algebraMap R F a * 1) = algebraMap R R a * ψ c 1 := by
          simpa [Algebra.smul_def] using (ψ c).map_smul a (1 : F)
        rw [← hA]
        exact hs }
  let L : Module.Dual R C →ₗ[C] (C →ₗ[F] Module.Dual R F) :=
    { toFun := adj
      map_add' := by
        intro φ ψ
        apply LinearMap.ext
        intro c
        apply LinearMap.ext
        intro a
        rfl
      map_smul' := by
        intro d φ
        apply LinearMap.ext
        intro c
        apply LinearMap.ext
        intro a
        change φ (d * (c * algebraMap F C a)) = φ ((d * c) * algebraMap F C a)
        congr 1; ring }
  apply LinearEquiv.ofBijective L
  constructor
  · intro φ ψ h
    apply LinearMap.ext
    intro c
    have h' := congrArg (fun f : C →ₗ[F] Module.Dual R F => f c) h
    have hz := congrArg (fun f : Module.Dual R F => f 1) h'
    simpa [L, adj] using hz
  · intro ψ
    refine ⟨unadj ψ, ?_⟩
    apply LinearMap.ext
    intro c
    apply LinearMap.ext
    intro a
    have hs := congrArg (fun f : Module.Dual R F => f 1) (ψ.map_smul a c)
    calc
      ψ (c * algebraMap F C a) 1 = ψ (algebraMap F C a * c) 1 := by rw [mul_comm c]
      _ = ψ c a := by
        simpa [Algebra.smul_def, algebraDualModule_smul_apply] using hs

private theorem dualAdjunction_apply_one_bridge
    {R F C : Type*} [CommRing R] [CommRing F] [CommRing C]
    [Algebra R F] [Algebra R C] [Algebra F C] [IsScalarTower R F C]
    (φ : Module.Dual R C) :
    letI : Module F (Module.Dual R F) := algebraDualModule R F
    letI : Module C (Module.Dual R C) := algebraDualModule R C
    letI : Module C (C →ₗ[F] Module.Dual R F) := dualHomModule
    dualAdjunction_bridge (R := R) (F := F) (C := C) φ 1 =
      dualRestrictLinear_bridge (IsScalarTower.toAlgHom R F C) φ := by
  let : Module F (Module.Dual R F) := algebraDualModule R F
  let : Module C (Module.Dual R C) := algebraDualModule R C
  let : Module C (C →ₗ[F] Module.Dual R F) := dualHomModule
  ext a
  change φ (1 * algebraMap F C a) = φ (algebraMap F C a)
  simp

private noncomputable def dualizingModule_commonChange_bridge
    {R F C S : Type*} [CommRing R] [CommRing F] [CommRing C] [CommRing S]
    [Algebra R F] [Algebra R C] [Algebra R S] [Algebra F C] [Algebra F S] [Algebra C S]
    [IsScalarTower R F C] [IsScalarTower R F S] [IsScalarTower F C S]
    [Module.Flat F S] [Module.FinitePresentation F C]
    (hpush : Algebra.IsPushout F S C S) :
    letI : Module F (Module.Dual R F) := algebraDualModule R F
    letI : Module C (Module.Dual R C) := algebraDualModule R C
    letI : Module C (C →ₗ[F] Module.Dual R F) := dualHomModule
    letI : Module S (Module.Dual R C ⊗[C] S) :=
      (TensorProduct.comm C (Module.Dual R C) S).toAddEquiv.module S
    letI : Module S (Module.Dual R F ⊗[F] S) :=
      (TensorProduct.comm F (Module.Dual R F) S).toAddEquiv.module S
    (Module.Dual R C ⊗[C] S) ≃ₗ[S] (Module.Dual R F ⊗[F] S) := by
  letI : Module F (Module.Dual R F) := algebraDualModule R F
  letI : Module C (Module.Dual R C) := algebraDualModule R C
  letI : Module C (C →ₗ[F] Module.Dual R F) := dualHomModule
  letI : IsScalarTower F C (C →ₗ[F] Module.Dual R F) := ⟨by
    intro f c ψ
    ext z x
    simp only [LinearMap.smul_apply, dualHomModule_smul_apply]
    calc
      ψ ((f • c) * z) x = ψ (f • (c * z)) x := by
        congr 2
        simp only [Algebra.smul_def]
        ring
      _ = (f • ψ (c * z)) x := congrArg (fun g : Module.Dual R F => g x) (ψ.map_smul f (c * z))
      _ = ψ (c * z) (f * x) := by simp [algebraDualModule_smul_apply]⟩
  letI : Module S (Module.Dual R C ⊗[C] S) :=
    (TensorProduct.comm C (Module.Dual R C) S).toAddEquiv.module S
  letI : Module S (Module.Dual R F ⊗[F] S) :=
    (TensorProduct.comm F (Module.Dual R F) S).toAddEquiv.module S
  let adj := dualAdjunction_bridge (R := R) (F := F) (C := C)
  let eSwap₁ : Module.Dual R C ⊗[C] S ≃ₗ[S] S ⊗[C] Module.Dual R C :=
    (TensorProduct.comm C (Module.Dual R C) S).toAddEquiv.toLinearEquiv (by
      intro s z
      change (TensorProduct.comm C (Module.Dual R C) S).toAddEquiv
        ((TensorProduct.comm C (Module.Dual R C) S).toAddEquiv.symm
          (s • (TensorProduct.comm C (Module.Dual R C) S).toAddEquiv z)) = _
      simp)
  let eAdj : S ⊗[C] Module.Dual R C ≃ₗ[S] S ⊗[C] (C →ₗ[F] Module.Dual R F) :=
    (TensorProduct.congr (LinearEquiv.refl C S) adj).toAddEquiv.toLinearEquiv (by
      intro s z
      induction z using TensorProduct.inductionOn with
      | add z z' hz hz' => simp only [map_add, hz, hz', smul_add]
      | tmul c φ => simp [TensorProduct.smul_tmul'])
  letI : Algebra.IsPushout F S C S := hpush
  let eCancel : S ⊗[C] (C →ₗ[F] Module.Dual R F) ≃ₗ[S]
      S ⊗[F] (C →ₗ[F] Module.Dual R F) :=
    Algebra.IsPushout.cancelBaseChange F S C S (C →ₗ[F] Module.Dual R F)
  let hBC : IsBaseChange S (LinearMap.baseChangeHom F S C (Module.Dual R F)) :=
    Module.FinitePresentation.isBaseChange_map F C (Module.Dual R F) S
  let eBase : S ⊗[F] (C →ₗ[F] Module.Dual R F) ≃ₗ[S]
      ((S ⊗[F] C) →ₗ[S] (S ⊗[F] Module.Dual R F)) := hBC.equiv
  let ePush : S ⊗[F] C ≃ₐ[S] S := Algebra.IsPushout.equiv F S C S
  let eArrow : ((S ⊗[F] C) →ₗ[S] (S ⊗[F] Module.Dual R F)) ≃ₗ[S]
      (S →ₗ[S] (S ⊗[F] Module.Dual R F)) :=
    LinearEquiv.arrowCongr ePush.toLinearEquiv (LinearEquiv.refl S (S ⊗[F] Module.Dual R F))
  let eEval : (S →ₗ[S] (S ⊗[F] Module.Dual R F)) ≃ₗ[S]
      (S ⊗[F] Module.Dual R F) :=
    { toFun := fun g => g 1
      invFun := fun m =>
        { toFun := fun s => s • m
          map_add' := fun _ _ => add_smul _ _ _
          map_smul' := fun _ _ => mul_smul _ _ _ }
      left_inv := by intro g; ext; simp
      right_inv := by intro m; simp
      map_add' := by intro f g; rfl
      map_smul' := by intro s g; rfl }
  let eSwap₂ : S ⊗[F] Module.Dual R F ≃ₗ[S] Module.Dual R F ⊗[F] S :=
    (TensorProduct.comm F (Module.Dual R F) S).symm.toAddEquiv.toLinearEquiv (by
      intro s z
      change (TensorProduct.comm F (Module.Dual R F) S).symm.toAddEquiv (s • z) =
        (TensorProduct.comm F (Module.Dual R F) S).symm.toAddEquiv
          (s • (TensorProduct.comm F (Module.Dual R F) S).toAddEquiv
            ((TensorProduct.comm F (Module.Dual R F) S).symm.toAddEquiv z))
      simp)
  exact eSwap₁.trans (eAdj.trans (eCancel.trans (eBase.trans (eArrow.trans (eEval.trans eSwap₂)))))

private theorem dualizingModule_commonChange_tmul_bridge
    {R F C S : Type*} [CommRing R] [CommRing F] [CommRing C] [CommRing S]
    [Algebra R F] [Algebra R C] [Algebra R S] [Algebra F C] [Algebra F S] [Algebra C S]
    [IsScalarTower R F C] [IsScalarTower R F S] [IsScalarTower F C S]
    [Module.Flat F S] [Module.FinitePresentation F C]
    (hpush : Algebra.IsPushout F S C S) (φ : Module.Dual R C) (s : S) :
    letI : Module F (Module.Dual R F) := algebraDualModule R F
    letI : Module C (Module.Dual R C) := algebraDualModule R C
    letI : Module C (C →ₗ[F] Module.Dual R F) := dualHomModule
    letI : Module S (Module.Dual R C ⊗[C] S) :=
      (TensorProduct.comm C (Module.Dual R C) S).toAddEquiv.module S
    letI : Module S (Module.Dual R F ⊗[F] S) :=
      (TensorProduct.comm F (Module.Dual R F) S).toAddEquiv.module S
    dualizingModule_commonChange_bridge hpush (φ ⊗ₜ[C] s) =
      dualRestrictLinear_bridge (IsScalarTower.toAlgHom R F C) φ ⊗ₜ[F] s := by
  let : Module F (Module.Dual R F) := algebraDualModule R F
  let : Module C (Module.Dual R C) := algebraDualModule R C
  let : Module C (C →ₗ[F] Module.Dual R F) := dualHomModule
  let : Module S (Module.Dual R C ⊗[C] S) :=
    (TensorProduct.comm C (Module.Dual R C) S).toAddEquiv.module S
  let : Module S (Module.Dual R F ⊗[F] S) :=
    (TensorProduct.comm F (Module.Dual R F) S).toAddEquiv.module S
  classical
  let e := dualizingModule_commonChange_bridge (R := R) (F := F) (C := C) (S := S) hpush
  have hsmul : φ ⊗ₜ[C] s = s • (φ ⊗ₜ[C] (1 : S)) := by
    apply (TensorProduct.comm C (Module.Dual R C) S).toAddEquiv.injective
    simpa [Equiv.smul_def] using (TensorProduct.smul_tmul' (R := C) (R' := S)
      (M := S) (N := Module.Dual R C) s (1 : S) φ).symm
  have hone : e (φ ⊗ₜ[C] (1 : S)) =
      dualRestrictLinear_bridge (IsScalarTower.toAlgHom R F C) φ ⊗ₜ[F] (1 : S) := by
    simp [e, dualizingModule_commonChange_bridge, dualRestrictLinear_bridge,
      LinearEquiv.trans_apply, Algebra.IsPushout.cancelBaseChange_tmul,
      IsBaseChange.equiv_tmul, LinearMap.baseChange_tmul,
      Algebra.TensorProduct.one_def, dualAdjunction_apply_one_bridge]
  calc
    e (φ ⊗ₜ[C] s) = e (s • (φ ⊗ₜ[C] (1 : S))) := congrArg e hsmul
    _ = s • e (φ ⊗ₜ[C] (1 : S)) := map_smul e s _
    _ = dualRestrictLinear_bridge (IsScalarTower.toAlgHom R F C) φ ⊗ₜ[F] s := by
      rw [hone]
      apply (TensorProduct.comm F (Module.Dual R F) S).toAddEquiv.injective
      simp [Equiv.smul_def, TensorProduct.smul_tmul']

/-- The identity algebra structure of `S` over itself. -/
local instance finiteProjectiveTarget_algebraSelf (S : Type v) [CommRing S] :
    Algebra S S := Algebra.id S

/-- The scalar tower `R → S → S`. -/
local instance finiteProjectiveTarget_towerSelf
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S] :
    IsScalarTower R S S := IsScalarTower.of_algebraMap_eq' (by
  ext r
  rfl)

/-- The `S`-module structure on `Hom_R(S, R)` given by `(s • f) x = f (s * x)`. -/
local instance finiteProjectiveTarget_dualModule
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S] :
    Module S (Module.Dual R S) := algebraDualModule R S

/-- The `R₁ ⊗[R] S`-module structure on `Hom_{R₁}(R₁ ⊗[R] S, R₁)` by precomposition with
multiplication. -/
local instance finiteProjectiveTarget_baseChangedDualModule
    (R : Type u) (R₁ : Type x) (S : Type v)
    [CommRing R] [CommRing R₁] [CommRing S] [Algebra R R₁] [Algebra R S] :
    Module (R₁ ⊗[R] S) (Module.Dual R₁ (R₁ ⊗[R] S)) :=
  algebraDualModule R₁ (R₁ ⊗[R] S)

private noncomputable def finiteProjectiveTargetEquiv
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (F : FiniteOpenFactorization.{u, v, w} R S)
    [Module.Finite R S] [Module.Projective R S] :
    letI : Algebra S S := Algebra.id S
    letI : IsScalarTower R S S := IsScalarTower.of_algebraMap_eq' (by
      ext r
      rfl)
    letI : Module S (Module.Dual R S) := algebraDualModule R S
    letI : Module S (Module.Dual R S ⊗[S] S) :=
      (TensorProduct.comm S (Module.Dual R S) S).toAddEquiv.module S
    (Module.Dual R S ⊗[S] S) ≃ₗ[S] dualizingModule F := by
  letI : Algebra S S := Algebra.id S
  letI : IsScalarTower R S S := IsScalarTower.of_algebraMap_eq' (by
    ext r
    rfl)
  letI : Algebra F.middle S := F.algebraTarget
  letI : IsScalarTower R F.middle S := F.scalarTower
  letI : Module.FinitePresentation F.middle S :=
    finite_factorization_middle_finitePresentation F
  let r : F.middle →ₐ[R] S := IsScalarTower.toAlgHom R F.middle S
  letI : IsScalarTower F.middle S S := IsScalarTower.of_algebraMap_eq (by
    intro c
    rfl)
  let : Module.Flat F.middle S := factorization_flat_bridge F
  letI : Algebra.IsEpi F.middle S := factorization_epi_bridge F
  have hpush : Algebra.IsPushout F.middle S S S := by
    exact @isPushout_of_flat_epi_of_injective F.middle S S
      inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance inferInstance (by
        intro x y h
        simpa using h)
  letI : Module S (Module.Dual R S) := algebraDualModule R S
  let e := @dualizingModule_commonChange_bridge R F.middle S S
      inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance inferInstance
      inferInstance inferInstance inferInstance
      inferInstance inferInstance inferInstance
      inferInstance inferInstance hpush
  exact e

private theorem finiteProjectiveTargetEquiv_apply
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (F : FiniteOpenFactorization.{u, v, w} R S)
    [Module.Finite R S] [Module.Projective R S]
    (φ : Module.Dual R S) (b : S) :
    finiteProjectiveTargetEquiv F (φ ⊗ₜ[S] b) =
      dualizingModule.tmul F
        (φ.comp (IsScalarTower.toAlgHom R F.middle S).toLinearMap) b := by
  unfold finiteProjectiveTargetEquiv
  let : Module.Flat F.middle S := factorization_flat_bridge F
  let : Module.FinitePresentation F.middle S :=
    finite_factorization_middle_finitePresentation F
  exact dualizingModule_commonChange_tmul_bridge _ φ b

private theorem finiteProjectiveTargetEquiv_baseChange
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (F : FiniteOpenFactorization.{u, v, w} R S)
    [Module.Finite R S] [Module.Projective R S]
    (R₁ : Type x) [CommRing R₁] [Algebra R R₁]
    [Module.Finite R₁ (R₁ ⊗[R] S)] [Module.Projective R₁ (R₁ ⊗[R] S)]
    (φ : Module.Dual R S) (b : S) :
    finiteProjectiveTargetEquiv
        (FiniteOpenFactorization.baseChange F R₁)
        (Module.Dual.baseChange R₁ φ ⊗ₜ[R₁ ⊗[R] S] (1 ⊗ₜ[R] b)) =
      dualizingModule.baseChange F R₁
        (finiteProjectiveTargetEquiv F (φ ⊗ₜ[S] b)) := by
  let S₁ := R₁ ⊗[R] S
  let F₁ := FiniteOpenFactorization.baseChange F R₁
  let : Algebra F.middle S := F.algebraTarget
  let : IsScalarTower R F.middle S := F.scalarTower
  let r : F.middle →ₐ[R] S := IsScalarTower.toAlgHom R F.middle S
  let r₁ : F₁.middle →ₐ[R₁] S₁ := IsScalarTower.toAlgHom R₁ F₁.middle S₁
  have hdual : (Module.Dual.baseChange R₁ φ).comp r₁.toLinearMap =
      Module.Dual.baseChange R₁ (φ.comp r.toLinearMap) := by
    change (Module.Dual.baseChange R₁ φ).comp
      (Algebra.TensorProduct.map (AlgHom.id R₁ R₁) r).toLinearMap = _
    ext a
    simp [Module.Dual.baseChange_apply_tmul]
  rw [finiteProjectiveTargetEquiv_apply F φ b,
    dualizingModule.baseChange_tmul,
    finiteProjectiveTargetEquiv_apply
      (FiniteOpenFactorization.baseChange F R₁)
      (Module.Dual.baseChange R₁ φ) (1 ⊗ₜ[R] b)]
  rw [hdual]

theorem baseChangeLinearMap_bijective_of_finite_projective_target
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [Module.Finite R S] [Module.Projective R S]
    (F : FiniteOpenFactorization.{u, v, w} R S)
    (R₁ : Type x) [CommRing R₁] [Algebra R R₁] :
    Function.Bijective (baseChangeLinearMap F R₁) := by
  let : Algebra S S := Algebra.id S
  let : IsScalarTower R S S := IsScalarTower.of_algebraMap_eq' (by
    ext r
    rfl)
  let : Module S (Module.Dual R S) := algebraDualModule R S
  let H := identityFactorization (A := R) (B := S)
  let : Module.Finite R H.middle := by
    change Module.Finite R S
    infer_instance
  let : Module.Projective R H.middle := by
    change Module.Projective R S
    infer_instance
  let S₁ := R₁ ⊗[R] S
  let F₁ := FiniteOpenFactorization.baseChange F R₁
  let H₁ := FiniteOpenFactorization.baseChange H R₁
  let : Module.Finite R₁ S₁ := by infer_instance
  let : Module.Projective R₁ S₁ := by infer_instance
  let : Algebra S S₁ := Algebra.TensorProduct.rightAlgebra
  let : Module S (dualizingModule F₁) := Module.compHom _ (algebraMap S S₁)
  let : IsScalarTower S S₁ (dualizingModule F₁) :=
    IsScalarTower.of_compHom S S₁ _
  let : Module S (dualizingModule H₁) := Module.compHom _ (algebraMap S S₁)
  let : IsScalarTower S S₁ (dualizingModule H₁) :=
    IsScalarTower.of_compHom S S₁ _
  let : Module S₁ (dualizingModule F₁) := inferInstance
  let : Module S₁ (dualizingModule H₁) := inferInstance
  let eF := finiteProjectiveTargetEquiv F
  let eH := finiteProjectiveTargetEquiv H
  let e : dualizingModule F ≃ₗ[S] dualizingModule H := eF.symm.trans eH
  let eF₁ := finiteProjectiveTargetEquiv F₁
  let eH₁ := finiteProjectiveTargetEquiv H₁
  let e₁ : dualizingModule F₁ ≃ₗ[S₁] dualizingModule H₁ := eF₁.symm.trans eH₁
  let eBC : (S₁ ⊗[S] dualizingModule F) →ₗ[S₁]
      (S₁ ⊗[S] dualizingModule H) := e.toLinearMap.baseChange S₁
  have hH : Function.Bijective (baseChangeLinearMap H R₁) :=
    baseChangeLinearMap_bijective_of_finite_projective H R₁
  have h0 (x : Module.Dual R S ⊗[S] S) :
      e₁ (baseChangeLinearMap F R₁ (1 ⊗ₜ[S] eF x)) =
        baseChangeLinearMap H R₁ (1 ⊗ₜ[S] eH x) := by
    induction x using TensorProduct.inductionOn with
    | add x y hx hy =>
      have hx' : (1 : S₁) ⊗ₜ[S] eF (x + y) =
          (1 : S₁) ⊗ₜ[S] eF x + (1 : S₁) ⊗ₜ[S] eF y := by
        rw [map_add, TensorProduct.tmul_add]
      have hy' : (1 : S₁) ⊗ₜ[S] eH (x + y) =
          (1 : S₁) ⊗ₜ[S] eH x + (1 : S₁) ⊗ₜ[S] eH y := by
        rw [map_add, TensorProduct.tmul_add]
      rw [hx', hy', map_add, map_add, map_add, hx, hy]
    | tmul φ b =>
      rw [baseChangeLinearMap_one_tmul, baseChangeLinearMap_one_tmul]
      have hF := finiteProjectiveTargetEquiv_baseChange F R₁ φ b
      have hH' := finiteProjectiveTargetEquiv_baseChange H R₁ φ b
      simp only [e₁, LinearEquiv.trans_apply]
      rw [← hF, LinearEquiv.symm_apply_apply, ← hH']
  have hbc (x : Module.Dual R S ⊗[S] S) :
      eBC ((1 : S₁) ⊗ₜ[S] eF x) = (1 : S₁) ⊗ₜ[S] eH x := by
    change (e.toLinearMap.baseChange S₁) ((1 : S₁) ⊗ₜ[S] eF x) = _
    rw [LinearMap.baseChange_tmul]
    change (1 : S₁) ⊗ₜ[S] eH (eF.symm (eF x)) = _
    rw [LinearEquiv.symm_apply_apply]
  have hCongr : e₁.toLinearMap.comp (baseChangeLinearMap F R₁) =
      (baseChangeLinearMap H R₁).comp eBC :=
    linearMap_eq_of_one_tmul _ _ (fun m => by
      obtain ⟨x, rfl⟩ := eF.surjective m
      rw [LinearMap.comp_apply, LinearMap.comp_apply, hbc x, LinearEquiv.coe_coe,
        h0 x])
  have heBase : Function.Bijective (e.toLinearMap.baseChange (R₁ ⊗[R] S)) :=
    (e.baseChange S (R₁ ⊗[R] S) _ _).bijective
  have hcomp : Function.Bijective
      (e₁.toLinearMap.comp (baseChangeLinearMap F R₁)) := by
    rw [hCongr, LinearMap.coe_comp]
    exact hH.comp heBase
  have he₁ : Function.Bijective e₁ := e₁.bijective
  constructor
  · intro x y hxy
    apply hcomp.1
    simpa using congrArg e₁ hxy
  · intro y
    obtain ⟨x, hx⟩ := hcomp.2 (e₁ y)
    refine ⟨x, ?_⟩
    apply he₁.1
    simpa using hx

noncomputable def dualizingModule_targetAlgEquiv
    {R C D E : Type*} [CommRing R] [CommRing C] [CommRing D] [CommRing E]
    [Algebra R C] [Algebra C D] [Algebra C E]
    (e : D ≃ₐ[C] E) :
    letI : Module D (Module.Dual R C ⊗[C] D) :=
      (TensorProduct.comm C (Module.Dual R C) D).toAddEquiv.module D
    letI : Module E (Module.Dual R C ⊗[C] D) :=
      Module.compHom _ e.symm.toRingHom
    letI : Module E (Module.Dual R C ⊗[C] E) :=
      (TensorProduct.comm C (Module.Dual R C) E).toAddEquiv.module E
    Module.Dual R C ⊗[C] D ≃ₗ[E] Module.Dual R C ⊗[C] E := by
  letI : Module D (Module.Dual R C ⊗[C] D) :=
    (TensorProduct.comm C (Module.Dual R C) D).toAddEquiv.module D
  letI : Module E (Module.Dual R C ⊗[C] D) :=
    Module.compHom _ e.symm.toRingHom
  letI : Module E (Module.Dual R C ⊗[C] E) :=
    (TensorProduct.comm C (Module.Dual R C) E).toAddEquiv.module E
  let eAdd := TensorProduct.congr (LinearEquiv.refl C (Module.Dual R C)) e.toLinearEquiv
  exact eAdd.toAddEquiv.toLinearEquiv (by
    intro s z
    induction z using TensorProduct.inductionOn with
    | add z z' hz hz' => simp only [map_add, hz, hz', smul_add]
    | tmul φ d =>
        have hsource : e.symm s • (φ ⊗ₜ[C] d) =
            φ ⊗ₜ[C] (e.symm s * d) := by
          apply (TensorProduct.comm C (Module.Dual R C) D).toAddEquiv.injective
          simp [(TensorProduct.comm C (Module.Dual R C) D).toAddEquiv.smul_def,
            TensorProduct.smul_tmul']
        have htarget : s • (φ ⊗ₜ[C] e d) =
            φ ⊗ₜ[C] (s * e d) := by
          apply (TensorProduct.comm C (Module.Dual R C) E).toAddEquiv.injective
          simp [(TensorProduct.comm C (Module.Dual R C) E).toAddEquiv.smul_def,
            TensorProduct.smul_tmul']
        change eAdd (e.symm s • (φ ⊗ₜ[C] d)) =
          s • eAdd (φ ⊗ₜ[C] d)
        rw [hsource]
        simp only [eAdd, TensorProduct.congr_tmul, LinearEquiv.refl_apply,
          AlgEquiv.toLinearEquiv_apply]
        change φ ⊗ₜ[C] e (e.symm s * d) = s • (φ ⊗ₜ[C] e d)
        rw [map_mul, e.apply_symm_apply]
        exact htarget.symm)

noncomputable def targetAwayBaseChangeAlgEquiv
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    (F : FiniteOpenFactorization.{u, v, w} A B)
    (A₁ : Type x) [CommRing A₁] [Algebra A A₁] (e : B) :
    let F₁ := FiniteOpenFactorization.baseChange F A₁
    let G := targetAwayFactorization F e
    let G₁ := FiniteOpenFactorization.baseChange G A₁
    let e₁ := (1 : A₁) ⊗ₜ[A] e
    let H₁ := targetAwayFactorization F₁ e₁
    let C := A₁ ⊗[A] F.middle
    letI : Algebra C (A₁ ⊗[A] Localization.Away e) := G₁.algebraTarget
    letI : Algebra C (Localization.Away e₁) := H₁.algebraTarget
    (A₁ ⊗[A] Localization.Away e) ≃ₐ[C]
      Localization.Away e₁ := by
  let F₁ := FiniteOpenFactorization.baseChange F A₁
  let G := targetAwayFactorization F e
  let G₁ := FiniteOpenFactorization.baseChange G A₁
  let e₁ := (1 : A₁) ⊗ₜ[A] e
  let H₁ := targetAwayFactorization F₁ e₁
  let C := A₁ ⊗[A] F.middle
  letI : Algebra C (A₁ ⊗[A] Localization.Away e) := G₁.algebraTarget
  letI : Algebra C (Localization.Away e₁) := H₁.algebraTarget
  let e₀ := IsLocalization.Away.tensorProductEquivTMulRight
    A A₁ e (Localization.Away e)
  let f : (A₁ ⊗[A] Localization.Away e) →ₐ[C]
      Localization.Away e₁ := {
    toRingHom := e₀.toRingHom
    commutes' := by
      intro c
      induction c using TensorProduct.inductionOn with
      | add c c' hc hc' =>
          calc
            e₀ (algebraMap C (A₁ ⊗[A] Localization.Away e) (c + c')) =
                e₀ (algebraMap C (A₁ ⊗[A] Localization.Away e) c +
                  algebraMap C (A₁ ⊗[A] Localization.Away e) c') := by rw [map_add]
            _ = e₀ (algebraMap C (A₁ ⊗[A] Localization.Away e) c) +
                e₀ (algebraMap C (A₁ ⊗[A] Localization.Away e) c') := map_add e₀ _ _
            _ = algebraMap C (Localization.Away e₁) c +
                algebraMap C (Localization.Away e₁) c' := congrArg₂ (· + ·) hc hc'
            _ = algebraMap C (Localization.Away e₁) (c + c') := by rw [map_add]
      | tmul a c =>
          change e₀ (a ⊗ₜ[A] algebraMap F.middle (Localization.Away e) c) =
            algebraMap (A₁ ⊗[A] F.middle) (Localization.Away e₁)
              (a ⊗ₜ[A] c)
          rw [IsScalarTower.algebraMap_apply F.middle B (Localization.Away e) c]
          rw [IsLocalization.Away.tensorProductEquivTMulRight_tmul]
          rfl }
  exact AlgEquiv.ofBijective f e₀.bijective

noncomputable def targetAwayBaseChangeDualizingEquiv
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    (F : FiniteOpenFactorization.{u, v, w} A B)
    (A₁ : Type x) [CommRing A₁] [Algebra A A₁] (e : B) :
    let F₁ := FiniteOpenFactorization.baseChange F A₁
    let G := targetAwayFactorization F e
    let G₁ := FiniteOpenFactorization.baseChange G A₁
    let e₁ := (1 : A₁) ⊗ₜ[A] e
    let H₁ := targetAwayFactorization F₁ e₁
    let C := A₁ ⊗[A] F.middle
    let D := A₁ ⊗[A] Localization.Away e
    let E := Localization.Away e₁
    letI : Algebra C D := G₁.algebraTarget
    letI : Algebra C E := H₁.algebraTarget
    let eD := targetAwayBaseChangeAlgEquiv F A₁ e;
    letI : Module D (Module.Dual A₁ C ⊗[C] D) :=
      (TensorProduct.comm C (Module.Dual A₁ C) D).toAddEquiv.module D
    letI : Module E (Module.Dual A₁ C ⊗[C] E) :=
      (TensorProduct.comm C (Module.Dual A₁ C) E).toAddEquiv.module E
    letI : Module E (dualizingModule G₁) := Module.compHom _ eD.symm.toRingHom
    letI : Module E (dualizingModule H₁) := dualizingModule.instModule H₁
    dualizingModule G₁ ≃ₗ[Localization.Away e₁] dualizingModule H₁ := by
  let F₁ := FiniteOpenFactorization.baseChange F A₁
  let G := targetAwayFactorization F e
  let G₁ := FiniteOpenFactorization.baseChange G A₁
  let e₁ := (1 : A₁) ⊗ₜ[A] e
  let H₁ := targetAwayFactorization F₁ e₁
  let C := A₁ ⊗[A] F.middle
  let D := A₁ ⊗[A] Localization.Away e
  let E := Localization.Away e₁
  letI : Algebra C D := G₁.algebraTarget
  letI : Algebra C E := H₁.algebraTarget
  let eD : D ≃ₐ[C] E := targetAwayBaseChangeAlgEquiv F A₁ e
  letI : Module D (Module.Dual A₁ C ⊗[C] D) :=
    (TensorProduct.comm C (Module.Dual A₁ C) D).toAddEquiv.module D
  letI : Module E (Module.Dual A₁ C ⊗[C] E) :=
    (TensorProduct.comm C (Module.Dual A₁ C) E).toAddEquiv.module E
  letI : Module E (dualizingModule G₁) := Module.compHom _ eD.symm.toRingHom
  letI : Module D (dualizingModule G₁) := dualizingModule.instModule G₁
  letI : Module E (dualizingModule H₁) := dualizingModule.instModule H₁
  letI : Module E (Module.Dual A₁ C ⊗[C] D) := Module.compHom _ eD.symm.toRingHom
  change Module.Dual A₁ C ⊗[C] D ≃ₗ[E] Module.Dual A₁ C ⊗[C] E
  exact dualizingModule_targetAlgEquiv eD

private theorem targetAwayBaseChangeDualizingEquiv_tmul
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    (F : FiniteOpenFactorization.{u, v, w} A B)
    (A₁ : Type x) [CommRing A₁] [Algebra A A₁] (e : B)
    (φ : Module.Dual A₁ (A₁ ⊗[A] F.middle))
    (d : A₁ ⊗[A] Localization.Away e) :
    let F₁ := FiniteOpenFactorization.baseChange F A₁
    let G := targetAwayFactorization F e
    let G₁ := FiniteOpenFactorization.baseChange G A₁
    let e₁ := (1 : A₁) ⊗ₜ[A] e
    let H₁ := targetAwayFactorization F₁ e₁
    let eD := targetAwayBaseChangeAlgEquiv F A₁ e;
      targetAwayBaseChangeDualizingEquiv F A₁ e
      (dualizingModule.tmul G₁ φ d) =
      dualizingModule.tmul H₁ φ
        ((eD.toRingHom) d) := by
  rfl

end dualizingModule
end Stacks.Discriminant
