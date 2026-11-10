module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import Mathlib.LinearAlgebra.Contraction
public import StacksCore.Tactic.StacksAttribute

/-!
# Left duals in the monoidal category of modules

Let `R` be a commutative ring and let `M` be an `R`-module. If `N` together with a coevaluation
`η : R → M ⊗_R N` and an evaluation `ε : N ⊗_R M → R` is a left dual of `M` in the monoidal
category of `R`-modules, then `M` and `N` are finite projective, the map
`Hom_R(M, R) → N`, `λ ↦ (λ ⊗ 1)(η)` is an isomorphism, and under this identification `ε` is
ordinary evaluation of a functional on a vector.

## Main definitions

* `ModuleCat.LeftDual.IsModuleDualPairing`: the two module triangle identities, stated for
  coevaluation at `1` and curried evaluation, with independent universes.
* `ModuleCat.LeftDual.coevaluationContraction`: contraction of a coevaluation tensor with a
  functional on its first factor.
* `ModuleCat.LeftDual.linearDualToLeftDual`: the canonical map from the linear dual to a chosen
  left dual.
* `ModuleCat.LeftDual.identityTensor`: the tensor in `M⁺ ⊗_R M` representing `id_M` for a finite
  projective module `M`.
* `ModuleCat.LeftDual.finiteProjectiveExactPairing`: the canonical exact pairing of a finite
  projective module with its linear dual.

## Main results

* `ModuleCat.LeftDual.finite_projective_and_linearDual_equiv_of_isModuleDualPairing`: from the
  two triangle identities, both modules are finite projective, contraction with coevaluation is
  an equivalence onto the chosen dual, and evaluation is application.
* `ModuleCat.LeftDual.finite_projective_and_linearDual_equiv_of_exactPairing`: the categorical
  formulation, for an `ExactPairing` in `ModuleCat R`.
* `ModuleCat.LeftDual.isModuleDualPairing_of_finite_projective`: the converse construction, which
  exhibits the linear dual of a finite projective module as a left dual.

## Implementation notes

The algebraic formulation permits independent universes for the ring and both modules.
`IsModuleDualPairing` records exactly the two triangle identities, using the value of
coevaluation at `1` and the curried evaluation. Its categorical specialization uses Mathlib's
`ExactPairing`; Mathlib's monoidal structure on `ModuleCat R` requires the ring and objects to
share a universe. The canonical map contracts the first tensor factor with a functional.

The converse construction `isModuleDualPairing_of_finite_projective` and the exact pairing
`finiteProjectiveExactPairing` built from it are supporting API for the dualizability of bounded
complexes of finite projective modules; they are not additional assertions of the tagged result.

## References

* [The Stacks Project, Tag 0FNJ](https://stacks.math.columbia.edu/tag/0FNJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory TensorProduct

universe u v w

namespace ModuleCat.LeftDual

/-- Contraction of a coevaluation tensor with a functional on its first factor. -/
def coevaluationContraction (R : Type u) (M : Type v) (N : Type w) [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (t : M ⊗[R] N) : Module.Dual R M →ₗ[R] N :=
  (TensorProduct.lid R N).toLinearMap.comp <|
    (LinearMap.applyₗ (R := R) t).comp <|
      (LinearMap.applyₗ (R := R) (LinearMap.id : N →ₗ[R] N)).comp <|
        TensorProduct.mapBilinear (RingHom.id R) M N R N

/-- Contraction with a coevaluation tensor applies the functional to the first tensor factor. -/
@[simp]
theorem coevaluationContraction_apply (R : Type u) (M : Type v) (N : Type w) [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (t : M ⊗[R] N) (f : Module.Dual R M) :
    coevaluationContraction R M N t f =
      TensorProduct.lid R N (TensorProduct.map f LinearMap.id t) := rfl

/-- The two triangle identities for modules, allowing independent universes. The map
`ε : N →ₗ[R] Module.Dual R M` is the curried evaluation, and `t` is coevaluation at `1`. -/
def IsModuleDualPairing (R : Type u) (M : Type v) (N : Type w) [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (t : M ⊗[R] N) (ε : N →ₗ[R] Module.Dual R M) : Prop :=
  dualTensorHom R M M (TensorProduct.map ε LinearMap.id (TensorProduct.comm R M N t)) =
      LinearMap.id ∧
    (coevaluationContraction R M N t).comp ε = LinearMap.id

/-- Evaluating the curried evaluation on a contraction reorders into an application of the
functional to the composite built from the coevaluation tensor. -/
private theorem evaluation_coevaluationContraction (R : Type u) (M : Type v) (N : Type w)
    [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (t : M ⊗[R] N) (ε : N →ₗ[R] Module.Dual R M) (f : Module.Dual R M) (m : M) :
    ε (coevaluationContraction R M N t f) m =
      f (dualTensorHom R M M
        (TensorProduct.map ε LinearMap.id (TensorProduct.comm R M N t)) m) := by
  induction t using TensorProduct.inductionOn with
  | tmul m' n => simp [mul_comm]
  | add x y hx hy => simp_all

/-- A module dual pairing makes both modules finite projective and identifies the given
left dual with the linear dual by contraction with coevaluation. This is the algebraic form of
`finite_projective_and_linearDual_equiv_of_exactPairing`, with independent universes. -/
theorem finite_projective_and_linearDual_equiv_of_isModuleDualPairing
    (R : Type u) (M : Type v) (N : Type w) [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (t : M ⊗[R] N) (ε : N →ₗ[R] Module.Dual R M) (h : IsModuleDualPairing R M N t ε) :
    Module.Finite R M ∧ Module.Projective R M ∧
      Module.Finite R N ∧ Module.Projective R N ∧
        ∃ e : Module.Dual R M ≃ₗ[R] N,
          e.toLinearMap = coevaluationContraction R M N t ∧
            ∀ (n : N) (m : M), ε n m = e.symm n m := by
  have hx : (1 : M →ₗ[R] M) ∈ (dualTensorHom R M M).range :=
    ⟨_, h.1⟩
  have : Module.Finite R M := Module.Finite.of_one_mem_range_dualTensorHom hx
  have : Module.Projective R M := Module.Projective.of_one_mem_range_dualTensorHom hx
  have hdual (f : Module.Dual R M) : ε (coevaluationContraction R M N t f) = f := by
    ext m
    rw [evaluation_coevaluationContraction, h.1, LinearMap.id_apply]
  let e : Module.Dual R M ≃ₗ[R] N :=
    { coevaluationContraction R M N t with
      invFun := ε
      left_inv := hdual
      right_inv := LinearMap.congr_fun h.2 }
  have : Module.Finite R N := Module.Finite.of_surjective e.toLinearMap e.surjective
  have : Module.Projective R N := .of_split ε e.toLinearMap h.2
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance, e, rfl, fun _ _ => rfl⟩

/-- The canonical linear map from the linear dual of `M` to a chosen left dual `N`, obtained by
applying the functional to the first factor of the coevaluation element. -/
def linearDualToLeftDual (R M N : Type u) [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [ExactPairing (ModuleCat.of R M) (ModuleCat.of R N)] : Module.Dual R M →ₗ[R] N :=
  coevaluationContraction R M N
    ((η_ (ModuleCat.of R M) (ModuleCat.of R N)).hom (1 : R))

/-- The canonical map to a left dual is contraction of the coevaluation tensor at `1`. -/
@[simp]
theorem linearDualToLeftDual_apply (R M N : Type u) [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [ExactPairing (ModuleCat.of R M) (ModuleCat.of R N)] (l : Module.Dual R M) :
    linearDualToLeftDual R M N l =
      TensorProduct.lid R N
        (TensorProduct.map l LinearMap.id
          ((η_ (ModuleCat.of R M) (ModuleCat.of R N)).hom (1 : R))) := rfl

/-- Elementwise form of the evaluation `ev` induced by `ε`, whiskered on the right by `N`,
after the inverse associator. -/
private theorem lift_whiskerRight_associator_inv_tmul_aux {R M N : Type u} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (ε : N →ₗ[R] Module.Dual R M) (ev : ModuleCat.of R N ⊗ ModuleCat.of R M ⟶ 𝟙_ (ModuleCat R))
    (hev : ev = ModuleCat.ofHom (TensorProduct.lift ε)) (x : M ⊗[R] N) (n : N) :
    (ev ▷ ModuleCat.of R N).hom
        ((α_ (ModuleCat.of R N) (ModuleCat.of R M) (ModuleCat.of R N)).inv.hom
          (n ⊗ₜ[R] x)) =
      1 ⊗ₜ[R] coevaluationContraction R M N x (ε n) := by
  subst hev
  induction x using TensorProduct.inductionOn with
  | tmul m n' =>
      change (ε n m) ⊗ₜ[R] n' =
        1 ⊗ₜ[R] coevaluationContraction R M N (m ⊗ₜ[R] n') (ε n)
      simp only [coevaluationContraction_apply, TensorProduct.map_tmul,
        LinearMap.id_apply, TensorProduct.lid_tmul, TensorProduct.tmul_smul,
        TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  | add x y hx hy =>
      simp only [coevaluationContraction_apply] at *
      simp only [tmul_add, map_add, hx, hy]

/-- Elementwise form of the evaluation `ev` induced by `ε`, whiskered on the left by `M`,
after the associator. -/
private theorem lift_whiskerLeft_associator_hom_tmul_aux {R M N : Type u} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (ε : N →ₗ[R] Module.Dual R M) (ev : ModuleCat.of R N ⊗ ModuleCat.of R M ⟶ 𝟙_ (ModuleCat R))
    (hev : ev = ModuleCat.ofHom (TensorProduct.lift ε)) (x : M ⊗[R] N) (m : M) :
    (ModuleCat.of R M ◁ ev).hom
        ((α_ (ModuleCat.of R M) (ModuleCat.of R N) (ModuleCat.of R M)).hom.hom
          (x ⊗ₜ[R] m)) =
      (dualTensorHom R M M
        (TensorProduct.map ε LinearMap.id (TensorProduct.comm R M N x)) m) ⊗ₜ[R] (1 : R) := by
  subst hev
  induction x using TensorProduct.inductionOn with
  | tmul m' n =>
      change m' ⊗ₜ[R] (ε n m) = _
      simp only [TensorProduct.comm_tmul, TensorProduct.map_tmul, LinearMap.id_apply,
        dualTensorHom_apply]
      rw [TensorProduct.smul_tmul]
      simp
  | add x y hx hy =>
      simp only [add_tmul, map_add, LinearMap.add_apply, hx, hy]

section ExactPairing

variable (R M N : Type u) [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [ExactPairing (ModuleCat.of R M) (ModuleCat.of R N)]

/-- The curried evaluation of a categorical exact pairing, as a linear map into the linear
dual. -/
private def pairingToDual : N →ₗ[R] Module.Dual R M :=
  TensorProduct.curry
    ((ε_ (ModuleCat.of R M) (ModuleCat.of R N)).hom : N ⊗[R] M →ₗ[R] R)

/-- The first triangle identity of a categorical exact pairing, read off elementwise on `M`. -/
private lemma triangle_M (m : M) :
    dualTensorHom R M M
      (TensorProduct.map (pairingToDual R M N) LinearMap.id
        (TensorProduct.comm R M N
          ((ExactPairing.coevaluation (ModuleCat.of R M) (ModuleCat.of R N)).hom 1))) m = m := by
  let t := (ExactPairing.coevaluation
    (ModuleCat.of R M) (ModuleCat.of R N)).hom (1 : R)
  have h := congrArg (fun f => f.hom ((1 : R) ⊗ₜ[R] m))
    (ExactPairing.evaluation_coevaluation
      (ModuleCat.of R M) (ModuleCat.of R N))
  simp only [ModuleCat.comp_apply] at h
  rw [ModuleCat.MonoidalCategory.whiskerRight_apply,
    ModuleCat.MonoidalCategory.leftUnitor_hom_apply,
    ModuleCat.MonoidalCategory.rightUnitor_inv_apply] at h
  have ht := lift_whiskerLeft_associator_hom_tmul_aux (pairingToDual R M N)
    (ε_ (ModuleCat.of R M) (ModuleCat.of R N))
    (ModuleCat.hom_ext (TensorProduct.ext' fun _ _ => rfl)) t m
  rw [ht] at h
  simpa using congrArg (TensorProduct.rid R M) h

/-- The second triangle identity of a categorical exact pairing, read off elementwise on `N`. -/
private lemma triangle_N (n : N) :
    linearDualToLeftDual R M N (pairingToDual R M N n) = n := by
  let t := (ExactPairing.coevaluation
    (ModuleCat.of R M) (ModuleCat.of R N)).hom (1 : R)
  have h := congrArg (fun f => f.hom (n ⊗ₜ[R] (1 : R)))
    (ExactPairing.coevaluation_evaluation
      (ModuleCat.of R M) (ModuleCat.of R N))
  simp only [ModuleCat.comp_apply] at h
  change (TensorProduct.lid R N)
    (TensorProduct.map (pairingToDual R M N n) LinearMap.id t) = n
  rw [ModuleCat.MonoidalCategory.whiskerLeft_apply,
    ModuleCat.MonoidalCategory.rightUnitor_hom_apply,
    ModuleCat.MonoidalCategory.leftUnitor_inv_apply] at h
  have ht := lift_whiskerRight_associator_inv_tmul_aux (pairingToDual R M N)
    (ε_ (ModuleCat.of R M) (ModuleCat.of R N))
    (ModuleCat.hom_ext (TensorProduct.ext' fun _ _ => rfl)) t n
  rw [ht] at h
  simpa using congrArg (TensorProduct.lid R N) h

/-- If `N` is a left dual of `M` in the monoidal category of `R`-modules, then `M` and `N` are
finite projective. Moreover, contraction with the coevaluation identifies `M⁺` with `N`, and
under this identification the given evaluation map sends `n ⊗ m` to the value at `m` of the
functional corresponding to `n`. -/
@[stacks 0FNJ]
theorem finite_projective_and_linearDual_equiv_of_exactPairing :
    Module.Finite R M ∧ Module.Projective R M ∧
      Module.Finite R N ∧ Module.Projective R N ∧
        ∃ e : Module.Dual R M ≃ₗ[R] N,
          e.toLinearMap = linearDualToLeftDual R M N ∧
            ∀ (n : N) (m : M),
              (ε_ (ModuleCat.of R M) (ModuleCat.of R N)).hom (n ⊗ₜ[R] m) = e.symm n m :=
  finite_projective_and_linearDual_equiv_of_isModuleDualPairing R M N
    ((η_ (ModuleCat.of R M) (ModuleCat.of R N)).hom 1) (pairingToDual R M N)
    ⟨LinearMap.ext (triangle_M R M N), LinearMap.ext (triangle_N R M N)⟩

end ExactPairing

/-- The tensor representing the identity of a finite projective module. -/
noncomputable def identityTensor (R : Type u) (M : Type v) [CommRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Projective R M] :
    Module.Dual R M ⊗[R] M :=
  (dualTensorHomEquiv R M M).symm LinearMap.id

/-- The identity tensor is sent to the identity by the contraction `M⁺ ⊗ M → End M`. -/
@[simp]
theorem dualTensorHom_identityTensor (R : Type u) (M : Type v) [CommRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Projective R M] :
    dualTensorHom R M M (identityTensor R M) = LinearMap.id :=
  (dualTensorHomEquiv R M M).apply_symm_apply LinearMap.id

/-- Contracting the swapped identity tensor with a functional returns that functional. -/
@[simp]
theorem coevaluationContraction_identityTensor (R : Type u) (M : Type v) [CommRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Projective R M]
    (f : Module.Dual R M) :
    coevaluationContraction R M (Module.Dual R M)
      (TensorProduct.comm R _ _ (identityTensor R M)) f = f := by
  ext m
  simpa using evaluation_coevaluationContraction R M (Module.Dual R M)
    (TensorProduct.comm R _ _ (identityTensor R M)) LinearMap.id f m

/-- Evaluation and the identity tensor satisfy both triangle identities for every finite
projective module, with no restriction on the universes of the ring and module. -/
theorem isModuleDualPairing_of_finite_projective (R : Type u) (M : Type v) [CommRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Projective R M] :
    IsModuleDualPairing R M (Module.Dual R M)
      (TensorProduct.comm R _ _ (identityTensor R M)) LinearMap.id :=
  ⟨by simp, LinearMap.ext (coevaluationContraction_identityTensor R M)⟩

/-- Elementwise form of the evaluation `ev` induced by `ε`, whiskered on the right by `N`,
after the inverse associator. -/
theorem lift_whiskerRight_associator_inv_tmul {R M N : Type u} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (ε : N →ₗ[R] Module.Dual R M) (ev : ModuleCat.of R N ⊗ ModuleCat.of R M ⟶ 𝟙_ (ModuleCat R))
    (hev : ev = ModuleCat.ofHom (TensorProduct.lift ε)) (x : M ⊗[R] N) (n : N) :
    (ev ▷ ModuleCat.of R N).hom
        ((α_ (ModuleCat.of R N) (ModuleCat.of R M) (ModuleCat.of R N)).inv.hom
          (n ⊗ₜ[R] x)) =
      1 ⊗ₜ[R] coevaluationContraction R M N x (ε n) :=
  lift_whiskerRight_associator_inv_tmul_aux ε ev hev x n

/-- Elementwise form of the evaluation `ev` induced by `ε`, whiskered on the left by `M`,
after the associator. -/
theorem lift_whiskerLeft_associator_hom_tmul {R M N : Type u} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (ε : N →ₗ[R] Module.Dual R M) (ev : ModuleCat.of R N ⊗ ModuleCat.of R M ⟶ 𝟙_ (ModuleCat R))
    (hev : ev = ModuleCat.ofHom (TensorProduct.lift ε)) (x : M ⊗[R] N) (m : M) :
    (ModuleCat.of R M ◁ ev).hom
        ((α_ (ModuleCat.of R M) (ModuleCat.of R N) (ModuleCat.of R M)).hom.hom
          (x ⊗ₜ[R] m)) =
      (dualTensorHom R M M
        (TensorProduct.map ε LinearMap.id (TensorProduct.comm R M N x)) m) ⊗ₜ[R] (1 : R) :=
  lift_whiskerLeft_associator_hom_tmul_aux ε ev hev x m

/-- Package the elementwise triangle identities as a categorical exact pairing. -/
@[instance_reducible]
def exactPairingOfIsModuleDualPairing (R M N : Type u) [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (t : M ⊗[R] N) (ε : N →ₗ[R] Module.Dual R M)
    (h : IsModuleDualPairing R M N t ε) :
    ExactPairing (ModuleCat.of R M) (ModuleCat.of R N) := by
  let η : 𝟙_ (ModuleCat R) ⟶ ModuleCat.of R M ⊗ ModuleCat.of R N :=
    ModuleCat.ofHom (LinearMap.toSpanSingleton R _ t)
  let ev : ModuleCat.of R N ⊗ ModuleCat.of R M ⟶ 𝟙_ (ModuleCat R) :=
    ModuleCat.ofHom (TensorProduct.lift ε)
  have hη (r : R) : η.hom r = r • t := rfl
  refine ⟨η, ev, ?_, ?_⟩
  · apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro n r
    change (ev ▷ ModuleCat.of R N).hom
      ((α_ (ModuleCat.of R N) (ModuleCat.of R M) (ModuleCat.of R N)).inv.hom
        (n ⊗ₜ[R] η.hom r)) = 1 ⊗ₜ[R] (r • n)
    rw [hη, TensorProduct.tmul_smul, map_smul, map_smul,
      lift_whiskerRight_associator_inv_tmul ε ev rfl]
    change r • (1 ⊗ₜ[R] ((coevaluationContraction R M N t).comp ε) n) = _
    rw [h.2]
    exact (TensorProduct.tmul_smul _ _ _).symm
  · apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro r m
    change (ModuleCat.of R M ◁ ev).hom
      ((α_ (ModuleCat.of R M) (ModuleCat.of R N) (ModuleCat.of R M)).hom.hom
        (η.hom r ⊗ₜ[R] m)) = (r • m) ⊗ₜ[R] 1
    rw [hη, ← TensorProduct.smul_tmul', map_smul, map_smul,
      lift_whiskerLeft_associator_hom_tmul ε ev rfl, h.1]
    exact TensorProduct.smul_tmul' _ _ _

/-- Evaluation and coevaluation of a finite projective module define its canonical left dual. -/
@[instance_reducible, sga "5 IIIB 5.0" "special case"]
noncomputable def finiteProjectiveExactPairing (R M : Type u) [CommRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Projective R M] :
    ExactPairing (ModuleCat.of R M) (ModuleCat.of R (Module.Dual R M)) :=
  exactPairingOfIsModuleDualPairing R M (Module.Dual R M)
    (TensorProduct.comm R _ _ (identityTensor R M)) LinearMap.id
    (isModuleDualPairing_of_finite_projective R M)

/-- Evaluation of the canonical pairing applies the functional to the vector. -/
@[simp, sga "5 IIIB 5.0" "special case"]
theorem finiteProjectiveExactPairing_evaluation (R M : Type u) [CommRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Projective R M]
    (f : Module.Dual R M) (m : M) :
    (@ExactPairing.evaluation _ _ _ _ _ (finiteProjectiveExactPairing R M)).hom
      (f ⊗ₜ[R] m) = f m := rfl

/-- Coevaluation of the canonical pairing sends `1` to the swapped identity tensor. -/
@[simp]
theorem finiteProjectiveExactPairing_coevaluation_one (R M : Type u) [CommRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Projective R M] :
    (@ExactPairing.coevaluation _ _ _ _ _ (finiteProjectiveExactPairing R M)).hom 1 =
      TensorProduct.comm R _ _ (identityTensor R M) := by
  change (1 : R) • (TensorProduct.comm R _ _ (identityTensor R M)) = _
  exact one_smul R _

/-- The entire evaluation map is the canonical contraction. -/
@[simp, sga "5 IIIB 5.0" "special case"]
theorem finiteProjectiveExactPairing_evaluation_hom (R M : Type u) [CommRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Projective R M] :
    (@ExactPairing.evaluation _ _ _ _ _ (finiteProjectiveExactPairing R M)).hom =
      contractLeft R M := rfl

/-- Coevaluation sends a scalar to that scalar times the identity tensor, with factors swapped. -/
@[simp]
theorem finiteProjectiveExactPairing_coevaluation (R M : Type u) [CommRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Projective R M] (r : R) :
    (@ExactPairing.coevaluation _ _ _ _ _ (finiteProjectiveExactPairing R M)).hom r =
      r • TensorProduct.comm R _ _ (identityTensor R M) := rfl

/-- For the canonical pairing, the identification with the linear dual is the identity. -/
theorem finiteProjectiveExactPairing_linearDualToLeftDual (R M : Type u) [CommRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Projective R M] :
    letI := finiteProjectiveExactPairing R M
    linearDualToLeftDual R M (Module.Dual R M) = LinearMap.id := by
  let := finiteProjectiveExactPairing R M
  change coevaluationContraction R M (Module.Dual R M)
    ((η_ (ModuleCat.of R M) (ModuleCat.of R (Module.Dual R M))).hom 1) = LinearMap.id
  rw [finiteProjectiveExactPairing_coevaluation_one]
  exact LinearMap.ext (coevaluationContraction_identityTensor R M)

end ModuleCat.LeftDual

end
