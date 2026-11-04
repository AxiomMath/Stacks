module

public import StacksFrontier.AlgebraicGeometry.TwoAffineCech.Family
public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.Cohomology
public import StacksFrontier.AlgebraicGeometry.ProperCohomologyFinite.Basic

/-!
# The cohomology of a base change to a field, read on the two-term Čech complex

Let `f : X ⟶ Spec A` be separated with a covering `U` of `X` by two affine opens, `F` a
quasi-coherent `𝒪_X`-module, and `X_K ⟶ X` the base change along a ring map `φ : A ⟶ K` to a field.
Then the cohomology of `F_K` on `X_K`, as a `K`-vector space
(`AlgebraicGeometry.cohomologyOverField`), is the kernel (degree `0`) and the cokernel (degree `1`)
of the base change `cechD ⊗_A K` of the two-term Čech differential of `F` on `X`, and it vanishes
in degrees `≥ 2`.

## Main results

* `Stacks.TwoAffineCech.cohomologyOverFieldZeroEquiv`: `H⁰(X_K, F_K)` is the kernel of
  `cechD ⊗_A K`.
* `Stacks.TwoAffineCech.cohomologyOverFieldOneEquiv`: `H¹(X_K, F_K)` is the cokernel of
  `cechD ⊗_A K`.
* `Stacks.TwoAffineCech.isZero_cohomologyOverField_of_two_le`: `Hⁿ(X_K, F_K) = 0` for `n ≥ 2`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open scoped TensorProduct

universe u

namespace Stacks.TwoAffineCech

/-! ### Kernels and cokernels transported along isomorphisms of complexes -/

section Linear

variable {R : Type u} [CommRing R] {C₀ C₁ D₀ D₁ : Type u} [AddCommGroup C₀] [AddCommGroup C₁]
  [AddCommGroup D₀] [AddCommGroup D₁] [Module R C₀] [Module R C₁] [Module R D₀] [Module R D₁]
  (d : C₀ →ₗ[R] C₁) (d' : D₀ →ₗ[R] D₁) (e₀ : C₀ ≃ₗ[R] D₀) (e₁ : C₁ ≃ₗ[R] D₁)
  (hd : e₁.toLinearMap ∘ₗ d = d' ∘ₗ e₀.toLinearMap)
include hd

/-- Kernels of conjugate maps are isomorphic. -/
def kerEquivOfComm : LinearMap.ker d ≃ₗ[R] LinearMap.ker d' :=
  e₀.ofSubmodules _ _ (by
    ext y
    rw [Submodule.mem_map_equiv, LinearMap.mem_ker, LinearMap.mem_ker,
      ← LinearEquiv.map_eq_zero_iff e₁,
      show e₁ (d (e₀.symm y)) = d' (e₀ (e₀.symm y)) from LinearMap.congr_fun hd _,
      LinearEquiv.apply_symm_apply])

/-- Cokernels of conjugate maps are isomorphic. -/
def cokerEquivOfComm : (C₁ ⧸ LinearMap.range d) ≃ₗ[R] (D₁ ⧸ LinearMap.range d') :=
  Submodule.Quotient.equiv _ _ e₁ (by
    rw [← LinearMap.range_comp, hd, LinearMap.range_comp_of_range_eq_top _ e₀.range])

end Linear

/-! ### Base change to a field -/

variable {A K : Type u} [CommRing A] [Field K] (φ : A →+* K)
  {X X' : Scheme.{u}} (f : X ⟶ Spec (.of A)) (f' : X' ⟶ Spec (.of K)) (g : X' ⟶ X)
  (hsq : IsPullback g f' f (Spec.map (CommRingCat.ofHom φ)))
  (U : Cover.{u} → X.Opens) (F : X.Modules) [IsSeparated f] [F.IsQuasicoherent]
  (hU : (⊤ : X.Opens) = ⨆ i, U i) (hUaff : ∀ i, IsAffineOpen (U i))

include hsq in
/-- The base change `f'` of the separated morphism `f` is separated. -/
theorem isSeparated_of_isPullback : IsSeparated f' :=
  MorphismProperty.of_isPullback hsq inferInstance

include hU in
/-- The preimages `g ⁻¹ᵁ U i` cover `X'`. -/
theorem top_eq_iSup_preimage : (⊤ : X'.Opens) = ⨆ i, g ⁻¹ᵁ U i := by
  rw [← Scheme.Hom.preimage_iSup, ← hU, Scheme.Hom.preimage_top]

omit [IsSeparated f] in
include hsq hUaff in
/-- The preimage under `g` of each affine open `U i` is affine. -/
theorem isAffineOpen_preimage (i : Cover.{u}) : IsAffineOpen (g ⁻¹ᵁ U i) :=
  Stacks.Cech.isAffineOpen_preimage_of_isPullback φ f f' g hsq (hUaff i)

/-- The cohomology over the field `K`, in the spelling of `AlgebraicGeometry.cohomologyOverField`,
is the cohomology read over the base ring through `Stacks.Cech.globalRingHom`. -/
theorem cohomologyOverField_eq (M : X'.Modules) (n : ℕ) :
    cohomologyOverField K f' M n =
      (ModuleCat.restrictScalars.{u} (Stacks.Cech.globalRingHom f').hom).obj
        ((((AlgebraicGeometry.moduleGlobalSections X')).rightDerived n).obj M) := by
  rw [cohomologyOverField_eq_restrictScalars_appTop]
  rfl

include hsq hU hUaff in
/-- **`H⁰` of the base change to a field is the kernel of the base-changed Čech differential.** -/
def cohomologyOverFieldZeroEquiv :
    letI : Algebra A K := φ.toAlgebra
    cohomologyOverField K f' ((Scheme.Modules.pullback g).obj F) 0 ≃ₗ[K]
      LinearMap.ker ((cechD f U F).baseChange K) :=
  letI : Algebra A K := φ.toAlgebra
  have : IsSeparated f' := isSeparated_of_isPullback φ f f' g hsq
  have : ((Scheme.Modules.pullback g).obj F).IsQuasicoherent := inferInstance
  ((eqToIso (cohomologyOverField_eq f' ((Scheme.Modules.pullback g).obj F) 0)) ≪≫
    cohomologyZeroIso f' (fun i => g ⁻¹ᵁ U i) ((Scheme.Modules.pullback g).obj F)
      (top_eq_iSup_preimage g U hU)
      (isAffineOpen_preimage φ f f' g hsq U hUaff)).toLinearEquiv.trans
    (kerEquivOfComm _ _ (baseChangeEquiv φ f f' g hsq U F hUaff 0)
      (baseChangeEquiv φ f f' g hsq U F hUaff 1) (baseChangeEquiv_comm φ f f' g hsq U F hUaff)).symm

include hsq hU hUaff in
/-- **`H¹` of the base change to a field is the cokernel of the base-changed Čech
differential.** -/
def cohomologyOverFieldOneEquiv :
    letI : Algebra A K := φ.toAlgebra
    cohomologyOverField K f' ((Scheme.Modules.pullback g).obj F) 1 ≃ₗ[K]
      (K ⊗[A] (Stacks.Cech.alternatingCechModuleComplex f U F).X 1 ⧸
        LinearMap.range ((cechD f U F).baseChange K)) :=
  letI : Algebra A K := φ.toAlgebra
  have : IsSeparated f' := isSeparated_of_isPullback φ f f' g hsq
  have : ((Scheme.Modules.pullback g).obj F).IsQuasicoherent := inferInstance
  ((eqToIso (cohomologyOverField_eq f' ((Scheme.Modules.pullback g).obj F) 1)) ≪≫
    cohomologyOneIso f' (fun i => g ⁻¹ᵁ U i) ((Scheme.Modules.pullback g).obj F)
      (top_eq_iSup_preimage g U hU)
      (isAffineOpen_preimage φ f f' g hsq U hUaff)).toLinearEquiv.trans
    (cokerEquivOfComm _ _ (baseChangeEquiv φ f f' g hsq U F hUaff 0)
      (baseChangeEquiv φ f f' g hsq U F hUaff 1) (baseChangeEquiv_comm φ f f' g hsq U F hUaff)).symm

include hsq hU hUaff in
/-- The cohomology of the base change to a field vanishes in degrees `≥ 2`. -/
theorem isZero_cohomologyOverField_of_two_le {n : ℕ} (hn : 2 ≤ n) :
    IsZero (cohomologyOverField K f' ((Scheme.Modules.pullback g).obj F) n) := by
  have : IsSeparated f' := isSeparated_of_isPullback φ f f' g hsq
  rw [cohomologyOverField_eq]
  exact isZero_cohomology_of_two_le f' (fun i => g ⁻¹ᵁ U i) ((Scheme.Modules.pullback g).obj F)
    (top_eq_iSup_preimage g U hU) (isAffineOpen_preimage φ f f' g hsq U hUaff) hn

end Stacks.TwoAffineCech
