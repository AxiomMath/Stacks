module

public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.RingTheory.Extension.Cotangent.Basic
public import StacksFrontier.Deformation.Artin.Infinitesimal.TangentFlatBaseChange
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Derivations along a ring map, and their flat base change

Let `Λ → P` be a ring map, let `P → A` be a ring map and let `M` be an `A`-module. The
`Λ`-derivations of `P` with values in `M`, regarded as a `P`-module through `P → A`, form an
`A`-module `chartDer Λ u M`, `u : P → A`. These are the tangent vectors `T_x(M)` of an affine
scheme `Spec P` over `Spec Λ` at the point `x : Spec A → Spec P`: a morphism `Spec A[M] → Spec P`
over `Spec Λ` restricting to `x` is a ring map `P → A[M]` lifting `P → A`, that is
`a ↦ (x(a), D a)` for a derivation `D`.

They are represented by the `A`-module `A ⊗_P Ω_{P/Λ}`, which is finitely presented when `P` is
of finite presentation over `Λ`. By Stacks 087R the representation commutes with flat base
change: for a flat `A`-algebra `C` and `N = C ⊗_A M`,
`C ⊗_A chartDer Λ u M = chartDer Λ (C ∘ u) N`. This is the algebra of the third paragraph of the
proof of Stacks 0DNT, `T_x(M) ⊗_A C = T_y(M ⊗_A C)` for an algebraic space locally of finite
presentation, at an affine chart.

## Main definitions

* `chartDer Λ u M` — the `Λ`-derivations of `P` into `M` along `u : P → A`, as additive maps.
* `chartDerEquiv` — their identification with `Hom_A(A ⊗_P Ω_{P/Λ}, M)`.

## Main results

* `exists_chartDer_flatBaseChange` — for `P` of finite presentation over `Λ` and a flat
  `A`-algebra `C`, there is a `C`-linear isomorphism `C ⊗_A chartDer Λ u M ≅ chartDer Λ (C ∘ u) N`
  sending `c ⊗ D` to `a ↦ c ⊗ D a`.

## Implementation notes

The module `M` carries its `P`- and `Λ`-module structures as instances compatible with the
`A`-module structure, rather than having them induced: this is the form in which Mathlib's
universal property of Kähler differentials applies. In applications they are installed locally
from the ring maps.
-/

@[expose] public noncomputable section

open TensorProduct

namespace StacksDraft.ChartDerivation

universe u₁ u₂ u₃ u₄ u₅ u₆

variable (Λ : Type u₁) {P : Type u₂} {A : Type u₃} [CommRing Λ] [CommRing P] [CommRing A]
  [Algebra Λ P]

/-- **The derivations of a chart along a point.** The `Λ`-derivations of `P` with values in an
`A`-module `M`, where `P` acts on `M` through `u : P → A`, as additive maps `P → M`. -/
@[sga "3 VIIA 1.2.0" "special case"]
public def chartDer (u : P →+* A) (M : Type u₄) [AddCommGroup M] [Module A M] :
    Submodule A (P →+ M) where
  carrier := {D | (∀ a b, D (a * b) = u a • D b + u b • D a) ∧
    ∀ c : Λ, D (algebraMap Λ P c) = 0}
  add_mem' := by
    rintro D E ⟨hD, hD'⟩ ⟨hE, hE'⟩
    refine ⟨fun a b => ?_, fun c => ?_⟩
    · simp only [AddMonoidHom.add_apply, hD, hE, smul_add]
      abel
    · simp [hD', hE']
  zero_mem' := ⟨fun _ _ => by simp, fun _ => rfl⟩
  smul_mem' := by
    rintro r D ⟨hD, hD'⟩
    refine ⟨fun a b => ?_, fun c => ?_⟩
    · simp only [AddMonoidHom.smul_apply, hD, smul_add]
      rw [smul_comm r (u a), smul_comm r (u b)]
    · simp [hD']

variable {Λ}

/-- A derivation of the chart satisfies the Leibniz rule along `u`:
`D (a * b) = u a • D b + u b • D a`. -/
public theorem chartDer_leibniz {u : P →+* A} {M : Type u₄} [AddCommGroup M] [Module A M]
    (D : chartDer Λ u M) (a b : P) :
    (D : P →+ M) (a * b) = u a • (D : P →+ M) b + u b • (D : P →+ M) a := D.2.1 a b

/-- A derivation of the chart vanishes on the image of `Λ` in `P`. -/
public theorem chartDer_algebraMap {u : P →+* A} {M : Type u₄} [AddCommGroup M] [Module A M]
    (D : chartDer Λ u M) (c : Λ) : (D : P →+ M) (algebraMap Λ P c) = 0 := D.2.2 c

variable (Λ P A) [Algebra P A]

section Equiv

variable (M : Type u₄) [AddCommGroup M] [Module A M] [Module P M] [IsScalarTower P A M]
  [Module Λ M] [IsScalarTower Λ P M]

/-- A derivation of the chart, as a `Λ`-derivation of `P` into `M` in Mathlib's sense. -/
public def chartDerToDerivation (D : chartDer Λ (algebraMap P A) M) : Derivation Λ P M where
  toFun := D.1
  map_add' := D.1.map_add
  map_smul' c a := by
    change D.1 (c • a) = c • D.1 a
    rw [Algebra.smul_def, chartDer_leibniz, chartDer_algebraMap, smul_zero, add_zero,
      algebraMap_smul]
    exact IsScalarTower.algebraMap_smul P c (D.1 a)
  map_one_eq_zero' := by
    change D.1 1 = 0
    simpa using chartDer_leibniz D 1 1
  leibniz' a b := by
    change D.1 (a * b) = a • D.1 b + b • D.1 a
    rw [chartDer_leibniz, algebraMap_smul, algebraMap_smul]

/-- The derivation of the chart attached to a map out of `A ⊗_P Ω_{P/Λ}`. -/
public def chartDerOfHom (φ : A ⊗[P] Ω[P⁄Λ] →ₗ[A] M) : chartDer Λ (algebraMap P A) M :=
  ⟨{ toFun := fun a => φ (1 ⊗ₜ KaehlerDifferential.D Λ P a)
     map_zero' := by simp
     map_add' := fun a b => by simp [tmul_add] },
    fun a b => by
      change φ (1 ⊗ₜ KaehlerDifferential.D Λ P (a * b)) =
        algebraMap P A a • φ (1 ⊗ₜ KaehlerDifferential.D Λ P b) +
          algebraMap P A b • φ (1 ⊗ₜ KaehlerDifferential.D Λ P a)
      rw [Derivation.leibniz, tmul_add, map_add, tmul_smul, tmul_smul,
        ← algebraMap_smul A a, ← algebraMap_smul A b, map_smul, map_smul],
    fun c => by
      change φ (1 ⊗ₜ KaehlerDifferential.D Λ P (algebraMap Λ P c)) = 0
      rw [Derivation.map_algebraMap, tmul_zero, map_zero]⟩

omit [Module P M] [IsScalarTower P A M] [Module Λ M] [IsScalarTower Λ P M] in
/-- The derivation `chartDerOfHom Λ P A M φ` sends `a : P` to `φ (1 ⊗ₜ d a)`. -/
@[simp]
public theorem chartDerOfHom_apply (φ : A ⊗[P] Ω[P⁄Λ] →ₗ[A] M) (a : P) :
    ((chartDerOfHom Λ P A M φ : chartDer Λ (algebraMap P A) M) : P →+ M) a =
      φ (1 ⊗ₜ KaehlerDifferential.D Λ P a) := rfl

/-- **The derivations of a chart are represented by `A ⊗_P Ω_{P/Λ}`.** -/
public def chartDerEquiv : (A ⊗[P] Ω[P⁄Λ] →ₗ[A] M) ≃ₗ[A] chartDer Λ (algebraMap P A) M where
  toFun := chartDerOfHom Λ P A M
  map_add' φ ψ := by
    ext
    rfl
  map_smul' r φ := by
    ext
    rfl
  invFun D := LinearMap.liftBaseChange A (chartDerToDerivation Λ P A M D).liftKaehlerDifferential
  left_inv φ := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro a ω
    rw [LinearMap.liftBaseChange_tmul]
    have hω : (chartDerToDerivation Λ P A M (chartDerOfHom Λ P A M φ)).liftKaehlerDifferential =
        (φ.restrictScalars P).comp (TensorProduct.mk P A Ω[P⁄Λ] 1) := by
      apply Derivation.liftKaehlerDifferential_unique
      ext b
      change (chartDerToDerivation Λ P A M (chartDerOfHom Λ P A M φ)).liftKaehlerDifferential
          (KaehlerDifferential.D Λ P b) = φ (1 ⊗ₜ KaehlerDifferential.D Λ P b)
      rw [Derivation.liftKaehlerDifferential_comp_D]
      rfl
    rw [hω]
    change a • φ (1 ⊗ₜ ω) = φ (a ⊗ₜ ω)
    rw [← map_smul, smul_tmul', smul_eq_mul, mul_one]
  right_inv D := by
    ext a
    change LinearMap.liftBaseChange A
      (chartDerToDerivation Λ P A M D).liftKaehlerDifferential
        (1 ⊗ₜ KaehlerDifferential.D Λ P a) = D.1 a
    rw [LinearMap.liftBaseChange_tmul, one_smul, Derivation.liftKaehlerDifferential_comp_D]
    rfl

/-- `chartDerEquiv` sends `φ : A ⊗_P Ω_{P/Λ} →ₗ[A] M` to the derivation `a ↦ φ (1 ⊗ₜ d a)`. -/
@[simp]
public theorem chartDerEquiv_apply (φ : A ⊗[P] Ω[P⁄Λ] →ₗ[A] M) (a : P) :
    ((chartDerEquiv Λ P A M φ : chartDer Λ (algebraMap P A) M) : P →+ M) a =
      φ (1 ⊗ₜ KaehlerDifferential.D Λ P a) := rfl

/-- The inverse of `chartDerEquiv` recovers a derivation of the chart on `1 ⊗ₜ d a`. -/
private theorem chartDerEquiv_symm_apply (D : chartDer Λ (algebraMap P A) M) (a : P) :
    (chartDerEquiv Λ P A M).symm D (1 ⊗ₜ KaehlerDifferential.D Λ P a) = (D : P →+ M) a := by
  rw [← chartDerEquiv_apply, LinearEquiv.apply_symm_apply]

end Equiv

section BaseChange

variable (C : Type u₅) [CommRing C] [Algebra A C] [Algebra P C] [IsScalarTower P A C]
  (M : Type u₄) [AddCommGroup M] [Module A M] [Module P M] [IsScalarTower P A M]
  [Module Λ M] [IsScalarTower Λ P M]
  (N : Type u₆) [AddCommGroup N] [Module C N] [Module P N] [IsScalarTower P C N]
  [Module Λ N] [IsScalarTower Λ P N]

/-- **Flat base change for the derivations of a chart** (the algebra of Stacks 0DNT at an affine
chart). Let `P` be of finite presentation over `Λ`, let `C` be a flat `A`-algebra and let `N` be
identified with `C ⊗_A M`. Then there is a `C`-linear isomorphism
`C ⊗_A chartDer Λ (algebraMap P A) M ≅ chartDer Λ (algebraMap P C) N` sending `c ⊗ D` to
`a ↦ c ⊗ D a`.

The derivations are `Hom_A(A ⊗_P Ω_{P/Λ}, -)`, the representing module is finitely presented
because `P` is of finite presentation over `Λ`, and the conclusion is the flat base change of
`Hom` out of a finitely presented module, Stacks 087R. -/
@[sga "3 III 0.14" "special case"]
public theorem exists_chartDer_flatBaseChange [Module.Flat A C] [Algebra.FinitePresentation Λ P]
    (hMN : (C ⊗[A] M) ≃ₗ[C] N) :
    ∃ e : (C ⊗[A] chartDer Λ (algebraMap P A) M) ≃ₗ[C] chartDer Λ (algebraMap P C) N,
      ∀ (c : C) (D : chartDer Λ (algebraMap P A) M) (a : P),
        ((e (c ⊗ₜ[A] D) : chartDer Λ (algebraMap P C) N) : P →+ N) a =
          hMN (c ⊗ₜ[A] (D : P →+ M) a) := by
  obtain ⟨e, he, -⟩ := StacksDraft.PseudoCoherence.existsUnique_homFlatBaseChange A C
    (A ⊗[P] Ω[P⁄Λ]) M (C ⊗[P] Ω[P⁄Λ]) N (chartDer Λ (algebraMap P A) M)
    (chartDer Λ (algebraMap P C) N) inferInstance
    (TensorProduct.AlgebraTensorModule.cancelBaseChange P A C C Ω[P⁄Λ])
    (chartDerEquiv Λ P A M).symm (chartDerEquiv Λ P C N).symm hMN
  refine ⟨e, fun c D a => ?_⟩
  have h := he c 1 D (1 ⊗ₜ KaehlerDifferential.D Λ P a)
  rw [TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul, one_smul, one_mul] at h
  rwa [chartDerEquiv_symm_apply, chartDerEquiv_symm_apply] at h

end BaseChange

end StacksDraft.ChartDerivation

end
