module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GroupCohomology.DiscreteModules
public import StacksFrontier.AlgebraicGeometry.ContinuousCohomology.DiscreteCompletedGroupAlgebraModule
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.UnibranchContinuousModules

/-!
# Twisting a finite continuous module by `Hom(A, -)`

Let `R` be a ring, not necessarily commutative, `Γ` a topological group and `A` a finite abelian
group with a continuous action of `Γ`. For a finite `R`-module `M` with a continuous action of
`Γ`, the group `Hom_ℤ(A, M)` is again a finite `R`-module (through `M`) with a continuous action
of `Γ` by conjugation, `(γ · φ)(a) = γ · φ(γ⁻¹ · a)`.

For `A = μ_n(k̄)`, `n = #Λ`, with `Γ = π₁(X, η̄)` acting through `Gal(k^{sep}/k)`, this is the Tate
twist `M(-1) = Hom(μ_n, M)` of [Stacks, Tag 03VK] and [Stacks, Tag 03VM]: on a module with trivial
geometric action, `σ` acts through `χ_cycl(σ)⁻¹ σ` (Section 03VJ), and it is the twist in which
`H²_c(X_k̄, ℱ_ρ) = M_{π₁(X_k̄)}(-1)` holds without a choice of root of unity.

## Main definitions

* `Stacks.GroupCohomology.homTwistRepresentation`: the conjugation action on `A →+ M`.
* `Stacks.GroupCohomology.homTwistFunctor`: `M ↦ Hom_ℤ(A, M)` on finite `R`-`Γ`-modules.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w w'

namespace Stacks.GroupCohomology

open Stacks.ContinuousCohomology (continuousModuleRho_mul_apply continuousModuleRho_one_apply)

open scoped Stacks.DiscreteModuleTopology

variable (R : Type u) [Ring R] {Γ : Type v} [Group Γ] [TopologicalSpace Γ]
  (A : Stacks.Injectives.ContinuousModule.{0, v, w'} ℤ Γ)

/-- Conjugation by `γ` on `Hom_ℤ(A, M)`: `φ ↦ γ ∘ φ ∘ γ⁻¹`. -/
def homTwistConj (M : Stacks.Injectives.ContinuousModule.{u, v, w} R Γ) (γ : Γ) :
    (A.obj.obj.V →+ M.obj.obj.V) →ₗ[R] (A.obj.obj.V →+ M.obj.obj.V) where
  toFun φ := (M.obj.obj.ρ γ).hom.toAddMonoidHom.comp (φ.comp (A.obj.obj.ρ γ⁻¹).hom.toAddMonoidHom)
  map_add' _ _ := AddMonoidHom.ext fun _ ↦ map_add (M.obj.obj.ρ γ).hom _ _
  map_smul' r _ := AddMonoidHom.ext fun _ ↦ map_smul (M.obj.obj.ρ γ).hom r _

/-- The conjugate `γ · φ` evaluated at `a` is `γ · φ(γ⁻¹ · a)`. -/
lemma homTwistConj_apply (M : Stacks.Injectives.ContinuousModule.{u, v, w} R Γ) (γ : Γ)
    (φ : A.obj.obj.V →+ M.obj.obj.V) (a : A.obj.obj.V) :
    homTwistConj R A M γ φ a = (M.obj.obj.ρ γ).hom (φ ((A.obj.obj.ρ γ⁻¹).hom a)) :=
  rfl

/-- **The conjugation action of `Γ` on `Hom_ℤ(A, M)`.** -/
def homTwistRepresentation (M : Stacks.Injectives.ContinuousModule.{u, v, w} R Γ) :
    Representation R Γ (A.obj.obj.V →+ M.obj.obj.V) where
  toFun γ := homTwistConj R A M γ
  map_one' := LinearMap.ext fun φ ↦ AddMonoidHom.ext fun a ↦ by
    change (M.obj.obj.ρ 1).hom (φ ((A.obj.obj.ρ 1⁻¹).hom a)) = φ a
    rw [inv_one, continuousModuleRho_one_apply, continuousModuleRho_one_apply]
  map_mul' g h := LinearMap.ext fun φ ↦ AddMonoidHom.ext fun a ↦ by
    change (M.obj.obj.ρ (g * h)).hom (φ ((A.obj.obj.ρ (g * h)⁻¹).hom a)) =
      (M.obj.obj.ρ g).hom ((M.obj.obj.ρ h).hom (φ ((A.obj.obj.ρ h⁻¹).hom
        ((A.obj.obj.ρ g⁻¹).hom a))))
    rw [mul_inv_rev, continuousModuleRho_mul_apply, continuousModuleRho_mul_apply]

variable [IsTopologicalGroup Γ]

/-- **The conjugation action on `Hom_ℤ(A, M)` is continuous for `A` finite.** -/
lemma isContinuous_homTwistRepresentation [Finite A.obj.obj.V]
    (M : Stacks.Injectives.ContinuousModule.{u, v, w} R Γ) :
    (actionOfRepresentation R Γ (A.obj.obj.V →+ M.obj.obj.V)
      (homTwistRepresentation R A M)).IsContinuous := by
  rw [isContinuous_actionOfRepresentation_iff]
  intro φ
  let H : Subgroup Γ :=
    { carrier := {γ | homTwistRepresentation R A M γ φ = φ}
      mul_mem' := fun {a b} ha hb ↦ by
        show homTwistRepresentation R A M (a * b) φ = φ
        rw [map_mul, Module.End.mul_apply, show homTwistRepresentation R A M b φ = φ from hb, ha]
      one_mem' := by
        show homTwistRepresentation R A M 1 φ = φ
        rw [map_one]; rfl
      inv_mem' := fun {a} ha ↦ by
        show homTwistRepresentation R A M a⁻¹ φ = φ
        conv_lhs => rw [← (show homTwistRepresentation R A M a φ = φ from ha)]
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]; rfl }
  show IsOpen (H : Set Γ)
  let O : Set Γ := ⋂ a : A.obj.obj.V, ({γ | (A.obj.obj.ρ γ).hom a = a} ∩
    {γ | (M.obj.obj.ρ γ).hom (φ a) = φ a})
  have hO : IsOpen O := isOpen_iInter_of_finite fun a ↦
    (isOpen_stabilizer ℤ Γ A a).inter (isOpen_stabilizer R Γ M (φ a))
  have h1 : (1 : Γ) ∈ O := Set.mem_iInter.mpr fun a ↦
    ⟨continuousModuleRho_one_apply ℤ A a, continuousModuleRho_one_apply R M (φ a)⟩
  refine Subgroup.isOpen_of_mem_nhds H (Filter.mem_of_superset (hO.mem_nhds h1) ?_)
  intro γ hγ
  have hγ' := Set.mem_iInter.mp hγ
  show homTwistRepresentation R A M γ φ = φ
  refine AddMonoidHom.ext fun a ↦ ?_
  show (M.obj.obj.ρ γ).hom (φ ((A.obj.obj.ρ γ⁻¹).hom a)) = φ a
  have hinv : (A.obj.obj.ρ γ⁻¹).hom a = a := by
    conv_lhs => rw [← (hγ' a).1]
    rw [← continuousModuleRho_mul_apply, inv_mul_cancel, continuousModuleRho_one_apply]
  rw [hinv]
  exact (hγ' a).2

variable [Finite A.obj.obj.V]

/-- **`Hom_ℤ(A, M)` as a finite `R`-module with a continuous action of `Γ`**, for `A` finite. -/
def homTwistObj (M : FiniteTypeContinuousModule.{u, v, w} R Γ) [Finite R] :
    FiniteTypeContinuousModule.{u, v, max w' w} R Γ :=
  ⟨ofRepresentation (homTwistRepresentation R A M.obj)
      (isContinuous_homTwistRepresentation R A M.obj), by
    have : Module.Finite R M.obj.obj.obj.V := M.property
    have : Finite M.obj.obj.obj.V := Module.finite_of_finite R
    have : Finite (A.obj.obj.V →+ M.obj.obj.obj.V) :=
      Finite.of_injective _ DFunLike.coe_injective
    change Module.Finite R (A.obj.obj.V →+ M.obj.obj.obj.V)
    exact Module.Finite.of_finite⟩

/-- **The twist `M ↦ Hom_ℤ(A, M)`** of finite `R`-modules with a continuous action of `Γ`, for a
finite `ℤ`-`Γ`-module `A`; for `A = μ_n` it is the Tate twist `M(-1)`. -/
def homTwistFunctor [Finite R] :
    FiniteTypeContinuousModule.{u, v, w} R Γ ⥤ FiniteTypeContinuousModule.{u, v, max w' w} R Γ where
  obj M := homTwistObj R A M
  map {M _} f := ObjectProperty.homMk ((homEquiv R Γ _ _).symm
    ⟨{ toFun φ := f.hom.hom.hom.hom.hom.toAddMonoidHom.comp φ
       map_add' _ _ := AddMonoidHom.comp_add _ _ _
       map_smul' r (φ : A.obj.obj.V →+ M.obj.obj.obj.V) := AddMonoidHom.ext fun a ↦
         map_smul f.hom.hom.hom.hom.hom r (φ a) },
      fun γ (φ : A.obj.obj.V →+ M.obj.obj.obj.V) ↦ AddMonoidHom.ext fun a ↦
        ConcreteCategory.congr_hom (f.hom.hom.hom.comm γ) (φ ((A.obj.obj.ρ γ⁻¹).hom a))⟩)
  map_id _ := rfl
  map_comp _ _ := rfl

end Stacks.GroupCohomology

end
