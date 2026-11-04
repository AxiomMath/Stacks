module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Tensoring an extension of scalars with a module flat over the base ring

Let `φ : R →+* A` be a homomorphism of commutative rings and `M` an `A`-module which is flat as
an `R`-module through `φ`. Then the functor `N ↦ M ⊗_A (A ⊗_R N)` from `R`-modules to `A`-modules
is exact: it is right exact as a composite of left adjoints, and it preserves injections because
`M ⊗_A (A ⊗_R N) = M ⊗_R N`, naturally in `N`
(`TensorProduct.AlgebraTensorModule.cancelBaseChange`).

## Main results

* `ModuleCat.preservesFiniteLimits_extendScalars_comp_tensorLeft`
* `ModuleCat.preservesFiniteColimits_extendScalars_comp_tensorLeft`
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped TensorProduct

universe u

namespace ModuleCat

variable {R A : Type u} [CommRing R] [CommRing A] (φ : R →+* A) (M : ModuleCat.{u} A)

/-- `N ↦ M ⊗_A (A ⊗_R N)` preserves finite colimits: both factors are left adjoints. -/
theorem preservesFiniteColimits_extendScalars_comp_tensorLeft :
    PreservesFiniteColimits (ModuleCat.extendScalars.{u, u, u} φ ⋙
      (curriedTensor (ModuleCat.{u} A)).obj M) := by
  have : PreservesColimitsOfSize.{0, 0} (ModuleCat.extendScalars.{u, u, u} φ) :=
    (ModuleCat.extendRestrictScalarsAdj φ).leftAdjoint_preservesColimits
  have : PreservesColimitsOfSize.{0, 0} ((curriedTensor (ModuleCat.{u} A)).obj M) :=
    (ihom.adjunction M).leftAdjoint_preservesColimits
  exact comp_preservesFiniteColimits _ _

/-- The underlying map of `M ⊗_A (A ⊗_R f)` is injective when `f` is and `M` is flat over `R`. -/
theorem injective_extendScalars_comp_tensorLeft_map
    (hM : letI : Module R M := Module.compHom M φ; Module.Flat R M)
    {N N' : ModuleCat.{u} R} (f : N ⟶ N') (hf : Function.Injective f.hom) :
    Function.Injective ((ModuleCat.extendScalars.{u, u, u} φ ⋙
      (curriedTensor (ModuleCat.{u} A)).obj M).map f).hom := by
  let : Algebra R A := φ.toAlgebra
  let : Module R M := Module.compHom M φ
  have : IsScalarTower R A M := ⟨fun r a m => by
    show (φ r * a) • m = φ r • (a • m)
    rw [mul_smul]⟩
  show Function.Injective (⇑(TensorProduct.AlgebraTensorModule.lTensor A M
    (TensorProduct.AlgebraTensorModule.lTensor A A f.hom)))
  have hnat := TensorProduct.AlgebraTensorModule.lTensor_comp_cancelBaseChange R A A (M := M) f.hom
  have hinj : Function.Injective (TensorProduct.AlgebraTensorModule.lTensor A M f.hom) :=
    Module.Flat.lTensor_preserves_injective_linearMap f.hom hf
  intro x y hxy
  have h' : (TensorProduct.AlgebraTensorModule.lTensor A M f.hom ∘ₗ
      (TensorProduct.AlgebraTensorModule.cancelBaseChange R A A M N).toLinearMap) x =
      (TensorProduct.AlgebraTensorModule.lTensor A M f.hom ∘ₗ
        (TensorProduct.AlgebraTensorModule.cancelBaseChange R A A M N).toLinearMap) y := by
    rw [hnat, LinearMap.comp_apply, LinearMap.comp_apply, hxy]
  exact (TensorProduct.AlgebraTensorModule.cancelBaseChange R A A M N).injective (hinj h')

/-- **`N ↦ M ⊗_A (A ⊗_R N)` preserves finite limits when `M` is flat over `R`.** -/
theorem preservesFiniteLimits_extendScalars_comp_tensorLeft
    (hM : letI : Module R M := Module.compHom M φ; Module.Flat R M) :
    PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u} φ ⋙
      (curriedTensor (ModuleCat.{u} A)).obj M) := by
  have := preservesFiniteColimits_extendScalars_comp_tensorLeft φ M
  have hbiprod : PreservesBinaryBiproducts (ModuleCat.extendScalars.{u, u, u} φ ⋙
      (curriedTensor (ModuleCat.{u} A)).obj M) :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  have hadd : (ModuleCat.extendScalars.{u, u, u} φ ⋙
      (curriedTensor (ModuleCat.{u} A)).obj M).Additive :=
    Functor.additive_of_preservesBinaryBiproducts _
  refine (Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono _).2 fun σ hσ => ⟨?_, ?_⟩
  · have := hσ.epi_g
    exact hσ.exact.map_of_epi_of_preservesCokernel (ModuleCat.extendScalars.{u, u, u} φ ⋙
      (curriedTensor (ModuleCat.{u} A)).obj M) inferInstance inferInstance
  · have hmono := hσ.mono_f
    rw [ModuleCat.mono_iff_injective]
    exact injective_extendScalars_comp_tensorLeft_map φ M hM σ.f
      ((ModuleCat.mono_iff_injective _).1 hmono)

end ModuleCat
