module

public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.IsTensorProduct
public import Mathlib.LinearAlgebra.FreeModule.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Faithfully flat descent of freeness of rank one

Let `R → S` be a faithfully flat ring map with `S` local, and let `M` be an `R`-module whose base
change `S ⊗[R] M` is free of rank one over `S`. Then `M` is free of rank one over `R`.

## Main results

* `Module.nonempty_linearEquiv_of_tensorProduct_of_faithfullyFlat`: freeness of rank one descends
  along a faithfully flat ring map with local target, stated for the base change `S ⊗[R] M`.
* `Module.nonempty_linearEquiv_of_isBaseChange_of_faithfullyFlat`: the same statement for an
  abstract base change `f : M →ₗ[R] N`.
* `Module.free_of_tensorProduct_of_faithfullyFlat`: the freeness half of the conclusion, as a
  `Module.Free` instance-shaped statement.
-/

@[expose] public section

universe u v w

open scoped TensorProduct

namespace Module

variable {R : Type u} [CommRing R] (S : Type v) [CommRing S] [Algebra R S]
  {M : Type w} [AddCommGroup M] [Module R M]

/-- If `S` is a local ring and `e : S ⊗[R] M ≃ₗ[S] S`, then some element `x` of `M` has
`e (1 ⊗ₜ x)` a unit of `S`. -/
private theorem exists_isUnit_apply_one_tmul [IsLocalRing S] (e : S ⊗[R] M ≃ₗ[S] S) :
    ∃ x : M, IsUnit (e (1 ⊗ₜ[R] x)) := by
  by_contra hcon
  simp only [not_exists] at hcon
  have hmem : ∀ x : M, e (1 ⊗ₜ[R] x) ∈ IsLocalRing.maximalIdeal S := fun x =>
    (IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr (hcon x))
  have key : ∀ v : S ⊗[R] M, e v ∈ IsLocalRing.maximalIdeal S := by
    intro v
    induction v using TensorProduct.induction_on with
    | zero => simp
    | tmul s x =>
      rw [TensorProduct.tmul_eq_smul_one_tmul, map_smul]
      exact Submodule.smul_mem _ _ (hmem x)
    | add v w hv hw =>
      rw [map_add]
      exact Submodule.add_mem _ hv hw
  have h1 : (1 : S) ∈ IsLocalRing.maximalIdeal S := by simpa using key (e.symm 1)
  exact mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal _).mp h1) isUnit_one

/-- For `x : M` with `e (1 ⊗ₜ x)` a unit of `S`, the base change along `R → S` of the map
`r ↦ r • x` is bijective. -/
private theorem bijective_lTensor_toSpanSingleton {x : M} (e : S ⊗[R] M ≃ₗ[S] S)
    (hx : IsUnit (e (1 ⊗ₜ[R] x))) :
    Function.Bijective ((LinearMap.toSpanSingleton R M x).lTensor S) := by
  have hcomp : ∀ v : S ⊗[R] R, e (((LinearMap.toSpanSingleton R M x).lTensor S) v) =
      (TensorProduct.rid R S) v * e (1 ⊗ₜ[R] x) := by
    intro v
    induction v using TensorProduct.induction_on with
    | zero => simp
    | tmul s r =>
      rw [LinearMap.lTensor_tmul, LinearMap.toSpanSingleton_apply, ← TensorProduct.smul_tmul,
        TensorProduct.tmul_eq_smul_one_tmul, map_smul, TensorProduct.rid_tmul, smul_eq_mul]
    | add v w hv hw =>
      rw [map_add, map_add, hv, hw, map_add, add_mul]
  obtain ⟨u, hu⟩ := hx
  have hmul : Function.Bijective (fun s : S => s * (u : S)) := by
    refine ⟨fun a b hab => ?_, fun c => ⟨c * (↑u⁻¹ : S), ?_⟩⟩
    · simpa using congrArg (fun t : S => t * (↑u⁻¹ : S)) hab
    · simp [mul_assoc]
  have h1 : Function.Bijective
      (⇑e ∘ ⇑((LinearMap.toSpanSingleton R M x).lTensor S)) := by
    have hfun : ⇑e ∘ ⇑((LinearMap.toSpanSingleton R M x).lTensor S) =
        (fun s : S => s * (u : S)) ∘ ⇑(TensorProduct.rid R S) := by
      funext v
      simpa [hu] using hcomp v
    rw [hfun]
    exact hmul.comp (TensorProduct.rid R S).bijective
  exact (Function.Bijective.of_comp_iff' e.bijective _).mp h1

/-- **Faithfully flat descent of freeness of rank one.** Let `R → S` be a faithfully flat ring
map with `S` a local ring, and let `M` be an `R`-module whose base change `S ⊗[R] M` is free of
rank one over `S`. Then `M` is free of rank one over `R`. -/
@[sga "1 VIII 1.11" "special case", sga "4½ Arcata 1.4.2" "special case"]
theorem nonempty_linearEquiv_of_tensorProduct_of_faithfullyFlat [IsLocalRing S]
    [Module.FaithfullyFlat R S] (e : S ⊗[R] M ≃ₗ[S] S) : Nonempty (M ≃ₗ[R] R) := by
  obtain ⟨x, hx⟩ := exists_isUnit_apply_one_tmul S e
  have hbij : Function.Bijective (LinearMap.toSpanSingleton R M x) :=
    (Module.FaithfullyFlat.lTensor_bijective_iff_bijective R S _).mp
      (bijective_lTensor_toSpanSingleton S e hx)
  exact ⟨(LinearEquiv.ofBijective (LinearMap.toSpanSingleton R M x) hbij).symm⟩

/-- **Faithfully flat descent of freeness of rank one**, for an abstract base change. Let `R → S`
be a faithfully flat ring map with `S` a local ring, let `M` be an `R`-module and let
`f : M →ₗ[R] N` exhibit the `S`-module `N` as the base change of `M` along `R → S`. If `N` is
free of rank one over `S`, then `M` is free of rank one over `R`. -/
@[sga "4½ Arcata 1.4.2" "special case"]
theorem nonempty_linearEquiv_of_isBaseChange_of_faithfullyFlat [IsLocalRing S]
    [Module.FaithfullyFlat R S] {N : Type*} [AddCommGroup N] [Module R N] [Module S N]
    [IsScalarTower R S N] (f : M →ₗ[R] N) (h : IsBaseChange S f) (e : N ≃ₗ[S] S) :
    Nonempty (M ≃ₗ[R] R) :=
  nonempty_linearEquiv_of_tensorProduct_of_faithfullyFlat S (h.equiv.trans e)

/-- The freeness half of `Module.nonempty_linearEquiv_of_tensorProduct_of_faithfullyFlat`: an
`R`-module whose base change to a faithfully flat local `S` is free of rank one is free. -/
theorem free_of_tensorProduct_of_faithfullyFlat [IsLocalRing S] [Module.FaithfullyFlat R S]
    (e : S ⊗[R] M ≃ₗ[S] S) : Module.Free R M := by
  obtain ⟨g⟩ := nonempty_linearEquiv_of_tensorProduct_of_faithfullyFlat S e
  exact Module.Free.of_equiv g.symm

end Module

end
