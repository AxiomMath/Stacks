module

public import Mathlib.RingTheory.MvPowerSeries.Basic
public import StacksFrontier.Examples.Flatness.OrdinaryCone.SegreBaseChange

/-!
# The completed Segre product over `k` is a base change of the one over `k₀`

Let `k` be a flat algebra over a commutative ring `k₀` (for instance a field extension), write
`A = k₀[X₀, X₁, X₂]`, `P = k[X₀, X₁, X₂]` and `R = k⟦X₀, X₁, X₂⟧`, and let `Γ_{k₀}` and `Γ_k` be
the Segre products of the ordinary cone, as algebras over `A` and `P`. Then
`R ⊗_A Γ_{k₀} ≅ R ⊗_P Γ_k` as `R`-algebras: `R ⊗_A Γ_{k₀} ≅ R ⊗_P (P ⊗_A Γ_{k₀})`, and
`P ⊗_A Γ_{k₀} ≅ k ⊗_{k₀} Γ_{k₀} ≅ Γ_k` compatibly with the maps from `P`.

## Main definitions

* `Stacks.Examples.OrdinaryCone.polySegreEquiv`: the `P`-algebra isomorphism
  `P ⊗_A Γ_{k₀} ≃ Γ_k`.
* `Stacks.Examples.OrdinaryCone.completedSegreBaseChange`: the `R`-algebra isomorphism
  `R ⊗_A Γ_{k₀} ≃ R ⊗_P Γ_k`.

## Main results

* `Stacks.Examples.OrdinaryCone.completedSegreBaseChange_tmul`: the isomorphism sends `r ⊗ g` to
  `r ⊗ g`, where `Γ_{k₀} → Γ_k` is induced by `k₀ → k`.
* `Stacks.Examples.OrdinaryCone.isEmpty_algHom_completedSegre`: an `R`-algebra receiving no
  `R`-algebra map from `R ⊗_P Γ_k` receives none from `R ⊗_A Γ_{k₀}` either.
-/

@[expose] public section

namespace Stacks.Examples.OrdinaryCone

open MvPolynomial TensorProduct

variable (k₀ k : Type*) [CommRing k₀] [CommRing k] [Algebra k₀ k]

/-- The ring map `k₀[X] → k⟦X⟧` factors through `k[X]`. -/
theorem algebraMap_mvPolynomial_mvPowerSeries_comp (σ : Type*) :
    (algebraMap (MvPolynomial σ k) (MvPowerSeries σ k)).comp
        (MvPolynomial.map (algebraMap k₀ k)) =
      algebraMap (MvPolynomial σ k₀) (MvPowerSeries σ k) := by
  refine MvPolynomial.ringHom_ext (fun a ↦ ?_) fun i ↦ ?_
  · simp [MvPowerSeries.algebraMap_apply', MvPowerSeries.map_C]
  · simp [MvPowerSeries.algebraMap_apply', MvPowerSeries.map_X]

section Poly

attribute [local instance] MvPolynomial.algebraMvPolynomial

/-- The map `k ⊗_{k₀} Γ_{k₀} → k[X₀, X₁, X₂] ⊗_{k₀[X₀, X₁, X₂]} Γ_{k₀}`. -/
noncomputable def segreToPolyTensor :
    k ⊗[k₀] segre k₀ →ₐ[k] MvPolynomial (Fin 3) k ⊗[MvPolynomial (Fin 3) k₀] segre k₀ :=
  Algebra.TensorProduct.lift (Algebra.ofId k _)
    ((Algebra.TensorProduct.includeRight (R := MvPolynomial (Fin 3) k₀)
      (A := MvPolynomial (Fin 3) k)).restrictScalars k₀) fun _ _ ↦ .all _ _

/-- The map `segreToPolyTensor` is surjective. -/
theorem segreToPolyTensor_surjective : Function.Surjective (segreToPolyTensor k₀ k) := by
  intro x
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | add x y hx hy =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact ⟨a + b, map_add _ _ _⟩
  | tmul p g =>
    induction p using MvPolynomial.induction_on generalizing g with
    | C a =>
      refine ⟨a ⊗ₜ g, ?_⟩
      simp [segreToPolyTensor, Algebra.TensorProduct.algebraMap_apply,
        Algebra.TensorProduct.tmul_mul_tmul, MvPolynomial.algebraMap_eq]
    | add p q hp hq =>
      obtain ⟨a, ha⟩ := hp g
      obtain ⟨b, hb⟩ := hq g
      exact ⟨a + b, by rw [map_add, ha, hb, add_tmul]⟩
    | mul_X p i hp =>
      obtain ⟨a, ha⟩ := hp (algebraMap (MvPolynomial (Fin 3) k₀) (segre k₀) (X i) * g)
      refine ⟨a, ?_⟩
      rw [ha, ← Algebra.smul_def, ← TensorProduct.smul_tmul, Algebra.smul_def,
        MvPolynomial.algebraMap_def, MvPolynomial.map_X, mul_comm]

/-- The `k[X₀, X₁, X₂]`-algebra map `k[X₀, X₁, X₂] ⊗_{k₀[X₀, X₁, X₂]} Γ_{k₀} → Γ_k`. -/
noncomputable def polySegreHom [Module.Flat k₀ k] :
    MvPolynomial (Fin 3) k ⊗[MvPolynomial (Fin 3) k₀] segre k₀ →ₐ[MvPolynomial (Fin 3) k]
      segre k :=
  letI : Algebra (MvPolynomial (Fin 3) k₀) (segre k) :=
    ((algebraMap (MvPolynomial (Fin 3) k) (segre k)).comp
      (algebraMap (MvPolynomial (Fin 3) k₀) (MvPolynomial (Fin 3) k))).toAlgebra
  haveI : IsScalarTower (MvPolynomial (Fin 3) k₀) (MvPolynomial (Fin 3) k) (segre k) :=
    IsScalarTower.of_algebraMap_eq' rfl
  Algebra.TensorProduct.lift (Algebra.ofId _ _)
    { segreMap k₀ k with
      commutes' := fun p ↦ segreMap_algebraMap k₀ k p } fun _ _ ↦ .all _ _

/-- `polySegreHom` sends `p ⊗ g` to `p · segreMap k₀ k g`. -/
@[simp]
theorem polySegreHom_tmul [Module.Flat k₀ k] (p : MvPolynomial (Fin 3) k) (g : segre k₀) :
    polySegreHom k₀ k (p ⊗ₜ g) =
      algebraMap (MvPolynomial (Fin 3) k) (segre k) p * segreMap k₀ k g :=
  rfl

/-- The composite of `segreToPolyTensor` and `polySegreHom` is the base change isomorphism
`segreBaseChange : k ⊗_{k₀} Γ_{k₀} ≃ Γ_k`. -/
theorem polySegreHom_comp_segreToPolyTensor [Module.Flat k₀ k] :
    ((polySegreHom k₀ k).restrictScalars k).comp (segreToPolyTensor k₀ k) =
      (segreBaseChange k₀ k : k ⊗[k₀] segre k₀ →ₐ[k] segre k) := by
  refine Algebra.TensorProduct.ext' fun a g ↦ ?_
  simp [segreToPolyTensor, Algebra.TensorProduct.algebraMap_apply,
    Algebra.TensorProduct.tmul_mul_tmul, IsScalarTower.algebraMap_apply k
      (MvPolynomial (Fin 3) k) (segre k)]

/-- For `k` flat over `k₀`, the map `polySegreHom` is bijective. -/
theorem polySegreHom_bijective [Module.Flat k₀ k] : Function.Bijective (polySegreHom k₀ k) := by
  have h (x : k ⊗[k₀] segre k₀) :
      polySegreHom k₀ k (segreToPolyTensor k₀ k x) = segreBaseChange k₀ k x :=
    congrArg (fun f ↦ f x) (polySegreHom_comp_segreToPolyTensor k₀ k)
  refine ⟨fun x y hxy ↦ ?_, fun z ↦ ?_⟩
  · obtain ⟨x, rfl⟩ := segreToPolyTensor_surjective k₀ k x
    obtain ⟨y, rfl⟩ := segreToPolyTensor_surjective k₀ k y
    rw [h, h] at hxy
    rw [(segreBaseChange k₀ k).injective hxy]
  · obtain ⟨x, rfl⟩ := (segreBaseChange k₀ k).surjective z
    exact ⟨_, h x⟩

/-- `k[X₀, X₁, X₂] ⊗_{k₀[X₀, X₁, X₂]} Γ_{k₀} ≃ Γ_k` as `k[X₀, X₁, X₂]`-algebras. -/
noncomputable def polySegreEquiv [Module.Flat k₀ k] :
    MvPolynomial (Fin 3) k ⊗[MvPolynomial (Fin 3) k₀] segre k₀ ≃ₐ[MvPolynomial (Fin 3) k]
      segre k :=
  AlgEquiv.ofBijective (polySegreHom k₀ k) (polySegreHom_bijective k₀ k)

/-- The algebras `k₀[X₀, X₁, X₂] → k[X₀, X₁, X₂] → k⟦X₀, X₁, X₂⟧` form a scalar tower. -/
theorem isScalarTower_mvPolynomial_mvPowerSeries :
    IsScalarTower (MvPolynomial (Fin 3) k₀) (MvPolynomial (Fin 3) k) (MvPowerSeries (Fin 3) k) :=
  IsScalarTower.of_algebraMap_eq' (algebraMap_mvPolynomial_mvPowerSeries_comp k₀ k (Fin 3)).symm

attribute [local instance] isScalarTower_mvPolynomial_mvPowerSeries

/-- `R ⊗_A Γ_{k₀} ≃ R ⊗_P (P ⊗_A Γ_{k₀})` for `A = k₀[X₀, X₁, X₂]`, `P = k[X₀, X₁, X₂]`,
`R = k⟦X₀, X₁, X₂⟧`. -/
noncomputable def completedSegreCancel :
    MvPowerSeries (Fin 3) k ⊗[MvPolynomial (Fin 3) k₀] segre k₀ ≃ₐ[MvPowerSeries (Fin 3) k]
      MvPowerSeries (Fin 3) k ⊗[MvPolynomial (Fin 3) k]
        (MvPolynomial (Fin 3) k ⊗[MvPolynomial (Fin 3) k₀] segre k₀) :=
  (Algebra.TensorProduct.cancelBaseChange (MvPolynomial (Fin 3) k₀) (MvPolynomial (Fin 3) k)
    (MvPowerSeries (Fin 3) k) (MvPowerSeries (Fin 3) k) (segre k₀)).symm

end Poly

/-- For `k` flat over `k₀`, `A = k₀[X₀, X₁, X₂]`, `P = k[X₀, X₁, X₂]` and `R = k⟦X₀, X₁, X₂⟧`:
`R ⊗_A Γ_{k₀} ≃ R ⊗_P Γ_k` as `R`-algebras. -/
noncomputable def completedSegreBaseChange [Module.Flat k₀ k] :
    MvPowerSeries (Fin 3) k ⊗[MvPolynomial (Fin 3) k₀] segre k₀ ≃ₐ[MvPowerSeries (Fin 3) k]
      MvPowerSeries (Fin 3) k ⊗[MvPolynomial (Fin 3) k] segre k :=
  (completedSegreCancel k₀ k).trans
    (Algebra.TensorProduct.congr AlgEquiv.refl (polySegreEquiv k₀ k))

/-- `completedSegreBaseChange` sends `r ⊗ g` to `r ⊗ segreMap k₀ k g`. -/
@[simp]
theorem completedSegreBaseChange_tmul [Module.Flat k₀ k] (r : MvPowerSeries (Fin 3) k)
    (g : segre k₀) : completedSegreBaseChange k₀ k (r ⊗ₜ g) = r ⊗ₜ segreMap k₀ k g := by
  simp [completedSegreBaseChange, completedSegreCancel, polySegreEquiv]

/-- An `R`-algebra `T` receiving no `R`-algebra map from `R ⊗_P Γ_k` receives none from
`R ⊗_A Γ_{k₀}`, for `A = k₀[X₀, X₁, X₂]`, `P = k[X₀, X₁, X₂]` and `R = k⟦X₀, X₁, X₂⟧`. -/
theorem isEmpty_algHom_completedSegre [Module.Flat k₀ k] (T : Type*) [Semiring T]
    [Algebra (MvPowerSeries (Fin 3) k) T] :
    IsEmpty
        (MvPowerSeries (Fin 3) k ⊗[MvPolynomial (Fin 3) k] segre k →ₐ[MvPowerSeries (Fin 3) k] T) →
      IsEmpty
        (MvPowerSeries (Fin 3) k ⊗[MvPolynomial (Fin 3) k₀] segre k₀ →ₐ[MvPowerSeries (Fin 3) k]
          T) :=
  fun _ ↦ ⟨fun f ↦ IsEmpty.false (f.comp (completedSegreBaseChange k₀ k).symm.toAlgHom)⟩

end Stacks.Examples.OrdinaryCone
