/-
Copyright (c) 2026 Stacks Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.Algebra.Exact.Basic
public import Mathlib.LinearAlgebra.Isomorphisms

/-!
# The cokernel of the first term of a short exact sequence of two-term complexes

Consider a commutative diagram of `R`-modules

```
M₀ --dM--> M₁
|α₀        |α₁
P₀ --dP--> P₁
|β₀        |β₁
Q₀ --dQ--> Q₁
```

whose columns are exact (`α₁` injective, `β₀` surjective). If `dP` is surjective, the snake
lemma identifies `coker dM` with `ker dQ / β₀(ker dP)`. This is the piece
`H⁰(P) ⟶ H⁰(Q) ⟶ H¹(M) ⟶ H¹(P) = 0` of the long exact cohomology sequence of a short exact
sequence of sheaves, read on two-term Čech complexes.

## Main definitions

* `Stacks.TwoTermComplex.kerMap`: the map `ker dP ⟶ ker dQ` induced by `β₀`.
* `Stacks.TwoTermComplex.cokerEquivOfExact`: `coker dM ≃ ker dQ / β₀(ker dP)`.
-/

@[expose] public noncomputable section

universe u

namespace Stacks.TwoTermComplex

variable {R : Type*} [CommRing R] {M₀ M₁ P₀ P₁ Q₀ Q₁ : Type*}
  [AddCommGroup M₀] [AddCommGroup M₁] [AddCommGroup P₀] [AddCommGroup P₁] [AddCommGroup Q₀]
  [AddCommGroup Q₁] [Module R M₀] [Module R M₁] [Module R P₀] [Module R P₁] [Module R Q₀]
  [Module R Q₁]
  {dM : M₀ →ₗ[R] M₁} {dP : P₀ →ₗ[R] P₁} {dQ : Q₀ →ₗ[R] Q₁}
  {α₀ : M₀ →ₗ[R] P₀} {α₁ : M₁ →ₗ[R] P₁} {β₀ : P₀ →ₗ[R] Q₀} {β₁ : P₁ →ₗ[R] Q₁}

variable (hβ : dQ ∘ₗ β₀ = β₁ ∘ₗ dP)

/-- The map `ker dP ⟶ ker dQ` induced by `β₀`. -/
def kerMap : LinearMap.ker dP →ₗ[R] LinearMap.ker dQ :=
  β₀.restrict fun p hp => by
    rw [LinearMap.mem_ker] at hp ⊢
    simpa [hp] using LinearMap.congr_fun hβ p

/-- The map `kerMap hβ` sends `p ∈ ker dP` to `β₀ p`. -/
@[simp]
theorem kerMap_apply (p : LinearMap.ker dP) : (kerMap hβ p : Q₀) = β₀ p := rfl

variable (hα : dP ∘ₗ α₀ = α₁ ∘ₗ dM) (hα₁ : Function.Injective α₁)
  (hex₀ : Function.Exact α₀ β₀) (hex₁ : Function.Exact α₁ β₁)
  (hβ₀ : Function.Surjective β₀) (hdP : Function.Surjective dP)

/-- The submodule `W = {p | dQ (β₀ p) = 0}` of `P₀`. -/
abbrev liftSpace : Submodule R P₀ := LinearMap.ker (dQ ∘ₗ β₀)

include hβ hex₁ in
/-- For `p ∈ W`, the element `dP p` lies in the image of `α₁`. -/
theorem dP_mem_range (p : liftSpace (dQ := dQ) (β₀ := β₀)) :
    dP p ∈ LinearMap.range α₁ :=
  (hex₁ _).1 ((LinearMap.congr_fun hβ p).symm.trans p.2)

/-- `W ⟶ M₁`, `p ↦ α₁⁻¹ (dP p)`. -/
def liftToM : liftSpace (dQ := dQ) (β₀ := β₀) →ₗ[R] M₁ :=
  (LinearEquiv.ofInjective α₁ hα₁).symm.toLinearMap ∘ₗ
    (dP ∘ₗ (liftSpace (dQ := dQ) (β₀ := β₀)).subtype).codRestrict (LinearMap.range α₁)
      (fun p => dP_mem_range hβ hex₁ p)

/-- For `p ∈ W`, `α₁ (liftToM p) = dP p`. -/
theorem α₁_liftToM (p : liftSpace (dQ := dQ) (β₀ := β₀)) :
    α₁ (liftToM hβ hα₁ hex₁ p) = dP p :=
  congrArg Subtype.val <|
    (LinearEquiv.ofInjective α₁ hα₁).apply_symm_apply ⟨dP p, dP_mem_range hβ hex₁ p⟩

/-- `W ⟶ ker dQ`, `p ↦ β₀ p`. -/
def liftToQ : liftSpace (dQ := dQ) (β₀ := β₀) →ₗ[R] LinearMap.ker dQ :=
  (β₀ ∘ₗ (liftSpace (dQ := dQ) (β₀ := β₀)).subtype).codRestrict (LinearMap.ker dQ)
    (fun p => p.2)

include hβ hex₁ hdP in
/-- If `dP` is surjective, the map `liftToM : W ⟶ M₁` is surjective. -/
theorem surjective_liftToM : Function.Surjective (liftToM hβ hα₁ hex₁) := by
  intro m
  obtain ⟨p, hp⟩ := hdP (α₁ m)
  have hW : p ∈ liftSpace (dQ := dQ) (β₀ := β₀) := by
    rw [LinearMap.mem_ker]
    have := LinearMap.congr_fun hβ p
    simp only [LinearMap.coe_comp, Function.comp_apply] at this ⊢
    rw [this, hp]
    exact (hex₁ _).2 ⟨m, rfl⟩
  exact ⟨⟨p, hW⟩, hα₁ ((α₁_liftToM hβ hα₁ hex₁ _).trans hp)⟩

include hβ₀ in
/-- If `β₀` is surjective, the map `liftToQ : W ⟶ ker dQ` is surjective. -/
theorem surjective_liftToQ : Function.Surjective (liftToQ (dQ := dQ) (β₀ := β₀)) := by
  intro q
  obtain ⟨p, hp⟩ := hβ₀ q
  have hW : p ∈ liftSpace (dQ := dQ) (β₀ := β₀) := by
    rw [LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply, hp]
    exact q.2
  exact ⟨⟨p, hW⟩, Subtype.ext hp⟩

include hα hex₀ in
/-- The preimage of `range dM` under `liftToM` equals the preimage of `range (kerMap hβ)` under
`liftToQ`. -/
theorem comap_liftToM_eq :
    (LinearMap.range dM).comap (liftToM hβ hα₁ hex₁) =
      (LinearMap.range (kerMap hβ)).comap (liftToQ (dQ := dQ) (β₀ := β₀)) := by
  ext p
  simp only [Submodule.mem_comap, LinearMap.mem_range]
  have hcomm (m : M₀) : dP (α₀ m) = α₁ (dM m) := LinearMap.congr_fun hα m
  constructor
  · rintro ⟨m', hm'⟩
    have hk : (p : P₀) - α₀ m' ∈ LinearMap.ker dP := by
      rw [LinearMap.mem_ker, map_sub, hcomm, hm', α₁_liftToM, sub_self]
    refine ⟨⟨_, hk⟩, Subtype.ext ?_⟩
    change β₀ ((p : P₀) - α₀ m') = β₀ p
    rw [map_sub, (hex₀ (α₀ m')).2 ⟨m', rfl⟩, sub_zero]
  · rintro ⟨⟨p', hp'⟩, hpp'⟩
    have hb : β₀ ((p : P₀) - p') = 0 := by
      rw [map_sub, show β₀ p' = β₀ p from congrArg Subtype.val hpp', sub_self]
    obtain ⟨m', hm'⟩ := (hex₀ _).1 hb
    refine ⟨m', hα₁ ?_⟩
    rw [α₁_liftToM, ← hcomm, hm', map_sub, LinearMap.mem_ker.1 hp', sub_zero]

/-- **The snake lemma for two-term complexes**: `coker dM ≃ ker dQ / β₀(ker dP)` when the columns
are exact and `dP` is onto. -/
def cokerEquivOfExact :
    (M₁ ⧸ LinearMap.range dM) ≃ₗ[R] (LinearMap.ker dQ ⧸ LinearMap.range (kerMap hβ)) :=
  let f₁ := (LinearMap.range dM).mkQ ∘ₗ liftToM hβ hα₁ hex₁
  let f₂ := (LinearMap.range (kerMap hβ)).mkQ ∘ₗ liftToQ (dQ := dQ) (β₀ := β₀)
  have hk : LinearMap.ker f₁ = LinearMap.ker f₂ := by
    rw [LinearMap.ker_comp, LinearMap.ker_comp, Submodule.ker_mkQ, Submodule.ker_mkQ]
    exact comap_liftToM_eq hβ hα hα₁ hex₀ hex₁
  (LinearMap.quotKerEquivOfSurjective f₁
      ((Submodule.mkQ_surjective _).comp (surjective_liftToM hβ hα₁ hex₁ hdP))).symm ≪≫ₗ
    Submodule.quotEquivOfEq _ _ hk ≪≫ₗ
    LinearMap.quotKerEquivOfSurjective f₂
      ((Submodule.mkQ_surjective _).comp (surjective_liftToQ hβ₀))

end Stacks.TwoTermComplex

end
