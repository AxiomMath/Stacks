module

public import Mathlib.RingTheory.IsTensorProduct

/-!
# Base change along a square of rings with bijective vertical maps

`IsBaseChange` depends on the ring maps along which it is read. This file records the two facts
needed to move a base change statement across an identification of the rings involved: base
change along a ring map whose algebra map is bijective is the identity
(`IsBaseChange.of_bijective_algebraMap`), and a base change along `Γ₂ → Γ₁` is a base change
along `R₂ → R₁` whenever `R₂ → Γ₂` and `R₁ → Γ₁` are bijective and the square of ring maps
commutes (`IsBaseChange.of_bijective_square`).

This is used when the rings of global functions of affine schemes are identified with given
rings, for instance the ring of global sections of `Spec A` with `A`.

## Main results

* `IsBaseChange.of_bijective_algebraMap`.
* `IsBaseChange.of_bijective_square`.
-/

@[expose] public noncomputable section

open TensorProduct

/-- **Base change along a ring map whose algebra map is bijective is the identity.** -/
theorem IsBaseChange.of_bijective_algebraMap {R S M : Type*} [CommRing R] [CommRing S]
    [Algebra R S] (hRS : Function.Bijective (algebraMap R S)) [AddCommGroup M] [Module R M]
    [Module S M] [IsScalarTower R S M] :
    IsBaseChange S (LinearMap.id : M →ₗ[R] M) := by
  let φ : S ⊗[R] M →ₗ[S] M := TensorProduct.AlgebraTensorModule.lift
    ((LinearMap.lsmul S M).restrictScalars₁₂ S R)
  refine IsBaseChange.of_equiv (LinearEquiv.ofBijective φ ⟨?_, ?_⟩) fun x => ?_
  · intro x y hxy
    have key : ∀ z : S ⊗[R] M, z = 1 ⊗ₜ φ z := by
      intro z
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul s m =>
          obtain ⟨r, rfl⟩ := hRS.2 s
          simp [φ, TensorProduct.smul_tmul', Algebra.algebraMap_eq_smul_one]
      | add a b ha hb => rw [map_add, tmul_add, ← ha, ← hb]
    rw [key x, key y, hxy]
  · exact fun m => ⟨1 ⊗ₜ m, by simp [φ]⟩
  · change φ (1 ⊗ₜ x) = x
    simp [φ]

/-- **Base change transported along a square of rings whose two vertical maps are bijective.** -/
theorem IsBaseChange.of_bijective_square {R₂ R₁ Γ₂ Γ₁ M N : Type*} [CommRing R₂] [CommRing R₁]
    [CommRing Γ₂] [CommRing Γ₁] [Algebra R₂ R₁] [Algebra R₂ Γ₂] [Algebra Γ₂ Γ₁] [Algebra R₁ Γ₁]
    [Algebra R₂ Γ₁] [IsScalarTower R₂ Γ₂ Γ₁] [IsScalarTower R₂ R₁ Γ₁]
    (h₁ : Function.Bijective (algebraMap R₁ Γ₁)) (h₂ : Function.Bijective (algebraMap R₂ Γ₂))
    [AddCommGroup M] [Module R₂ M] [Module Γ₂ M] [IsScalarTower R₂ Γ₂ M]
    [AddCommGroup N] [Module Γ₁ N] [Module Γ₂ N] [IsScalarTower Γ₂ Γ₁ N] [Module R₁ N]
    [IsScalarTower R₁ Γ₁ N] [Module R₂ N] [IsScalarTower R₂ R₁ N] [IsScalarTower R₂ Γ₂ N]
    [IsScalarTower R₂ Γ₁ N]
    (f : M →ₗ[Γ₂] N) (hf : IsBaseChange Γ₁ f) :
    IsBaseChange R₁ (f.restrictScalars R₂) := by
  let e1 : R₁ ⊗[R₂] M ≃ₗ[R₂] Γ₁ ⊗[R₂] M := TensorProduct.congr
    (LinearEquiv.ofBijective ((Algebra.linearMap R₁ Γ₁).restrictScalars R₂) h₁)
    (LinearEquiv.refl R₂ M)
  let e2 := ((IsBaseChange.of_bijective_algebraMap (M := M) h₂).comp hf).equiv
  have he : ∀ (r : R₁) (z : R₁ ⊗[R₂] M), e2 (e1 (r • z)) = r • e2 (e1 z) := by
    intro r z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul s m =>
        rw [TensorProduct.smul_tmul']
        change e2 (algebraMap R₁ Γ₁ (r * s) ⊗ₜ m) = r • e2 (algebraMap R₁ Γ₁ s ⊗ₜ m)
        rw [IsBaseChange.equiv_tmul, IsBaseChange.equiv_tmul, map_mul, mul_smul,
          algebraMap_smul]
    | add a b ha hb => rw [smul_add, map_add, map_add, ha, hb, map_add, map_add, smul_add]
  let e : R₁ ⊗[R₂] M ≃ₗ[R₁] N :=
    { e1.trans (e2.restrictScalars R₂) with map_smul' := he }
  refine IsBaseChange.of_equiv e fun m => ?_
  change e2 (algebraMap R₁ Γ₁ 1 ⊗ₜ m) = f m
  rw [IsBaseChange.equiv_tmul, map_one, one_smul]
  rfl

end
