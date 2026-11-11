module

public import StacksFrontier.LinearAlgebra.TensorAlgebra.SemilinearMap

/-!
# Exterior powers of semilinear bijections

The `n`-th exterior power `ExteriorAlgebra.powMapₛₗ n σ f : ⋀[R]^n M ⟶ ⋀[R']^n N` of a semilinear
map `f : M →ₛₗ[σ] N` along a ring isomorphism `σ : R ≃+* R'` is bijective when `f` is.

## Main results

* `ExteriorAlgebra.bijective_powMapₛₗ`.
-/

@[expose] public section

noncomputable section

namespace ExteriorAlgebra

/-- **The exterior power of a semilinear bijection along a ring isomorphism is bijective.** -/
theorem bijective_powMapₛₗ {R R' : Type*} [CommRing R] [CommRing R'] {M N : Type*}
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R' N] (σ : R ≃+* R')
    (f : M →ₛₗ[σ.toRingHom] N) (hf : Function.Bijective f) (n : ℕ) :
    Function.Bijective (powMapₛₗ n σ.toRingHom f) := by
  let e := Equiv.ofBijective f hf
  let g : N →ₛₗ[σ.symm.toRingHom] M :=
    { toFun := e.symm
      map_add' := fun x y ↦ hf.1 ((e.apply_symm_apply _).trans ((congrArg₂ (· + ·)
        (e.apply_symm_apply x) (e.apply_symm_apply y)).symm.trans (map_add f _ _).symm))
      map_smul' := fun r x ↦ hf.1 (by
        change f (e.symm (r • x)) = f (σ.symm r • e.symm x)
        rw [f.map_smulₛₗ]
        exact (e.apply_symm_apply _).trans (by
          change r • x = σ (σ.symm r) • f (e.symm x)
          rw [RingEquiv.apply_symm_apply]
          exact congrArg (r • ·) (e.apply_symm_apply x).symm)) }
  have hgf : ∀ m, g (f m) = m := fun m ↦ e.symm_apply_apply m
  have hfg : ∀ x, f (g x) = x := fun x ↦ e.apply_symm_apply x
  have h1 : ∀ z, powMapₛₗ n σ.symm.toRingHom g (powMapₛₗ n σ.toRingHom f z) = z := fun z ↦
    (powMapₛₗ_eq_comp n f g LinearMap.id (fun r ↦ (σ.symm_apply_apply r).symm)
      (fun m ↦ (hgf m).symm) z).symm.trans (powMapₛₗ_eq_self n _ (fun _ ↦ rfl) (fun _ ↦ rfl) z)
  have h2 : ∀ z, powMapₛₗ n σ.toRingHom f (powMapₛₗ n σ.symm.toRingHom g z) = z := fun z ↦
    (powMapₛₗ_eq_comp n g f LinearMap.id (fun r ↦ (σ.apply_symm_apply r).symm)
      (fun m ↦ (hfg m).symm) z).symm.trans (powMapₛₗ_eq_self n _ (fun _ ↦ rfl) (fun _ ↦ rfl) z)
  exact ⟨Function.LeftInverse.injective h1, Function.RightInverse.surjective h2⟩

end ExteriorAlgebra

end
