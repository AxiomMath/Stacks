module

public import StacksFrontier.RingTheory.BeauvilleLaszlo.GlueableModule

@[expose] public section

/-!
# Glueability is an isomorphism invariant

Let `(R → S, f)` be a pair of a ring map and an element of `R`. Glueability of an `R`-module
`M` for `(R → S, f)` (`BeauvilleLaszlo.IsGlueableFor`) is the exactness of the
Beauville--Laszlo sequence `0 → M → (M ⊗[R] S) ⊕ (M ⊗[R] R_f) → M ⊗[R] S_f → 0`. Both maps
of that sequence are natural in the module, so glueability only depends on `M` up to
`R`-linear isomorphism.

## Main results

* `BeauvilleLaszlo.isGlueableFor_of_linearEquiv`, `BeauvilleLaszlo.isGlueableFor_linearEquiv_iff`:
  glueability for `(R → S, f)` is an invariant of the `R`-module up to isomorphism.

-/

namespace BeauvilleLaszlo

section

universe u v w w'

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable {M : Type w} [AddCommGroup M] [Module R M]
variable {N : Type w'} [AddCommGroup N] [Module R N]

/-- Glueability for `(R → S, f)` only depends on the `R`-module up to isomorphism: both maps
of the Beauville--Laszlo sequence are natural in the module, so an `R`-linear isomorphism
`M ≃ₗ[R] N` carries the sequence of `M` to the sequence of `N`. -/
public theorem isGlueableFor_of_linearEquiv (e : M ≃ₗ[R] N) (f : R)
    (h : IsGlueableFor (S := S) M f) : IsGlueableFor (S := S) N f := by
  obtain ⟨hinj, hexact, hsurj⟩ := h
  set u := e.rTensor (Localization.Away (algebraMap R S f)) with hu
  set t := (e.rTensor S).prodCongr (e.rTensor (Localization.Away f)) with ht
  have hbase : ∀ x : TensorProduct R M S, baseChangeToAway (S := S) N f (e.rTensor S x) =
      u (baseChangeToAway (S := S) M f x) := by
    intro x
    induction x with
    | zero => simp
    | tmul m s => simp [hu]
    | add x y hx hy => simp [hx, hy]
  have hloc : ∀ x : TensorProduct R M (Localization.Away f),
      localizedBaseChangeToAway (S := S) N f (e.rTensor (Localization.Away f) x) =
        u (localizedBaseChangeToAway (S := S) M f x) := by
    intro x
    induction x with
    | zero => simp
    | tmul m x => simp [hu]
    | add x y hx hy => simp [hx, hy]
  have sq₁ : toTensorBaseChanges (S := S) N f ∘ₗ (e : M →ₗ[R] N) =
      (t : _ →ₗ[R] _) ∘ₗ toTensorBaseChanges (S := S) M f :=
    LinearMap.ext fun m ↦ by simp [ht]
  have sq₂ : tensorAwayDifference (S := S) N f ∘ₗ (t : _ →ₗ[R] _) =
      (u : _ →ₗ[R] _) ∘ₗ tensorAwayDifference (S := S) M f := by
    refine LinearMap.ext fun x ↦ ?_
    obtain ⟨x₁, x₂⟩ := x
    have h₁ := hbase x₁
    have h₂ := hloc x₂
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, ht,
      LinearEquiv.prodCongr_apply, tensorAwayDifference_apply, map_sub] at h₁ h₂ ⊢
    rw [h₁, h₂]
  refine ⟨?_, Function.Exact.of_ladder_linearEquiv_of_exact sq₁ sq₂ hexact, ?_⟩
  · intro x y hxy
    obtain ⟨a, rfl⟩ := e.surjective x
    obtain ⟨b, rfl⟩ := e.surjective y
    have ha := LinearMap.congr_fun sq₁ a
    have hb := LinearMap.congr_fun sq₁ b
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe] at ha hb
    rw [ha, hb] at hxy
    exact congrArg _ (hinj (t.injective hxy))
  · intro z
    obtain ⟨y, hy⟩ := hsurj (u.symm z)
    refine ⟨t y, ?_⟩
    have h := LinearMap.congr_fun sq₂ y
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe] at h
    rw [h, hy, u.apply_symm_apply]

/-- Glueability for `(R → S, f)` is invariant under `R`-linear isomorphism of the module. -/
public theorem isGlueableFor_linearEquiv_iff (e : M ≃ₗ[R] N) (f : R) :
    IsGlueableFor (S := S) M f ↔ IsGlueableFor (S := S) N f :=
  ⟨isGlueableFor_of_linearEquiv e f, isGlueableFor_of_linearEquiv e.symm f⟩

end

end BeauvilleLaszlo

end
