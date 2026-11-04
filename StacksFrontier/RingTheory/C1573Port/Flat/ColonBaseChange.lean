module

public import Mathlib.RingTheory.Flat.Equalizer
public import Mathlib.RingTheory.Ideal.Colon
public import Mathlib.RingTheory.IsTensorProduct
public import Mathlib.LinearAlgebra.TensorProduct.Quotient

namespace Ideal.C1573
end Ideal.C1573

/-!
# Colon ideals commute with flat base change

Let `R ⟶ R'` be a flat ring map, let `K` be an `R`-module with base change `K'` along it, let
`L ⊆ K` be a submodule and `k ∈ K`. The colon ideal `(L : k) = {r ∈ R | r k ∈ L}` extends to the
colon ideal `(L R' : k)` of the extended submodule.

## Main results

* `Ideal.C1573.map_colon_singleton_le`: `(L : k) R' ⊆ (L R' : k)`, with no flatness assumption.
* `Ideal.C1573.map_colon_singleton_of_isBaseChange`: `(L : k) R' = (L R' : k)`.
-/

@[expose] public section

open scoped TensorProduct

universe u v w x

namespace Ideal

open _root_.Ideal.C1573
variable {R : Type u} {R' : Type v} {K : Type w} {K' : Type x} [CommRing R] [CommRing R']
  [Algebra R R'] [AddCommGroup K] [Module R K] [AddCommGroup K'] [Module R K'] [Module R' K']
  [IsScalarTower R R' K'] {ψ : K →ₗ[R] K'}

/-- The extension of the colon ideal `(L : k)` along `R → R'` lies in `(L R' : k)`. -/
theorem C1573.map_colon_singleton_le (L : Submodule R K) (k : K) :
    Ideal.map (algebraMap R R') (L.colon {k}) ≤
      (Submodule.span R' (ψ '' L)).colon {ψ k} := by
  rw [Ideal.map_le_iff_le_comap]
  intro r hr
  rw [Submodule.mem_colon_singleton] at hr
  rw [Ideal.mem_comap, Submodule.mem_colon_singleton, algebraMap_smul, ← map_smul]
  exact Submodule.subset_span ⟨_, hr, rfl⟩

/-- **Colon ideals commute with flat base change.** -/
theorem C1573.map_colon_singleton_of_isBaseChange [Module.Flat R R'] (hψ : IsBaseChange R' ψ)
    (L : Submodule R K) (k : K) :
    Ideal.map (algebraMap R R') (L.colon {k}) =
      (Submodule.span R' (ψ '' L)).colon {ψ k} := by
  refine le_antisymm (map_colon_singleton_le L k) fun r' hr' => ?_
  rw [Submodule.mem_colon_singleton] at hr'
  let lam : R →ₗ[R] K ⧸ L := L.mkQ ∘ₗ LinearMap.toSpanSingleton R K k
  have hker : LinearMap.ker lam = L.colon {k} := by
    ext r
    simp only [LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply,
      LinearMap.toSpanSingleton_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
      Submodule.mem_colon_singleton, lam]
  have hkill : TensorProduct.AlgebraTensorModule.lTensor R' R' lam (r' ⊗ₜ 1) = 0 := by
    show r' ⊗ₜ[R] lam 1 = 0
    rw [show lam 1 = Submodule.Quotient.mk k by simp [lam]]
    apply (TensorProduct.tensorQuotientEquiv R' L).injective
    rw [TensorProduct.tensorQuotientEquiv_apply_mk_tmul, map_zero,
      Submodule.Quotient.mk_eq_zero]
    have hspan : r' • ψ k ∈ Submodule.span R' (ψ '' L) := hr'
    have heq : r' ⊗ₜ[R] k = hψ.equiv.symm (r' • ψ k) := by
      rw [← hψ.equiv_tmul, LinearEquiv.symm_apply_apply]
    rw [heq]
    refine Submodule.span_induction (p := fun z _ => hψ.equiv.symm z ∈
      LinearMap.range (TensorProduct.map (LinearMap.id : R' →ₗ[R] R') L.subtype)) ?_ ?_ ?_ ?_
      hspan
    · rintro _ ⟨x, hx, rfl⟩
      rw [IsBaseChange.equiv_symm_apply]
      exact ⟨1 ⊗ₜ ⟨x, hx⟩, rfl⟩
    · rw [map_zero]; exact zero_mem _
    · intro a b _ _ ha hb
      rw [map_add]; exact add_mem ha hb
    · intro c a _ ha
      rw [LinearEquiv.map_smul]
      obtain ⟨w, hw⟩ := ha
      refine ⟨c • w, ?_⟩
      rw [← hw]
      clear hw
      induction w using TensorProduct.induction_on with
      | zero => simp
      | tmul x y => simp [TensorProduct.smul_tmul']
      | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]
  obtain ⟨z, hz⟩ := (Module.Flat.ker_lTensor_eq (R := R) R' R' lam).le
    (LinearMap.mem_ker.2 hkill)
  have hrid : ∀ w : R' ⊗[R] LinearMap.ker lam,
      Algebra.TensorProduct.rid R R' R' (TensorProduct.AlgebraTensorModule.lTensor R' R'
        (LinearMap.ker lam).subtype w) ∈ Ideal.map (algebraMap R R') (L.colon {k}) := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul c a =>
      simp only [TensorProduct.AlgebraTensorModule.lTensor_tmul, Submodule.coe_subtype,
        Algebra.TensorProduct.rid_tmul]
      rw [Algebra.smul_def, mul_comm]
      exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ (hker.le a.2))
    | add x y hx hy => rw [map_add, map_add]; exact add_mem hx hy
  have := hrid z
  rwa [hz, Algebra.TensorProduct.rid_tmul, one_smul] at this

end Ideal

end
