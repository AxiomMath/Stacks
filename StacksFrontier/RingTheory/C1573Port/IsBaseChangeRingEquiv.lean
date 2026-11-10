module

public import Mathlib.RingTheory.IsTensorProduct
public import StacksFrontier.RingTheory.SpreadingOut.FlatModel

namespace IsBaseChange.C1573
end IsBaseChange.C1573

/-!
# Comparing two base changes

Two base changes of `M` to `S` compared by an `S`-linear map compatible with the structure maps are
compared by a bijection (`IsBaseChange.C1573.bijective_of_comp_eq`). A base change transports along
an isomorphism of the coefficient rings together with compatible isomorphisms of the modules
(`IsBaseChange.C1573.of_ringEquiv_of_equiv_comm`).
-/

@[expose] public section

open TensorProduct

namespace IsBaseChange

open _root_.IsBaseChange.C1573
variable {R S M N : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]
  [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N] [Module S N]
  [IsScalarTower R S N]

/-- **Two base changes compared by a compatible linear map are compared by a bijection.** -/
theorem C1573.bijective_of_comp_eq {N' : Type*} [AddCommMonoid N'] [Module R N'] [Module S N']
    [IsScalarTower R S N'] {f : M →ₗ[R] N} {f' : M →ₗ[R] N'} (h : IsBaseChange S f)
    (h' : IsBaseChange S f') (φ : N →ₗ[S] N') (hφ : ∀ m, φ (f m) = f' m) :
    Function.Bijective φ := by
  have hφ' : φ = h'.equiv.toLinearMap ∘ₗ h.equiv.symm.toLinearMap :=
    h.algHom_ext _ _ fun m => by simp [hφ, IsBaseChange.equiv_symm_apply, IsBaseChange.equiv_tmul]
  rw [hφ']
  exact (h.equiv.symm.trans h'.equiv).bijective

/-- **Transport of a base change along isomorphisms of the coefficient ring and of the modules.**
Let `σ : S ≃+* S'` be compatible with the structure maps from `R`, `eM : M ≃ₗ[R] M'`, and
`eN : N ≃+ N'` be `σ`-semilinear.  If `f' : M' → N'` is a base change to `S'` and
`f' ∘ eM = eN ∘ f`, then `f` is a base change to `S`. -/
theorem C1573.of_ringEquiv_of_equiv_comm {S' M' N' : Type*} [CommSemiring S'] [Algebra R S']
    [AddCommMonoid M'] [Module R M'] [AddCommMonoid N'] [Module R N'] [Module S' N']
    [IsScalarTower R S' N'] (σ : S ≃+* S') (hσ : ∀ r, σ (algebraMap R S r) = algebraMap R S' r)
    (eM : M ≃ₗ[R] M') (eN : N ≃+ N') (heN : ∀ (s : S) (n : N), eN (s • n) = σ s • eN n)
    {f : M →ₗ[R] N} {f' : M' →ₗ[R] N'} (comm : ∀ m, f' (eM m) = eN (f m))
    (h : IsBaseChange S' f') : IsBaseChange S f := by
  let : Module S' N := Module.compHom N σ.symm.toRingHom
  have : IsScalarTower R S' N := IsScalarTower.of_algebraMap_smul fun r n => by
    change σ.symm (algebraMap R S' r) • n = r • n
    rw [← hσ, RingEquiv.symm_apply_apply, algebraMap_smul]
  let eN' : N ≃ₗ[S'] N' :=
    { eN with
      map_smul' := fun s' n => by
        change eN (σ.symm s' • n) = s' • eN n
        rw [heN, RingEquiv.apply_symm_apply] }
  have h' : IsBaseChange S' f := (IsBaseChange.iff_of_equiv_comm eM eN'
    (LinearMap.ext fun m => comm m)).mpr h
  exact IsBaseChange.of_algEquiv (AlgEquiv.ofRingEquiv (f := σ) hσ)
    (fun s n => by
      change σ.symm (σ s) • n = s • n
      rw [RingEquiv.symm_apply_apply]) h'

/-- **A base change transported along isomorphisms of the coefficient ring and of the modules.**
With `σ`, `eM`, `eN` as in `IsBaseChange.C1573.of_ringEquiv_of_equiv_comm`, the composite
`eN⁻¹ ∘ f' ∘ eM` is `R`-linear and a base change to `S`. -/
theorem C1573.exists_of_ringEquiv {S' M' N' : Type*} [CommSemiring S'] [Algebra R S']
    [AddCommMonoid M'] [Module R M'] [AddCommMonoid N'] [Module R N'] [Module S' N']
    [IsScalarTower R S' N'] (σ : S ≃+* S') (hσ : ∀ r, σ (algebraMap R S r) = algebraMap R S' r)
    (eM : M ≃ₗ[R] M') (eN : N ≃+ N') (heN : ∀ (s : S) (n : N), eN (s • n) = σ s • eN n)
    (f' : M' →ₗ[R] N') (h : IsBaseChange S' f') :
    ∃ f : M →ₗ[R] N, (∀ m, f m = eN.symm (f' (eM m))) ∧ IsBaseChange S f := by
  let f : M →ₗ[R] N :=
    { toFun := fun m => eN.symm (f' (eM m))
      map_add' := fun m m' => by simp only [map_add]
      map_smul' := fun r m => by
        refine (AddEquiv.symm_apply_eq eN).2 ?_
        rw [RingHom.id_apply, ← algebraMap_smul S r (eN.symm (f' (eM m))), heN, hσ,
          AddEquiv.apply_symm_apply, algebraMap_smul, map_smul, map_smul] }
  exact ⟨f, fun _ => rfl, of_ringEquiv_of_equiv_comm σ hσ eM eN heN
    (fun m => (eN.apply_symm_apply (f' (eM m))).symm) h⟩

end IsBaseChange
