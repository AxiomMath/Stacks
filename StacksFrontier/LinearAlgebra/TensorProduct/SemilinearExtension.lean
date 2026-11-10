module

public import Mathlib.LinearAlgebra.TensorProduct.Basic

/-!
# The linear extension of a semilinear map, and its bijectivity

Let `f : R →+* S` be a map of commutative rings, `M` an `R`-module and `N` an `S`-module. An
additive map `σ : M → N` which is semilinear along `f`, `σ (r • m) = f r • σ m`, extends to the
additive map `S ⊗_R M → N`, `s ⊗ m ↦ s • σ m`; it is bijective exactly when `σ` presents `N` as
the base change of `M` along `f`.

This file records how bijectivity of the extension behaves under a commuting square of rings

`R → S`, `R' → S'`, `e_R : R ≃ R'`, `e_S : S ≃ S'`

along which `M ≃ M'` and a map `Λ : N → N'` are semilinear: if `Λ ∘ σ = v ∘ τ` then the
extensions of `σ` and of `v` are compared by the transport of the tensor product along the
square, which is bijective, so that

* if the extension of `σ` is bijective, then `Λ` is bijective exactly when the extension of `v`
  is;
* if `Λ` is bijective, the extension of `σ` is bijective exactly when the extension of `v` is.

The module structure of `S` over `R` is an argument together with the hypothesis that it is the
one given by `f`, rather than a local instance: that is how the two structures in play on
`S` are kept apart in the applications, where `S` already carries other module structures.

## Main definitions

* `Stacks.SemilinearExtension.extend`: the extension `S ⊗_R M → N` of a semilinear map.

## Main results

* `Stacks.SemilinearExtension.bijective_iff_bijective_extend`: the first of the two statements.
* `Stacks.SemilinearExtension.bijective_extend_iff_bijective_extend`: the second.
-/

@[expose] public section

open TensorProduct

namespace Stacks.SemilinearExtension

section Extend

variable {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) [Module R S]
  {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N]

/-- The extension `S ⊗_R M → N`, `s ⊗ m ↦ s • σ m`, of an additive map `σ : M → N` which is
semilinear along `f`, the `R`-module structure of `S` being the one given by `f`. -/
def extend (hS : ∀ (r : R) (s : S), r • s = f r * s) (σ : M →+ N)
    (hσ : ∀ (r : R) (m : M), σ (r • m) = f r • σ m) : S ⊗[R] M →+ N :=
  TensorProduct.liftAddHom
    (AddMonoidHom.mk' (fun s => AddMonoidHom.mk' (fun m => s • σ m)
        (fun m m' => by rw [map_add, smul_add]))
      (fun s s' => AddMonoidHom.ext fun m => add_smul s s' (σ m)))
    (fun r s m => by
      change (r • s) • σ m = s • σ (r • m)
      rw [hS, hσ, mul_comm, mul_smul])

/-- The extension of `σ` sends `s ⊗ m` to `s • σ m`. -/
@[simp]
theorem extend_tmul (hS : ∀ (r : R) (s : S), r • s = f r * s) (σ : M →+ N)
    (hσ : ∀ (r : R) (m : M), σ (r • m) = f r • σ m) (s : S) (m : M) :
    extend f hS σ hσ (s ⊗ₜ m) = s • σ m :=
  rfl

end Extend

section Square

variable {R S R' S' : Type*} [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
  (f : R →+* S) (f' : R' →+* S') [Module R S] [Module R' S']
  (hS : ∀ (r : R) (s : S), r • s = f r * s) (hS' : ∀ (r : R') (s : S'), r • s = f' r * s)
  (eR : R ≃+* R') (eS : S ≃+* S') (hsq : ∀ r, eS (f r) = f' (eR r))
  {M N M' N' : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N]
  [AddCommGroup M'] [Module R' M'] [AddCommGroup N'] [Module S' N']

/-- The transport `S ⊗_R M → S' ⊗_{R'} M'`, `s ⊗ m ↦ e_S s ⊗ τ m`, of a tensor product along a
square of rings with invertible vertical maps and an additive equivalence of modules semilinear
along the left one. -/
def transport (τ : M ≃+ M') (hτ : ∀ (r : R) (m : M), τ (r • m) = eR r • τ m) :
    S ⊗[R] M →+ S' ⊗[R'] M' :=
  TensorProduct.liftAddHom
    (AddMonoidHom.mk'
      (fun s => (TensorProduct.mk R' S' M' (eS s)).toAddMonoidHom.comp τ.toAddMonoidHom)
      (fun s s' => AddMonoidHom.ext fun m => by
        change (eS (s + s')) ⊗ₜ[R'] τ m = (eS s) ⊗ₜ[R'] τ m + (eS s') ⊗ₜ[R'] τ m
        rw [map_add, TensorProduct.add_tmul]))
    (fun r s m => by
      change (eS (r • s)) ⊗ₜ[R'] τ m = (eS s) ⊗ₜ[R'] τ (r • m)
      rw [hS, map_mul, hsq, hτ, ← hS', TensorProduct.smul_tmul])

/-- The transport sends `s ⊗ m` to `e_S s ⊗ τ m`. -/
@[simp]
theorem transport_tmul (τ : M ≃+ M') (hτ : ∀ (r : R) (m : M), τ (r • m) = eR r • τ m)
    (s : S) (m : M) :
    transport f f' hS hS' eR eS hsq τ hτ (s ⊗ₜ m) = eS s ⊗ₜ τ m :=
  rfl

/-- The transport of a tensor product along a square of rings with invertible vertical maps is
bijective, the inverse being the transport along the inverse square. -/
theorem bijective_transport (τ : M ≃+ M') (hτ : ∀ (r : R) (m : M), τ (r • m) = eR r • τ m) :
    Function.Bijective (transport f f' hS hS' eR eS hsq τ hτ) := by
  have hsq' : ∀ r, eS.symm (f' r) = f (eR.symm r) := fun r => by
    conv_lhs => rw [← eR.apply_symm_apply r, ← hsq]
    rw [eS.symm_apply_apply]
  have hτ' : ∀ (r : R') (m : M'), τ.symm (r • m) = eR.symm r • τ.symm m := fun r m => by
    apply τ.injective
    rw [AddEquiv.apply_symm_apply, hτ, RingEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
  refine Function.bijective_iff_has_inverse.mpr
    ⟨transport f' f hS' hS eR.symm eS.symm hsq' τ.symm hτ', fun z => ?_, fun z => ?_⟩ <;>
  induction z using TensorProduct.inductionOn with
  | tmul s m => simp
  | add z w hz hw => rw [map_add, map_add, hz, hw]

variable (σ : M →+ N) (hσ : ∀ (r : R) (m : M), σ (r • m) = f r • σ m)
  (v : M' →+ N') (hv : ∀ (r : R') (m : M'), v (r • m) = f' r • v m)
  (τ : M ≃+ M') (hτ : ∀ (r : R) (m : M), τ (r • m) = eR r • τ m)
  (Λ : N →+ N') (hΛ : ∀ (s : S) (n : N), Λ (s • n) = eS s • Λ n)
  (hcomm : ∀ m, Λ (σ m) = v (τ m))

include hcomm hΛ in
/-- The extensions of `σ` and of `v` are compared by the transport of the tensor product. -/
theorem extend_transport (z : S ⊗[R] M) :
    extend f' hS' v hv (transport f f' hS hS' eR eS hsq τ hτ z) = Λ (extend f hS σ hσ z) := by
  induction z using TensorProduct.inductionOn with
  | tmul s m => simp [hΛ, hcomm]
  | add z w hz hw => rw [map_add, map_add, hz, hw, map_add, map_add]

/-- The extension of `v` after the transport is `Λ` after the extension of `σ`. -/
private theorem extend_comp_transport (hΛ : ∀ (s : S) (n : N), Λ (s • n) = eS s • Λ n)
    (hcomm : ∀ m, Λ (σ m) = v (τ m)) :
    ⇑(extend f' hS' v hv) ∘ ⇑(transport f f' hS hS' eR eS hsq τ hτ) =
      ⇑Λ ∘ ⇑(extend f hS σ hσ) :=
  funext fun z => extend_transport f f' hS hS' eR eS hsq σ hσ v hv τ hτ Λ hΛ hcomm z

include hcomm hΛ eR hsq hτ in
/-- **If `σ` presents `N` as a base change, then `Λ` is bijective exactly when the extension of
`v` is.** -/
theorem bijective_iff_bijective_extend (hσb : Function.Bijective (extend f hS σ hσ)) :
    Function.Bijective Λ ↔ Function.Bijective (extend f' hS' v hv) := by
  rw [← Function.Bijective.of_comp_iff Λ hσb, ← extend_comp_transport f f' hS hS' eR eS hsq σ hσ
    v hv τ hτ Λ hΛ hcomm,
    Function.Bijective.of_comp_iff _ (bijective_transport f f' hS hS' eR eS hsq τ hτ)]

include hcomm hΛ eR hsq hτ in
/-- **If `Λ` is bijective, the extension of `σ` is bijective exactly when the extension of `v`
is.** -/
theorem bijective_extend_iff_bijective_extend (hΛb : Function.Bijective Λ) :
    Function.Bijective (extend f hS σ hσ) ↔ Function.Bijective (extend f' hS' v hv) := by
  rw [← Function.Bijective.of_comp_iff' hΛb, ← extend_comp_transport f f' hS hS' eR eS hsq σ hσ
    v hv τ hτ Λ hΛ hcomm,
    Function.Bijective.of_comp_iff _ (bijective_transport f f' hS hS' eR eS hsq τ hτ)]

end Square

end Stacks.SemilinearExtension

end
