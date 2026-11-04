module

public import Mathlib.LinearAlgebra.ExteriorPower.Basis

/-!
# Linear maps out of an exterior power prescribed on an ordered basis

Let `b : Module.Basis ι R M` be a basis of `M` indexed by a linearly ordered type.  Then
`Module.Basis.exteriorPower` makes `⋀[R]^n M` free on the `n`-element subsets of `ι`, the basis
vector indexed by a subset being the wedge of its elements **in increasing order**.  A linear
map out of `⋀[R]^n M` is therefore prescribed by its values on increasing tuples, through
`Module.Basis.constr`.

Consumers rarely have an increasing tuple in hand: wedging a further basis vector on the left,
for instance, produces `b (v 0) ∧ ⋯ ∧ b (v n)` in whatever order it comes.  This module records
the value of such a map on an arbitrary injective tuple: it is the prescribed value, provided
the prescription is itself alternating in the index tuple.

## Main results

* `Module.Basis.exteriorPower_constr_ιMulti` — the value of
  `(b.exteriorPower n).constr R (f ∘ enumeration)` on `b ∘ v`, for an arbitrary injective
  `v : Fin n → ι` and an `f` transforming by the sign under permutations of the tuple.
* `Module.Basis.exteriorPower_ιMulti_eq_zsmul` — the same sorting, recorded for a consumer
  that is only additive: the wedge of an injective tuple of basis vectors is an **integer**
  multiple of a basis vector of the exterior power.
* `Set.powersetCard.ofFinEmbEquiv_symm_map` — the increasing enumeration a basis of an
  exterior power is indexed by commutes with an order embedding of the index type.
-/

@[expose] public noncomputable section

open Module

namespace Set.powersetCard

/-- **The increasing enumeration of a subset commutes with an order embedding.**  Pushing the
enumeration of a `n`-element subset `s` of `I` forward along `e : I ↪o J` enumerates the image
subset, because an order embedding preserves the order the enumeration is taken in. -/
theorem ofFinEmbEquiv_symm_map {I J : Type*} [LinearOrder I] [LinearOrder J] {n : ℕ}
    (s : Set.powersetCard I n) (e : I ↪o J) :
    e ∘ Set.powersetCard.ofFinEmbEquiv.symm s =
      Set.powersetCard.ofFinEmbEquiv.symm (Set.powersetCard.map n e.toEmbedding s) := by
  have h : Set.powersetCard.ofFinEmbEquiv
      ((Set.powersetCard.ofFinEmbEquiv.symm s).trans e) =
      Set.powersetCard.map n e.toEmbedding s := by
    apply SetLike.coe_injective
    ext i
    simp only [Set.powersetCard.ofFinEmbEquiv_apply, Set.powersetCard.coe_ofFinEmb,
      Set.powersetCard.coe_map, Set.mem_range, Set.mem_image]
    show (∃ j, e (Set.powersetCard.ofFinEmbEquiv.symm s j) = i) ↔ ∃ j, j ∈ s ∧ e j = i
    constructor
    · rintro ⟨j, rfl⟩
      exact ⟨_, (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem s _).mp ⟨j, rfl⟩, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      obtain ⟨k, rfl⟩ := (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem s j).mpr hj
      exact ⟨k, rfl⟩
  exact congrArg DFunLike.coe ((Equiv.eq_symm_apply Set.powersetCard.ofFinEmbEquiv).mpr h)

end Set.powersetCard

namespace Module.Basis

/-- Sorting an injective tuple by a permutation gives the increasing enumeration of its image, and
the wedge of the sorted tuple of basis vectors is the corresponding basis vector. -/
private theorem exists_perm_comp_eq_symm_and_ιMulti_eq {R M ι : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [LinearOrder ι] (b : Module.Basis ι R M) (n : ℕ)
    (v : Fin n → ι) (hv : Function.Injective v) :
    ∃ (s : Set.powersetCard ι n) (sigma : Equiv.Perm (Fin n)),
      v ∘ sigma = Set.powersetCard.ofFinEmbEquiv.symm s ∧
        exteriorPower.ιMulti R n (b ∘ (v ∘ sigma)) = b.exteriorPower n s := by
  classical
  have hc : (Finset.image v Finset.univ).card = n :=
    (Finset.card_image_of_injective Finset.univ hv).trans (Finset.card_fin n)
  let s : Set.powersetCard ι n := ⟨Finset.image v Finset.univ, hc⟩
  let sigma : Equiv.Perm (Fin n) :=
    (Finset.orderIsoOfFin (Finset.image v Finset.univ) hc).toEquiv.trans
      ((Set.equivOfEq Fintype.coe_image_univ).trans (Equiv.ofInjective v hv).symm)
  have hsort : v ∘ sigma = Set.powersetCard.ofFinEmbEquiv.symm s := by
    ext i
    simp only [Function.comp_apply, sigma, Equiv.trans_apply, OrderIso.coe_toEquiv,
      Equiv.apply_ofInjective_symm]
    rfl
  refine ⟨s, sigma, hsort, ?_⟩
  rw [hsort, exteriorPower.basis_apply]
  rfl

/-- **The value on an arbitrary injective tuple of a map prescribed on the exterior basis.**
If `f : (Fin n → ι) → N` transforms by the sign of the permutation, then the linear map on
`⋀[R]^n M` prescribed by `f` on increasing tuples takes the wedge `b (v 0) ∧ ⋯ ∧ b (v (n - 1))`
of any injective tuple `v` to `f v`.

Both hypotheses are needed: without injectivity the wedge is zero while `f v` need not be, and
without the sign rule the prescription is not consistent with reordering. -/
theorem exteriorPower_constr_ιMulti {R M N ι : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] [AddCommGroup N] [Module R N] [LinearOrder ι] (b : Module.Basis ι R M) (n : ℕ)
    (f : (Fin n → ι) → N)
    (hf : ∀ (v : Fin n → ι) (sigma : Equiv.Perm (Fin n)), f (v ∘ sigma) = sigma.sign • f v)
    (v : Fin n → ι) (hv : Function.Injective v) :
    (b.exteriorPower n).constr R (fun s ↦ f (Set.powersetCard.ofFinEmbEquiv.symm s))
        (exteriorPower.ιMulti R n (b ∘ v)) = f v := by
  obtain ⟨s, sigma, hsort, he⟩ := exists_perm_comp_eq_symm_and_ιMulti_eq b n v hv
  have h := congrArg ((b.exteriorPower n).constr R
      (fun s ↦ f (Set.powersetCard.ofFinEmbEquiv.symm s))) he
  rw [Module.Basis.constr_basis, ← hsort, hf, ← Function.comp_assoc, AlternatingMap.map_perm,
    Units.smul_def, map_zsmul] at h
  exact (MulAction.injective sigma.sign) h

/-- **A wedge of basis vectors is an integer multiple of a basis vector.**  For an injective
tuple `v : Fin n → ι`, the wedge `b (v 0) ∧ ⋯ ∧ b (v (n - 1))` is `± 1` times the basis vector
of `⋀[R]^n M` indexed by the image of `v`, the sign being that of the permutation sorting `v`.

`Module.Basis.exteriorPower_constr_ιMulti` says the same thing in the form an `R`-linear
consumer needs.  This is the form an **additive** consumer needs: a map that is only
`ℤ`-linear cannot be prescribed by `Module.Basis.constr`, but it is still determined on
wedges of basis vectors, and that is exactly the content of this statement. -/
theorem exteriorPower_ιMulti_eq_zsmul {R M ι : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] [LinearOrder ι] (b : Module.Basis ι R M) (n : ℕ) (v : Fin n → ι)
    (hv : Function.Injective v) :
    ∃ (s : Set.powersetCard ι n) (c : ℤ),
      exteriorPower.ιMulti R n (fun k ↦ b (v k)) = c • b.exteriorPower n s := by
  obtain ⟨s, sigma, -, he⟩ := exists_perm_comp_eq_symm_and_ιMulti_eq b n v hv
  refine ⟨s, (sigma.sign : ℤ), ?_⟩
  rw [← he, show (b ∘ (v ∘ sigma)) = (b ∘ v) ∘ sigma from rfl,
    (exteriorPower.ιMulti R n).map_perm, Units.smul_def, smul_smul, ← Units.val_mul,
    Int.units_mul_self, Units.val_one, one_smul]
  rfl

end Module.Basis

end
