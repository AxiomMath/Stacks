module

public import StacksFrontier.RingTheory.Depth.Defs.Defs

/-!
# Depth along a semilinear isomorphism of modules

Let `e : A ≃+* B` be an isomorphism of commutative rings and let `φ : M ≃+ N` be an additive
isomorphism between an `A`-module `M` and a `B`-module `N` which is `e`-semilinear, that is
`φ (a • m) = e a • φ m`. Then `φ` matches the `M`-regular sequences with terms in an ideal
`I ⊆ A` with the `N`-regular sequences with terms in `I.map e`, and it carries `I • M` onto
`(I.map e) • N`. Both branches of the definition of `Module.depth` therefore transport, and
`depth_I(M) = depth_{I.map e}(N)`.

This generalizes `Module.depth_eq_of_ringEquiv`, which is the case `M = A`, `N = B` and
`φ = e`, and `Module.depth_eq_depth_of_linearEquiv`, which is the case `A = B` and
`e = RingEquiv.refl`.

## Main results

* `Module.smul_top_mem_of_semilinearEquiv`: `φ` carries `I • M` into `(I.map e) • N`.
* `Module.isRegular_iff_of_semilinearEquiv`: `rs` is `M`-regular exactly when `rs.map e` is
  `N`-regular.
* `Module.depth_eq_of_semilinearEquiv`: `depth_I(M) = depth_{I.map e}(N)`.

## Implementation notes

The regular sequences are matched by Mathlib's `AddEquiv.isRegular_congr`, whose hypothesis is
exactly the semilinearity of `φ` read along the two lists `rs` and `rs.map e`. The saturation
branch is handled by `smul_top_mem_of_semilinearEquiv`, proved by
`Submodule.smul_induction_on` because the two submodules live over different rings and so no
`Submodule.map` relates them.

The equality is deduced from the inequality `Module.depth_le_of_semilinearEquiv` applied twice,
once to `(e, φ)` and once to `(e.symm, φ.symm)`; the second application needs only that
`I.map e` maps back to `I` along `e.symm`.
-/

@[expose] public section

open RingTheory.Sequence

namespace Module

variable {A B : Type*} [CommRing A] [CommRing B] (e : A ≃+* B) (I : Ideal A)
variable {M N : Type*} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module B N]
variable (φ : M ≃+ N) (hφ : ∀ (a : A) (m : M), φ (a • m) = e a • φ m)

include hφ in
/-- An `e`-semilinear additive isomorphism carries `I • M` into `(I.map e) • N`: a generator
`a • m` with `a ∈ I` goes to `e a • φ m`, and `e a` lies in `I.map e`. -/
public theorem smul_top_mem_of_semilinearEquiv {x : M} (hx : x ∈ I • (⊤ : Submodule A M)) :
    φ x ∈ (I.map (e : A →+* B)) • (⊤ : Submodule B N) := by
  refine Submodule.smul_induction_on hx (fun a ha m _ => ?_) (fun y z hy hz => ?_)
  · rw [hφ a m]
    exact Submodule.smul_mem_smul (Ideal.mem_map_of_mem _ ha) Submodule.mem_top
  · rw [map_add]
    exact Submodule.add_mem _ hy hz

include hφ in
/-- An `e`-semilinear additive isomorphism carries a saturated module to a saturated one: if
`I • M = M` then `(I.map e) • N = N`. -/
public theorem smul_top_eq_top_of_semilinearEquiv (h : I • (⊤ : Submodule A M) = ⊤) :
    (I.map (e : A →+* B)) • (⊤ : Submodule B N) = ⊤ := by
  refine Submodule.eq_top_iff'.mpr fun y => ?_
  have hy : φ.symm y ∈ I • (⊤ : Submodule A M) := by rw [h]; exact Submodule.mem_top
  have hmem := smul_top_mem_of_semilinearEquiv e I φ hφ hy
  rwa [φ.apply_symm_apply] at hmem

include hφ in
/-- An `e`-semilinear additive isomorphism matches the regular sequences: a list `rs` of
elements of `A` is `M`-regular exactly when `rs.map e` is `N`-regular. -/
public theorem isRegular_iff_of_semilinearEquiv (rs : List A) :
    IsRegular M rs ↔ IsRegular N (rs.map (e : A →+* B)) :=
  AddEquiv.isRegular_congr (e := φ)
    (List.forall₂_map_right_iff.mpr (List.forall₂_same.mpr fun a _ m => hφ a m))

include hφ in
/-- **Depth does not decrease along a semilinear isomorphism of modules.** The `M`-regular
sequences with terms in `I` are carried to `N`-regular sequences with terms in `I.map e` of the
same length, and a saturated `M` forces a saturated `N`. -/
public theorem depth_le_of_semilinearEquiv :
    Module.depth A I M ≤ Module.depth B (I.map (e : A →+* B)) N := by
  rw [Module.depth, Module.depth]
  by_cases h : I • (⊤ : Submodule A M) = ⊤
  · rw [ite_eq_left h, ite_eq_left (smul_top_eq_top_of_semilinearEquiv e I φ hφ h)]
  · by_cases h2 : (I.map (e : A →+* B)) • (⊤ : Submodule B N) = ⊤
    · rw [ite_eq_left h2]
      exact le_top
    · rw [ite_eq_right h, ite_eq_right h2]
      refine iSup₂_le fun rs ⟨hmem, hreg⟩ => ?_
      have hmem' : ∀ b ∈ rs.map (e : A →+* B), b ∈ I.map (e : A →+* B) := by
        intro b hb
        obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hb
        exact Ideal.mem_map_of_mem _ (hmem a ha)
      have hreg' : IsRegular N (rs.map (e : A →+* B)) :=
        (isRegular_iff_of_semilinearEquiv e φ hφ rs).1 hreg
      calc ((rs.length : ℕ∞)) = (((rs.map (e : A →+* B)).length : ℕ∞)) := by simp
        _ ≤ _ := le_iSup₂ (f := fun (ss : List B) (_ : ss ∈ {ss : List B |
              (∀ b ∈ ss, b ∈ I.map (e : A →+* B)) ∧ IsRegular N ss}) =>
              ((ss.length : ℕ∞))) _ ⟨hmem', hreg'⟩

include hφ in
/-- **Depth transports along a semilinear isomorphism of modules.** If `e : A ≃+* B` and
`φ : M ≃+ N` satisfy `φ (a • m) = e a • φ m`, then `depth_I(M) = depth_{I.map e}(N)` for every
ideal `I ⊆ A`. -/
public theorem depth_eq_of_semilinearEquiv :
    Module.depth A I M = Module.depth B (I.map (e : A →+* B)) N := by
  refine le_antisymm (depth_le_of_semilinearEquiv e I φ hφ) ?_
  have hφ' : ∀ (b : B) (n : N), φ.symm (b • n) = e.symm b • φ.symm n := by
    intro b n
    have := hφ (e.symm b) (φ.symm n)
    rw [φ.apply_symm_apply, e.apply_symm_apply] at this
    rw [← this, φ.symm_apply_apply]
  have h := depth_le_of_semilinearEquiv e.symm (I.map (e : A →+* B)) φ.symm hφ'
  rwa [Ideal.map_map, show ((e.symm : B →+* A).comp (e : A →+* B)) = RingHom.id A from by
    ext a; simp, Ideal.map_id] at h

end Module

end
