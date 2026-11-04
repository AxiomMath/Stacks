module

public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.TensorProduct.MvPolynomial
public import StacksFrontier.Examples.Flatness.OrdinaryCone.Segre

/-!
# Base change of the Segre product of the ordinary cone

For an algebra `k'` over a commutative ring `k`, the cone
`G = k[x, y, z]/(z³ + (y² + xy) z + x³)` satisfies `k' ⊗_k G_k ≅ G_{k'}`, and when `k'` is flat
over `k` the Segre product satisfies `k' ⊗_k Γ_k ≅ Γ_{k'}`, compatibly with the maps from
`k[X₀, X₁, X₂]` and `k'[X₀, X₁, X₂]`. Flatness enters through the inclusion `Γ_k ⊆ G_k[s, t]`,
which stays injective after base change. Every field is flat over a subfield, so for instance the
Segre product over a field of characteristic two is the base change of the one over `𝔽₂`.

## Main definitions

* `Stacks.Examples.OrdinaryCone.coneMap`: the map `G_k → G_{k'}`.
* `Stacks.Examples.OrdinaryCone.coneBaseChange`: the isomorphism `k' ⊗_k G_k ≃ G_{k'}`.
* `Stacks.Examples.OrdinaryCone.segreMap`: the map `Γ_k → Γ_{k'}`.
* `Stacks.Examples.OrdinaryCone.segreBaseChange`: the isomorphism `k' ⊗_k Γ_k ≃ Γ_{k'}` for
  `k'` flat over `k`.

## Main results

* `Stacks.Examples.OrdinaryCone.segreBaseChange_one_tmul_algebraMap`: the isomorphism is
  compatible with the maps from the polynomial rings in three variables.
-/

@[expose] public section

namespace Stacks.Examples.OrdinaryCone

open MvPolynomial TensorProduct

variable (k k' : Type*) [CommRing k] [CommRing k'] [Algebra k k']

/-- The map of cones `G_k → G_{k'}` induced by `k → k'`. -/
noncomputable def coneMap : Cone k →ₐ[k] Cone k' :=
  Cone.lift k (Cone.x k') (Cone.y k') (Cone.z k') (Cone.equation_eq_zero k')

/-- `coneMap` sends the coordinate `x` of `G_k` to the coordinate `x` of `G_{k'}`. -/
@[simp]
theorem coneMap_x : coneMap k k' (Cone.x k) = Cone.x k' :=
  Cone.lift_x ..

/-- `coneMap` sends the coordinate `y` of `G_k` to the coordinate `y` of `G_{k'}`. -/
@[simp]
theorem coneMap_y : coneMap k k' (Cone.y k) = Cone.y k' :=
  Cone.lift_y ..

/-- `coneMap` sends the coordinate `z` of `G_k` to the coordinate `z` of `G_{k'}`. -/
@[simp]
theorem coneMap_z : coneMap k k' (Cone.z k) = Cone.z k' :=
  Cone.lift_z ..

/-- `coneMap` sends the class of the variable `X i` in `G_k` to the class of `X i` in `G_{k'}`. -/
@[simp]
theorem coneMap_mk_X (i : Fin 3) :
    coneMap k k' (Ideal.Quotient.mk _ (X i)) = Ideal.Quotient.mk _ (X i) := by
  rw [coneMap, Cone.lift_mk, aeval_X]
  fin_cases i <;> rfl

/-- The map `G_{k'} → k' ⊗_k G_k` inverse to the base change map. -/
noncomputable def coneBaseChangeInv : Cone k' →ₐ[k'] k' ⊗[k] Cone k :=
  Cone.lift k' (1 ⊗ₜ Cone.x k) (1 ⊗ₜ Cone.y k) (1 ⊗ₜ Cone.z k) (by
    have := congrArg (Algebra.TensorProduct.includeRight (R := k) (A := k'))
      (Cone.equation_eq_zero k)
    simp only [map_add, map_mul, map_pow, map_zero,
      Algebra.TensorProduct.includeRight_apply] at this
    exact this)

/-- The cone commutes with base change: `k' ⊗_k G_k ≃ G_{k'}`. -/
noncomputable def coneBaseChange : k' ⊗[k] Cone k ≃ₐ[k'] Cone k' :=
  AlgEquiv.ofAlgHom
    (Algebra.TensorProduct.lift (Algebra.ofId k' (Cone k')) (coneMap k k')
      fun _ _ ↦ .all _ _)
    (coneBaseChangeInv k k')
    (Cone.algHom_ext k' (by simp [coneBaseChangeInv])
      (by simp [coneBaseChangeInv]) (by simp [coneBaseChangeInv]))
    (by
      refine Algebra.TensorProduct.ext (AlgHom.ext fun a ↦ ?_) ?_
      · simp [Algebra.TensorProduct.algebraMap_apply]
      · exact Cone.algHom_ext k (by simp [coneBaseChangeInv])
          (by simp [coneBaseChangeInv]) (by simp [coneBaseChangeInv]))

/-- `coneBaseChange` sends `a ⊗ g` to `a · coneMap g`. -/
@[simp]
theorem coneBaseChange_tmul (a : k') (g : Cone k) :
    coneBaseChange k k' (a ⊗ₜ g) = algebraMap k' (Cone k') a * coneMap k k' g :=
  rfl

/-- The map `k' ⊗_k G_k[s, t] → G_{k'}[s, t]`. -/
noncomputable def polyBaseChange :
    k' ⊗[k] MvPolynomial (Fin 2) (Cone k) →ₐ[k'] MvPolynomial (Fin 2) (Cone k') :=
  Algebra.TensorProduct.lift (Algebra.ofId k' _) (mapAlgHom (coneMap k k')) fun _ _ ↦ .all _ _

/-- The map `k' ⊗_k G_k[s, t] → G_{k'}[s, t]` is injective. -/
theorem polyBaseChange_injective : Function.Injective (polyBaseChange k k') := by
  let e := MvPolynomial.rTensorAlgEquiv (R := k) (S := k') (N := Cone k) (σ := Fin 2)
  have h : polyBaseChange k k' =
      (mapAlgHom (coneBaseChange k k' : k' ⊗[k] Cone k →ₐ[k'] _)).comp e.toAlgHom := by
    refine Algebra.TensorProduct.ext' fun a p ↦ MvPolynomial.ext _ _ fun d ↦ ?_
    simp [e, polyBaseChange, Algebra.TensorProduct.lift_tmul, mapAlgHom_apply, coeff_map,
      coeff_C_mul]
  rw [h]
  exact (MvPolynomial.map_injective _ (coneBaseChange k k').injective).comp e.injective

/-- The map `G_k[s, t] → G_{k'}[s, t]` induced by `coneMap` sends each generator `u v` of the
Segre product over `k` to the corresponding generator over `k'`. -/
@[simp]
theorem mapAlgHom_coneMap_segreGen (i : Fin 3) (j : Fin 2) :
    mapAlgHom (coneMap k k') (segreGen k i j) = segreGen k' i j := by
  simp [segreGen, mapAlgHom_apply]

/-- The map `G_k[s, t] → G_{k'}[s, t]` induced by `coneMap` sends `Γ_k` into `Γ_{k'}`. -/
theorem mapAlgHom_coneMap_mem_segre {p : MvPolynomial (Fin 2) (Cone k)} (hp : p ∈ segre k) :
    mapAlgHom (coneMap k k') p ∈ segre k' := by
  induction hp using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨ij, rfl⟩ := hx
    rw [mapAlgHom_coneMap_segreGen]
    exact Algebra.subset_adjoin ⟨ij, rfl⟩
  | algebraMap r =>
    rw [AlgHom.commutes, IsScalarTower.algebraMap_apply k k']
    exact Subalgebra.algebraMap_mem _ _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy

/-- The map of Segre products `Γ_k → Γ_{k'}` induced by `k → k'`. -/
noncomputable def segreMap : segre k →ₐ[k] segre k' :=
  ((mapAlgHom (coneMap k k')).comp (segre k).val).codRestrict ((segre k').restrictScalars k)
    fun x ↦ mapAlgHom_coneMap_mem_segre k k' x.2

/-- As an element of `G_{k'}[s, t]`, the image of `x` under `segreMap` is the image of `x` under
the map `G_k[s, t] → G_{k'}[s, t]` induced by `coneMap`. -/
@[simp]
theorem coe_segreMap (x : segre k) :
    (segreMap k k' x : MvPolynomial (Fin 2) (Cone k')) = mapAlgHom (coneMap k k') x :=
  rfl

/-- `segreMap` sends each generator `u v` of `Γ_k` to the corresponding generator of `Γ_{k'}`. -/
@[simp]
theorem segreMap_segreElem (i : Fin 3) (j : Fin 2) :
    segreMap k k' (segreElem k i j) = segreElem k' i j :=
  Subtype.ext (mapAlgHom_coneMap_segreGen k k' i j)

/-- `segreMap` is compatible with the maps from the polynomial rings in three variables. -/
theorem segreMap_algebraMap (p : MvPolynomial (Fin 3) k) :
    segreMap k k' (algebraMap (MvPolynomial (Fin 3) k) (segre k) p) =
      algebraMap (MvPolynomial (Fin 3) k') (segre k') (MvPolynomial.map (algebraMap k k') p) := by
  suffices (segreMap k k').comp (segreBase k) =
      ((segreBase k').restrictScalars k).comp (mapAlgHom (Algebra.ofId k k')) from
    congrArg (fun f ↦ f p) this
  refine MvPolynomial.algHom_ext fun i ↦ ?_
  fin_cases i <;> simp [mapAlgHom_apply]

/-- The map `k' ⊗_k Γ_k → Γ_{k'}`. -/
noncomputable def segreBaseChangeHom : k' ⊗[k] segre k →ₐ[k'] segre k' :=
  Algebra.TensorProduct.lift (Algebra.ofId k' _) (segreMap k k') fun _ _ ↦ .all _ _

/-- The map `k' ⊗_k Γ_k → Γ_{k'}` is surjective. -/
theorem segreBaseChangeHom_surjective : Function.Surjective (segreBaseChangeHom k k') := by
  rw [← AlgHom.range_eq_top, eq_top_iff, ← adjoin_segreElem k', Algebra.adjoin_le_iff]
  rintro _ ⟨ij, rfl⟩
  exact ⟨1 ⊗ₜ segreElem k ij.1 ij.2, by simp [segreBaseChangeHom]⟩

/-- For `k'` flat over `k`, the map `k' ⊗_k Γ_k → Γ_{k'}` is injective. -/
theorem segreBaseChangeHom_injective [Module.Flat k k'] :
    Function.Injective (segreBaseChangeHom k k') := by
  have hval : Function.Injective (((segre k).val.toLinearMap).lTensor k') :=
    Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective
  have key (x : k' ⊗[k] segre k) : (segreBaseChangeHom k k' x : MvPolynomial (Fin 2) (Cone k')) =
      polyBaseChange k k' (((segre k).val.toLinearMap).lTensor k' x) := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [segreBaseChangeHom, polyBaseChange]
    | add x y hx hy => simp only [map_add, Subalgebra.coe_add, hx, hy]
  intro x y h
  exact hval (polyBaseChange_injective k k' (by rw [← key, ← key, h]))

/-- The Segre product commutes with flat base change: `k' ⊗_k Γ_k ≃ Γ_{k'}`. -/
noncomputable def segreBaseChange [Module.Flat k k'] : k' ⊗[k] segre k ≃ₐ[k'] segre k' :=
  AlgEquiv.ofBijective (segreBaseChangeHom k k')
    ⟨segreBaseChangeHom_injective k k', segreBaseChangeHom_surjective k k'⟩

/-- `segreBaseChange` sends `a ⊗ x` to `a · segreMap x`. -/
@[simp]
theorem segreBaseChange_tmul [Module.Flat k k'] (a : k') (x : segre k) :
    segreBaseChange k k' (a ⊗ₜ x) = algebraMap k' (segre k') a * segreMap k k' x :=
  rfl

/-- The isomorphism `k' ⊗_k Γ_k ≃ Γ_{k'}` is compatible with the maps from `k[X₀, X₁, X₂]` and
`k'[X₀, X₁, X₂]`. -/
theorem segreBaseChange_one_tmul_algebraMap [Module.Flat k k'] (p : MvPolynomial (Fin 3) k) :
    segreBaseChange k k' (1 ⊗ₜ algebraMap (MvPolynomial (Fin 3) k) (segre k) p) =
      algebraMap (MvPolynomial (Fin 3) k') (segre k') (MvPolynomial.map (algebraMap k k') p) := by
  rw [segreBaseChange_tmul, map_one, one_mul, segreMap_algebraMap]

end Stacks.Examples.OrdinaryCone
