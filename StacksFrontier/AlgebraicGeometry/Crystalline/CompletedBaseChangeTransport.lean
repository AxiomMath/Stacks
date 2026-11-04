module

public import StacksFrontier.AlgebraicGeometry.Crystalline.CompletedBaseChangeCancel
public import StacksFrontier.AlgebraicGeometry.Crystalline.CompletedDeRhamTransport
public import StacksFrontier.AlgebraicGeometry.Crystalline.Cosimplicial.BaseChangeConnectionsHorizontal

/-!
# A base-changed de Rham complex along an isomorphic algebra, in the pushed form

Let `D → D_b` and `D → D'` be two algebras over `D` identified by a ring isomorphism
`u : D_b ≃ D'` over `D`, with an identification of their forms.  Let `(M, ∇)` be a `D`-module with
a completed connection, `M_b` a `D_b`-module identified with the completed base change
`β : (D_b ⊗_D M)^∧ ≃ M_b`, and `∇_b` the base change of `∇` transported along `β`.

This module identifies `M_b ⊗^∧_{D_b} Ω^*_{D_b}` with `M ⊗^∧_D Ω'^*`, the de Rham complex of `M`
over `D` with the connection pushed into the forms of `D'` — compatibly with the differentials
and with the map induced by `m ⊗ ω ↦ β(1 ⊗ m) ⊗ ω`.  In the proof of
[Stacks, Proposition 60.21.3, Tag 07LG] `D_b` is the ring `D(b)` of the cosimplicial degree `b`,
`D'` is the completed divided power polynomial algebra `D⟨ξ⟩^∧` of
[Stacks, Lemma 60.17.5, Tag 07L2], and the second complex is the one
[Stacks, Lemma 60.21.2, Tag 07LD] is proved for.

## Main results

* `Crystalline.CompletedConnection.baseChangeRingEquivMap` — the map of completed base changes
  induced by `u`.
* `Crystalline.CompletedConnection.baseChange_baseChangeRingEquivMap` — **base change is
  natural** in the algebra: `u` carries the base change of `∇` along `D → D_b` to its base
  change along `D → D'`.
* `Crystalline.baseChangePushedEquiv` — the identification of the two complexes, degree by degree.
* `Crystalline.baseChangePushedEquiv_differential` — it commutes with the differentials.
* `Crystalline.baseChangePushedEquiv_comparisonValues` — it carries the map of
  `m ⊗ ω ↦ β(1 ⊗ m) ⊗ ψ_b ω` to `1_M ⊗ ψ`.

## References

* [Stacks Project, Proposition 60.21.3, Tag 07LG](https://stacks.math.columbia.edu/tag/07LG)
* [Stacks Project, Lemma 60.21.2, Tag 07LD](https://stacks.math.columbia.edu/tag/07LD)
-/

@[expose] public noncomputable section

universe u

open DividedPowers
open scoped TensorProduct

namespace Crystalline

section Transport

variable (p : ℕ) {D Db D' : Type u} [CommRing D] [CommRing Db] [CommRing D'] [Algebra D Db]
  [Algebra D D'] (u : Db ≃+* D') (hu : ∀ c : D, u (algebraMap D Db c) = algebraMap D D' c)
  (M : Type u) [AddCommGroup M] [Module D M]

/-- The `D`-linear map underlying an isomorphism of `D`-algebras. -/
def ringEquivLinear : Db →ₗ[D] D' where
  toFun := u
  map_add' := map_add u
  map_smul' c x := by
    rw [Algebra.smul_def, map_mul, hu, RingHom.id_apply, Algebra.smul_def]

/-- The map `D_b ⊗_D M → D' ⊗_D M` induced by an isomorphism of `D`-algebras, semilinear over
it. -/
def tensorMapOfAlgRingEquiv : Db ⊗[D] M →ₛₗ[(u : Db →+* D')] D' ⊗[D] M where
  toFun := TensorProduct.map (ringEquivLinear u hu) LinearMap.id
  map_add' := map_add _
  map_smul' c x := by
    induction x using TensorProduct.induction_on with
    | zero => simp only [smul_zero, _root_.map_zero]
    | tmul b m =>
      rw [TensorProduct.smul_tmul', TensorProduct.map_tmul, TensorProduct.map_tmul,
        TensorProduct.smul_tmul']
      change u (c * b) ⊗ₜ[D] m = (u c * u b) ⊗ₜ[D] m
      rw [map_mul]
    | add x y hx hy => simp only [smul_add, _root_.map_add, hx, hy]

/-- The map `D_b ⊗_D M → D' ⊗_D M` sends `b ⊗ m` to `u b ⊗ m`. -/
theorem tensorMapOfAlgRingEquiv_tmul (b : Db) (m : M) :
    tensorMapOfAlgRingEquiv u hu M (b ⊗ₜ m) = u b ⊗ₜ m := rfl

/-- **The map of completed base changes `(D_b ⊗_D M)^∧ → (D' ⊗_D M)^∧` induced by `u`.** -/
def CompletedConnection.baseChangeRingEquivMap :
    CompletedConnection.baseChangeCarrier p D Db M →ₛₗ[(u : Db →+* D')]
      CompletedConnection.baseChangeCarrier p D D' M :=
  adicCompletionMapₛₗ (tensorMapOfAlgRingEquiv u hu M) (map_pAdicIdeal_le p _)

/-- On the image of `D_b ⊗_D M`, the map of completed base changes is `tensorMapOfAlgRingEquiv`. -/
theorem CompletedConnection.baseChangeRingEquivMap_of (t : Db ⊗[D] M) :
    CompletedConnection.baseChangeRingEquivMap p u hu M (AdicCompletion.of _ _ t) =
      AdicCompletion.of _ _ (tensorMapOfAlgRingEquiv u hu M t) :=
  adicCompletionMapₛₗ_of _ _ t

/-- The map of completed base changes sends `1 ⊗ m` to `1 ⊗ m`. -/
theorem CompletedConnection.baseChangeRingEquivMap_baseChangeInclusion (m : M) :
    CompletedConnection.baseChangeRingEquivMap p u hu M
        (CompletedConnection.baseChangeInclusion p D Db M m) =
      CompletedConnection.baseChangeInclusion p D D' M m := by
  rw [CompletedConnection.baseChangeInclusion_apply, CompletedConnection.baseChangeRingEquivMap_of,
    tensorMapOfAlgRingEquiv_tmul, map_one]
  rfl

include hu in
/-- The inverse of an isomorphism of `D`-algebras is one too. -/
theorem ringEquiv_symm_algebraMap_of_comm :
    ∀ c : D, u.symm (algebraMap D D' c) = algebraMap D Db c := fun c => by
  rw [← hu, RingEquiv.symm_apply_apply]

/-- The map of completed base changes induced by `u.symm` is a left inverse of the one induced by
`u`. -/
theorem CompletedConnection.baseChangeRingEquivMap_symm_baseChangeMap
    (x : CompletedConnection.baseChangeCarrier p D Db M) :
    CompletedConnection.baseChangeRingEquivMap p u.symm (ringEquiv_symm_algebraMap_of_comm u hu) M
        (CompletedConnection.baseChangeRingEquivMap p u hu M x) = x :=
  adicCompletionMapₛₗ_comp_eq_self _ _ _ _ (fun t => by
    induction t using TensorProduct.induction_on with
    | zero => simp only [_root_.map_zero]
    | tmul b m =>
      show u.symm (u b) ⊗ₜ m = b ⊗ₜ m
      rw [RingEquiv.symm_apply_apply]
    | add x y hx hy => rw [_root_.map_add, _root_.map_add, hx, hy]) x

/-- The map of completed base changes induced by `u.symm` is a right inverse of the one induced by
`u`. -/
theorem CompletedConnection.baseChangeRingEquivMap_baseChangeMap_symm
    (x : CompletedConnection.baseChangeCarrier p D D' M) :
    CompletedConnection.baseChangeRingEquivMap p u hu M
        (CompletedConnection.baseChangeRingEquivMap p u.symm
          (ringEquiv_symm_algebraMap_of_comm u hu) M
          x) = x :=
  adicCompletionMapₛₗ_comp_eq_self _ _ _ _ (fun t => by
    induction t using TensorProduct.induction_on with
    | zero => simp only [_root_.map_zero]
    | tmul b m =>
      show u (u.symm b) ⊗ₜ m = b ⊗ₜ m
      rw [RingEquiv.apply_symm_apply]
    | add x y hx hy => rw [_root_.map_add, _root_.map_add, hx, hy]) x

end Transport

section Naturality

variable (p : ℕ) {D Db D' : Type u} [CommRing D] [CommRing Db] [CommRing D'] [Algebra D Db]
  [Algebra D D'] (u : Db ≃+* D') (hu : ∀ c : D, u (algebraMap D Db c) = algebraMap D D' c)
  (M : Type u) [AddCommGroup M] [Module D M]
  (Om : ℕ → Type u) [∀ i, AddCommGroup (Om i)] [∀ i, Module D (Om i)]
  (OmB : ℕ → Type u) [∀ i, AddCommGroup (OmB i)] [∀ i, Module Db (OmB i)]
  (Om' : ℕ → Type u) [∀ i, AddCommGroup (Om' i)] [∀ i, Module D' (Om' i)]
  [∀ i, Module D (Om' i)] [∀ i, IsScalarTower D D' (Om' i)]
  {d : D → Om 1} (dB : Db → OmB 1) (d' : D' → Om' 1)
  (nabla : CompletedConnection p D (Om 1) d M)
  (psiB : ∀ i, Om i →ₛₗ[algebraMap D Db] OmB i) (psi : ∀ i, Om i →ₗ[D] Om' i)
  (fB : ∀ i, OmB i →ₛₗ[(u : Db →+* D')] Om' i)
  (hfpsi : ∀ (i : ℕ) (ω : Om i), fB i (psiB i ω) = psi i ω)
  (hfd : ∀ x : Db, fB 1 (dB x) = d' (u x))
  (hdBadd : ∀ x y : Db, dB (x + y) = dB x + dB y)
  (hdBleib : ∀ x y : Db, dB (x * y) = x • dB y + y • dB x)
  (hpsiB1 : ∀ x : D, psiB 1 (d x) = dB (algebraMap D Db x))
  (hd'add : ∀ x y : D', d' (x + y) = d' x + d' y)
  (hd'leib : ∀ x y : D', d' (x * y) = x • d' y + y • d' x)
  (hpsi1 : ∀ x : D, semilinearOfScalarTower D D' (psi 1) (d x) = d' (algebraMap D D' x))

include hfpsi hfd in
/-- **Base change is natural in the algebra**: the map of completed base changes induced by an
isomorphism `u : D_b ≃ D'` of `D`-algebras carries the base change of `∇` along `D → D_b` to its
base change along `D → D'`, read through the identification of the forms. -/
theorem CompletedConnection.baseChange_baseChangeRingEquivMap
    (x : CompletedConnection.baseChangeCarrier p D Db M) :
    CompletedConnection.baseChange p D D' M (Om 1) (Om' 1) d'
        (semilinearOfScalarTower D D' (psi 1)) nabla hd'add hd'leib hpsi1
        (CompletedConnection.baseChangeRingEquivMap p u hu M x) =
      CompletedDeRham.comparisonValues p Db D' (u : Db →+* D')
        (CompletedConnection.baseChangeCarrier p D Db M)
        (CompletedConnection.baseChangeCarrier p D D' M)
        (CompletedConnection.baseChangeRingEquivMap p u hu M) OmB Om' fB 1
        (CompletedConnection.baseChange p D Db M (Om 1) (OmB 1) dB (psiB 1) nabla hdBadd hdBleib
          hpsiB1 x) := by
  rw [← sub_eq_zero]
  let δ : CompletedConnection.baseChangeCarrier p D Db M →+
      CompletedTensor p D' (Om' 1) (CompletedConnection.baseChangeCarrier p D D' M) :=
    AddMonoidHom.mk' (fun x => CompletedConnection.baseChange p D D' M (Om 1) (Om' 1) d'
        (semilinearOfScalarTower D D' (psi 1)) nabla hd'add hd'leib hpsi1
        (CompletedConnection.baseChangeRingEquivMap p u hu M x) -
      CompletedDeRham.comparisonValues p Db D' (u : Db →+* D')
        (CompletedConnection.baseChangeCarrier p D Db M)
        (CompletedConnection.baseChangeCarrier p D D' M)
        (CompletedConnection.baseChangeRingEquivMap p u hu M) OmB Om' fB 1
        (CompletedConnection.baseChange p D Db M (Om 1) (OmB 1) dB (psiB 1) nabla hdBadd
          hdBleib hpsiB1 x))
      (fun x y => by
        rw [_root_.map_add, CompletedConnection.map_add, CompletedConnection.map_add,
          _root_.map_add]
        abel)
  refine eq_zero_of_baseChangeInclusion p (u : Db →+* D') δ (fun c y => ?_) (fun m => ?_) x
  · simp only [δ, AddMonoidHom.mk'_apply]
    rw [(CompletedConnection.baseChangeRingEquivMap p u hu M).map_smulₛₗ,
      CompletedConnection.baseChange_smul, CompletedConnection.baseChange_smul, _root_.map_add,
      (CompletedDeRham.comparisonValues p Db D' (u : Db →+* D') _ _
        (CompletedConnection.baseChangeRingEquivMap p u hu M) OmB Om' fB 1).map_smulₛₗ,
      CompletedDeRham.comparisonValues_of_tmul, hfd]
    rw [smul_sub]
    simp only [RingEquiv.coe_toRingHom]
    abel
  · simp only [δ, AddMonoidHom.mk'_apply]
    rw [CompletedConnection.baseChangeRingEquivMap_baseChangeInclusion,
      CompletedConnection.baseChange_inclusion, CompletedConnection.baseChange_inclusion,
      sub_eq_zero]
    refine adicCompletionMapₛₗ_comp_apply _ _ _ _ _ _ (fun y => ?_) (nabla m)
    induction y using TensorProduct.induction_on with
    | zero => simp only [_root_.map_zero]
    | tmul m' η =>
      show CompletedConnection.baseChangeInclusion p D D' M m' ⊗ₜ[D']
          semilinearOfScalarTower D D' (psi 1) η =
        CompletedConnection.baseChangeRingEquivMap p u hu M
            (CompletedConnection.baseChangeInclusion p D Db M m') ⊗ₜ[D'] fB 1 (psiB 1 η)
      rw [CompletedConnection.baseChangeRingEquivMap_baseChangeInclusion, hfpsi]
      rfl
    | add y z hy hz => rw [_root_.map_add, _root_.map_add, _root_.map_add, hy, hz]

end Naturality

section Pushed

variable (p : ℕ) {D Db D' : Type u} [CommRing D] [CommRing Db] [CommRing D'] [Algebra D Db]
  [Algebra D D'] (u : Db ≃+* D') (hu : ∀ c : D, u (algebraMap D Db c) = algebraMap D D' c)
  (M : Type u) [AddCommGroup M] [Module D M]
  (Om : ℕ → Type u) [∀ i, AddCommGroup (Om i)] [∀ i, Module D (Om i)]
  (OmB : ℕ → Type u) [∀ i, AddCommGroup (OmB i)] [∀ i, Module Db (OmB i)]
  (Om' : ℕ → Type u) [∀ i, AddCommGroup (Om' i)] [∀ i, Module D' (Om' i)]
  [∀ i, Module D (Om' i)] [∀ i, IsScalarTower D D' (Om' i)]
  {d : D → Om 1} (dB : Db → OmB 1) (d' : D' → Om' 1) (dD : D → Om' 1)
  (nabla : CompletedConnection p D (Om 1) d M)
  (psiB : ∀ i, Om i →ₛₗ[algebraMap D Db] OmB i) (psi : ∀ i, Om i →ₗ[D] Om' i)
  (fB : ∀ i, OmB i →ₛₗ[(u : Db →+* D')] Om' i)
  (fBinv : ∀ i, Om' i →ₛₗ[(u.symm : D' →+* Db)] OmB i)
  (hfB : ∀ (i : ℕ) (ω : OmB i), fBinv i (fB i ω) = ω)
  (hfB' : ∀ (i : ℕ) (ω : Om' i), fB i (fBinv i ω) = ω)
  (hfpsi : ∀ (i : ℕ) (ω : Om i), fB i (psiB i ω) = psi i ω)
  (hfd : ∀ x : Db, fB 1 (dB x) = d' (u x))
  (hdBadd : ∀ x y : Db, dB (x + y) = dB x + dB y)
  (hdBleib : ∀ x y : Db, dB (x * y) = x • dB y + y • dB x)
  (hpsiB1 : ∀ x : D, psiB 1 (d x) = dB (algebraMap D Db x))
  (hd'add : ∀ x y : D', d' (x + y) = d' x + d' y)
  (hd'leib : ∀ x y : D', d' (x * y) = x • d' y + y • d' x)
  (hpsi1 : ∀ x : D, semilinearOfScalarTower D D' (psi 1) (d x) = d' (algebraMap D D' x))
  (MB : Type u) [AddCommGroup MB] [Module Db MB]
  (β : CompletedConnection.baseChangeCarrier p D Db M ≃ₗ[Db] MB)

/-- The identification of `M_b` with `(D' ⊗_D M)^∧`: the inverse of `β` followed by the map of
completed base changes of `u`. -/
def pushedModuleMap : MB →ₛₗ[(u : Db →+* D')] CompletedConnection.baseChangeCarrier p D D' M :=
  (CompletedConnection.baseChangeRingEquivMap p u hu M).comp β.symm.toLinearMap

/-- Its inverse. -/
def pushedModuleMapInv :
    CompletedConnection.baseChangeCarrier p D D' M →ₛₗ[(u.symm : D' →+* Db)] MB :=
  β.toLinearMap.comp
    (CompletedConnection.baseChangeRingEquivMap p u.symm (ringEquiv_symm_algebraMap_of_comm u hu) M)

/-- `pushedModuleMapInv` is a left inverse of `pushedModuleMap`. -/
theorem pushedModuleMapInv_pushedModuleMap (y : MB) :
    pushedModuleMapInv p u hu M MB β (pushedModuleMap p u hu M MB β y) = y := by
  show β (CompletedConnection.baseChangeRingEquivMap p u.symm _ M
    (CompletedConnection.baseChangeRingEquivMap p u hu M (β.symm y))) = y
  rw [CompletedConnection.baseChangeRingEquivMap_symm_baseChangeMap, LinearEquiv.apply_symm_apply]

/-- `pushedModuleMapInv` is a right inverse of `pushedModuleMap`. -/
theorem pushedModuleMap_pushedModuleMapInv
    (y : CompletedConnection.baseChangeCarrier p D D' M) :
    pushedModuleMap p u hu M MB β (pushedModuleMapInv p u hu M MB β y) = y := by
  show CompletedConnection.baseChangeRingEquivMap p u hu M
    (β.symm (β (CompletedConnection.baseChangeRingEquivMap p u.symm _ M y))) = y
  rw [LinearEquiv.symm_apply_apply, CompletedConnection.baseChangeRingEquivMap_baseChangeMap_symm]

/-- On `β x`, the identification `pushedModuleMap` is the map of completed base changes of `u`
applied to `x`. -/
theorem pushedModuleMap_apply (x : CompletedConnection.baseChangeCarrier p D Db M) :
    pushedModuleMap p u hu M MB β (β x) =
      CompletedConnection.baseChangeRingEquivMap p u hu M x := by
  show CompletedConnection.baseChangeRingEquivMap p u hu M (β.symm (β x)) = _
  rw [LinearEquiv.symm_apply_apply]

/-- **The identification `M_b ⊗̂_{D_b} Ω_b^i ≃ M ⊗̂_D Ω'^i`**, degree by degree: the comparison of
`M_b` with `(D' ⊗_D M)^∧` and of the forms, followed by the cancellation
`Crystalline.completedBaseChangeCancel`. -/
def baseChangePushedEquiv (i : ℕ) :
    CompletedTensor p Db (OmB i) MB ≃+ CompletedTensor p D (Om' i) M where
  toFun x := completedBaseChangeCancel p D D' (Om' i) M
    (CompletedDeRham.isoValuesFwd p u (pushedModuleMap p u hu M MB β) fB i x)
  invFun y := CompletedDeRham.isoValuesBwd p u (pushedModuleMapInv p u hu M MB β) fBinv i
    ((completedBaseChangeCancel p D D' (Om' i) M).symm y)
  left_inv x := by
    simp only [AddEquiv.symm_apply_apply]
    exact CompletedDeRham.isoValues_bwd_fwd p u _ _ fB fBinv
      (pushedModuleMapInv_pushedModuleMap p u hu M MB β) hfB i x
  right_inv y := by
    simp only
    rw [CompletedDeRham.isoValues_fwd_bwd p u _ _ fB fBinv
      (pushedModuleMap_pushedModuleMapInv p u hu M MB β) hfB' i,
      AddEquiv.apply_symm_apply]
  map_add' x y := by simp only [_root_.map_add]

/-- The identification `M_b ⊗̂_{D_b} Ω_b^i ≃ M ⊗̂_D Ω'^i` is the comparison of the modules and of
the forms followed by `Crystalline.completedBaseChangeCancel`. -/
theorem baseChangePushedEquiv_apply (i : ℕ) (x : CompletedTensor p Db (OmB i) MB) :
    baseChangePushedEquiv p u hu M OmB Om' fB fBinv hfB hfB' MB β i x =
      completedBaseChangeCancel p D D' (Om' i) M
        (CompletedDeRham.isoValuesFwd p u (pushedModuleMap p u hu M MB β) fB i x) := rfl

include hfpsi in
/-- **The identification carries the map `m ⊗ ω ↦ g m ⊗ ψ_b ω` to `1_M ⊗ ψ`**, where
`g m = β (1 ⊗ m)`. -/
theorem baseChangePushedEquiv_comparisonValues (g : M →ₛₗ[algebraMap D Db] MB)
    (hg : ∀ m, g m = β (CompletedConnection.baseChangeInclusion p D Db M m)) (i : ℕ)
    (z : CompletedTensor p D (Om i) M) :
    baseChangePushedEquiv p u hu M OmB Om' fB fBinv hfB hfB' MB β i
        (CompletedDeRham.comparisonValues p D Db (algebraMap D Db) M MB g Om OmB psiB i z) =
      CompletedDeRham.completedLTensor p D M (psi i) z := by
  let F : CompletedTensor p D (Om i) M →+ CompletedTensor p D (Om' i) M :=
    (baseChangePushedEquiv p u hu M OmB Om' fB fBinv hfB hfB' MB β i).toAddMonoidHom.comp
      (CompletedDeRham.comparisonValues p D Db (algebraMap D Db) M MB g Om OmB psiB i)
  suffices h : F = CompletedDeRham.completedLTensor p D M (psi i) from DFunLike.congr_fun h z
  refine completedTensor_addMonoidHom_ext p fun m ω => ?_
  show baseChangePushedEquiv p u hu M OmB Om' fB fBinv hfB hfB' MB β i
      (CompletedDeRham.comparisonValues p D Db (algebraMap D Db) M MB g Om OmB psiB i
        (toCompletedTensor p D (Om i) M (m ⊗ₜ ω))) =
    CompletedDeRham.completedLTensor p D M (psi i) (toCompletedTensor p D (Om i) M (m ⊗ₜ ω))
  rw [CompletedDeRham.comparisonValues_of_tmul, baseChangePushedEquiv_apply,
    CompletedDeRham.comparisonValues_of_tmul, hg, pushedModuleMap_apply,
    CompletedConnection.baseChangeRingEquivMap_baseChangeInclusion, hfpsi,
    ← completedBaseChangeCancel_symm_of_tmul, AddEquiv.apply_symm_apply,
    CompletedDeRham.completedLTensor_toCompletedTensor_tmul]

end Pushed

section PushedDifferential

variable (p : ℕ) {D Db D' : Type u} [CommRing D] [CommRing Db] [CommRing D'] [Algebra D Db]
  [Algebra D D'] (u : Db ≃+* D') (hu : ∀ c : D, u (algebraMap D Db c) = algebraMap D D' c)
  (M : Type u) [AddCommGroup M] [Module D M]
  (Om : ℕ → Type u) [∀ i, AddCommGroup (Om i)] [∀ i, Module D (Om i)]
  (OmB : ℕ → Type u) [∀ i, AddCommGroup (OmB i)] [∀ i, Module Db (OmB i)]
  (Om' : ℕ → Type u) [∀ i, AddCommGroup (Om' i)] [∀ i, Module D' (Om' i)]
  [∀ i, Module D (Om' i)] [∀ i, IsScalarTower D D' (Om' i)]
  {d : D → Om 1} (dB : Db → OmB 1) (d' : D' → Om' 1) (dD : D → Om' 1)
  (nabla : CompletedConnection p D (Om 1) d M)
  (psiB : ∀ i, Om i →ₛₗ[algebraMap D Db] OmB i) (psi : ∀ i, Om i →ₗ[D] Om' i)
  (fB : ∀ i, OmB i →ₛₗ[(u : Db →+* D')] Om' i)
  (fBinv : ∀ i, Om' i →ₛₗ[(u.symm : D' →+* Db)] OmB i)
  (hfB : ∀ (i : ℕ) (ω : OmB i), fBinv i (fB i ω) = ω)
  (hfB' : ∀ (i : ℕ) (ω : Om' i), fB i (fBinv i ω) = ω)
  (hfpsi : ∀ (i : ℕ) (ω : Om i), fB i (psiB i ω) = psi i ω)
  (hfd : ∀ x : Db, fB 1 (dB x) = d' (u x))
  (hdBadd : ∀ x y : Db, dB (x + y) = dB x + dB y)
  (hdBleib : ∀ x y : Db, dB (x * y) = x • dB y + y • dB x)
  (hpsiB1 : ∀ x : D, psiB 1 (d x) = dB (algebraMap D Db x))
  (hd'add : ∀ x y : D', d' (x + y) = d' x + d' y)
  (hd'leib : ∀ x y : D', d' (x * y) = x • d' y + y • d' x)
  (hpsi1 : ∀ x : D, semilinearOfScalarTower D D' (psi 1) (d x) = d' (algebraMap D D' x))
  (MB : Type u) [AddCommGroup MB] [Module Db MB]
  (β : CompletedConnection.baseChangeCarrier p D Db M ≃ₗ[Db] MB)
  (wedgeB : ∀ i, OmB i →ₗ[Db] OmB 1 →ₗ[Db] OmB (i + 1)) (deRhamB : ∀ i, OmB i →+ OmB (i + 1))
  (hleibB : CompletedDeRham.IsGradedLeibniz Db OmB wedgeB deRhamB dB)
  (wedge' : ∀ i, Om' i →ₗ[D'] Om' 1 →ₗ[D'] Om' (i + 1)) (deRham' : ∀ i, Om' i →+ Om' (i + 1))
  (hleib' : CompletedDeRham.IsGradedLeibniz D' Om' wedge' deRham' d')
  (hfwedge : ∀ (i : ℕ) (ω : OmB i) (η : OmB 1),
    fB (i + 1) (wedgeB i ω η) = wedge' i (fB i ω) (fB 1 η))
  (hfdeRham : ∀ (i : ℕ) (ω : OmB i), fB (i + 1) (deRhamB i ω) = deRham' i (fB i ω))
  (wedgeD : ∀ i, Om' i →ₗ[D] Om' 1 →ₗ[D] Om' (i + 1))
  (hwedgeD : ∀ (i : ℕ) (ω : Om' i) (η : Om' 1), wedgeD i ω η = wedge' i ω η)
  (hleibD : CompletedDeRham.IsGradedLeibniz D Om' wedgeD deRham' dD)
  (nablaD : CompletedConnection p D (Om' 1) dD M)
  (hnablaD : ∀ m : M, nablaD m = CompletedDeRham.completedLTensor p D M (psi 1) (nabla m))
  (nablaB : CompletedConnection p Db (OmB 1) dB MB)
  (hnablaB : ∀ x, nablaB (β x) =
    CompletedDeRham.isoValuesFwd p (RingEquiv.refl Db) β.toLinearMap (fun _ => LinearMap.id) 1
      (CompletedConnection.baseChange p D Db M (Om 1) (OmB 1) dB (psiB 1) nabla hdBadd hdBleib
        hpsiB1 x))

include hfpsi hfd hnablaB in
/-- `∇_b` corresponds to the base change of `∇` along `D → D'` under the identification of
`M_b` with `(D' ⊗_D M)^∧`. -/
theorem baseChange_pushedModuleMap (y : MB) :
    CompletedConnection.baseChange p D D' M (Om 1) (Om' 1) d'
        (semilinearOfScalarTower D D' (psi 1)) nabla hd'add hd'leib hpsi1
        (pushedModuleMap p u hu M MB β y) =
      CompletedDeRham.comparisonValues p Db D' (u : Db →+* D') MB
        (CompletedConnection.baseChangeCarrier p D D' M) (pushedModuleMap p u hu M MB β)
        OmB Om' fB 1 (nablaB y) := by
  rw [← β.apply_symm_apply y, pushedModuleMap_apply, hnablaB,
    CompletedConnection.baseChange_baseChangeRingEquivMap p u hu M Om OmB Om' dB d' nabla psiB psi
      fB
      hfpsi hfd hdBadd hdBleib hpsiB1 hd'add hd'leib hpsi1]
  refine adicCompletionMapₛₗ_comp_apply _ _ _ _ _ _ (fun t => ?_) _
  induction t using TensorProduct.induction_on with
  | zero => simp only [_root_.map_zero]
  | tmul x ω =>
    show CompletedConnection.baseChangeRingEquivMap p u hu M x ⊗ₜ[D'] fB 1 ω =
      pushedModuleMap p u hu M MB β (β x) ⊗ₜ[D'] fB 1 ω
    rw [pushedModuleMap_apply]
  | add a b ha hb => rw [_root_.map_add, _root_.map_add, _root_.map_add, ha, hb]

include hfpsi hfd hnablaB hfwedge hfdeRham hwedgeD hnablaD hd'add hd'leib hpsi1 hleib' hdBadd
  hdBleib hpsiB1 in
/-- **The identification `M_b ⊗̂_{D_b} Ω_b^* ≃ M ⊗̂_D Ω'^*` commutes with the de Rham
differentials** of `∇_b` and of the connection `∇` pushed into `Ω'¹`. -/
theorem baseChangePushedEquiv_differential (i : ℕ) (x : CompletedTensor p Db (OmB i) MB) :
    baseChangePushedEquiv p u hu M OmB Om' fB fBinv hfB hfB' MB β (i + 1)
        (CompletedDeRham.differential p Db OmB wedgeB deRhamB MB nablaB hleibB i x) =
      CompletedDeRham.differential p D Om' wedgeD deRham' M nablaD hleibD i
        (baseChangePushedEquiv p u hu M OmB Om' fB fBinv hfB hfB' MB β i x) := by
  rw [baseChangePushedEquiv_apply, baseChangePushedEquiv_apply,
    ← CompletedDeRham.differential_comparisonValues p Db D' (u : Db →+* D') MB
      (CompletedConnection.baseChangeCarrier p D D' M) (pushedModuleMap p u hu M MB β)
      OmB Om' fB wedgeB wedge' deRhamB deRham' nablaB
      (CompletedConnection.baseChange p D D' M (Om 1) (Om' 1) d'
        (semilinearOfScalarTower D D' (psi 1)) nabla hd'add hd'leib hpsi1) hleibB hleib'
      hfwedge hfdeRham
      (baseChange_pushedModuleMap p u hu M Om OmB Om' dB d' nabla psiB psi fB hfpsi hfd
        hdBadd hdBleib hpsiB1 hd'add hd'leib hpsi1 MB β nablaB hnablaB) i x]
  exact completedBaseChangeCancel_differential p D D' M Om Om' wedge' wedgeD hwedgeD deRham' d' dD
    nabla psi hd'add hd'leib hleib' hleibD nablaD hnablaD hpsi1 i _

end PushedDifferential

end Crystalline

end
