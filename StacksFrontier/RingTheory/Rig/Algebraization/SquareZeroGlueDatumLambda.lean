module

public import StacksFrontier.RingTheory.Rig.Algebraization.SquareZeroGlueDatumLocalization
public import StacksFrontier.RingTheory.Rig.Algebraization.SquareZeroLiftLambda

/-!
# The square-zero ideal of the ring glued from a glueing datum

For a glueing datum `D`, the kernel `N T` of the surjection `T → S` of the glued ring is a
quotient of `P = S ⊗[R] N` through the multiplication map `Λ : P → T`. This file records the
components of `Λ` and proves that `T` is of finite type over `R`.

## Main definitions

* `Rig.SquareZeroLift.GlueDatum.Lam`: the multiplication `Λ : S ⊗[R] N → T`.

## Main results

* `Rig.SquareZeroLift.GlueDatum.finiteType_glued`: the glued ring is of finite type over `R`.
-/

@[expose] public section

namespace Rig.SquareZeroLift.GlueDatum

open TensorProduct Cech FormalGlueing

universe u

variable {R : Type u} [CommRing R] {N : Ideal R} (hN : N ^ 2 = ⊥)
variable {k : ℕ} {f : Fin k → R}
variable {S : Type u} [CommRing S] [Algebra R S]
variable {H : Type u} [CommRing H] [Algebra R H]
variable {e : (H ⧸ N.map (algebraMap R H)) ≃ₐ[R] Sh f S}
variable (D : GlueDatum N f S H e)
variable [IsNoetherianRing S] (hNS : N.map (algebraMap R S) = ⊥)
variable (hflat : ∀ i, Module.Flat R (Localization.Away (algebraMap R H (f i))))

include hN in
/-- The identification `T ⧸ N T ≅ S`. -/
noncomputable def qeT : (D.TT ⧸ N.map (algebraMap R D.TT)) ≃ₐ[R]
    S :=
  (Ideal.quotientEquivAlgOfEq R (D.ker_prS hN hNS hflat).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (D.prS_surjective hN hflat))

/-- The identification `qeT` sends the class of `t` to `prS t`. -/
theorem qeT_mk (t : D.TT) :
    D.qeT hN hNS hflat (Ideal.Quotient.mk _ t) = D.prS t := by
  simp only [qeT]
  rfl

include hN in
/-- The multiplication `Λ : S ⊗[R] N → T`. -/
noncomputable def Lam : PS N S →ₗ[R] D.TT :=
  theta N hN (D.qeT hN hNS hflat).symm.toAlgHom

/-- The class of `t` in `T ⧸ N T` is the image of `prS t` under the inverse of `qeT`. -/
theorem mk_eq_qeT_symm (t : D.TT) :
    Ideal.Quotient.mk _ t =
      (D.qeT hN hNS hflat).symm.toAlgHom (D.prS t) := by
  rw [← D.qeT_mk hN hNS hflat]
  simp

/-- If `prS t = a`, then `Λ (a ⊗ n) = n • t`. -/
theorem Lam_tmul (a : S) (n : N) (t : D.TT) (ht : D.prS t = a) :
    D.Lam hN hNS hflat (a ⊗ₜ n) = (n : R) • t :=
  theta_tmul N hN _ a n t (ht ▸ D.mk_eq_qeT_symm hN hNS hflat t)

/-- The image of `Λ` lies in the kernel of `prS`. -/
theorem prS_Lam (z : PS N S) : D.prS (D.Lam hN hNS hflat z) = 0 :=
  (D.ker_prS hN hNS hflat).ge (theta_mem N hN (D.qeT hN hNS hflat).symm.toAlgHom z)

/-- `β (Λ z) = θ_λ' z` when `λ'` is compatible with the class of `t` modulo `N T`. -/
private theorem map_Lam_eq_theta {B' : Type*} [CommRing B'] [Algebra R B'] (β : D.TT →ₐ[R] B')
    (L' : S →ₐ[R] B' ⧸ N.map (algebraMap R B'))
    (h : ∀ t, Ideal.Quotient.mk _ (β t) = L' (D.prS t)) (z : PS N S) :
    β (D.Lam hN hNS hflat z) = theta N hN L' z := by
  apply theta_naturality
  ext a
  obtain ⟨t, rfl⟩ := D.prS_surjective hN hflat a
  rw [AlgHom.comp_apply, ← D.mk_eq_qeT_symm hN, redMap_mk, h]

/-- The `H`-component of `Λ z` is `muH0 (z ⊗ 1)`. -/
theorem prH_Lam (z : PS N S) :
    D.prH (D.Lam hN hNS hflat z) = muH0 N hN f S H e (z ⊗ₜ 1) := by
  rw [muH0_tmul_one]
  exact D.map_Lam_eq_theta hN hNS hflat _ _ D.mk_prH z

/-- The component of `Λ z` at a singleton `u` is `muV` applied to the image of `z` in the
localization at `u`. -/
theorem prV_Lam (u : {s : Finset (Fin k) // s.card = 1}) (z : PS N S) :
    D.prV u (D.Lam hN hNS hflat z) =
      muV N hN f S D.L u.1 (LocalizedModule.mkLinearMap _ _ z) := by
  rw [muV_mk]
  exact D.map_Lam_eq_theta hN hNS hflat _ _ (D.mk_prV u) z

/-- The image of `Λ` lies in `N T`. -/
theorem Lam_mem (z : PS N S) :
    D.Lam hN hNS hflat z ∈ N.map (algebraMap R D.TT) :=
  theta_mem N hN _ z

/-- Every element of `N T` lies in the image of `Λ`. -/
theorem exists_Lam_eq (x : D.TT)
    (hx : x ∈ N.map (algebraMap R D.TT)) :
    ∃ z, D.Lam hN hNS hflat z = x := by
  obtain ⟨w, rfl⟩ := exists_multT_eq N hN _ x hx
  refine ⟨(LinearEquiv.rTensor N (D.qeT hN hNS hflat).toLinearEquiv) w, ?_⟩
  have : ((D.qeT hN hNS hflat).symm.toAlgHom.toLinearMap.rTensor N) ∘ₗ
      (LinearEquiv.rTensor N (D.qeT hN hNS hflat).toLinearEquiv).toLinearMap =
      LinearMap.id := by
    refine TensorProduct.ext' fun a n ↦ ?_
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.rTensor_tmul,
      LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, LinearMap.id_apply]
    congr 1
    exact (D.qeT hN hNS hflat).symm_apply_apply a
  simp only [Lam, theta, LinearMap.comp_apply]
  exact congrArg (multT N hN _) (LinearMap.congr_fun this w)

/-- If `prS t = a`, then `Λ (a • z) = t * Λ z`. -/
theorem Lam_smul (a : S) (z : PS N S) (t : D.TT)
    (ht : D.prS t = a) :
    D.Lam hN hNS hflat (a • z) = t * D.Lam hN hNS hflat z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul b n =>
    rw [TensorProduct.smul_tmul', smul_eq_mul]
    exact theta_mul N hN _ a b n t (ht ▸ D.mk_eq_qeT_symm hN hNS hflat t)
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, mul_add]

/-- If `muH0 (z ⊗ 1) = 0` and the image of `z` in each localization at a singleton vanishes, then
`Λ z = 0`. -/
theorem Lam_eq_zero (z : PS N S) (hH : muH0 N hN f S H e (z ⊗ₜ 1) = 0)
    (hV : ∀ u : {s : Finset (Fin k) // s.card = 1},
      LocalizedModule.mkLinearMap (cechSub (gS f S) u.1) (PS N S) z = 0) :
    D.Lam hN hNS hflat z = 0 := by
  apply D.ext_glued
  · exact D.prS_Lam hN hNS hflat z
  · exact (D.prH_Lam hN hNS hflat z).trans hH
  · funext u
    exact (D.prV_Lam hN hNS hflat u z).trans (by rw [hV u, map_zero]; rfl)

include hN hNS hflat in
/-- **The glued ring is of finite type.** -/
theorem finiteType_glued [Algebra.FiniteType R S] :
    Algebra.FiniteType R D.TT := by
  classical
  obtain ⟨s, hs⟩ := (Algebra.FiniteType.out : (⊤ : Subalgebra R S).FG)
  choose lift hlift using D.prS_surjective hN hflat
  let A := Algebra.adjoin R ((s.image lift : Finset _) : Set D.TT)
  have hmap : A.map D.prS = ⊤ := by
    rw [AlgHom.map_adjoin, ← hs]
    congr 1
    rw [Finset.coe_image, Set.image_image]
    simp only [hlift, Set.image_id']
  have hA (x : D.TT) : ∃ a ∈ A, D.prS a = D.prS x :=
    Subalgebra.mem_map.mp (hmap ▸ Algebra.mem_top : D.prS x ∈ A.map D.prS)
  have hsub {x y : D.TT} (h : D.prS y = D.prS x) : x - y ∈ N.map (algebraMap R D.TT) := by
    rw [← D.ker_prS hN hNS hflat]
    show D.prS (x - y) = 0
    rw [map_sub, h, sub_self]
  have hNA : ∀ x ∈ N.map (algebraMap R D.TT), x ∈ A := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨n, -, rfl⟩ := hy
      exact A.algebraMap_mem n
    | zero => exact A.zero_mem
    | add x y _ _ hx hy => exact A.add_mem hx hy
    | smul c x hxN hx =>
      obtain ⟨a, ha, hac⟩ := hA c
      have h0 : (c - a) * x = 0 := by
        have : (c - a) * x ∈ N.map (algebraMap R D.TT) ^ 2 := by
          rw [pow_two]
          exact Ideal.mul_mem_mul (hsub hac) hxN
        rwa [map_sq_eq_bot N hN] at this
      rw [smul_eq_mul, show c * x = a * x by rw [← sub_eq_zero, ← sub_mul, h0]]
      exact A.mul_mem ha hx
  refine ⟨⟨s.image lift, eq_top_iff.mpr fun x _ ↦ ?_⟩⟩
  obtain ⟨a, ha, hax⟩ := hA x
  rw [show x = a + (x - a) by ring]
  exact A.add_mem ha (hNA _ (hsub hax))

end Rig.SquareZeroLift.GlueDatum

end
