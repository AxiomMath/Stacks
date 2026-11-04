module

public import StacksFrontier.RingTheory.Rig.Algebraization.SquareZeroLiftEtale
import all StacksFrontier.RingTheory.Localization.Glueing.FormalGlueingComplex

/-!
# The square-zero ideal of the glued ring

In the setting of `StacksFrontier.RingTheory.Rig.Algebraization.SquareZeroLiftRing`, the kernel
`N T` of the surjection `T → S` is a quotient of `P = S ⊗[R] N` through the multiplication map
`Λ : P → T`. This file records the components of `Λ`, proves that `T` is of finite type over
`R`, and proves a torsion-descent lemma for flat maps that are isomorphisms modulo an ideal,
used for the effectivity of the glueing in
`StacksFrontier.RingTheory.Rig.Algebraization.SquareZeroLiftComplete`.

## Main definitions

* `Rig.SquareZeroLift.Lam`: the multiplication `Λ : S ⊗[R] N → T`.

## Main results

* `Rig.SquareZeroLift.finiteType_glued`: the glued ring is of finite type over `R`.
* `Rig.SquareZeroLift.exists_eq_unitMap_of_torsion`: torsion descent.
-/

@[expose] public section

namespace Rig.SquareZeroLift

open TensorProduct Cech FormalGlueing
open _root_.IPowerTorsion (unitMap)

universe u

/-- **Torsion descent.** If `A → A'` is flat and an isomorphism modulo a finitely generated
ideal `J`, an element of `M ⊗[A] A'` killed by `J ^ m` is the base change of an element of `M`
killed by `J ^ m`. -/
theorem exists_eq_unitMap_of_torsion {A A' : Type*} [CommRing A] [CommRing A'] [Algebra A A']
    (J : Ideal A) (hflat : Module.Flat A A')
    (hq : Function.Bijective
      (Ideal.quotientMap (J.map (algebraMap A A')) (algebraMap A A') Ideal.le_comap_map))
    {M : Type*} [AddCommGroup M] [Module A M] (m : ℕ) (hm : 0 < m) (hJ : (J ^ m).FG)
    (k : M ⊗[A] A') (hk : ∀ c ∈ J ^ m, c • k = 0) :
    ∃ z : M, (∀ c ∈ J ^ m, c • z = 0) ∧ unitMap A A' M z = k := by
  classical
  obtain ⟨s, hs⟩ := hJ
  let c : s → A := Subtype.val
  let φ : M →ₗ[A] (s → M) := LinearMap.pi fun i ↦ c i • LinearMap.id
  have hφk : φ.rTensor A' k = 0 := by
    apply (TensorProduct.piLeft A A' (fun _ : s ↦ M)).symm.symm.injective
    rw [map_zero]
    funext i
    have hc : c i ∈ J ^ m := hs ▸ Submodule.subset_span i.2
    have h1 : ∀ w : M ⊗[A] A', TensorProduct.piLeft A A' (fun _ : s ↦ M) (φ.rTensor A' w) i =
        c i • w := by
      intro w
      induction w using TensorProduct.induction_on with
      | zero => simp
      | tmul x y => simp [φ, TensorProduct.smul_tmul']
      | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy, smul_add]
    rw [LinearEquiv.symm_symm, h1, hk _ hc]
    rfl
  obtain ⟨w, hw⟩ := (Module.Flat.rTensor_exact A' φ.exact_subtype_ker_map k).mp hφk
  have key : ∀ y ∈ LinearMap.ker φ, ∀ a ∈ J ^ m, a • y = 0 := by
    intro y hy a ha
    rw [← hs] at ha
    induction ha using Submodule.span_induction with
    | mem a ha => simpa [φ, c] using congrFun hy ⟨a, ha⟩
    | zero => simp
    | add a b _ _ ha hb => rw [add_smul, ha, hb, add_zero]
    | smul a b _ hb => rw [smul_eq_mul, mul_smul, hb, smul_zero]
  have htors : IsIPowerTorsion A (LinearMap.ker φ) J :=
    fun x ↦ ⟨m, hm, fun a ha ↦ Subtype.ext (key x.1 x.2 a ha)⟩
  obtain ⟨z, hz⟩ := (unitMap_bijective_of_torsion J hflat hq _ htors).2 w
  refine ⟨z.1, key z.1 z.2, ?_⟩
  rw [← hw, ← hz]
  simp [unitMap]

variable {R : Type u} [CommRing R] (N : Ideal R) (hN : N ^ 2 = ⊥)
variable {k : ℕ} (f : Fin k → R)
variable (S : Type u) [CommRing S] [Algebra R S]
variable (H : Type u) [CommRing H] [Algebra R H]
variable (e : (H ⧸ N.map (algebraMap R H)) ≃ₐ[R] Sh f S)
variable (L : ∀ s : Finset (Fin k), NilLift R N (Sl f S s))
variable (hL : ∀ s, s.Nonempty → Algebra.Etale R (L s).carrier)
variable [IsNoetherianRing S] (hNS : N.map (algebraMap R S) = ⊥)
variable (hflat : ∀ i, Module.Flat R (Localization.Away (algebraMap R H (f i))))

/-- The identification `T ⧸ N T ≅ S`. -/
noncomputable def qeT : (TT N hN f S H e L hL ⧸ N.map (algebraMap R (TT N hN f S H e L hL))) ≃ₐ[R]
    S :=
  (Ideal.quotientEquivAlgOfEq R (ker_prS N hN f S H e L hL hNS hflat).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (prS_surjective N hN f S H e L hL hflat))

/-- The identification `qeT` sends the class of `t` to its image `prS t` in `S`. -/
theorem qeT_mk (t : TT N hN f S H e L hL) :
    qeT N hN f S H e L hL hNS hflat (Ideal.Quotient.mk _ t) = prS N hN f S H e L hL t := by
  simp only [qeT]
  rfl

/-- The multiplication `Λ : S ⊗[R] N → T`. -/
noncomputable def Lam : PS N S →ₗ[R] TT N hN f S H e L hL :=
  theta N hN (qeT N hN f S H e L hL hNS hflat).symm.toAlgHom

/-- The class of `t` in `T ⧸ N T` is the inverse of `qeT` applied to `prS t`. -/
theorem mk_eq_qeT_symm (t : TT N hN f S H e L hL) :
    Ideal.Quotient.mk _ t =
      (qeT N hN f S H e L hL hNS hflat).symm.toAlgHom (prS N hN f S H e L hL t) := by
  rw [← qeT_mk N hN f S H e L hL hNS hflat]
  simp

/-- If `t : T` lifts `a : S`, then `Lam (a ⊗ₜ n) = n • t`. -/
theorem Lam_tmul (a : S) (n : N) (t : TT N hN f S H e L hL) (ht : prS N hN f S H e L hL t = a) :
    Lam N hN f S H e L hL hNS hflat (a ⊗ₜ n) = (n : R) • t :=
  theta_tmul N hN _ a n t (by rw [mk_eq_qeT_symm N hN f S H e L hL hNS hflat, ht])

/-- The image of `Lam z` in `S` vanishes. -/
theorem prS_Lam (z : PS N S) : prS N hN f S H e L hL (Lam N hN f S H e L hL hNS hflat z) = 0 :=
  (ker_prS N hN f S H e L hL hNS hflat).ge
    (theta_mem N hN (qeT N hN f S H e L hL hNS hflat).symm.toAlgHom z)

/-- If `β : T → B'` reduces modulo `N` to `L' ∘ prS`, then `β (Lam z) = θ_{L'} z`. -/
private theorem map_Lam_eq_theta {B' : Type*} [CommRing B'] [Algebra R B']
    (β : TT N hN f S H e L hL →ₐ[R] B') (L' : S →ₐ[R] B' ⧸ N.map (algebraMap R B'))
    (h : ∀ t, Ideal.Quotient.mk _ (β t) = L' (prS N hN f S H e L hL t)) (z : PS N S) :
    β (Lam N hN f S H e L hL hNS hflat z) = theta N hN L' z := by
  rw [Lam]
  apply theta_naturality
  ext a
  obtain ⟨t, rfl⟩ := prS_surjective N hN f S H e L hL hflat a
  rw [AlgHom.comp_apply, ← mk_eq_qeT_symm, redMap_mk, h]

/-- The image of `Lam z` in `H` is `muH0 (z ⊗ₜ 1)`. -/
theorem prH_Lam (z : PS N S) :
    prH N hN f S H e L hL (Lam N hN f S H e L hL hNS hflat z) = muH0 N hN f S H e (z ⊗ₜ 1) := by
  rw [muH0_tmul_one]
  exact map_Lam_eq_theta N hN f S H e L hL hNS hflat _ _ (mk_prH N hN f S H e L hL) z

/-- The image of `Lam z` in the component indexed by a singleton `u` is `muV` applied to the
localization of `z`. -/
theorem prV_Lam (u : {s : Finset (Fin k) // s.card = 1}) (z : PS N S) :
    prV N hN f S H e L hL u (Lam N hN f S H e L hL hNS hflat z) =
      muV N hN f S L u.1 (LocalizedModule.mkLinearMap _ _ z) := by
  rw [muV_mk]
  exact map_Lam_eq_theta N hN f S H e L hL hNS hflat _ _ (mk_prV N hN f S H e L hL u) z

/-- The image of `Lam` lies in the ideal `N T`. -/
theorem Lam_mem (z : PS N S) :
    Lam N hN f S H e L hL hNS hflat z ∈ N.map (algebraMap R (TT N hN f S H e L hL)) :=
  theta_mem N hN _ z

/-- Every element of the ideal `N T` is in the image of `Lam`. -/
theorem exists_Lam_eq (x : TT N hN f S H e L hL)
    (hx : x ∈ N.map (algebraMap R (TT N hN f S H e L hL))) :
    ∃ z, Lam N hN f S H e L hL hNS hflat z = x := by
  obtain ⟨w, rfl⟩ := exists_multT_eq N hN _ x hx
  refine ⟨(LinearEquiv.rTensor N (qeT N hN f S H e L hL hNS hflat).toLinearEquiv) w, ?_⟩
  have : ((qeT N hN f S H e L hL hNS hflat).symm.toAlgHom.toLinearMap.rTensor N) ∘ₗ
      (LinearEquiv.rTensor N (qeT N hN f S H e L hL hNS hflat).toLinearEquiv).toLinearMap =
      LinearMap.id := by
    apply TensorProduct.ext'
    intro a n
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.rTensor_tmul,
      LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, LinearMap.id_apply]
    congr 1
    exact (qeT N hN f S H e L hL hNS hflat).symm_apply_apply a
  simp only [Lam, theta, LinearMap.comp_apply]
  exact congrArg (multT N hN _) (LinearMap.congr_fun this w)

/-- If `t : T` lifts `a : S`, then `Lam (a • z) = t * Lam z`. -/
theorem Lam_smul (a : S) (z : PS N S) (t : TT N hN f S H e L hL)
    (ht : prS N hN f S H e L hL t = a) :
    Lam N hN f S H e L hL hNS hflat (a • z) = t * Lam N hN f S H e L hL hNS hflat z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul b n =>
    rw [TensorProduct.smul_tmul', smul_eq_mul]
    exact theta_mul N hN _ a b n t (by rw [mk_eq_qeT_symm N hN f S H e L hL hNS hflat, ht])
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, mul_add]

/-- If `muH0 (z ⊗ₜ 1) = 0` and `z` vanishes in every localization at a singleton, then
`Lam z = 0`. -/
theorem Lam_eq_zero (z : PS N S) (hH : muH0 N hN f S H e (z ⊗ₜ 1) = 0)
    (hV : ∀ u : {s : Finset (Fin k) // s.card = 1},
      LocalizedModule.mkLinearMap (cechSub (gS f S) u.1) (PS N S) z = 0) :
    Lam N hN f S H e L hL hNS hflat z = 0 := by
  apply ext_glued N hN f S H e L hL
  · exact prS_Lam N hN f S H e L hL hNS hflat z
  · exact (prH_Lam N hN f S H e L hL hNS hflat z).trans hH
  · funext u
    exact (prV_Lam N hN f S H e L hL hNS hflat u z).trans (by rw [hV u, map_zero]; rfl)

include hNS hflat in
/-- If `S` is of finite type over `R`, then so is the glued ring `T`. -/
theorem finiteType_glued [Algebra.FiniteType R S] :
    Algebra.FiniteType R (TT N hN f S H e L hL) := by
  classical
  obtain ⟨s, hs⟩ := (Algebra.FiniteType.out : (⊤ : Subalgebra R S).FG)
  choose lift hlift using prS_surjective N hN f S H e L hL hflat
  let A := Algebra.adjoin R ((s.image lift : Finset _) : Set (TT N hN f S H e L hL))
  have hmap : A.map (prS N hN f S H e L hL) = ⊤ := by
    rw [AlgHom.map_adjoin, ← hs]
    congr 1
    ext y
    simp [hlift]
  have hA : ∀ x, ∃ a ∈ A, prS N hN f S H e L hL a = prS N hN f S H e L hL x := fun x ↦
    Subalgebra.mem_map.mp (hmap ▸ Algebra.mem_top)
  have hsub : ∀ x a, prS N hN f S H e L hL a = prS N hN f S H e L hL x →
      x - a ∈ N.map (algebraMap R (TT N hN f S H e L hL)) := by
    intro x a h
    rw [← ker_prS N hN f S H e L hL hNS hflat]
    simp [h]
  have hNA : ∀ x ∈ N.map (algebraMap R (TT N hN f S H e L hL)), x ∈ A := by
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
        refine Ideal.mem_bot.mp ((map_sq_eq_bot N hN _).le ?_)
        rw [pow_two]
        exact Ideal.mul_mem_mul (hsub c a hac) hxN
      rw [smul_eq_mul, show c * x = a * x by rw [← sub_eq_zero, ← sub_mul, h0]]
      exact A.mul_mem ha hx
  refine ⟨⟨s.image lift, eq_top_iff.mpr fun x _ ↦ ?_⟩⟩
  obtain ⟨a, ha, hax⟩ := hA x
  rw [show x = a + (x - a) by ring]
  exact A.add_mem ha (hNA _ (hsub x a hax))

end Rig.SquareZeroLift

end
