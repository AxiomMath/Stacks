module

public import StacksFrontier.RingTheory.Rig.Algebraization.SquareZeroLiftSurj

/-!
# The kernel of the projection of the glued ring onto `S`

In the setting of `StacksFrontier.RingTheory.Rig.Algebraization.SquareZeroLiftRing`, this file
proves that the kernel of the projection `T → S` is `N T`. An element `(0, h, v)` of the kernel
has `h ∈ N H` and `v_i ∈ N V_i`; these come from a pair of the glueing complex of
`P = S ⊗[R] N` lying in the kernel of its second map, hence from an element of `P` by
`FormalGlueing.glueingComplex_exact`, whose image under multiplication is `(0, h, v)`.

## Main results

* `Rig.SquareZeroLift.ker_prS`: the kernel of `T → S` is `N T`.
-/

@[expose] public section

namespace Rig.SquareZeroLift

open TensorProduct Cech FormalGlueing

universe u

/-- The image of the multiplication map `B ⊗[R] N → B` lies in the ideal `N B`. -/
theorem mulT0_mem {R : Type*} [CommRing R] (N : Ideal R) (B : Type*) [CommRing B] [Algebra R B]
    (z : B ⊗[R] N) : mulT0 N B z ∈ N.map (algebraMap R B) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul b n =>
    simp only [mulT0, TensorProduct.lift.tmul, LinearMap.restrictScalars_apply, mulN_apply,
      Algebra.smul_def]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ n.2)
  | add x y hx hy => rw [map_add]; exact add_mem hx hy

/-- If `β : T → B` and `γ : T → X` are compatible with `L : X → B ⧸ N B`, then `β` carries the
multiplication `T ⊗[R] N → T` to `θ_L ∘ (γ ⊗ N)`. -/
theorem map_mulT0 {R : Type*} [CommRing R] (N : Ideal R) (hN : N ^ 2 = ⊥) {T X B : Type*}
    [CommRing T] [Algebra R T] [CommRing X] [Algebra R X] [CommRing B] [Algebra R B]
    (γ : T →ₐ[R] X) (β : T →ₐ[R] B) (L : X →ₐ[R] B ⧸ N.map (algebraMap R B))
    (h : ∀ t, Ideal.Quotient.mk _ (β t) = L (γ t)) (z : T ⊗[R] N) :
    β (mulT0 N T z) = theta N hN L (γ.toLinearMap.rTensor N z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul t n =>
    simp only [mulT0, TensorProduct.lift.tmul, LinearMap.restrictScalars_apply, mulN_apply,
      map_smul, LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply]
    exact (theta_tmul N hN L (γ t) n (β t) (h t)).symm
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

variable {R : Type u} [CommRing R] (N : Ideal R) (hN : N ^ 2 = ⊥)
variable {k : ℕ} (f : Fin k → R)
variable (S : Type u) [CommRing S] [Algebra R S]
variable (H : Type u) [CommRing H] [Algebra R H]
variable (e : (H ⧸ N.map (algebraMap R H)) ≃ₐ[R] Sh f S)
variable (L : ∀ s : Finset (Fin k), NilLift R N (Sl f S s))
variable (hL : ∀ s, s.Nonempty → Algebra.Etale R (L s).carrier)

/-- The projection `T → V_u`, reduced modulo `N V_u`, is `lam u ∘ prS`. -/
theorem mk_prV (u : {s : Finset (Fin k) // s.card = 1}) (t : TT N hN f S H e L hL) :
    Ideal.Quotient.mk _ (prV N hN f S H e L hL u t) =
      lam N f S L u.1 (prS N hN f S H e L hL t) := by
  have h2 := ((mem_glued N hN f S H e L hL t.1).mp t.2).2.1 u
  rw [← (L u.1).qe_mk N] at h2
  simp only [lam, AlgHom.comp_apply, IsScalarTower.coe_toAlgHom']
  show _ = ((L u.1).qe N).symm (algebraMap S (Sl f S u.1) t.1.1)
  rw [← h2]
  exact (((L u.1).qe N).symm_apply_apply _).symm

/-- The projection `T → H`, reduced modulo `N H`, is the composite of `prS` with
`S → Sh f S ≃ H ⧸ N H`. -/
theorem mk_prH (t : TT N hN f S H e L hL) :
    Ideal.Quotient.mk _ (prH N hN f S H e L hL t) =
      (e.symm.toAlgHom.comp (IsScalarTower.toAlgHom R S (Sh f S))) (prS N hN f S H e L hL t) := by
  rw [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', ← compat]
  simp

/-- **The kernel of `T → S` is `N T`.** -/
theorem ker_prS [IsNoetherianRing S] (hNS : N.map (algebraMap R S) = ⊥)
    (hflat : ∀ i, Module.Flat R (Localization.Away (algebraMap R H (f i)))) :
    RingHom.ker (prS N hN f S H e L hL).toRingHom =
      N.map (algebraMap R (TT N hN f S H e L hL)) := by
  have hn0 : ∀ n ∈ N, algebraMap R S n = 0 := fun n hn ↦
    Ideal.mem_bot.1 (hNS ▸ Ideal.mem_map_of_mem _ hn)
  apply le_antisymm
  · intro x hx
    have hx0 : x.1.1 = 0 := hx
    obtain ⟨h1, h2, h3, h4⟩ := (mem_glued N hN f S H e L hL x.1).mp x.2
    simp only [hx0, map_zero] at h1 h2
    have hh : x.1.2.1 ∈ N.map (algebraMap R H) := by
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      exact e.injective (h1.trans (map_zero e).symm)
    obtain ⟨y, hy⟩ := exists_muH0_eq N hN f S H e x.1.2.1 hh
    choose xu hxu using fun u : {s : Finset (Fin k) // s.card = 1} ↦
      exists_muV_eq N hN f S L u.1 (x.1.2.2 u) (((L u.1).mem_iff N _).mpr (h2 u))
    have hβ : glueingBeta (Sh f S) (gS f S) (PS N S) (y, xu) = 0 := by
      apply Prod.ext
      · funext u
        apply muH_injective N hN f S H e hflat u.1 (nonempty_of_card_eq u)
        show muH N hN f S H e u.1 (LocalizedModule.mkLinearMap _ _ y -
          LocalizedModule.map (cechSub (gS f S) u.1)
            ((TensorProduct.mk S (PS N S) (Sh f S)).flip 1) (xu u)) = muH N hN f S H e u.1 0
        rw [map_sub, muH_mk, muH_unit_eq_rho_muV N hN f S H e L hL u.1 (nonempty_of_card_eq u),
          hxu, h3, hy, sub_self, map_zero]
      · funext T
        show -(glueingDifferential (gS f S) (PS N S) 1 xu T) = 0
        rw [neg_eq_zero]
        apply muV_injective N hN f S L hL T.1 (nonempty_of_card_eq T)
        rw [muV_cechDiff N hN f S L hL 1 (by norm_num), map_zero]
        have : (fun s : {s : Finset (Fin k) // s.card = 1} ↦ muV N hN f S L s.1 (xu s)) =
            x.1.2.2 := funext hxu
        rw [this, h4]
        rfl
    obtain ⟨z, hz⟩ := ((glueingComplex_exact S (Sh f S) (gS f S) (PS N S) (flat_Sh f S)
      (quotientMap_Sh_bijective f S)).2 (y, xu)).mp hβ
    obtain ⟨z', rfl⟩ := LinearMap.rTensor_surjective N
      (g := (prS N hN f S H e L hL).toLinearMap)
      (prS_surjective N hN f S H e L hL hflat) z
    have hz1 : (prS N hN f S H e L hL).toLinearMap.rTensor N z' ⊗ₜ (1 : Sh f S) = y :=
      congrArg Prod.fst hz
    have hz2 : ∀ u, LocalizedModule.mkLinearMap (cechSub (gS f S) u.1) (PS N S)
        ((prS N hN f S H e L hL).toLinearMap.rTensor N z') = xu u :=
      fun u ↦ congrFun (congrArg Prod.snd hz) u
    have hxeq : mulT0 N (TT N hN f S H e L hL) z' = x := by
      apply ext_glued
      · rw [hx0]
        show prS N hN f S H e L hL (mulT0 N _ z') = 0
        rw [map_mulT0 N hN (prS N hN f S H e L hL) (prS N hN f S H e L hL)
          (Ideal.Quotient.mkₐ R (N.map (algebraMap R S))) (fun _ ↦ rfl)]
        induction ((prS N hN f S H e L hL).toLinearMap.rTensor N z') using
          TensorProduct.induction_on with
        | zero => simp
        | tmul a n =>
          rw [theta_tmul N hN _ a n a rfl, Algebra.smul_def]
          rw [hn0 n n.2, zero_mul]
        | add a b ha hb => rw [map_add, ha, hb, add_zero]
      · show prH N hN f S H e L hL (mulT0 N _ z') = x.1.2.1
        rw [map_mulT0 N hN (prS N hN f S H e L hL) (prH N hN f S H e L hL) _
          (mk_prH N hN f S H e L hL), ← hy, ← hz1, muH0_tmul_one]
      · funext u
        show prV N hN f S H e L hL u (mulT0 N _ z') = x.1.2.2 u
        rw [map_mulT0 N hN (prS N hN f S H e L hL) (prV N hN f S H e L hL u) _
          (mk_prV N hN f S H e L hL u), ← hxu, ← hz2, muV_mk]
    rw [← hxeq]
    exact mulT0_mem N _ z'
  · rw [Ideal.map_le_iff_le_comap]
    intro n hn
    simp only [Ideal.mem_comap, RingHom.mem_ker, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      AlgHom.commutes]
    exact hn0 n hn

end Rig.SquareZeroLift

end
