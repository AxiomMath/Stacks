module

public import StacksFrontier.RingTheory.Rig.Algebraization.SquareZeroGlueDatumSurj
public import StacksFrontier.RingTheory.Rig.Algebraization.SquareZeroLiftKer

/-!
# The kernel of the projection onto `S` of the ring glued from a glueing datum

For a glueing datum `D`, the kernel of the projection `T → S` of the glued ring is `N T`. An
element `(0, h, v)` of the kernel has `h ∈ N H` and `v_i ∈ N V_i`; these come from a pair of the
glueing complex of `P = S ⊗[R] N` lying in the kernel of its second map, hence from an element of
`P` by `FormalGlueing.glueingComplex_exact`, whose image under multiplication is `(0, h, v)`.

## Main results

* `Rig.SquareZeroLift.GlueDatum.ker_prS`: the kernel of `T → S` is `N T`.
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

/-- The `V_u`-component of an element `t` of the glued ring, reduced modulo `N`, is the image of
its `S`-component under `lam N f S D.L u.1`. -/
theorem mk_prV (u : {s : Finset (Fin k) // s.card = 1}) (t : D.TT) :
    Ideal.Quotient.mk _ (D.prV u t) =
      lam N f S D.L u.1 (D.prS t) := by
  have h2 := ((D.mem_glued t.1).mp t.2).2.1 u
  rw [← (D.L u.1).qe_mk N] at h2
  simp only [lam, AlgHom.comp_apply, IsScalarTower.coe_toAlgHom']
  change _ = ((D.L u.1).qe N).symm (algebraMap S (Sl f S u.1) t.1.1)
  rw [← h2]
  exact (((D.L u.1).qe N).symm_apply_apply _).symm

/-- The `H`-component of an element `t` of the glued ring, reduced modulo `N`, is the image of
its `S`-component in `Sh f S` transported back along `e`. -/
theorem mk_prH (t : D.TT) :
    Ideal.Quotient.mk _ (D.prH t) =
      (e.symm.toAlgHom.comp (IsScalarTower.toAlgHom R S (Sh f S))) (D.prS t) := by
  rw [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', ← D.compat]
  simp

include hN in
/-- **The kernel of `T → S` is `N T`.** -/
theorem ker_prS [IsNoetherianRing S] (hNS : N.map (algebraMap R S) = ⊥)
    (hflat : ∀ i, Module.Flat R (Localization.Away (algebraMap R H (f i)))) :
    RingHom.ker D.prS.toRingHom =
      N.map (algebraMap R D.TT) := by
  have hNS0 : ∀ n ∈ N, algebraMap R S n = 0 := fun n hn ↦ by
    simpa [hNS] using Ideal.mem_map_of_mem (algebraMap R S) hn
  apply le_antisymm
  · intro x hx
    have hx0 : x.1.1 = 0 := hx
    obtain ⟨h1, h2, h3, h4⟩ := (D.mem_glued x.1).mp x.2
    simp only [hx0, map_zero] at h1 h2
    have hh : x.1.2.1 ∈ N.map (algebraMap R H) := by
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      exact e.injective (h1.trans (map_zero e).symm)
    obtain ⟨y, hy⟩ := exists_muH0_eq N hN f S H e x.1.2.1 hh
    choose xu hxu using fun u : {s : Finset (Fin k) // s.card = 1} ↦
      exists_muV_eq N hN f S D.L u.1 (x.1.2.2 u) (((D.L u.1).mem_iff N _).mpr (h2 u))
    have hβ : glueingBeta (Sh f S) (gS f S) (PS N S) (y, xu) = 0 := by
      apply Prod.ext
      · funext u
        apply muH_injective N hN f S H e hflat u.1 (nonempty_of_card_eq u)
        change muH N hN f S H e u.1 (LocalizedModule.mkLinearMap _ _ y -
          LocalizedModule.map (cechSub (gS f S) u.1)
            ((TensorProduct.mk S (PS N S) (Sh f S)).flip 1) (xu u)) = muH N hN f S H e u.1 0
        rw [map_sub, muH_mk, D.muH_unit_eq_rho_muV hN u.1 (nonempty_of_card_eq u),
          hxu, h3, hy, sub_self, map_zero]
      · funext T
        change -(glueingDifferential (gS f S) (PS N S) 1 xu T) = 0
        rw [neg_eq_zero]
        apply D.muV_injective hN T.1 (nonempty_of_card_eq T)
        rw [D.muV_cechDiff hN 1 (by norm_num), map_zero]
        have : (fun s : {s : Finset (Fin k) // s.card = 1} ↦ muV N hN f S D.L s.1 (xu s)) =
            x.1.2.2 := funext hxu
        rw [this, h4]
        rfl
    obtain ⟨z, hz⟩ := ((glueingComplex_exact S (Sh f S) (gS f S) (PS N S) (flat_Sh f S)
      (quotientMap_Sh_bijective f S)).2 (y, xu)).mp hβ
    obtain ⟨z', rfl⟩ := LinearMap.rTensor_surjective N
      (g := D.prS.toLinearMap)
      (D.prS_surjective hN hflat) z
    have hz1 : D.prS.toLinearMap.rTensor N z' ⊗ₜ (1 : Sh f S) = y :=
      congrArg Prod.fst hz
    have hz2 : ∀ u, LocalizedModule.mkLinearMap (cechSub (gS f S) u.1) (PS N S)
        (D.prS.toLinearMap.rTensor N z') = xu u :=
      fun u ↦ congrFun (congrArg Prod.snd hz) u
    have hxeq : mulT0 N D.TT z' = x := by
      apply D.ext_glued
      · rw [hx0]
        change D.prS (mulT0 N _ z') = 0
        rw [map_mulT0 N hN D.prS D.prS
          (Ideal.Quotient.mkₐ R (N.map (algebraMap R S))) (fun _ ↦ rfl)]
        induction (D.prS.toLinearMap.rTensor N z') using
          TensorProduct.inductionOn with
        | tmul a n =>
          rw [theta_tmul N hN _ a n a rfl, Algebra.smul_def, hNS0 n n.2, zero_mul]
        | add a b ha hb => rw [map_add, ha, hb, add_zero]
      · change D.prH (mulT0 N _ z') = x.1.2.1
        rw [map_mulT0 N hN D.prS D.prH _
          D.mk_prH, ← hy, ← hz1, muH0_tmul_one]
      · funext u
        change D.prV u (mulT0 N _ z') = x.1.2.2 u
        rw [map_mulT0 N hN D.prS (D.prV u) _
          (D.mk_prV u), ← hxu, ← hz2, muV_mk]
    rw [← hxeq]
    exact mulT0_mem N _ z'
  · rw [Ideal.map_le_iff_le_comap]
    intro n hn
    simp only [Ideal.mem_comap, RingHom.mem_ker, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      AlgHom.commutes]
    exact hNS0 n hn

end Rig.SquareZeroLift.GlueDatum

end
