module

public import StacksFrontier.RingTheory.Rig.Algebraization.SquareZeroGlueDatumLambda
public import StacksFrontier.RingTheory.Rig.Algebraization.SquareZeroLiftComplete
import all StacksFrontier.RingTheory.Localization.Glueing.FormalGlueingComplex

/-!
# The completion of the ring glued from a glueing datum

For a glueing datum `D`, the projection `φ : T → H` of the glued ring induces isomorphisms
`T ⧸ Iⁿ T ≅ H ⧸ Iⁿ H` for `I = (f₁, …, f_k)` and all `n`.

## Main results

* `Rig.SquareZeroLift.GlueDatum.exists_sub_prH_mem`: surjectivity of `T ⧸ Iⁿ T → H ⧸ Iⁿ H`.
* `Rig.SquareZeroLift.GlueDatum.mem_map_of_prH_mem`: injectivity of `T ⧸ Iⁿ T → H ⧸ Iⁿ H`.
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
open _root_.IPowerTorsion (unitMap)

variable [IsNoetherianRing S] (hNS : N.map (algebraMap R S) = ⊥)
variable (hflat : ∀ i, Module.Flat R (Localization.Away (algebraMap R H (f i))))

include hN hflat in
/-- Every `c : H` is congruent to some `D.prH t` modulo `Iⁿ H + N H`. -/
theorem exists_sub_prH_mem_sup (n : ℕ) (c : H) :
    ∃ t, c - D.prH t ∈
      ((Ideal.span (Set.range f)) ^ n).map (algebraMap R H) ⊔ N.map (algebraMap R H) := by
  obtain ⟨s, hs⟩ := exists_sub_mem_Sh f S n (e (Ideal.Quotient.mk _ c))
  obtain ⟨t, rfl⟩ := D.prS_surjective hN hflat s
  refine ⟨t, mem_map_of_e_mem N f S H e ?_⟩
  rwa [map_sub, map_sub, D.compat]

include hN hflat in
/-- Every `j ∈ N H` is congruent to some `D.prH t` modulo `Iⁿ H`. -/
theorem exists_sub_prH_mem_of_mem (n : ℕ) (j : H) (hj : j ∈ N.map (algebraMap R H)) :
    ∃ t, j - D.prH t ∈ ((Ideal.span (Set.range f)) ^ n).map (algebraMap R H) := by
  induction hj using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨r, -, rfl⟩ := hx
    exact ⟨algebraMap R _ r, by simp⟩
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨a + b, by rw [map_add, add_sub_add_comm]; exact add_mem ha hb⟩
  | smul c x hxN hx =>
    obtain ⟨t, ht⟩ := hx
    obtain ⟨tc, htc⟩ := D.exists_sub_prH_mem_sup hN hflat n c
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp htc
    refine ⟨tc * t, ?_⟩
    have hbx : b * x = 0 := by
      rw [← Ideal.mem_bot, ← map_sq_eq_bot N hN, pow_two]
      exact Ideal.mul_mem_mul hb hxN
    have : c • x - D.prH (tc * t) =
        D.prH tc * (x - D.prH t) + a * x + b * x := by
      rw [smul_eq_mul, map_mul, show c = D.prH tc + a + b by
        rw [add_assoc, hab]; ring]
      ring
    rw [this, hbx, add_zero]
    exact add_mem (Ideal.mul_mem_left _ _ ht) (Ideal.mul_mem_right _ _ ha)

include hN hflat in
/-- Surjectivity of `T ⧸ Iⁿ T → H ⧸ Iⁿ H`. -/
theorem exists_sub_prH_mem (n : ℕ) (c : H) :
    ∃ t, c - D.prH t ∈ ((Ideal.span (Set.range f)) ^ n).map (algebraMap R H) := by
  obtain ⟨t₀, ht₀⟩ := D.exists_sub_prH_mem_sup hN hflat n c
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp ht₀
  obtain ⟨t₁, ht₁⟩ := D.exists_sub_prH_mem_of_mem hN hflat n b hb
  refine ⟨t₀ + t₁, ?_⟩
  rw [map_add, show c - (D.prH t₀ + D.prH t₁) =
    a + (b - D.prH t₁) by linear_combination -hab]
  exact add_mem ha ht₁

omit [IsNoetherianRing S] in
/-- `Psi` sends `D.prH t` to the image of `D.prS t` in `Sh f S`. -/
theorem Psi_prH (t : D.TT) :
    Psi N f S H e (D.prH t) = algebraMap S _ (D.prS t) :=
  D.compat t

/-- If `u ⊗ₜ 1 ∈ Iⁿ (PH N f S)` with `0 < n`, then `u ∈ Iⁿ (PS N S)`. -/
private theorem mem_smul_top_of_tmul_one_mem (n : ℕ) (hn : 0 < n) (u : PS N S)
    (hu1 : u ⊗ₜ (1 : Sh f S) ∈ (((Ideal.span (Set.range f)) ^ n).map (algebraMap R S)) •
      (⊤ : Submodule S (PH N f S))) :
    u ∈ (((Ideal.span (Set.range f)) ^ n).map (algebraMap R S)) •
      (⊤ : Submodule S (PS N S)) := by
  set K : Ideal S := ((Ideal.span (Set.range f)) ^ n).map (algebraMap R S)
  let q := (K • (⊤ : Submodule S (PS N S))).mkQ
  refine (Submodule.Quotient.mk_eq_zero _).mp (?_ : q u = 0)
  apply unitMap_eq_zero_of_torsion (Ideal.span (Set.range (gS f S))) (flat_Sh f S)
    (quotientMap_Sh_bijective f S)
  · refine ⟨n, hn, fun c hc ↦ ?_⟩
    rw [span_range_gS] at hc
    rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact Submodule.smul_mem_smul (by simp only [K, Ideal.map_pow]; exact hc) Submodule.mem_top
  · change q.rTensor (Sh f S) (u ⊗ₜ 1) = 0
    refine Submodule.smul_induction_on hu1 (fun c hc x _ ↦ ?_)
      (fun x y hx hy ↦ by rw [map_add, hx, hy, add_zero])
    rw [map_smul]
    induction (q.rTensor (Sh f S) x) using TensorProduct.inductionOn with
    | tmul a b =>
      rw [TensorProduct.smul_tmul']
      obtain ⟨a', rfl⟩ := Submodule.mkQ_surjective _ a
      rw [← map_smul q, Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero _).mpr
        (Submodule.smul_mem_smul hc Submodule.mem_top), TensorProduct.zero_tmul]
    | add a b ha hb => rw [smul_add, ha, hb, add_zero]

/-- Every element of `J S` is the image under `D.prS` of an element of `J T`. -/
private theorem exists_mem_map_prS_eq (hN : N ^ 2 = ⊥)
    (hflat : ∀ i, Module.Flat R (Localization.Away (algebraMap R H (f i)))) (J : Ideal R) {x : S}
    (hx : x ∈ J.map (algebraMap R S)) :
    ∃ t ∈ J.map (algebraMap R D.TT), D.prS t = x := by
  refine (Ideal.mem_map_iff_of_surjective D.prS.toRingHom (D.prS_surjective hN hflat)).mp ?_
  rwa [Ideal.map_map, AlgHom.toRingHom_eq_coe, AlgHom.comp_algebraMap]

include hNS hflat in
/-- If `z ⊗ₜ 1 - w₁` lies in the kernel of `muH0` for some `w₁ ∈ Iⁿ (PH N f S)`, then
`D.Lam z ∈ Iⁿ T`. -/
theorem Lam_mem_of_tmul (n : ℕ) (hn : 0 < n) (z : PS N S) (w₁ : PH N f S)
    (hw₁ : w₁ ∈ (((Ideal.span (Set.range f)) ^ n).map (algebraMap R S)) •
      (⊤ : Submodule S (PH N f S)))
    (hD : muH0 N hN f S H e (z ⊗ₜ 1 - w₁) = 0) :
    D.Lam hN hNS hflat z ∈
      ((Ideal.span (Set.range f)) ^ n).map (algebraMap R D.TT) := by
  obtain ⟨z₀, hz₀, hz₀V⟩ := exists_tmul_eq_of_muH0_eq_zero N hN f S H e hflat _ hD
  have hLz₀ : D.Lam hN hNS hflat z₀ = 0 :=
    D.Lam_eq_zero hN hNS hflat z₀ (by rw [hz₀, hD]) hz₀V
  let u : PS N S := z - z₀
  have hu1 : u ⊗ₜ (1 : Sh f S) = w₁ := by
    simp only [u, TensorProduct.sub_tmul, hz₀]
    abel
  have hLu : D.Lam hN hNS hflat u ∈
      ((Ideal.span (Set.range f)) ^ n).map (algebraMap R D.TT) := by
    refine Submodule.smul_induction_on (mem_smul_top_of_tmul_one_mem n hn u (hu1 ▸ hw₁))
      (fun c hc x _ ↦ ?_)
      (fun x y hx hy ↦ by simpa only [map_add] using add_mem hx hy)
    obtain ⟨tc, htc, htc'⟩ := D.exists_mem_map_prS_eq hN hflat _ hc
    rw [D.Lam_smul hN hNS hflat c x tc htc']
    exact Ideal.mul_mem_right _ _ htc
  rwa [show z = u + z₀ from (sub_add_cancel z z₀).symm, map_add, hLz₀, add_zero]

omit [IsNoetherianRing S] in
/-- The reduction `Psi : H → Sh f S` is surjective. -/
private theorem exists_Psi_eq (y : Sh f S) : ∃ h : H, Psi N f S H e h = y := by
  obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (e.symm y)
  exact ⟨b, by simp [Psi, hb]⟩

/-- If `y ∈ K • ⊤`, then `x ⊗ₜ y ∈ K • ⊤`. -/
private theorem tmul_mem_ideal_smul_top {A M P : Type*} [CommRing A] [AddCommGroup M] [Module A M]
    [AddCommGroup P] [Module A P] (K : Ideal A) (x : M) {y : P}
    (hy : y ∈ K • (⊤ : Submodule A P)) : x ⊗ₜ[A] y ∈ K • (⊤ : Submodule A (M ⊗[A] P)) := by
  refine Submodule.smul_induction_on hy (fun c hc p _ ↦ ?_) (fun p q hp hq ↦ ?_)
  · rw [TensorProduct.tmul_smul]
    exact Submodule.smul_mem_smul hc Submodule.mem_top
  · rw [TensorProduct.tmul_add]
    exact add_mem hp hq

/-- Regrouping `z ⊗ₜ 1 - (∑ sₗ • zₗ) ⊗ₜ 1 - (w + ∑ zₗ ⊗ₜ (yₗ - sₗ))` as
`z ⊗ₜ 1 - ∑ zₗ ⊗ₜ yₗ - w`. -/
private theorem tmul_one_sub_sum_smul_tmul_one_sub {A M B ι : Type*} [CommRing A] [AddCommGroup M]
    [Module A M] [CommRing B] [Algebra A B] [Fintype ι] (z : M) (zl : ι → M) (sl : ι → A)
    (yh : ι → B) (w : M ⊗[A] B) :
    z ⊗ₜ[A] (1 : B) - (∑ l, sl l • zl l) ⊗ₜ[A] (1 : B) -
        (w + ∑ l, zl l ⊗ₜ[A] (yh l - algebraMap A B (sl l))) =
      z ⊗ₜ[A] (1 : B) - ∑ l, zl l ⊗ₜ[A] yh l - w := by
  have h1 : ∀ l, (sl l • zl l) ⊗ₜ[A] (1 : B) +
      zl l ⊗ₜ[A] (yh l - algebraMap A B (sl l)) = zl l ⊗ₜ[A] yh l := fun l ↦ by
    rw [TensorProduct.smul_tmul, Algebra.smul_def, mul_one, ← TensorProduct.tmul_add]
    congr 1
    abel
  have h1' : ∑ l, zl l ⊗ₜ[A] yh l = ∑ l, (sl l • zl l) ⊗ₜ[A] (1 : B) +
      ∑ l, zl l ⊗ₜ[A] (yh l - algebraMap A B (sl l)) :=
    (Finset.sum_congr rfl fun l _ ↦ (h1 l).symm).trans Finset.sum_add_distrib
  rw [TensorProduct.sum_tmul, h1']
  abel

include hNS hflat in
/-- If the image of `z ⊗ₜ 1` under `muH0` is a sum `∑ aᵢ • i` with `aᵢ ∈ Iⁿ`, then there are
`z₁` with `D.Lam z₁ ∈ Iⁿ T` and `w₁ ∈ Iⁿ (PH N f S)` such that `z ⊗ₜ 1 - z₁ ⊗ₜ 1 - w₁` lies in
the kernel of `muH0`. -/
theorem exists_approx (n : ℕ) (z : PS N S) (s : Finset H) (a : H → R)
    (ha : ∀ i, a i ∈ (Ideal.span (Set.range f)) ^ n)
    (hsum : ∑ i ∈ s, a i • i = muH0 N hN f S H e (z ⊗ₜ 1)) :
    ∃ z₁ : PS N S, D.Lam hN hNS hflat z₁ ∈
        ((Ideal.span (Set.range f)) ^ n).map (algebraMap R D.TT) ∧
      ∃ w₁ ∈ (((Ideal.span (Set.range f)) ^ n).map (algebraMap R S)) •
          (⊤ : Submodule S (PH N f S)),
        muH0 N hN f S H e (z ⊗ₜ 1 - z₁ ⊗ₜ 1 - w₁) = 0 := by
  classical
  let Ψ := Psi N f S H e
  have hsum' : ∑ i : s, a i • (i : H) = muH0 N hN f S H e (z ⊗ₜ 1) :=
    (Finset.sum_coe_sort s fun i ↦ a i • i).trans hsum
  have hrel : ∑ i : s, algebraMap R S (a i) • Ψ (i : H) = 0 := by
    simpa [Ψ, ← hsum'] using Psi_eq_zero N f S H e (muH0_mem N hN f S H e (z ⊗ₜ 1))
  have := flat_Sh f S
  obtain ⟨m, σ, yh, hxσ, hσ⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero hrel
  choose τ hτ using D.prS_surjective hN hflat
  choose yt hyt using fun l ↦ exists_Psi_eq (N := N) (H := H) (e := e) (yh l)
  have hq : ∀ i : s, (i : H) - ∑ l, D.prH (τ (σ i l)) * yt l ∈
      N.map (algebraMap R H) := fun i ↦ by
    rw [← Psi_sub_eq_zero_iff N f S H e, map_sub, map_sum, show Ψ (i : H) = _ from hxσ i]
    simp only [map_mul, D.Psi_prH, hτ, hyt, Algebra.smul_def, sub_self]
  choose w hw using fun i : s ↦ exists_muH0_eq N hN f S H e _ (hq i)
  let y : Fin m → D.TT := fun l ↦ ∑ i : s, a i • τ (σ i l)
  have hyker : ∀ l, y l ∈ N.map (algebraMap R D.TT) := fun l ↦ by
    rw [← D.ker_prS hN hNS hflat]
    change D.prS (y l) = 0
    simp only [y, map_sum, Algebra.smul_def, map_mul, AlgHom.commutes, hτ]
    exact hσ l
  have hyIn : ∀ l, y l ∈ ((Ideal.span (Set.range f)) ^ n).map
      (algebraMap R D.TT) := fun l ↦ Submodule.sum_mem _ fun i _ ↦ by
    rw [Algebra.smul_def]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (ha i))
  choose zl hzl using fun l ↦ D.exists_Lam_eq hN hNS hflat (y l) (hyker l)
  choose sl hsl using fun l ↦ exists_sub_mem_Sh f S n (yh l)
  refine ⟨∑ l, sl l • zl l, ?_, ∑ i : s, a i • w i +
    ∑ l, zl l ⊗ₜ (yh l - algebraMap S _ (sl l)), ?_, ?_⟩
  · rw [map_sum]
    refine Submodule.sum_mem _ fun l _ ↦ ?_
    rw [D.Lam_smul hN hNS hflat _ _ (τ (sl l)) (hτ _), hzl]
    exact Ideal.mul_mem_left _ _ (hyIn l)
  · refine add_mem (Submodule.sum_mem _ fun i _ ↦ ?_) (Submodule.sum_mem _ fun l _ ↦ ?_)
    · rw [← algebraMap_smul S (a i) (w i)]
      exact Submodule.smul_mem_smul (Ideal.mem_map_of_mem _ (ha i)) Submodule.mem_top
    · have hm := hsl l
      rw [map_pow_Sh, ← Ideal.map_pow] at hm
      exact tmul_mem_ideal_smul_top _ _ (by rwa [Ideal.smul_top_eq_map])
  · rw [tmul_one_sub_sum_smul_tmul_one_sub, map_sub, map_sub, map_sum, map_sum]
    simp only [map_smul, hw, muH0_tmul_mul N hN f S H e _ _ _ (hyt _)]
    simp only [← D.prH_Lam hN hNS hflat, hzl, y, map_sum, map_smul]
    rw [sum_comm_smul_mul, D.prH_Lam hN, ← hsum']
    simp only [smul_sub, Finset.sum_sub_distrib]
    abel

include hN hNS hflat in
/-- Injectivity of `T ⧸ Iⁿ T → H ⧸ Iⁿ H`. -/
theorem mem_map_of_prH_mem (n : ℕ) (t : D.TT)
    (hH : D.prH t ∈ ((Ideal.span (Set.range f)) ^ n).map (algebraMap R H)) :
    t ∈ ((Ideal.span (Set.range f)) ^ n).map (algebraMap R D.TT) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [pow_zero, Ideal.one_eq_top, Ideal.map_top]
    exact Submodule.mem_top
  have hS : D.prS t ∈ ((Ideal.span (Set.range f)) ^ n).map (algebraMap R S) :=
    mem_of_algebraMap_mem_Sh f S n _ (by rw [← D.Psi_prH]; exact e_mem_map N f S H e hH)
  obtain ⟨t', ht', htt'⟩ := D.exists_mem_map_prS_eq hN hflat _ hS
  have hker : t - t' ∈ N.map (algebraMap R D.TT) := by
    rw [← D.ker_prS hN hNS hflat]
    change D.prS (t - t') = 0
    rw [map_sub, sub_eq_zero, htt']
  have hH' : D.prH (t - t') ∈
      ((Ideal.span (Set.range f)) ^ n).map (algebraMap R H) := by
    rw [map_sub]
    refine sub_mem hH ?_
    have := Ideal.mem_map_of_mem D.prH.toRingHom ht'
    rwa [Ideal.map_map, AlgHom.toRingHom_eq_coe, AlgHom.comp_algebraMap] at this
  suffices t - t' ∈ ((Ideal.span (Set.range f)) ^ n).map
      (algebraMap R D.TT) by
    simpa using add_mem this ht'
  obtain ⟨z, hz⟩ := D.exists_Lam_eq hN hNS hflat _ hker
  rw [← hz] at hH' ⊢
  rw [D.prH_Lam hN] at hH'
  obtain ⟨s, a, ha, hsum⟩ := exists_finite_sum H hH'
  obtain ⟨z₁, hz₁, w₁, hw₁, hD⟩ := D.exists_approx hN hNS hflat n z s a ha hsum
  have h2 := D.Lam_mem_of_tmul hN hNS hflat n hn (z - z₁) w₁ hw₁
    (by rwa [TensorProduct.sub_tmul])
  rw [map_sub] at h2
  simpa using add_mem h2 hz₁

end Rig.SquareZeroLift.GlueDatum

end
