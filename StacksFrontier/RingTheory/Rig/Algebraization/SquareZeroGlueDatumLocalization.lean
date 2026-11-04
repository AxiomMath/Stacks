module

public import StacksFrontier.RingTheory.Rig.Algebraization.SquareZeroGlueDatumKer
public import StacksFrontier.RingTheory.Rig.Algebraization.SquareZeroLiftEtale

/-!
# The lifts of a glueing datum are localizations of the glued ring

For a glueing datum `D`, the projection `T → V_{i}` of the glued ring identifies `V_{i}` with the
localization `T[1 / f i]`.

## Main results

* `Rig.SquareZeroLift.GlueDatum.isLocalization_prV`: `V_{i}` is the localization of `T` at `f i`.
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

include hN in
/-- If the transition map `D.sig h hs` from the lift over `s` to the lift over `t`, where
`s ⊆ t ⊆ insert a s`, kills `w`, then `w` is killed by a power of `f a`. -/
theorem sig_eq_zero (a : Fin k) {s t : Finset (Fin k)} (h : s ⊆ t) (ht : t ⊆ insert a s)
    (hs : s.Nonempty) (w : (D.L s).carrier) (hw : D.sig h hs w = 0) :
    ∃ m : ℕ, f a ^ m • w = 0 := by
  have h1 : locS f S h ((D.L s).ψ w) = 0 := by rw [← D.psi_sig h hs, hw, map_zero]
  obtain ⟨m₁, hm₁⟩ := locS_eq_zero f S a h ht _ h1
  have h2 : f a ^ m₁ • w ∈ N.map (algebraMap R (D.L s).carrier) := by
    rw [NilLift.mem_iff, map_smul, hm₁]
  obtain ⟨y, hy⟩ := exists_muV_eq N hN f S D.L s _ h2
  have h3 : cechι (gS f S) (PS N S) h y = 0 := by
    apply D.muV_injective hN t (hs.mono h)
    rw [D.muV_cechι hN h hs, hy, map_smul, hw, smul_zero, map_zero]
  obtain ⟨m₂, hm₂⟩ := exists_pow_smul_eq_zero_of_cechι_eq_zero (gS f S) a h ht y h3
  refine ⟨m₂ + m₁, ?_⟩
  have : f a ^ m₂ • y = 0 := by
    rw [← hm₂, gS, ← map_pow, algebraMap_smul]
  rw [pow_add, mul_smul, ← hy, ← map_smul, this, map_zero]

/-- An element of a ring killed in the localization at `r` is killed by a power of `r`. -/
private theorem exists_pow_smul_eq_zero_of_algebraMap_eq_zero {A B : Type u} [CommRing A]
    [CommRing B] [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B] (r : R)
    [IsLocalization.Away (algebraMap R A r) B] (x : A) (hx : algebraMap A B x = 0) :
    ∃ n : ℕ, r ^ n • x = 0 := by
  obtain ⟨n, hn⟩ := IsLocalization.Away.exists_of_eq (algebraMap R A r)
    (show algebraMap A B x = algebraMap A B 0 by rw [hx, map_zero])
  exact ⟨n, by rwa [mul_zero, ← map_pow, ← Algebra.smul_def] at hn⟩

include hN in
/-- An element of the glued ring whose projection to `V_{i}` vanishes is killed by a power of
`f i`. -/
theorem prV_eq_zero_torsion [IsNoetherianRing S]
    (_hflat : ∀ i, Module.Flat R (Localization.Away (algebraMap R H (f i))))
    (i : Fin k) (t : D.TT)
    (ht : D.prV (singletonIndex i) t = 0) :
    ∃ n : ℕ, f i ^ n • t = 0 := by
  classical
  obtain ⟨h1, h2, h3, h4⟩ := (D.mem_glued t.1).mp t.2
  rw [cechDiff_one_eq_zero_iff] at h4
  have ht' : t.1.2.2 (singletonIndex i) = 0 := ht
  obtain ⟨n₁, hn₁⟩ := exists_pow_smul_eq_zero_of_algebraMap_eq_zero (B := Sl f S {i})
    (rs f {i}) t.1.1 (by rw [← h2 (singletonIndex i), ht', map_zero])
  obtain ⟨n₂, hn₂⟩ := exists_pow_smul_eq_zero_of_algebraMap_eq_zero (B := Hl f H {i})
    (rs f {i}) t.1.2.1 (by rw [← h3 (singletonIndex i), ht', map_zero])
  have hV : ∀ u : {s : Finset (Fin k) // s.card = 1}, ∃ m : ℕ, f i ^ m • t.1.2.2 u = 0 := by
    intro u
    by_cases hu : i ∈ u.1
    · have : u = singletonIndex i := by
        obtain ⟨j, hj⟩ := Finset.card_eq_one.mp u.2
        apply Subtype.ext
        rw [hj] at hu ⊢
        simp only [Finset.mem_singleton] at hu
        rw [hu]
      subst this
      exact ⟨0, by rw [ht', smul_zero]⟩
    · let T : {s : Finset (Fin k) // s.card = 2} :=
        ⟨insert i u.1, by rw [Finset.card_insert_of_notMem hu, u.2]⟩
      have hiT : (singletonIndex i).1 ⊆ T.1 := by simp [T]
      have huT : u.1 ⊆ T.1 := Finset.subset_insert _ _
      have := h4 T (singletonIndex i) u hiT huT
      rw [D.ιV_apply _ (nonempty_of_card_eq _),
        D.ιV_apply _ (nonempty_of_card_eq _), ht', map_zero] at this
      exact D.sig_eq_zero hN i huT (le_refl _) (nonempty_of_card_eq u) _ this.symm
  rw [rs_singleton] at hn₁ hn₂
  choose m hm using hV
  let M : ℕ := ∑ u, m u
  have hkill : ∀ {A : Type u} [AddCommGroup A] [Module R A] (x : A) {n n' : ℕ},
      f i ^ n • x = 0 → n ≤ n' → f i ^ n' • x = 0 := by
    intro A _ _ x n n' h hle
    rw [← Nat.sub_add_cancel hle, pow_add, mul_smul, h, smul_zero]
  refine ⟨n₁ + n₂ + M, D.ext_glued ?_ ?_ ?_⟩
  · exact hkill t.1.1 hn₁ (by omega)
  · exact hkill t.1.2.1 hn₂ (by omega)
  · funext u
    exact hkill (t.1.2.2 u) (hm u)
      ((Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ u)).trans
        (Nat.le_add_left _ _))

include hN in
/-- For `v` in `V_{i}`, some `f i ^ n • v` agrees with the projection of an element of the glued
ring modulo the extension of `N` to `V_{i}`. -/
theorem exists_pow_smul_sub_prV_mem [IsNoetherianRing S]
    (hflat : ∀ i, Module.Flat R (Localization.Away (algebraMap R H (f i))))
    (i : Fin k) (v : (D.L (singletonIndex i).1).carrier) :
    ∃ (n : ℕ) (t : D.TT), f i ^ n • v - D.prV _ t ∈
      N.map (algebraMap R (D.L (singletonIndex i).1).carrier) := by
  obtain ⟨n, c, hc⟩ := IsLocalization.Away.surj (algebraMap R S (rs f {i}))
    ((D.L (singletonIndex i).1).ψ v)
  obtain ⟨t, rfl⟩ := D.prS_surjective hN hflat c
  refine ⟨n, t, ?_⟩
  have h2 := ((D.mem_glued t.1).mp t.2).2.1 (singletonIndex i)
  rw [NilLift.mem_iff, map_sub, map_smul, show D.prV _ t = t.1.2.2 _ from rfl,
    h2, sub_eq_zero]
  show _ = algebraMap S _ (D.prS t)
  rw [← hc, Algebra.smul_def, mul_comm, ← rs_singleton f i, map_pow,
    IsScalarTower.algebraMap_apply R S (Sl f S _)]

include hN in
/-- For `v` in `V_{i}`, some `f i ^ n • v` is the projection of an element of the glued ring. -/
theorem exists_pow_smul_eq_prV [IsNoetherianRing S]
    (hflat : ∀ i, Module.Flat R (Localization.Away (algebraMap R H (f i))))
    (i : Fin k) (v : (D.L (singletonIndex i).1).carrier) :
    ∃ (n : ℕ) (t : D.TT), f i ^ n • v = D.prV _ t := by
  let V := (D.L (singletonIndex i).1).carrier
  have hB : ∀ w ∈ N.map (algebraMap R V),
      ∃ (n : ℕ) (t : D.TT), f i ^ n • w = D.prV _ t := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨n', hn', rfl⟩ := hx
      exact ⟨0, algebraMap R _ n', by rw [pow_zero, one_smul, AlgHom.commutes]⟩
    | zero => exact ⟨0, 0, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, t, ht⟩ := hx
      obtain ⟨b, t', ht'⟩ := hy
      refine ⟨a + b, f i ^ b • t + f i ^ a • t', ?_⟩
      rw [map_add, map_smul, map_smul, ← ht, ← ht', smul_add, smul_smul, smul_smul, ← pow_add,
        ← pow_add, add_comm b a]
    | smul c x hxN hx =>
      obtain ⟨a, t, ht⟩ := hx
      obtain ⟨b, t', ht'⟩ := D.exists_pow_smul_sub_prV_mem hN hflat i c
      refine ⟨b + a, t' * t, ?_⟩
      have h0 : (f i ^ b • c - D.prV _ t') * (f i ^ a • x) = 0 := by
        have : (f i ^ b • c - D.prV _ t') * (f i ^ a • x) ∈
            N.map (algebraMap R V) ^ 2 := by
          rw [pow_two]
          exact Ideal.mul_mem_mul ht' (Submodule.smul_of_tower_mem _ _ hxN)
        rwa [map_sq_eq_bot N hN V] at this
      rw [sub_mul, sub_eq_zero] at h0
      rw [map_mul, ← ht, ← h0, smul_mul_smul_comm, ← pow_add, add_comm b a]
      rfl
  obtain ⟨n, t, ht⟩ := D.exists_pow_smul_sub_prV_mem hN hflat i v
  obtain ⟨m, t', ht'⟩ := hB _ ht
  refine ⟨m + n, f i ^ m • t + t', ?_⟩
  rw [map_add, map_smul, ← ht', smul_sub, smul_smul, ← pow_add]
  abel

include hN in
/-- The lift `V_{i}` is the localization of the glued ring at `f i`. -/
theorem isLocalization_prV [IsNoetherianRing S]
    (hflat : ∀ i, Module.Flat R (Localization.Away (algebraMap R H (f i)))) (i : Fin k) :
    letI := (D.prV (singletonIndex i)).toRingHom.toAlgebra
    IsLocalization.Away (algebraMap R D.TT (f i))
      (D.L (singletonIndex i).1).carrier := by
  let := (D.prV (singletonIndex i)).toRingHom.toAlgebra
  have halg : ∀ t, algebraMap D.TT (D.L (singletonIndex i).1).carrier t =
      D.prV _ t := fun _ ↦ rfl
  refine IsLocalization.Away.mk _ ?_ (fun v ↦ ?_) (fun a b hab ↦ ?_)
  · rw [halg, AlgHom.commutes, ← rs_singleton f i]
    exact isUnit_V N hN f S D.L (le_refl _)
  · obtain ⟨n, t, ht⟩ := D.exists_pow_smul_eq_prV hN hflat i v
    refine ⟨n, t, ?_⟩
    rw [halg, halg, ← ht, AlgHom.commutes, Algebra.smul_def, map_pow, mul_comm]
  · rw [halg, halg, ← sub_eq_zero, ← map_sub] at hab
    obtain ⟨n, hn⟩ := D.prV_eq_zero_torsion hN hflat i _ hab
    refine ⟨n, ?_⟩
    rw [← sub_eq_zero, ← mul_sub, ← map_pow, ← Algebra.smul_def, hn]

end Rig.SquareZeroLift.GlueDatum

end
