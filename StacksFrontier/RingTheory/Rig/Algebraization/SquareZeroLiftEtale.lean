module

public import StacksFrontier.RingTheory.Rig.Algebraization.SquareZeroLiftKer
public import StacksFrontier.RingTheory.Rig.RigEtaleLocus

/-!
# The glued ring is étale away from `V(f)`

In the setting of `StacksFrontier.RingTheory.Rig.Algebraization.SquareZeroLiftRing`, the projection
`T → V_{i}` identifies `V_{i}` with the localization `T[1 / f i]`. Since `V_{i}` is étale over
`R`, the glued ring `T` is étale over the complement of `V(f₁, …, f_k)`.

## Main results

* `Rig.SquareZeroLift.isLocalization_prV`: `V_{i}` is the localization of `T` at `f i`.
* `Rig.SquareZeroLift.isEtaleOutside_glued`: `T` is étale away from `V(f)`.
-/

@[expose] public section

namespace Rig.SquareZeroLift

open TensorProduct Cech FormalGlueing

universe u

variable {R : Type u} [CommRing R] (N : Ideal R) (hN : N ^ 2 = ⊥)
variable {k : ℕ} (f : Fin k → R)
variable (S : Type u) [CommRing S] [Algebra R S]
variable (H : Type u) [CommRing H] [Algebra R H]
variable (e : (H ⧸ N.map (algebraMap R H)) ≃ₐ[R] Sh f S)
variable (L : ∀ s : Finset (Fin k), NilLift R N (Sl f S s))
variable (hL : ∀ s, s.Nonempty → Algebra.Etale R (L s).carrier)

/-- If `t ⊆ insert a s`, then `r_t` divides `f a * r_s`. -/
theorem rs_insert_dvd (a : Fin k) {s t : Finset (Fin k)} (ht : t ⊆ insert a s) :
    rs f t ∣ f a * rs f s := by
  refine (Finset.prod_dvd_prod_of_subset _ _ _ ht).trans ?_
  by_cases ha : a ∈ s
  · rw [Finset.insert_eq_of_mem ha]
    exact dvd_mul_left _ _
  · rw [rs, Finset.prod_insert ha]

/-- For `s ⊆ t ⊆ insert a s`, an element of `S_s` killed by the transition map `S_s → S_t`
is killed by a power of `f a`. -/
theorem locS_eq_zero (a : Fin k) {s t : Finset (Fin k)} (h : s ⊆ t) (ht : t ⊆ insert a s)
    (x : Sl f S s) (hx : locS f S h x = 0) : ∃ m : ℕ, f a ^ m • x = 0 := by
  obtain ⟨n, c, hc⟩ := IsLocalization.Away.surj (algebraMap R S (rs f s)) x
  have h1 : algebraMap S (Sl f S t) c = 0 := by
    rw [← locS_algebraMap f S h, ← hc, map_mul, hx, zero_mul]
  rw [← map_zero (algebraMap S (Sl f S t))] at h1
  obtain ⟨m, hm⟩ := IsLocalization.Away.exists_of_eq (algebraMap R S (rs f t)) h1
  rw [mul_zero] at hm
  obtain ⟨q, hq⟩ := rs_insert_dvd f a ht
  have h2 : algebraMap R S (f a * rs f s) ^ m * c = 0 := by
    rw [hq, map_mul, mul_pow]
    linear_combination (algebraMap R S q ^ m) * hm
  have hu : IsUnit (algebraMap S (Sl f S s) (algebraMap R S (rs f s))) :=
    IsLocalization.Away.algebraMap_isUnit _
  refine ⟨m, ?_⟩
  have h3 : (algebraMap S (Sl f S s) (algebraMap R S (rs f s)) ^ m *
      algebraMap S (Sl f S s) (algebraMap R S (rs f s)) ^ n) * (f a ^ m • x) = 0 := by
    have : (algebraMap S (Sl f S s) (algebraMap R S (rs f s)) ^ m *
        algebraMap S (Sl f S s) (algebraMap R S (rs f s)) ^ n) * (f a ^ m • x) =
        algebraMap S (Sl f S s) (algebraMap R S (f a * rs f s) ^ m * c) := by
      rw [Algebra.smul_def, IsScalarTower.algebraMap_apply R S (Sl f S s)]
      simp only [map_mul, map_pow]
      rw [← hc]
      ring
    rw [this, h2, map_zero]
  exact ((hu.pow m).mul (hu.pow n)).mul_left_cancel (h3.trans (mul_zero _).symm)

include hL in
/-- For `s ⊆ t ⊆ insert a s` with `s` nonempty, an element of `V_s` killed by the transition
map `σ_{s,t} : V_s → V_t` is killed by a power of `f a`. -/
theorem sig_eq_zero (a : Fin k) {s t : Finset (Fin k)} (h : s ⊆ t) (ht : t ⊆ insert a s)
    (hs : s.Nonempty) (w : (L s).carrier) (hw : sig N hN f S L hL h hs w = 0) :
    ∃ m : ℕ, f a ^ m • w = 0 := by
  have h1 : locS f S h ((L s).ψ w) = 0 := by rw [← psi_sig N hN f S L hL h hs, hw, map_zero]
  obtain ⟨m₁, hm₁⟩ := locS_eq_zero f S a h ht _ h1
  have h2 : f a ^ m₁ • w ∈ N.map (algebraMap R (L s).carrier) := by
    rw [NilLift.mem_iff, map_smul, hm₁]
  obtain ⟨y, hy⟩ := exists_muV_eq N hN f S L s _ h2
  have h3 : cechι (gS f S) (PS N S) h y = 0 := by
    apply muV_injective N hN f S L hL t (hs.mono h)
    rw [muV_cechι N hN f S L hL h hs, hy, map_smul, hw, smul_zero, map_zero]
  obtain ⟨m₂, hm₂⟩ := exists_pow_smul_eq_zero_of_cechι_eq_zero (gS f S) a h ht y h3
  refine ⟨m₂ + m₁, ?_⟩
  have : f a ^ m₂ • y = 0 := by
    rw [← hm₂, gS, ← map_pow, algebraMap_smul]
  rw [pow_add, mul_smul, ← hy, ← map_smul, this, map_zero]

/-- The product `r_{i}` over a singleton is `f i`. -/
theorem rs_singleton (i : Fin k) : rs f {i} = f i := Finset.prod_singleton f i

/-- An element killed by `f i ^ m` is killed by every larger power of `f i`. -/
private theorem pow_smul_eq_zero_of_le {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]
    (a : A) {m n : ℕ} (x : M) (h : m ≤ n) (hx : a ^ m • x = 0) : a ^ n • x = 0 := by
  rw [← Nat.sub_add_cancel h, pow_add, mul_smul, hx, smul_zero]

/-- An element of an `R`-algebra `A` that vanishes in `A_{r_{i}}` is killed by a power of `f i`. -/
private theorem exists_pow_smul_eq_zero_of_algebraMap_eq_zero {A : Type*} [CommRing A]
    [Algebra R A] (i : Fin k) (x : A)
    (hx : algebraMap A (Localization.Away (algebraMap R A (rs f {i}))) x = 0) :
    ∃ n : ℕ, f i ^ n • x = 0 := by
  obtain ⟨n, hn⟩ := IsLocalization.Away.exists_of_eq (algebraMap R A (rs f {i}))
    (hx.trans (map_zero _).symm)
  rw [mul_zero, rs_singleton, ← map_pow] at hn
  exact ⟨n, by rw [Algebra.smul_def, hn]⟩

include hL in
/-- An element of the glued ring `T` whose projection to `V_{i}` vanishes is killed by a power
of `f i`. -/
theorem prV_eq_zero_torsion [IsNoetherianRing S]
    (_hflat : ∀ i, Module.Flat R (Localization.Away (algebraMap R H (f i))))
    (i : Fin k) (t : TT N hN f S H e L hL)
    (ht : prV N hN f S H e L hL (singletonIndex i) t = 0) :
    ∃ n : ℕ, f i ^ n • t = 0 := by
  classical
  obtain ⟨h1, h2, h3, h4⟩ := (mem_glued N hN f S H e L hL t.1).mp t.2
  rw [cechDiff_one_eq_zero_iff] at h4
  rw [prV_apply] at ht
  obtain ⟨n₁, hn₁⟩ := exists_pow_smul_eq_zero_of_algebraMap_eq_zero f i t.1.1
    (by rw [← h2 (singletonIndex i), ht, map_zero])
  obtain ⟨n₂, hn₂⟩ := exists_pow_smul_eq_zero_of_algebraMap_eq_zero f i t.1.2.1
    (by rw [← h3 (singletonIndex i), ht, map_zero])
  have hV : ∀ u : {s : Finset (Fin k) // s.card = 1}, ∃ m : ℕ, f i ^ m • t.1.2.2 u = 0 := by
    intro u
    by_cases hu : i ∈ u.1
    · obtain rfl : u = singletonIndex i := by
        obtain ⟨j, hj⟩ := Finset.card_eq_one.mp u.2
        apply Subtype.ext
        rw [hj] at hu ⊢
        simp only [Finset.mem_singleton] at hu
        rw [hu]
      exact ⟨0, by rw [ht, smul_zero]⟩
    · let T : {s : Finset (Fin k) // s.card = 2} :=
        ⟨insert i u.1, by rw [Finset.card_insert_of_notMem hu, u.2]⟩
      have hiT : (singletonIndex i).1 ⊆ T.1 := by simp [T]
      have huT : u.1 ⊆ T.1 := Finset.subset_insert _ _
      have := h4 T (singletonIndex i) u hiT huT
      rw [ιV_apply N hN f S L hL _ (nonempty_of_card_eq _),
        ιV_apply N hN f S L hL _ (nonempty_of_card_eq _), ht, map_zero] at this
      exact sig_eq_zero N hN f S L hL i huT (le_refl _) (nonempty_of_card_eq u) _ this.symm
  choose m hm using hV
  let M : ℕ := ∑ u, m u
  refine ⟨n₁ + n₂ + M, ext_glued N hN f S H e L hL ?_ ?_ ?_⟩
  · exact pow_smul_eq_zero_of_le (f i) t.1.1 (by omega) hn₁
  · exact pow_smul_eq_zero_of_le (f i) t.1.2.1 (by omega) hn₂
  · funext u
    exact pow_smul_eq_zero_of_le (f i) (t.1.2.2 u) ((Finset.single_le_sum
      (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ u)).trans (Nat.le_add_left _ _)) (hm u)

/-- For `v ∈ V_{i}`, some `f i ^ n • v` agrees with the projection of an element of the glued
ring `T` modulo `N V_{i}`. -/
theorem exists_pow_smul_sub_prV_mem [IsNoetherianRing S]
    (hflat : ∀ i, Module.Flat R (Localization.Away (algebraMap R H (f i))))
    (i : Fin k) (v : (L (singletonIndex i).1).carrier) :
    ∃ (n : ℕ) (t : TT N hN f S H e L hL), f i ^ n • v - prV N hN f S H e L hL _ t ∈
      N.map (algebraMap R (L (singletonIndex i).1).carrier) := by
  obtain ⟨n, c, hc⟩ := IsLocalization.Away.surj (algebraMap R S (rs f {i}))
    ((L (singletonIndex i).1).ψ v)
  obtain ⟨t, rfl⟩ := prS_surjective N hN f S H e L hL hflat c
  refine ⟨n, t, ?_⟩
  have h2 := ((mem_glued N hN f S H e L hL t.1).mp t.2).2.1 (singletonIndex i)
  rw [NilLift.mem_iff, map_sub, map_smul, prV_apply, h2, sub_eq_zero]
  show _ = algebraMap S _ (prS N hN f S H e L hL t)
  rw [← hc, Algebra.smul_def, mul_comm, ← rs_singleton f i, map_pow,
    IsScalarTower.algebraMap_apply R S (Sl f S _)]

/-- For `v ∈ V_{i}`, some `f i ^ n • v` is the projection of an element of the glued ring `T`. -/
theorem exists_pow_smul_eq_prV [IsNoetherianRing S]
    (hflat : ∀ i, Module.Flat R (Localization.Away (algebraMap R H (f i))))
    (i : Fin k) (v : (L (singletonIndex i).1).carrier) :
    ∃ (n : ℕ) (t : TT N hN f S H e L hL), f i ^ n • v = prV N hN f S H e L hL _ t := by
  let V := (L (singletonIndex i).1).carrier
  have hB : ∀ w ∈ N.map (algebraMap R V),
      ∃ (n : ℕ) (t : TT N hN f S H e L hL), f i ^ n • w = prV N hN f S H e L hL _ t := by
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
      obtain ⟨b, t', ht'⟩ := exists_pow_smul_sub_prV_mem N hN f S H e L hL hflat i c
      refine ⟨b + a, t' * t, ?_⟩
      have hx' : f i ^ a • x ∈ N.map (algebraMap R V) := Submodule.smul_of_tower_mem _ _ hxN
      have h0 : (f i ^ b • c - prV N hN f S H e L hL _ t') * (f i ^ a • x) = 0 := by
        have : (f i ^ b • c - prV N hN f S H e L hL _ t') * (f i ^ a • x) ∈
            N.map (algebraMap R V) ^ 2 := by
          rw [pow_two]
          exact Ideal.mul_mem_mul ht' hx'
        rwa [map_sq_eq_bot N hN V] at this
      rw [sub_mul, sub_eq_zero] at h0
      rw [map_mul, ← ht, ← h0, smul_mul_smul_comm, ← pow_add, add_comm b a]
      rfl
  obtain ⟨n, t, ht⟩ := exists_pow_smul_sub_prV_mem N hN f S H e L hL hflat i v
  obtain ⟨m, t', ht'⟩ := hB _ ht
  refine ⟨m + n, f i ^ m • t + t', ?_⟩
  rw [map_add, map_smul, ← ht', smul_sub, smul_smul, ← pow_add]
  abel

/-- The lift `V_{i}` is the localization of the glued ring at `f i`. -/
theorem isLocalization_prV [IsNoetherianRing S]
    (hflat : ∀ i, Module.Flat R (Localization.Away (algebraMap R H (f i)))) (i : Fin k) :
    letI := (prV N hN f S H e L hL (singletonIndex i)).toRingHom.toAlgebra
    IsLocalization.Away (algebraMap R (TT N hN f S H e L hL) (f i))
      (L (singletonIndex i).1).carrier := by
  let := (prV N hN f S H e L hL (singletonIndex i)).toRingHom.toAlgebra
  have halg : ∀ t, algebraMap (TT N hN f S H e L hL) (L (singletonIndex i).1).carrier t =
      prV N hN f S H e L hL _ t := fun _ ↦ rfl
  refine IsLocalization.Away.mk _ ?_ (fun v ↦ ?_) (fun a b hab ↦ ?_)
  · rw [halg, AlgHom.commutes, ← rs_singleton f i]
    exact isUnit_V N hN f S L (le_refl _)
  · obtain ⟨n, t, ht⟩ := exists_pow_smul_eq_prV N hN f S H e L hL hflat i v
    refine ⟨n, t, ?_⟩
    rw [halg, halg, ← ht, AlgHom.commutes, Algebra.smul_def, map_pow, mul_comm]
  · rw [halg, halg, ← sub_eq_zero, ← map_sub] at hab
    obtain ⟨n, hn⟩ := prV_eq_zero_torsion N hN f S H e L hL hflat i _ hab
    refine ⟨n, ?_⟩
    rw [← sub_eq_zero, ← mul_sub, ← map_pow, ← Algebra.smul_def, hn]

/-- **The glued ring is étale away from `V(f)`.** -/
theorem isEtaleOutside_glued [IsNoetherianRing S]
    (hflat : ∀ i, Module.Flat R (Localization.Away (algebraMap R H (f i)))) :
    IsEtaleOutside (Ideal.span (Set.range f)) (TT N hN f S H e L hL) := by
  rw [isEtaleOutside_iff]
  intro q hq hle
  obtain ⟨i, hi⟩ : ∃ i, algebraMap R (TT N hN f S H e L hL) (f i) ∉ q := by
    by_contra! hcon
    exact hle (Ideal.span_le.mpr (Set.range_subset_iff.mpr hcon))
  let := (prV N hN f S H e L hL (singletonIndex i)).toRingHom.toAlgebra
  have := isLocalization_prV N hN f S H e L hL hflat i
  have : IsScalarTower R (TT N hN f S H e L hL) (L (singletonIndex i).1).carrier :=
    IsScalarTower.of_algebraMap_eq fun r ↦ ((prV N hN f S H e L hL _).commutes r).symm
  have := hL _ (nonempty_of_card_eq (singletonIndex i))
  have : Algebra.FormallyEtale R
      (Localization.Away (algebraMap R (TT N hN f S H e L hL) (f i))) :=
    .of_equiv ((IsLocalization.algEquiv
      (Submonoid.powers (algebraMap R (TT N hN f S H e L hL) (f i)))
      (L (singletonIndex i).1).carrier
      (Localization.Away (algebraMap R (TT N hN f S H e L hL) (f i)))).restrictScalars R)
  exact (Algebra.basicOpen_subset_etaleLocus_iff (R := R)).mpr this
    (show (⟨q, hq⟩ : PrimeSpectrum _) ∈ PrimeSpectrum.basicOpen _ from hi)

end Rig.SquareZeroLift

end
