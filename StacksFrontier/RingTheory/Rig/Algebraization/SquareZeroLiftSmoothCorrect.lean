module

public import StacksFrontier.RingTheory.Rig.Algebraization.SquareZeroLiftSmoothCocycle

/-!
# Correcting a choice of charts

In the setting of `StacksFrontier.RingTheory.Rig.Algebraization.SquareZeroLiftSmoothCocycle`, the
defects `D` and `E` of a choice of charts, viewed as cochains of the glueing complex, and the
choice of charts obtained by correcting the maps `φ_i` and the chart changes `γ_{ij}` by given
cochains.

## Main results

* `Rig.SquareZeroLift.ChartData.exists_compatible`: there is a choice of charts whose chart
  changes satisfy `γ_{ij} γ_{jl} = γ_{il}` and `φ_i γ_{ij} = φ_j`.
-/

@[expose] public section

namespace Rig.SquareZeroLift

open TensorProduct

universe u

variable {R : Type u} [CommRing R] {N : Ideal R} (hN : N ^ 2 = ⊥)
variable {k : ℕ} {f : Fin k → R}
variable {S : Type u} [CommRing S] [Algebra R S]
variable {H : Type u} [CommRing H] [Algebra R H]
variable {e : (H ⧸ N.map (algebraMap R H)) ≃ₐ[R] Sh f S}
variable {W : ∀ i : Fin k, NilLift R N (Sl f S {i})}

/-! ### Sorted indices -/

/-- The `i`-th smallest element of a finite set of indices with `p` elements. -/
noncomputable def srt {p : ℕ} (T : {s : Finset (Fin k) // s.card = p}) (i : Fin p) : Fin k :=
  T.1.orderEmbOfFin T.2 i

/-- The `i`-th smallest element of `T` lies in `T`. -/
theorem srt_mem {p : ℕ} (T : {s : Finset (Fin k) // s.card = p}) (i : Fin p) : srt T i ∈ T.1 :=
  Finset.orderEmbOfFin_mem _ _ i

/-- The map `srt T` is strictly increasing. -/
theorem srt_lt {p : ℕ} (T : {s : Finset (Fin k) // s.card = p}) {i j : Fin p} (h : i < j) :
    srt T i < srt T j :=
  (T.1.orderEmbOfFin T.2).strictMono h

/-- A strictly increasing map `Fin p → Fin k` with values in `T` is `srt T`. -/
theorem srt_eq {p : ℕ} (T : {s : Finset (Fin k) // s.card = p}) (g : Fin p → Fin k)
    (hg : StrictMono g) (hgT : ∀ i, g i ∈ T.1) (i : Fin p) : srt T i = g i := by
  rw [srt, ← Finset.orderEmbOfFin_unique T.2 hgT hg]

/-- If `T = {a, b}` with `a < b`, then the elements of `T` in increasing order are `a`, `b`. -/
theorem srt_pair (T : {s : Finset (Fin k) // s.card = 2}) {a b : Fin k} (hab : a < b)
    (hT : T.1 = {a, b}) : srt T 0 = a ∧ srt T 1 = b := by
  have hg : StrictMono ![a, b] := fun i j hij ↦ by fin_cases i <;> fin_cases j <;> simp_all
  have hgT : ∀ i, ![a, b] i ∈ T.1 := fun i ↦ by rw [hT]; fin_cases i <;> simp
  exact ⟨srt_eq T _ hg hgT 0, srt_eq T _ hg hgT 1⟩

/-- If `T = {a, b, c}` with `a < b < c`, then the elements of `T` in increasing order are `a`, `b`,
`c`. -/
theorem srt_triple (T : {s : Finset (Fin k) // s.card = 3}) {a b c : Fin k} (hab : a < b)
    (hbc : b < c) (hT : T.1 = {a, b, c}) : srt T 0 = a ∧ srt T 1 = b ∧ srt T 2 = c := by
  have hg : StrictMono ![a, b, c] := fun i j hij ↦ by
    fin_cases i <;> fin_cases j <;> simp_all [hab.trans hbc]
  have hgT : ∀ i, ![a, b, c] i ∈ T.1 := fun i ↦ by rw [hT]; fin_cases i <;> simp
  exact ⟨srt_eq T _ hg hgT 0, srt_eq T _ hg hgT 1, srt_eq T _ hg hgT 2⟩

/-- A set `{x, y, z}` with `x < y < z` has three elements. -/
private theorem card_triple_of_lt {x y z : Fin k} (hxy : x < y) (hyz : y < z) :
    ({x, y, z} : Finset (Fin k)).card = 3 := by
  rw [Finset.card_insert_of_notMem (by simp; omega), Finset.card_pair (ne_of_lt hyz)]

namespace ChartData

variable (C : ChartData N f S H e W)
variable (hflat : ∀ i, Module.Flat R (Localization.Away (algebraMap R H (f i))))
variable [hW : ∀ i, Module.Flat R (W i).carrier]

omit hW in
/-- The defect `C.DH` at `a < b` equals the defect at `a' < b'` when `a = a'` and `b = b'`. -/
theorem DH_congr {a b a' b' : Fin k} (ha' : a = a') (hb' : b = b') (hab : a < b) (hab' : a' < b')
    (s : Finset (Fin k)) (ha : a ∈ s) (hb : b ∈ s) (ha2 : a' ∈ s) (hb2 : b' ∈ s) :
    C.DH hN hflat a b hab s ha hb = C.DH hN hflat a' b' hab' s ha2 hb2 := by
  subst ha' hb'
  rfl

/-- The defect `C.EV` at `a < b < c` equals the defect at `a' < b' < c'` when `a = a'`, `b = b'`
and `c = c'`. -/
theorem EV_congr {a b c a' b' c' : Fin k} (ha' : a = a') (hb' : b = b') (hc' : c = c')
    (hab : a < b) (hbc : b < c) (hab' : a' < b') (hbc' : b' < c') (s : Finset (Fin k))
    (ha : a ∈ s) (hb : b ∈ s) (hc : c ∈ s) (ha2 : a' ∈ s) (hb2 : b' ∈ s) (hc2 : c' ∈ s) :
    C.EV hN a b c hab hbc s ha hb hc = C.EV hN a' b' c' hab' hbc' s ha2 hb2 hc2 := by
  subst ha' hb' hc'
  rfl

/-- The defect cochain `D` on the pairs of indices. -/
noncomputable def Dfam : FamTerm (derH N f S) 2 := fun T ↦
  C.DH hN hflat (srt T 0) (srt T 1) (srt_lt T (by decide)) T.1 (srt_mem T 0) (srt_mem T 1)

/-- The defect cochain `E` on the triples of indices. -/
noncomputable def Efam : FamTerm (derV N f S) 3 := fun T ↦
  C.EV hN (srt T 0) (srt T 1) (srt T 2) (srt_lt T (by decide)) (srt_lt T (by decide)) T.1
    (srt_mem T 0) (srt_mem T 1) (srt_mem T 2)

/-- The value of `C.Dfam` on `T = {a, b}` with `a < b` is the defect `C.DH` at `a`, `b`. -/
theorem Dfam_eq (T : {s : Finset (Fin k) // s.card = 2}) {a b : Fin k} (hab : a < b)
    (hT : T.1 = {a, b}) (ha : a ∈ T.1) (hb : b ∈ T.1) :
    C.Dfam hN hflat T = C.DH hN hflat a b hab T.1 ha hb := by
  obtain ⟨h0, h1⟩ := srt_pair T hab hT
  exact C.DH_congr hN hflat h0 h1 _ _ _ _ _ _ _

/-- The value of `C.Efam` on `T = {a, b, c}` with `a < b < c` is the defect `C.EV` at `a`, `b`,
`c`. -/
theorem Efam_eq (T : {s : Finset (Fin k) // s.card = 3}) {a b c : Fin k} (hab : a < b)
    (hbc : b < c) (hT : T.1 = {a, b, c}) (ha : a ∈ T.1) (hb : b ∈ T.1) (hc : c ∈ T.1) :
    C.Efam hN T = C.EV hN a b c hab hbc T.1 ha hb hc := by
  obtain ⟨h0, h1, h2⟩ := srt_triple T hab hbc hT
  exact C.EV_congr hN h0 h1 h2 _ _ _ _ _ _ _ _ _ _ _

/-- The Čech differential of `C.Dfam` on a triple `T` is the image of `C.Efam T` under `derT`. -/
theorem cechDiff_Dfam (T : {s : Finset (Fin k) // s.card = 3}) :
    cechDiff (derH N f S) (derιH N f S) 2 (C.Dfam hN hflat) T = derT N f S T.1 (C.Efam hN T) := by
  obtain ⟨a, b, c, hab, hbc, hT⟩ := exists_sorted_triple T
  have hac := hab.trans hbc
  have ha : a ∈ T.1 := by simp [hT]
  have hb : b ∈ T.1 := by simp [hT]
  have hc : c ∈ T.1 := by simp [hT]
  have s1 : ({b, c} : Finset (Fin k)) ⊆ T.1 := pair_subset_of_mem hb hc
  have s2 : ({a, c} : Finset (Fin k)) ⊆ T.1 := pair_subset_of_mem ha hc
  have s3 : ({a, b} : Finset (Fin k)) ⊆ T.1 := pair_subset_of_mem ha hb
  rw [cechDiff_two_apply (derH N f S) (derιH N f S) _ T hab hbc hT
    ⟨{b, c}, Finset.card_pair (ne_of_lt hbc)⟩ ⟨{a, c}, Finset.card_pair (ne_of_lt hac)⟩
    ⟨{a, b}, Finset.card_pair (ne_of_lt hab)⟩ rfl rfl rfl s1 s2 s3,
    C.Dfam_eq hN hflat _ hbc rfl (mem_pair_left b c) (mem_pair_right b c),
    C.Dfam_eq hN hflat _ hac rfl (mem_pair_left a c) (mem_pair_right a c),
    C.Dfam_eq hN hflat _ hab rfl (mem_pair_left a b) (mem_pair_right a b),
    C.DH_loc hN hflat b c hbc s1, C.DH_loc hN hflat a c hac s2, C.DH_loc hN hflat a b hab s3,
    C.Efam_eq hN T hab hbc hT ha hb hc]
  exact C.DH_cocycle hN hflat a b c hab hbc T.1 ha hb hc

/-- The Čech differential of `C.Efam` vanishes. -/
theorem cechDiff_Efam (T : {s : Finset (Fin k) // s.card = 4}) :
    cechDiff (derV N f S) (derιV N f S) 3 (C.Efam hN) T = 0 := by
  obtain ⟨a, b, c, d, hab, hbc, hcd, hT⟩ := exists_sorted_quadruple T
  have ha : a ∈ T.1 := by simp [hT]
  have hb : b ∈ T.1 := by simp [hT]
  have hc : c ∈ T.1 := by simp [hT]
  have hd : d ∈ T.1 := by simp [hT]
  have sub3 : ∀ {x y z : Fin k}, x ∈ T.1 → y ∈ T.1 → z ∈ T.1 →
      ({x, y, z} : Finset (Fin k)) ⊆ T.1 := fun hx hy hz ↦
    Finset.insert_subset_iff.mpr ⟨hx, pair_subset_of_mem hy hz⟩
  have m1 : ∀ x y z : Fin k, x ∈ ({x, y, z} : Finset (Fin k)) := by simp
  have m2 : ∀ x y z : Fin k, y ∈ ({x, y, z} : Finset (Fin k)) := by simp
  have m3 : ∀ x y z : Fin k, z ∈ ({x, y, z} : Finset (Fin k)) := by simp
  rw [cechDiff_three_apply (derV N f S) (derιV N f S) _ T hab hbc hcd hT
    ⟨{b, c, d}, card_triple_of_lt hbc hcd⟩ ⟨{a, c, d}, card_triple_of_lt (hab.trans hbc) hcd⟩
    ⟨{a, b, d}, card_triple_of_lt hab (hbc.trans hcd)⟩ ⟨{a, b, c}, card_triple_of_lt hab hbc⟩
    rfl rfl rfl rfl
    (sub3 hb hc hd) (sub3 ha hc hd) (sub3 ha hb hd) (sub3 ha hb hc),
    C.Efam_eq hN _ hbc hcd rfl (m1 b c d) (m2 b c d) (m3 b c d),
    C.Efam_eq hN _ (hab.trans hbc) hcd rfl (m1 a c d) (m2 a c d) (m3 a c d),
    C.Efam_eq hN _ hab (hbc.trans hcd) rfl (m1 a b d) (m2 a b d) (m3 a b d),
    C.Efam_eq hN _ hab hbc rfl (m1 a b c) (m2 a b c) (m3 a b c),
    C.EV_loc hN, C.EV_loc hN, C.EV_loc hN, C.EV_loc hN]
  exact C.EV_cocycle hN a b c d hab hbc hcd T.1 ha hb hc hd

end ChartData

/-! ### Comparing two choices of charts -/

section Compare

/-- An element `w` of `W_{i,s}` with `ψ w = v` has the same image under `ψ` as the restriction of
some `w₀ ∈ W_{i,t}` with `ψ w₀ = v`, for `i ∈ t ⊆ s`. -/
private theorem exists_psi_eq_resW {i : Fin k} {t s : Finset (Fin k)} (hsub : t ⊆ s) (hit : i ∈ t)
    (hi : i ∈ s) (v : S) (w : (Wc N f S W i s hi).carrier)
    (hw : (Wc N f S W i s hi).ψ w = algebraMap S _ v) :
    ∃ w₀ : (Wc N f S W i t hit).carrier, (Wc N f S W i t hit).ψ w₀ = algebraMap S _ v ∧
      (Wc N f S W i s hi).ψ w = (Wc N f S W i s hi).ψ (resW N f S W i hsub hit w₀) := by
  obtain ⟨w₀, hw₀⟩ := (Wc N f S W i t hit).surj (algebraMap S _ v)
  refine ⟨w₀, hw₀, ?_⟩
  rw [hw]
  exact ((psi_resW N f S W i hsub _ w₀).trans (by rw [hw₀, locS_algebraMap])).symm

variable (C C' : ChartData N f S H e W)
variable (hflat : ∀ i, Module.Flat R (Localization.Away (algebraMap R H (f i))))
variable [hW : ∀ i, Module.Flat R (W i).carrier]

omit hW in
/-- The reduction modulo `N` of `C₀.φ i w` is the image of `ψ w` under `lamXHEquiv`. -/
theorem mk_φ_reduction (C₀ : ChartData N f S H e W) (i : Fin k) :
    ∀ w, Ideal.Quotient.mk _ (C₀.φ i w) = lamXHEquiv N f S H e {i}
      (IsScalarTower.toAlgHom R (Sl f S {i}) (Sl f S {i} ⊗[S] Sh f S)
        ((Wc N f S W i {i} (Finset.mem_singleton_self i)).ψ w)) :=
  reductionH _ _ (C₀.hφ i)

omit hW in
/-- The reduction modulo `N` of `C₀.γ a b hab w` is the image of `ψ w` under the inverse of the
reduction isomorphism `qe` of the `a`-chart. -/
theorem mk_γ_reduction (C₀ : ChartData N f S H e W) (a b : Fin k) (hab : a < b) :
    ∀ w, Ideal.Quotient.mk _ (C₀.γ a b hab w) =
      ((Wc N f S W a {a, b} (mem_pair_left a b)).qe N).symm
        (IsScalarTower.toAlgHom R (Sl f S {a, b}) (Sl f S {a, b})
          ((Wc N f S W b {a, b} (mem_pair_right a b)).ψ w)) :=
  reductionV _ _ _ (C₀.hγ a b hab)

/-- The derivation by which the maps `φ_i` of two choices of charts differ. -/
noncomputable def dφ (i : Fin k) : derH N f S {i} :=
  haveI := flat_Hl f H hflat {i} ⟨i, Finset.mem_singleton_self i⟩
  defect N hN f S (lamXHEquiv N f S H e {i}) (Wc N f S W i {i} (Finset.mem_singleton_self i))
    (IsScalarTower.toAlgHom R (Sl f S {i}) (Sl f S {i} ⊗[S] Sh f S))
    (algebraMap_toAlgHom_algebraMap f S) (C'.φ i) (C.φ i) (mk_φ_reduction C' i)
    (mk_φ_reduction C i)

/-- The derivation by which the chart changes `γ_{ab}` of two choices of charts differ. -/
noncomputable def dγ (a b : Fin k) (hab : a < b) : derV N f S {a, b} :=
  defect N hN f S ((Wc N f S W a {a, b} (mem_pair_left a b)).qe N).symm
    (Wc N f S W b {a, b} (mem_pair_right a b))
    (IsScalarTower.toAlgHom R (Sl f S {a, b}) (Sl f S {a, b}))
    (algebraMap_toAlgHom_algebraMap f S) (C'.γ a b hab) (C.γ a b hab) (mk_γ_reduction C' a b hab)
    (mk_γ_reduction C a b hab)

omit hW in
/-- On an element `w` with `ψ w = v`, the maps `φc` of `C'` and `C` differ by `thetaE` of the
restriction of `dφ` to `s`, evaluated at `v`. -/
theorem φc_sub (i : Fin k) (s : Finset (Fin k)) (hi : i ∈ s) (v : S)
    (w : (Wc N f S W i s hi).carrier) (hw : (Wc N f S W i s hi).ψ w = algebraMap S _ v) :
    C'.φc i s hi w - C.φc i s hi w = thetaE N hN (lamXHEquiv N f S H e s)
      (derιH N f S (Finset.singleton_subset_iff.mpr hi) (dφ hN C C' hflat i) v) := by
  have := flat_Hl f H hflat s ⟨i, hi⟩
  have := flat_Hl f H hflat {i} ⟨i, Finset.mem_singleton_self i⟩
  have hsub : ({i} : Finset (Fin k)) ⊆ s := Finset.singleton_subset_iff.mpr hi
  obtain ⟨w₀, hw₀, hlift⟩ :=
    exists_psi_eq_resW (W := W) hsub (Finset.mem_singleton_self i) hi v w hw
  rewrite [sub_eq_sub_of_psi_eq N hN f S _ _ _
      (fun w ↦ (C'.mk_φc i s hi w).trans (C.mk_φc i s hi w).symm) hlift]
  rewrite [ChartData.φc, ChartData.φc, locMapH_resW, locMapH_resW, ← map_sub,
    derιH_apply, thetaE_rTensor N hN (lamXHEquiv N f S H e {i}) (lamXHEquiv N f S H e s)
      (locXH f S hsub) ((locH f H hsub).restrictScalars R) (redMap_locH_lamXH hsub)]
  rewrite [dφ, thetaE_defect N hN f S _ _ _ _ _ _ _ _ v w₀ hw₀]
  rfl

/-- On an element `w` with `ψ w = v`, the chart changes `γc` of `C'` and `C` differ by `thetaE` of
the restriction of `dγ` to `s`, evaluated at `v`. -/
theorem γc_sub (a b : Fin k) (hab : a < b) (s : Finset (Fin k)) (ha : a ∈ s) (hb : b ∈ s) (v : S)
    (w : (Wc N f S W b s hb).carrier) (hw : (Wc N f S W b s hb).ψ w = algebraMap S _ v) :
    C'.γc a b hab s ha hb w - C.γc a b hab s ha hb w = thetaE N hN ((Wc N f S W a s ha).qe N).symm
      (derιV N f S (pair_subset_of_mem ha hb) (dγ hN C C' a b hab) v) := by
  have hsub : ({a, b} : Finset (Fin k)) ⊆ s := pair_subset_of_mem ha hb
  obtain ⟨w₀, hw₀, hlift⟩ := exists_psi_eq_resW (W := W) hsub (mem_pair_right a b) hb v w hw
  rewrite [sub_eq_sub_of_psi_eq N hN f S _ _ _
      (fun w ↦ (reductionV ha hb _ (C'.psi_γc a b hab s ha hb) w).trans
        (reductionV ha hb _ (C.psi_γc a b hab s ha hb) w).symm) hlift]
  rewrite [ChartData.γc, ChartData.γc, locMap_resW, locMap_resW, ← map_sub, derιV_apply,
    thetaE_rTensor N hN ((Wc N f S W a {a, b} (mem_pair_left a b)).qe N).symm
      ((Wc N f S W a s ha).qe N).symm (locS f S hsub) (resW N f S W a hsub (mem_pair_left a b))
      (redMap_resW_qe hsub (mem_pair_left a b))]
  rewrite [dγ, thetaE_defect N hN f S _ _ _ _ _ _ _ _ v w₀ hw₀]
  rfl

end Compare

/-! ### The corrected charts -/

section Corrected

variable (C : ChartData N f S H e W)
variable (hflat : ∀ i, Module.Flat R (Localization.Away (algebraMap R H (f i))))
variable [hW : ∀ i, Module.Flat R (W i).carrier]

/-- Restriction of derivations along `s ⊆ s` is the identity. -/
theorem derιV_refl {s : Finset (Fin k)} (h : s ⊆ s) (D : derV N f S s) : derιV N f S h D = D := by
  have hid : locS f S h = AlgHom.id R (Sl f S s) :=
    AlgHom.coe_ringHom_injective <| IsLocalization.ringHom_ext
      (Submonoid.powers (algebraMap R S (rs f s))) (RingHom.ext fun a ↦ by simp)
  ext v
  rw [derιV_apply, hid, AlgHom.toLinearMap_id, LinearMap.rTensor_id, LinearMap.id_apply]

namespace ChartData

omit hW in
open FormalGlueing in
/-- There is a map `φ'` with the same reduction as `C.φ i` whose defect against `C.φ i` is the
value of `y` at `{i}`. -/
theorem exists_correct_φ (y : FamTerm (derH N f S) 1) (i : Fin k) :
    ∃ (φ' : (Wc N f S W i {i} (Finset.mem_singleton_self i)).carrier →ₐ[R] Hl f H {i})
      (hφ' : ∀ w, Ideal.Quotient.mk _ (φ' w) = lamXHEquiv N f S H e {i}
        (IsScalarTower.toAlgHom R (Sl f S {i}) (Sl f S {i} ⊗[S] Sh f S)
          ((Wc N f S W i {i} (Finset.mem_singleton_self i)).ψ w))),
      haveI := flat_Hl f H hflat {i} ⟨i, Finset.mem_singleton_self i⟩
      defect N hN f S (lamXHEquiv N f S H e {i}) (Wc N f S W i {i} (Finset.mem_singleton_self i))
        (IsScalarTower.toAlgHom R (Sl f S {i}) (Sl f S {i} ⊗[S] Sh f S))
        (algebraMap_toAlgHom_algebraMap f S) φ' (C.φ i) hφ' (mk_φ_reduction C i) =
      y (singletonIndex i) := by
  have := flat_Hl f H hflat {i} ⟨i, Finset.mem_singleton_self i⟩
  exact exists_defect_eq N hN f S (lamXHEquiv N f S H e {i}) _ (C.φ i) (mk_φ_reduction C i) _

/-- There is a map `γ'` with the same reduction as `C.γ a b hab` whose defect against `C.γ a b hab`
is the value of `x` at `{a, b}`. -/
theorem exists_correct_γ (x : FamTerm (derV N f S) 2) (a b : Fin k) (hab : a < b) :
    ∃ (γ' : (Wc N f S W b {a, b} (mem_pair_right a b)).carrier →ₐ[R]
        (Wc N f S W a {a, b} (mem_pair_left a b)).carrier)
      (hγ' : ∀ w, Ideal.Quotient.mk _ (γ' w) =
        ((Wc N f S W a {a, b} (mem_pair_left a b)).qe N).symm
          (IsScalarTower.toAlgHom R (Sl f S {a, b}) (Sl f S {a, b})
            ((Wc N f S W b {a, b} (mem_pair_right a b)).ψ w))),
      defect N hN f S ((Wc N f S W a {a, b} (mem_pair_left a b)).qe N).symm
        (Wc N f S W b {a, b} (mem_pair_right a b))
        (IsScalarTower.toAlgHom R (Sl f S {a, b}) (Sl f S {a, b}))
        (algebraMap_toAlgHom_algebraMap f S) γ' (C.γ a b hab) hγ' (mk_γ_reduction C a b hab) =
      x ⟨{a, b}, Finset.card_pair (ne_of_lt hab)⟩ :=
  exists_defect_eq N hN f S _ _ (C.γ a b hab) (mk_γ_reduction C a b hab) _

/-- The choice of charts corrected by `y` and `x`. -/
noncomputable def correct (y : FamTerm (derH N f S) 1) (x : FamTerm (derV N f S) 2) :
    ChartData N f S H e W where
  φ i := (C.exists_correct_φ hN hflat y i).choose
  hφ i w := by
    have := (C.exists_correct_φ hN hflat y i).choose_spec.choose w
    rwa [toAlgHom_tensor_apply, lamXHEquiv_apply, lamXH_tmul, map_one, mul_one] at this
  γ a b hab := (C.exists_correct_γ hN x a b hab).choose
  hγ a b hab w := by
    have := (C.exists_correct_γ hN x a b hab).choose_spec.choose w
    rwa [toAlgHom_self_apply, AlgEquiv.eq_symm_apply, NilLift.qe_mk] at this

/-- The maps `φ_i` of `C.correct y x` differ from those of `C` by the value of `y` at `{i}`. -/
theorem dφ_correct (y : FamTerm (derH N f S) 1) (x : FamTerm (derV N f S) 2) (i : Fin k) :
    dφ hN C (C.correct hN hflat y x) hflat i = y (FormalGlueing.singletonIndex i) :=
  (C.exists_correct_φ hN hflat y i).choose_spec.choose_spec

/-- The chart changes `γ_{ab}` of `C.correct y x` differ from those of `C` by the value of `x` at
`{a, b}`. -/
theorem dγ_correct (y : FamTerm (derH N f S) 1) (x : FamTerm (derV N f S) 2) (a b : Fin k)
    (hab : a < b) :
    dγ hN C (C.correct hN hflat y x) a b hab = x ⟨{a, b}, Finset.card_pair (ne_of_lt hab)⟩ :=
  (C.exists_correct_γ hN x a b hab).choose_spec.choose_spec

omit hW in
/-- The map `C₀.φc a s ha` sends `thetaE z` in the `a`-chart to `thetaE` of the image of `z` under
`Sl f S s → Sl f S s ⊗[S] Sh f S`. -/
theorem φc_thetaE (C₀ : ChartData N f S H e W) (a : Fin k) (s : Finset (Fin k)) (ha : a ∈ s)
    (z : Sl f S s ⊗[R] N) :
    C₀.φc a s ha (thetaE N hN ((Wc N f S W a s ha).qe N).symm z) =
      thetaE N hN (lamXHEquiv N f S H e s)
        ((IsScalarTower.toAlgHom R (Sl f S s) (Sl f S s ⊗[S] Sh f S)).toLinearMap.rTensor N z) :=
  (thetaE_rTensor N hN _ _ _ _ (C₀.redMap_φc_qe a s ha) z).symm

omit hW in
/-- The chart change `C₀.γc a b hab s ha hb` sends `thetaE z` in the `b`-chart to `thetaE z` in the
`a`-chart. -/
theorem γc_thetaE (C₀ : ChartData N f S H e W) (a b : Fin k) (hab : a < b) (s : Finset (Fin k))
    (ha : a ∈ s) (hb : b ∈ s) (z : Sl f S s ⊗[R] N) :
    C₀.γc a b hab s ha hb (thetaE N hN ((Wc N f S W b s hb).qe N).symm z) =
      thetaE N hN ((Wc N f S W a s ha).qe N).symm z := by
  simpa only [AlgHom.toLinearMap_id, LinearMap.rTensor_id, LinearMap.id_apply] using
    (thetaE_rTensor N hN ((Wc N f S W b s hb).qe N).symm ((Wc N f S W a s ha).qe N).symm
      (AlgHom.id R (Sl f S s)) (C₀.γc a b hab s ha hb) (C₀.redMap_γc_qe a b hab s ha hb) z).symm

open FormalGlueing in
/-- After the correction, the defect `D` vanishes. -/
theorem DH_correct_eq_zero (y : FamTerm (derH N f S) 1) (x : FamTerm (derV N f S) 2)
    (hy : ∀ T, cechDiff (derH N f S) (derιH N f S) 1 y T - derT N f S T.1 (x T) =
      C.Dfam hN hflat T)
    (a b : Fin k) (hab : a < b) :
    (C.correct hN hflat y x).DH hN hflat a b hab {a, b} (mem_pair_left a b)
      (mem_pair_right a b) = 0 := by
  set C' := C.correct hN hflat y x
  have := flat_Hl f H hflat {a, b} ⟨a, mem_pair_left a b⟩
  ext v
  apply thetaE_injective N hN (lamXHEquiv N f S H e {a, b})
  rw [Derivation.zero_apply, map_zero]
  obtain ⟨w, hw⟩ := (Wc N f S W b {a, b} (mem_pair_right a b)).surj (algebraMap S _ v)
  let T : {s : Finset (Fin k) // s.card = 2} := ⟨{a, b}, Finset.card_pair (ne_of_lt hab)⟩
  have hT := hy T
  rw [cechDiff_one_apply (derH N f S) (derιH N f S) y T hab rfl (singletonIndex a)
      (singletonIndex b) rfl rfl (by simp [T]) (by simp [T]),
    C.Dfam_eq hN hflat T hab rfl (mem_pair_left a b) (mem_pair_right a b)] at hT
  have e1 := congrArg
    (fun D : derH N f S {a, b} ↦ thetaE N hN (lamXHEquiv N f S H e {a, b}) (D v)) hT
  simp only [Derivation.sub_apply, map_sub] at e1
  have hw' : (Wc N f S W a {a, b} (mem_pair_left a b)).ψ
      (C'.γc a b hab {a, b} (mem_pair_left a b) (mem_pair_right a b) w) = algebraMap S _ v :=
    (C'.psi_γc a b hab {a, b} _ _ w).trans hw
  have h1 := φc_sub hN C C' hflat a {a, b} (mem_pair_left a b) v _ hw'
  have h2 := φc_sub hN C C' hflat b {a, b} (mem_pair_right a b) v w hw
  have h3 := congrArg (C.φc a {a, b} (mem_pair_left a b))
    (γc_sub hN C C' a b hab {a, b} (mem_pair_left a b) (mem_pair_right a b) v w hw)
  rw [map_sub, φc_thetaE hN C a {a, b} (mem_pair_left a b), dγ_correct, derιV_refl] at h3
  rw [dφ_correct] at h1 h2
  have h4 := C.thetaE_DH hN hflat a b hab {a, b} (mem_pair_left a b) (mem_pair_right a b) v w hw
  rw [C'.thetaE_DH hN hflat a b hab {a, b} (mem_pair_left a b) (mem_pair_right a b) v w hw]
  rw [derT_apply] at e1
  linear_combination h1 - h2 + h3 - h4 - e1

open FormalGlueing in
/-- After the correction, the defect `E` vanishes. -/
theorem EV_correct_eq_zero (y : FamTerm (derH N f S) 1) (x : FamTerm (derV N f S) 2)
    (hx : ∀ T, cechDiff (derV N f S) (derιV N f S) 2 x T = -C.Efam hN T)
    (a b c : Fin k) (hab : a < b) (hbc : b < c) :
    (C.correct hN hflat y x).EV hN a b c hab hbc {a, b, c} (by simp) (by simp) (by simp) = 0 := by
  set C' := C.correct hN hflat y x
  have ha : a ∈ ({a, b, c} : Finset (Fin k)) := by simp
  have hb : b ∈ ({a, b, c} : Finset (Fin k)) := by simp
  have hc : c ∈ ({a, b, c} : Finset (Fin k)) := by simp
  have hac := hab.trans hbc
  ext v
  apply thetaE_injective N hN ((Wc N f S W a {a, b, c} ha).qe N).symm
  rw [Derivation.zero_apply, map_zero]
  obtain ⟨w, hw⟩ := (Wc N f S W c {a, b, c} hc).surj (algebraMap S _ v)
  let T : {s : Finset (Fin k) // s.card = 3} := ⟨{a, b, c}, card_triple_of_lt hab hbc⟩
  have hT := hx T
  rw [cechDiff_two_apply (derV N f S) (derιV N f S) x T hab hbc rfl
      ⟨{b, c}, Finset.card_pair (ne_of_lt hbc)⟩ ⟨{a, c}, Finset.card_pair (ne_of_lt hac)⟩
      ⟨{a, b}, Finset.card_pair (ne_of_lt hab)⟩ rfl rfl rfl (pair_subset_of_mem hb hc)
      (pair_subset_of_mem ha hc) (pair_subset_of_mem ha hb),
    C.Efam_eq hN T hab hbc rfl ha hb hc] at hT
  have e1 := congrArg (fun D : derV N f S {a, b, c} ↦
    thetaE N hN ((Wc N f S W a {a, b, c} ha).qe N).symm (D v)) hT
  simp only [Derivation.add_apply, Derivation.sub_apply, Derivation.neg_apply, map_add, map_sub,
    map_neg] at e1
  have hwb : (Wc N f S W b {a, b, c} hb).ψ (C.γc b c hbc {a, b, c} hb hc w) = algebraMap S _ v :=
    (C.psi_γc b c hbc _ hb hc w).trans hw
  have g1 := γc_sub hN C C' b c hbc {a, b, c} hb hc v w hw
  have g2 := γc_sub hN C C' a b hab {a, b, c} ha hb v _ hwb
  have g3 := γc_sub hN C C' a c hac {a, b, c} ha hc v w hw
  have g4 := congrArg (C'.γc a b hab {a, b, c} ha hb) g1
  rw [map_sub, γc_thetaE hN C' a b hab {a, b, c} ha hb] at g4
  rw [dγ_correct] at g1 g2 g3 g4
  have h4 := C.thetaE_EV hN a b c hab hbc {a, b, c} ha hb hc v w hw
  rw [C'.thetaE_EV hN a b c hab hbc {a, b, c} ha hb hc v w hw]
  linear_combination g4 + g2 - g3 - h4 + e1

include C hN hflat in
/-- **Compatible charts exist.** There is a choice of charts whose chart changes satisfy the
cocycle condition on triples and are compatible with the maps to the `H_s` on pairs. -/
theorem exists_compatible [Module.FinitePresentation S Ω[S⁄R]] [IsNoetherianRing S] :
    ∃ C' : ChartData N f S H e W,
      (∀ (a b : Fin k) (hab : a < b),
        (C'.φc a {a, b} (mem_pair_left a b)).comp
            (C'.γc a b hab {a, b} (mem_pair_left a b) (mem_pair_right a b)) =
          C'.φc b {a, b} (mem_pair_right a b)) ∧
      (∀ (a b c : Fin k) (hab : a < b) (hbc : b < c),
        (C'.γc a b hab {a, b, c} (by simp) (by simp)).comp
            (C'.γc b c hbc {a, b, c} (by simp) (by simp)) =
          C'.γc a c (hab.trans hbc) {a, b, c} (by simp) (by simp)) := by
  obtain ⟨y, x, hy, hx⟩ := exists_family_correction N f S (C.Dfam hN hflat) (C.Efam hN)
    (C.cechDiff_Dfam hN hflat) (C.cechDiff_Efam hN)
  refine ⟨C.correct hN hflat y x, fun a b hab ↦ ?_, fun a b c hab hbc ↦ ?_⟩
  · have := flat_Hl f H hflat {a, b} ⟨a, mem_pair_left a b⟩
    exact eq_of_defect_eq_zero N hN f S _ _ _ _ (isUnit_Hl f H {a, b}) _ _ _ _
      (C.DH_correct_eq_zero hN hflat y x hy a b hab)
  · exact eq_of_defect_eq_zero N hN f S _ _ _ _
      (isUnit_Wc N f S W a (le_refl _) (by simp)) _ _ _ _
      (C.EV_correct_eq_zero hN hflat y x hx a b c hab hbc)

end ChartData

end Corrected

end Rig.SquareZeroLift

end
