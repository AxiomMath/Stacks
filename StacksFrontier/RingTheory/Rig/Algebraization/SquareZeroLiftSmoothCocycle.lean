module

public import StacksFrontier.RingTheory.Rig.Algebraization.SquareZeroLiftSmoothDatum
public import StacksFrontier.RingTheory.Rig.Algebraization.SquareZeroLiftSmoothCech

/-!
# The Čech cocycle of a choice of charts

In the setting of `StacksFrontier.RingTheory.Rig.Algebraization.SquareZeroLiftSmoothDatum`, a
choice of maps `φ_i : W_{i,{i}} → H_{f i}` lifting `χ` and of chart changes
`γ_{ij} : W_{j,{i,j}} → W_{i,{i,j}}` (`i < j`) lifting the identity of `S_{f_i f_j}` has two
defects: on a pair `i < j` the derivation `D_{ij}` measuring `φ_i γ_{ij} - φ_j`, and on a triple
`i < j < l` the derivation `E_{ijl}` measuring `γ_{ij} γ_{jl} - γ_{il}`. This file shows that
`dD = E ⊗ 1` and `dE = 0`.
-/

@[expose] public section

namespace Rig.SquareZeroLift

open TensorProduct

universe u

variable {R : Type u} [CommRing R] (N : Ideal R) (hN : N ^ 2 = ⊥)
variable {k : ℕ} (f : Fin k → R)
variable (S : Type u) [CommRing S] [Algebra R S]
variable (H : Type u) [CommRing H] [Algebra R H]
variable (e : (H ⧸ N.map (algebraMap R H)) ≃ₐ[R] Sh f S)
variable (W : ∀ i : Fin k, NilLift R N (Sl f S {i}))

/-- If `a ∈ s` and `b ∈ s`, then `{a, b} ⊆ s`. -/
theorem pair_subset_of_mem {a b : Fin k} {s : Finset (Fin k)} (ha : a ∈ s) (hb : b ∈ s) :
    ({a, b} : Finset (Fin k)) ⊆ s :=
  Finset.insert_subset_iff.mpr ⟨ha, Finset.singleton_subset_iff.mpr hb⟩

/-- `i ∈ {i, j}`. -/
theorem mem_pair_left (i j : Fin k) : i ∈ ({i, j} : Finset (Fin k)) := by simp

/-- `j ∈ {i, j}`. -/
theorem mem_pair_right (i j : Fin k) : j ∈ ({i, j} : Finset (Fin k)) := by simp

/-- A choice of charts for the smooth square-zero lifting step. -/
structure ChartData where
  /-- The maps `φ_i : W_{i,{i}} → H_{f i}`. -/
  φ : ∀ i, (Wc N f S W i {i} (Finset.mem_singleton_self i)).carrier →ₐ[R] Hl f H {i}
  hφ : ∀ i v, Ideal.Quotient.mk _ (φ i v) =
    chi N f S H e {i} ((Wc N f S W i {i} (Finset.mem_singleton_self i)).ψ v)
  /-- The chart changes `γ_{ij} : W_{j,{i,j}} → W_{i,{i,j}}`. -/
  γ : ∀ i j, i < j → (Wc N f S W j {i, j} (mem_pair_right i j)).carrier →ₐ[R]
    (Wc N f S W i {i, j} (mem_pair_left i j)).carrier
  hγ : ∀ i j h v, (Wc N f S W i {i, j} (mem_pair_left i j)).ψ (γ i j h v) =
    (Wc N f S W j {i, j} (mem_pair_right i j)).ψ v

variable {N f S H e W}

namespace ChartData

variable (C : ChartData N f S H e W)

/-- The map `φ_{i,s} : W_{i,s} → H_s`. -/
noncomputable def φc (i : Fin k) (s : Finset (Fin k)) (hi : i ∈ s) :
    (Wc N f S W i s hi).carrier →ₐ[R] Hl f H s :=
  locMapH N f S H W (Finset.singleton_subset_iff.mpr hi) (Finset.mem_singleton_self i) (C.φ i)

/-- The chart change `γ_{ij,s} : W_{j,s} → W_{i,s}`. -/
noncomputable def γc (i j : Fin k) (h : i < j) (s : Finset (Fin k)) (hi : i ∈ s) (hj : j ∈ s) :
    (Wc N f S W j s hj).carrier →ₐ[R] (Wc N f S W i s hi).carrier :=
  locMap N f S W (pair_subset_of_mem hi hj) (mem_pair_left i j) (mem_pair_right i j) (C.γ i j h)

/-- The reduction of `φ_{i,s}` modulo `N` is `χ` composed with the structure map of `W_{i,s}`. -/
theorem mk_φc (i : Fin k) (s : Finset (Fin k)) (hi : i ∈ s) (v : (Wc N f S W i s hi).carrier) :
    Ideal.Quotient.mk _ (C.φc i s hi v) = chi N f S H e s ((Wc N f S W i s hi).ψ v) :=
  mk_locMapH N f S H e W _ _ _ (C.hφ i) v

/-- The chart change `γ_{ij,s}` is compatible with the structure maps of `W_{j,s}` and
`W_{i,s}`. -/
theorem psi_γc (i j : Fin k) (h : i < j) (s : Finset (Fin k)) (hi : i ∈ s) (hj : j ∈ s)
    (v : (Wc N f S W j s hj).carrier) :
    (Wc N f S W i s hi).ψ (C.γc i j h s hi hj v) = (Wc N f S W j s hj).ψ v :=
  psi_locMap N f S W _ _ _ _ (C.hγ i j h) v

end ChartData

/-! ### The reduction conditions -/

/-- The scalar-tower map `S_s → S_s` is the identity. -/
theorem toAlgHom_self_apply {s : Finset (Fin k)} (x : Sl f S s) :
    IsScalarTower.toAlgHom R (Sl f S s) (Sl f S s) x = x := rfl

/-- The scalar-tower map `S_s → S_s ⊗[S] S^∧` sends `x` to `x ⊗ 1`. -/
theorem toAlgHom_tensor_apply {s : Finset (Fin k)} (x : Sl f S s) :
    IsScalarTower.toAlgHom R (Sl f S s) (Sl f S s ⊗[S] Sh f S) x = x ⊗ₜ 1 := rfl

/-- A map `a : W_{j,s} → W_{i,s}` compatible with the structure maps reduces modulo `N` to the
identity of `S_s`, read through the isomorphisms `W_{•,s} / N ≃ S_s`. -/
theorem reductionV {i j : Fin k} {s : Finset (Fin k)} (hi : i ∈ s) (hj : j ∈ s)
    (a : (Wc N f S W j s hj).carrier →ₐ[R] (Wc N f S W i s hi).carrier)
    (ha : ∀ w, (Wc N f S W i s hi).ψ (a w) = (Wc N f S W j s hj).ψ w) (w) :
    Ideal.Quotient.mk _ (a w) = ((Wc N f S W i s hi).qe N).symm
      (IsScalarTower.toAlgHom R (Sl f S s) (Sl f S s) ((Wc N f S W j s hj).ψ w)) := by
  rw [toAlgHom_self_apply, AlgEquiv.eq_symm_apply, NilLift.qe_mk, ha]

/-- A map `φ : W_{j,s} → H_s` lifting `χ` reduces modulo `N` to the map
`S_s → S_s ⊗[S] S^∧`, `x ↦ x ⊗ 1`, read through `lamXHEquiv`. -/
theorem reductionH {j : Fin k} {s : Finset (Fin k)} (hj : j ∈ s)
    (φ : (Wc N f S W j s hj).carrier →ₐ[R] Hl f H s)
    (hφ : ∀ w, Ideal.Quotient.mk _ (φ w) = chi N f S H e s ((Wc N f S W j s hj).ψ w)) (w) :
    Ideal.Quotient.mk _ (φ w) = lamXHEquiv N f S H e s
      (IsScalarTower.toAlgHom R (Sl f S s) (Sl f S s ⊗[S] Sh f S) ((Wc N f S W j s hj).ψ w)) := by
  rw [toAlgHom_tensor_apply, lamXHEquiv_apply, lamXH_tmul, map_one, mul_one, hφ]

/-! ### The defects -/

namespace ChartData

variable (C : ChartData N f S H e W)
variable (hflat : ∀ i, Module.Flat R (Localization.Away (algebraMap R H (f i))))
variable [hW : ∀ i, Module.Flat R (W i).carrier]

omit hW in
/-- The composite `φ_{a,s} γ_{ab,s}` reduces modulo `N` to `χ` composed with the structure map of
`W_{b,s}`. -/
theorem mk_φc_γc (a b : Fin k) (hab : a < b) (s : Finset (Fin k)) (ha : a ∈ s) (hb : b ∈ s) (w) :
    Ideal.Quotient.mk _ ((C.φc a s ha).comp (C.γc a b hab s ha hb) w) =
      chi N f S H e s ((Wc N f S W b s hb).ψ w) :=
  (C.mk_φc a s _ _).trans (congrArg (chi N f S H e s) (C.psi_γc a b hab s ha hb w))

/-- The defect `D_{ab}` of `φ_a γ_{ab}` and `φ_b` at the level `s ⊇ {a, b}`. -/
noncomputable def DH (a b : Fin k) (hab : a < b) (s : Finset (Fin k)) (ha : a ∈ s) (hb : b ∈ s) :
    derH N f S s :=
  haveI := flat_Hl f H hflat s ⟨a, ha⟩
  defect N hN f S (lamXHEquiv N f S H e s) (Wc N f S W b s hb)
    (IsScalarTower.toAlgHom R (Sl f S s) (Sl f S s ⊗[S] Sh f S))
    (algebraMap_toAlgHom_algebraMap f S)
    ((C.φc a s ha).comp (C.γc a b hab s ha hb)) (C.φc b s hb)
    (reductionH hb _ (C.mk_φc_γc a b hab s ha hb))
    (reductionH hb _ (C.mk_φc b s hb))

omit hW in
/-- Under `thetaE`, the value of `D_{ab}` at `v` is `φ_a(γ_{ab}(w)) - φ_b(w)` for any `w` lifting
the image of `v`. -/
theorem thetaE_DH (a b : Fin k) (hab : a < b) (s : Finset (Fin k)) (ha : a ∈ s) (hb : b ∈ s)
    (v : S) (w : (Wc N f S W b s hb).carrier)
    (hw : (Wc N f S W b s hb).ψ w = algebraMap S _ v) :
    thetaE N hN (lamXHEquiv N f S H e s) (C.DH hN hflat a b hab s ha hb v) =
      C.φc a s ha (C.γc a b hab s ha hb w) - C.φc b s hb w := by
  have := flat_Hl f H hflat s ⟨a, ha⟩
  exact thetaE_defect N hN f S _ _ _ _ _ _ _ _ v w hw

/-- The defect `E_{abc}` of `γ_{ab} γ_{bc}` and `γ_{ac}` at the level `s ⊇ {a, b, c}`. -/
noncomputable def EV (a b c : Fin k) (hab : a < b) (hbc : b < c) (s : Finset (Fin k))
    (ha : a ∈ s) (hb : b ∈ s) (hc : c ∈ s) : derV N f S s :=
  defect N hN f S ((Wc N f S W a s ha).qe N).symm (Wc N f S W c s hc)
    (IsScalarTower.toAlgHom R (Sl f S s) (Sl f S s)) (algebraMap_toAlgHom_algebraMap f S)
    ((C.γc a b hab s ha hb).comp (C.γc b c hbc s hb hc)) (C.γc a c (hab.trans hbc) s ha hc)
    (reductionV _ _ _ fun w ↦ (C.psi_γc a b hab s ha hb _).trans (C.psi_γc b c hbc s hb hc w))
    (reductionV _ _ _ fun w ↦ C.psi_γc a c (hab.trans hbc) s ha hc w)

/-- Under `thetaE`, the value of `E_{abc}` at `v` is `γ_{ab}(γ_{bc}(w)) - γ_{ac}(w)` for any `w`
lifting the image of `v`. -/
theorem thetaE_EV (a b c : Fin k) (hab : a < b) (hbc : b < c) (s : Finset (Fin k))
    (ha : a ∈ s) (hb : b ∈ s) (hc : c ∈ s) (v : S) (w : (Wc N f S W c s hc).carrier)
    (hw : (Wc N f S W c s hc).ψ w = algebraMap S _ v) :
    thetaE N hN ((Wc N f S W a s ha).qe N).symm (C.EV hN a b c hab hbc s ha hb hc v) =
      C.γc a b hab s ha hb (C.γc b c hbc s hb hc w) - C.γc a c (hab.trans hbc) s ha hc w :=
  thetaE_defect N hN f S _ _ _ _ _ _ _ _ v w hw

end ChartData

/-! ### Localization of the defects -/

variable (f S) in
/-- The localization `S_s → S_t` as an `S`-algebra map. -/
noncomputable def locSS {s t : Finset (Fin k)} (h : s ⊆ t) : Sl f S s →ₐ[S] Sl f S t :=
  IsLocalization.Away.liftAlgHom (algebraMap R S (rs f s)) (f := Algebra.ofId S (Sl f S t))
    (IsLocalization.Away.isUnit_of_dvd _ (map_dvd _ (rs_dvd f h)))

variable (f S) in
/-- `locSS` agrees with the localization map `locS`. -/
theorem locSS_apply {s t : Finset (Fin k)} (h : s ⊆ t) (x : Sl f S s) :
    locSS f S h x = locS f S h x := rfl

variable (f S) in
/-- The localization `S_s ⊗[S] S^∧ → S_t ⊗[S] S^∧`. -/
noncomputable def locXH {s t : Finset (Fin k)} (h : s ⊆ t) :
    Sl f S s ⊗[S] Sh f S →ₐ[R] Sl f S t ⊗[S] Sh f S :=
  (Algebra.TensorProduct.map (locSS f S h) (AlgHom.id S (Sh f S))).restrictScalars R

variable (f S) in
/-- `locXH` sends `x ⊗ y` to `locS x ⊗ y`. -/
theorem locXH_tmul {s t : Finset (Fin k)} (h : s ⊆ t) (x : Sl f S s) (y : Sh f S) :
    locXH f S h (x ⊗ₜ y) = locS f S h x ⊗ₜ y := rfl

/-- The restriction `derιH` of a derivation `D` is `D` followed by `locXH ⊗ N`. -/
theorem derιH_apply {s t : Finset (Fin k)} (h : s ⊆ t) (D : derH N f S s) (v : S) :
    derιH N f S h D v = (locXH f S h).toLinearMap.rTensor N (D v) := by
  show AlgebraTensorModule.rTensor R N ((locSL f S h).rTensor (Sh f S)) (D v) = _
  induction D v using TensorProduct.induction_on with
  | zero => simp
  | tmul p n =>
    rw [AlgebraTensorModule.rTensor_tmul, LinearMap.rTensor_tmul]
    congr 1
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/-- Reduction modulo `N` is functorial: `redMap N β' ∘ redMap N β = redMap N (β' ∘ β)`. -/
theorem redMap_comp {B₁ B₂ B₃ : Type*} [CommRing B₁] [Algebra R B₁] [CommRing B₂] [Algebra R B₂]
    [CommRing B₃] [Algebra R B₃] (β : B₁ →ₐ[R] B₂) (β' : B₂ →ₐ[R] B₃) (x) :
    redMap N β' (redMap N β x) = redMap N (β'.comp β) x := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

/-- The reduction of the localization `H_s → H_t` carries `lamH` at level `s` to `lamH` at
level `t`. -/
theorem redMap_locH_lamH {s t : Finset (Fin k)} (h : s ⊆ t) (y : Sh f S) :
    redMap N ((locH f H h).restrictScalars R) (lamH N f S H e s y) = lamH N f S H e t y := by
  simp only [lamH, redH, AlgHom.comp_apply, redMap_comp, locH_comp_toAlgHom]

/-- The reduction of the localization `H_s → H_t` corresponds, under `lamXHEquiv`, to
`locXH : S_s ⊗[S] S^∧ → S_t ⊗[S] S^∧`. -/
theorem redMap_locH_lamXH {s t : Finset (Fin k)} (h : s ⊆ t) (z : Sl f S s ⊗[S] Sh f S) :
    redMap N ((locH f H h).restrictScalars R) (lamXHEquiv N f S H e s z) =
      lamXHEquiv N f S H e t (locXH f S h z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
    rw [lamXHEquiv_apply, lamXHEquiv_apply, lamXH_tmul, locXH_tmul, lamXH_tmul, map_mul,
      redMap_locH_lamH]
    congr 1
    exact AlgHom.congr_fun (redMap_locH_chi N f S H e h) x
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

/-- The inverse of `NilLift.qe` sends `ψ v` to the class of `v`. -/
private theorem qe_symm_psi {C : Type u} [CommRing C] [Algebra R C] (L : NilLift R N C)
    (v : L.carrier) : (L.qe N).symm (L.ψ v) = Ideal.Quotient.mk _ v :=
  (AlgEquiv.symm_apply_eq _).mpr (L.qe_mk N v).symm

/-- The reduction of the restriction `W_{i,s} → W_{i,t}` corresponds, under the isomorphisms
`W_{i,•} / N ≃ S_•`, to the localization `S_s → S_t`. -/
theorem redMap_resW_qe {i : Fin k} {s t : Finset (Fin k)} (h : s ⊆ t) (hi : i ∈ s)
    (x : Sl f S s) :
    redMap N (resW N f S W i h hi) (((Wc N f S W i s hi).qe N).symm x) =
      ((Wc N f S W i t (h hi)).qe N).symm (locS f S h x) := by
  obtain ⟨v, rfl⟩ := (Wc N f S W i s hi).surj x
  rw [qe_symm_psi, redMap_mk, AlgEquiv.eq_symm_apply, NilLift.qe_mk, psi_resW]

namespace ChartData

variable (C : ChartData N f S H e W)
variable (hflat : ∀ i, Module.Flat R (Localization.Away (algebraMap R H (f i))))
variable [hW : ∀ i, Module.Flat R (W i).carrier]

omit hW in
/-- The maps `φ_{a,s}` and `φ_{a,t}` commute with the restrictions `W_{a,s} → W_{a,t}` and
`H_s → H_t`. -/
theorem φc_resW (a : Fin k) {s t : Finset (Fin k)} (h : s ⊆ t) (ha : a ∈ s)
    (v : (Wc N f S W a s ha).carrier) :
    C.φc a t (h ha) (resW N f S W a h ha v) = locH f H h (C.φc a s ha v) := by
  rw [φc, ← locMapH_locMapH N f S H W (Finset.singleton_subset_iff.mpr ha)
    (Finset.mem_singleton_self a) h, locMapH_resW]
  rfl

omit hW in
/-- The chart changes `γ_{ab,s}` and `γ_{ab,t}` commute with the restrictions from level `s` to
level `t`. -/
theorem γc_resW (a b : Fin k) (hab : a < b) {s t : Finset (Fin k)} (h : s ⊆ t)
    (ha : a ∈ s) (hb : b ∈ s) (v : (Wc N f S W b s hb).carrier) :
    C.γc a b hab t (h ha) (h hb) (resW N f S W b h hb v) =
      resW N f S W a h ha (C.γc a b hab s ha hb v) := by
  rw [γc, ← locMap_locMap N f S W (pair_subset_of_mem ha hb) (mem_pair_left a b)
    (mem_pair_right a b) h, locMap_resW]
  rfl

omit hW in
/-- The restriction of the defect `D_{ab}` from level `s` to level `t ⊇ s` is `D_{ab}` at
level `t`. -/
theorem DH_loc (a b : Fin k) (hab : a < b) {s t : Finset (Fin k)} (h : s ⊆ t)
    (ha : a ∈ s) (hb : b ∈ s) :
    derιH N f S h (C.DH hN hflat a b hab s ha hb) = C.DH hN hflat a b hab t (h ha) (h hb) := by
  have := flat_Hl f H hflat t ⟨a, h ha⟩
  refine Derivation.ext fun v ↦ ?_
  apply thetaE_injective N hN (lamXHEquiv N f S H e t)
  obtain ⟨w, hw⟩ := (Wc N f S W b s hb).surj (algebraMap S _ v)
  rewrite [derιH_apply, thetaE_rTensor N hN (lamXHEquiv N f S H e s) (lamXHEquiv N f S H e t)
      (locXH f S h) ((locH f H h).restrictScalars R) (redMap_locH_lamXH h),
    C.thetaE_DH hN hflat a b hab s ha hb v w hw,
    C.thetaE_DH hN hflat a b hab t (h ha) (h hb) v (resW N f S W b h hb w)
      ((psi_resW N f S W b h hb w).trans (by rw [hw, locS_algebraMap])),
    C.γc_resW a b hab h ha hb, C.φc_resW a h ha, C.φc_resW b h hb, AlgHom.restrictScalars_apply,
    map_sub]
  rfl

/-- The restriction of the defect `E_{abc}` from level `s` to level `t ⊇ s` is `E_{abc}` at
level `t`. -/
theorem EV_loc (a b c : Fin k) (hab : a < b) (hbc : b < c) {s t : Finset (Fin k)} (h : s ⊆ t)
    (ha : a ∈ s) (hb : b ∈ s) (hc : c ∈ s) :
    derιV N f S h (C.EV hN a b c hab hbc s ha hb hc) =
      C.EV hN a b c hab hbc t (h ha) (h hb) (h hc) := by
  refine Derivation.ext fun v ↦ ?_
  apply thetaE_injective N hN ((Wc N f S W a t (h ha)).qe N).symm
  obtain ⟨w, hw⟩ := (Wc N f S W c s hc).surj (algebraMap S _ v)
  rewrite [derιV_apply, thetaE_rTensor N hN ((Wc N f S W a s ha).qe N).symm
      ((Wc N f S W a t (h ha)).qe N).symm (locS f S h) (resW N f S W a h ha)
      (redMap_resW_qe h ha),
    C.thetaE_EV hN a b c hab hbc s ha hb hc v w hw,
    C.thetaE_EV hN a b c hab hbc t (h ha) (h hb) (h hc) v (resW N f S W c h hc w)
      ((psi_resW N f S W c h hc w).trans (by rw [hw, locS_algebraMap])),
    C.γc_resW b c hbc h hb hc, C.γc_resW a b hab h ha hb, C.γc_resW a c (hab.trans hbc) h ha hc,
    map_sub]
  rfl

end ChartData

/-! ### The Čech differential in degree three -/

section CechThree

variable {r : ℕ} (X : Finset (Fin r) → Type*) [∀ s, AddCommGroup (X s)]
  (ι : ∀ {s t : Finset (Fin r)}, s ⊆ t → X s →+ X t)

open FormalGlueing Cech in
/-- The Čech differential in degree three, on a quadruple `{i, j, l, m}` with `i < j < l < m`. -/
theorem cechDiff_three_apply (x : FamTerm X 3)
    (T : {s : Finset (Fin r) // s.card = 4}) {i j l m : Fin r} (hij : i < j) (hjl : j < l)
    (hlm : l < m) (hT : T.1 = {i, j, l, m}) (u₁ u₂ u₃ u₄ : {s : Finset (Fin r) // s.card = 3})
    (h₁ : u₁.1 = {j, l, m}) (h₂ : u₂.1 = {i, l, m}) (h₃ : u₃.1 = {i, j, m})
    (h₄ : u₄.1 = {i, j, l})
    (hs₁ : u₁.1 ⊆ T.1) (hs₂ : u₂.1 ⊆ T.1) (hs₃ : u₃.1 ⊆ T.1) (hs₄ : u₄.1 ⊆ T.1) :
    cechDiff X ι 3 x T = ι hs₁ (x u₁) - ι hs₂ (x u₂) + ι hs₃ (x u₃) - ι hs₄ (x u₄) := by
  obtain ⟨T, hT4⟩ := T
  simp only at hT
  subst hT
  let a : ({i, j, l, m} : Finset (Fin r)) := ⟨i, by simp⟩
  let b : ({i, j, l, m} : Finset (Fin r)) := ⟨j, by simp⟩
  let c : ({i, j, l, m} : Finset (Fin r)) := ⟨l, by simp⟩
  let d : ({i, j, l, m} : Finset (Fin r)) := ⟨m, by simp⟩
  have hab : a ≠ b := fun h ↦ hij.ne (congrArg Subtype.val h)
  have hac : a ≠ c := fun h ↦ (hij.trans hjl).ne (congrArg Subtype.val h)
  have had : a ≠ d := fun h ↦ ((hij.trans hjl).trans hlm).ne (congrArg Subtype.val h)
  have hbc : b ≠ c := fun h ↦ hjl.ne (congrArg Subtype.val h)
  have hbd : b ≠ d := fun h ↦ (hjl.trans hlm).ne (congrArg Subtype.val h)
  have hcd : c ≠ d := fun h ↦ hlm.ne (congrArg Subtype.val h)
  have hTa : ({i, j, l, m} : Finset (Fin r)).attach = {a, b, c, d} := by
    ext k
    simp only [Finset.mem_attach, Finset.mem_insert, Finset.mem_singleton, true_iff]
    rcases k with ⟨k, hk⟩
    rcases (show k = i ∨ k = j ∨ k = l ∨ k = m by simpa using hk) with h | h | h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Or.inl (Subtype.ext h))
    · exact Or.inr (Or.inr (Or.inl (Subtype.ext h)))
    · exact Or.inr (Or.inr (Or.inr (Subtype.ext h)))
  have hsi : cechSign ({i, j, l, m} : Finset (Fin r)) i = 1 := by
    have : ({i, j, l, m} : Finset (Fin r)).filter (· < i) = ∅ := by ext k; simp; omega
    simp [cechSign, this]
  have hsj : cechSign ({i, j, l, m} : Finset (Fin r)) j = -1 := by
    have : ({i, j, l, m} : Finset (Fin r)).filter (· < j) = {i} := by ext k; simp; omega
    simp [cechSign, this]
  have hsl : cechSign ({i, j, l, m} : Finset (Fin r)) l = 1 := by
    have : ({i, j, l, m} : Finset (Fin r)).filter (· < l) = {i, j} := by ext k; simp; omega
    simp [cechSign, this, Finset.card_pair (ne_of_lt hij)]
  have hsm : cechSign ({i, j, l, m} : Finset (Fin r)) m = -1 := by
    have : ({i, j, l, m} : Finset (Fin r)).filter (· < m) = {i, j, l} := by ext k; simp; omega
    have hcard : ({i, j, l} : Finset (Fin r)).card = 3 := by
      rw [Finset.card_insert_of_notMem (by simp; omega), Finset.card_pair (ne_of_lt hjl)]
    simp [cechSign, this, hcard]
  rw [cechDiff_apply, hTa, Finset.sum_insert (by simp [hab, hac, had]),
    Finset.sum_insert (by simp [hbc, hbd]), Finset.sum_pair hcd]
  have ea : (eraseIndex 3 ⟨{i, j, l, m}, hT4⟩ a).1 = u₁.1 := by
    rw [h₁]; ext k; simp [eraseIndex, a]; omega
  have eb : (eraseIndex 3 ⟨{i, j, l, m}, hT4⟩ b).1 = u₂.1 := by
    rw [h₂]; ext k; simp [eraseIndex, b]; omega
  have ec : (eraseIndex 3 ⟨{i, j, l, m}, hT4⟩ c).1 = u₃.1 := by
    rw [h₃]; ext k; simp [eraseIndex, c]; omega
  have ed : (eraseIndex 3 ⟨{i, j, l, m}, hT4⟩ d).1 = u₄.1 := by
    rw [h₄]; ext k; simp [eraseIndex, d]; omega
  rw [component_congr X ι x (Subtype.ext ea) _ hs₁, component_congr X ι x (Subtype.ext eb) _ hs₂,
    component_congr X ι x (Subtype.ext ec) _ hs₃, component_congr X ι x (Subtype.ext ed) _ hs₄]
  simp only [a, b, c, d, hsi, hsj, hsl, hsm, one_smul, neg_smul]
  abel

/-- A four-element subset of `Fin r` is `{i, j, l, m}` for some `i < j < l < m`. -/
theorem exists_sorted_quadruple (T : {s : Finset (Fin r) // s.card = 4}) :
    ∃ i j l m : Fin r, i < j ∧ j < l ∧ l < m ∧ T.1 = {i, j, l, m} := by
  let g := T.1.orderEmbOfFin T.2
  refine ⟨g 0, g 1, g 2, g 3, g.strictMono (by decide), g.strictMono (by decide),
    g.strictMono (by decide), ?_⟩
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    obtain ⟨y, rfl⟩ : x ∈ Set.range g := by rw [Finset.range_orderEmbOfFin]; exact hx
    fin_cases y <;> simp
  · rw [T.2]
    exact Finset.card_le_four

end CechThree

/-! ### The cocycle identities -/

/-- The map `derT` sends a derivation `D` to `D` followed by `(x ↦ x ⊗ 1) ⊗ N`. -/
theorem derT_apply (s : Finset (Fin k)) (D : derV N f S s) (v : S) :
    derT N f S s D v =
      (IsScalarTower.toAlgHom R (Sl f S s) (Sl f S s ⊗[S] Sh f S)).toLinearMap.rTensor N (D v) := by
  show AlgebraTensorModule.rTensor R N _ (D v) = _
  induction D v using TensorProduct.induction_on with
  | zero => simp
  | tmul x n => rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy]

namespace ChartData

variable (C : ChartData N f S H e W)
variable (hflat : ∀ i, Module.Flat R (Localization.Away (algebraMap R H (f i))))
variable [hW : ∀ i, Module.Flat R (W i).carrier]

omit hW in
/-- The reduction of `φ_{a,s}` corresponds, under `W_{a,s} / N ≃ S_s` and `lamXHEquiv`, to the
map `S_s → S_s ⊗[S] S^∧`, `x ↦ x ⊗ 1`. -/
theorem redMap_φc_qe (a : Fin k) (s : Finset (Fin k)) (ha : a ∈ s) (x : Sl f S s) :
    redMap N (C.φc a s ha) (((Wc N f S W a s ha).qe N).symm x) =
      lamXHEquiv N f S H e s (IsScalarTower.toAlgHom R (Sl f S s) (Sl f S s ⊗[S] Sh f S) x) := by
  obtain ⟨w, rfl⟩ := (Wc N f S W a s ha).surj x
  rw [qe_symm_psi, redMap_mk, ← reductionH ha _ (C.mk_φc a s ha)]

omit hW in
/-- The reduction of `γ_{ab,s}` corresponds, under the isomorphisms `W_{•,s} / N ≃ S_s`, to the
identity of `S_s`. -/
theorem redMap_γc_qe (a b : Fin k) (hab : a < b) (s : Finset (Fin k)) (ha : a ∈ s) (hb : b ∈ s)
    (x : Sl f S s) :
    redMap N (C.γc a b hab s ha hb) (((Wc N f S W b s hb).qe N).symm x) =
      ((Wc N f S W a s ha).qe N).symm (AlgHom.id R (Sl f S s) x) := by
  obtain ⟨w, rfl⟩ := (Wc N f S W b s hb).surj x
  rw [qe_symm_psi, redMap_mk, AlgHom.id_apply, AlgEquiv.eq_symm_apply, NilLift.qe_mk, psi_γc]

/-- In an additive commutative group, `x₁ - x₂ - (x₃ - x₂) + (x₄ - x₁) = x₄ - x₃`. -/
theorem abel_three {G : Type*} [AddCommGroup G] (x₁ x₂ x₃ x₄ : G) :
    x₁ - x₂ - (x₃ - x₂) + (x₄ - x₁) = x₄ - x₃ := by abel

/-- In an additive commutative group, `x₁ - x₂ - (x₃ - x₄) + (x₂ - x₄) - (x₁ - x₃) = 0`. -/
theorem abel_four {G : Type*} [AddCommGroup G] (x₁ x₂ x₃ x₄ : G) :
    x₁ - x₂ - (x₃ - x₄) + (x₂ - x₄) - (x₁ - x₃) = 0 := by abel

/-- `dD = E ⊗ 1` at a level containing a triple `a < b < c`. -/
theorem DH_cocycle (a b c : Fin k) (hab : a < b) (hbc : b < c) (s : Finset (Fin k))
    (ha : a ∈ s) (hb : b ∈ s) (hc : c ∈ s) :
    C.DH hN hflat b c hbc s hb hc - C.DH hN hflat a c (hab.trans hbc) s ha hc +
        C.DH hN hflat a b hab s ha hb =
      derT N f S s (C.EV hN a b c hab hbc s ha hb hc) := by
  have := flat_Hl f H hflat s ⟨a, ha⟩
  refine Derivation.ext fun v ↦ ?_
  apply thetaE_injective N hN (lamXHEquiv N f S H e s)
  obtain ⟨w, hw⟩ := (Wc N f S W c s hc).surj (algebraMap S _ v)
  have hw' : (Wc N f S W b s hb).ψ (C.γc b c hbc s hb hc w) = algebraMap S _ v :=
    (C.psi_γc b c hbc s hb hc w).trans hw
  rewrite [Derivation.add_apply, Derivation.sub_apply, map_add, map_sub,
    C.thetaE_DH hN hflat b c hbc s hb hc v w hw,
    C.thetaE_DH hN hflat a c (hab.trans hbc) s ha hc v w hw,
    C.thetaE_DH hN hflat a b hab s ha hb v _ hw', derT_apply,
    thetaE_rTensor N hN ((Wc N f S W a s ha).qe N).symm (lamXHEquiv N f S H e s)
      (IsScalarTower.toAlgHom R (Sl f S s) (Sl f S s ⊗[S] Sh f S)) (C.φc a s ha)
      (C.redMap_φc_qe a s ha),
    C.thetaE_EV hN a b c hab hbc s ha hb hc v w hw, map_sub]
  exact abel_three _ _ _ _

/-- `dE = 0` at a level containing a quadruple `a < b < c < d`. -/
theorem EV_cocycle (a b c d : Fin k) (hab : a < b) (hbc : b < c) (hcd : c < d)
    (s : Finset (Fin k)) (ha : a ∈ s) (hb : b ∈ s) (hc : c ∈ s) (hd : d ∈ s) :
    C.EV hN b c d hbc hcd s hb hc hd - C.EV hN a c d (hab.trans hbc) hcd s ha hc hd +
      C.EV hN a b d hab (hbc.trans hcd) s ha hb hd - C.EV hN a b c hab hbc s ha hb hc = 0 := by
  refine Derivation.ext fun v ↦ ?_
  apply thetaE_injective N hN ((Wc N f S W a s ha).qe N).symm
  obtain ⟨w, hw⟩ := (Wc N f S W d s hd).surj (algebraMap S _ v)
  have hw' : (Wc N f S W c s hc).ψ (C.γc c d hcd s hc hd w) = algebraMap S _ v :=
    (C.psi_γc c d hcd s hc hd w).trans hw
  have hnat : ∀ z, thetaE N hN ((Wc N f S W a s ha).qe N).symm z =
      C.γc a b hab s ha hb (thetaE N hN ((Wc N f S W b s hb).qe N).symm z) := by
    intro z
    have := thetaE_rTensor N hN ((Wc N f S W b s hb).qe N).symm ((Wc N f S W a s ha).qe N).symm
      (AlgHom.id R (Sl f S s)) (C.γc a b hab s ha hb) (C.redMap_γc_qe a b hab s ha hb) z
    rwa [AlgHom.toLinearMap_id, LinearMap.rTensor_id, LinearMap.id_apply] at this
  rewrite [Derivation.sub_apply, Derivation.add_apply, Derivation.sub_apply, map_sub, map_add,
    map_sub, hnat (C.EV hN b c d hbc hcd s hb hc hd v),
    C.thetaE_EV hN b c d hbc hcd s hb hc hd v w hw,
    C.thetaE_EV hN a c d (hab.trans hbc) hcd s ha hc hd v w hw,
    C.thetaE_EV hN a b d hab (hbc.trans hcd) s ha hb hd v w hw,
    C.thetaE_EV hN a b c hab hbc s ha hb hc v _ hw', map_sub, Derivation.zero_apply, map_zero]
  exact abel_four _ _ _ _

end ChartData

end Rig.SquareZeroLift

end
