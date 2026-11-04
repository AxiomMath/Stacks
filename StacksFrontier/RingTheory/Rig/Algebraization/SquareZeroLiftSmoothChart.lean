module

public import StacksFrontier.RingTheory.Rig.Algebraization.SquareZeroLiftCompare
public import StacksFrontier.RingTheory.Rig.Algebraization.SquareZeroLiftSmoothDerivation

/-!
# Charts and defects for the smooth square-zero lifting step

In the setting of `StacksFrontier.RingTheory.Rig.Algebraization.SquareZeroLiftData`, the smooth
version of the square-zero lifting step glues lifts `W_i` of the localizations `S_{f i}` which,
unlike in the étale case, are not unique: two of them over `S_s` are related by many
isomorphisms, and two algebra maps between them lifting the identity differ by a derivation. This
file sets up the bookkeeping for those differences.

* `Rig.SquareZeroLift.NilLift.locAway`: a lift of `S_t`, localized at `r_s` for `t ⊆ s`, is a
  lift of `S_s`.
* `Rig.SquareZeroLift.thetaL`: for a lift `L` of `S_s`, the multiplication map
  `S_s ⊗[R] N → L`, an isomorphism onto `N L` when `L` is flat over `R`.
* `Rig.SquareZeroLift.defectL`: two algebra maps `L → L'` between lifts of `S_s` that both lift
  the identity of `S_s` differ by a derivation `S → S_s ⊗[R] N`, read through `thetaL`.
-/

@[expose] public section

namespace Rig.SquareZeroLift

open TensorProduct

universe u

variable {R : Type u} [CommRing R] (N : Ideal R) (hN : N ^ 2 = ⊥)
variable {k : ℕ} (f : Fin k → R)
variable (S : Type u) [CommRing S] [Algebra R S]

/-! ### Localizing a lift -/

section LocAway

/-- For `t ⊆ s`, the image of `r_s` under `locS ∘ ψ : L → S_s` is a unit. -/
theorem isUnit_locS_comp_psi {t s : Finset (Fin k)} (L : NilLift R N (Sl f S t)) (h : t ⊆ s) :
    IsUnit (((locS f S h).comp L.ψ) (algebraMap R L.carrier (rs f s))) := by
  rw [AlgHom.commutes, IsScalarTower.algebraMap_apply R S (Sl f S s)]
  exact IsLocalization.Away.algebraMap_isUnit _

/-- The reduction map of a localized lift. -/
noncomputable def locAwayψ {t s : Finset (Fin k)} (L : NilLift R N (Sl f S t)) (h : t ⊆ s) :
    Localization.Away (algebraMap R L.carrier (rs f s)) →ₐ[R] Sl f S s :=
  IsLocalization.Away.liftAlgHom (algebraMap R L.carrier (rs f s))
    (isUnit_locS_comp_psi N f S L h)

/-- On the image of `L`, the reduction map of the localized lift is `locS ∘ ψ`. -/
@[simp]
theorem locAwayψ_algebraMap {t s : Finset (Fin k)} (L : NilLift R N (Sl f S t)) (h : t ⊆ s)
    (v : L.carrier) :
    locAwayψ N f S L h (algebraMap L.carrier _ v) = locS f S h (L.ψ v) := by
  simp [locAwayψ, IsLocalization.Away.liftAlgHom_apply, IsLocalization.Away.lift_eq]

/-- A section of `S_t` killed by `locS` is killed by a power of `r_s` already in `S_t`. -/
theorem exists_pow_smul_eq_zero_of_locS {t s : Finset (Fin k)} (h : t ⊆ s) (x : Sl f S t)
    (hx : locS f S h x = 0) : ∃ m : ℕ, rs f s ^ m • x = 0 := by
  obtain ⟨n, c, hc⟩ := IsLocalization.Away.surj (algebraMap R S (rs f t)) x
  have h1 : algebraMap S (Sl f S s) c = 0 := by
    rw [← locS_algebraMap f S h, ← hc, map_mul, hx, zero_mul]
  rw [← map_zero (algebraMap S (Sl f S s))] at h1
  obtain ⟨m, hm⟩ := IsLocalization.Away.exists_of_eq (algebraMap R S (rs f s)) h1
  rw [mul_zero] at hm
  refine ⟨m, ?_⟩
  set u := algebraMap S (Sl f S t) (algebraMap R S (rs f t))
  have hu : IsUnit u := IsLocalization.Away.algebraMap_isUnit _
  have h3 : u ^ n * (rs f s ^ m • x) = 0 := by
    rw [Algebra.smul_def, IsScalarTower.algebraMap_apply R S (Sl f S t)]
    calc u ^ n * (algebraMap S (Sl f S t) (algebraMap R S (rs f s ^ m)) * x)
        = algebraMap S (Sl f S t) (algebraMap R S (rs f s ^ m)) * (x * u ^ n) := by ring
      _ = algebraMap S (Sl f S t) (algebraMap R S (rs f s) ^ m * c) := by
          rw [hc, map_pow, map_mul]
      _ = 0 := by rw [hm, map_zero]
  exact (hu.pow n).mul_left_cancel (h3.trans (mul_zero _).symm)

/-- The reduction map `L_{r_s} → S_s` of a localized lift is surjective. -/
theorem locAwayψ_surjective {t s : Finset (Fin k)} (L : NilLift R N (Sl f S t)) (h : t ⊆ s) :
    Function.Surjective (locAwayψ N f S L h) := by
  intro y
  obtain ⟨n, c, hc⟩ := IsLocalization.Away.surj (algebraMap R S (rs f s)) y
  obtain ⟨v, hv⟩ := L.surj (algebraMap S (Sl f S t) c)
  let r : Submonoid.powers (algebraMap R L.carrier (rs f s)) :=
    ⟨algebraMap R L.carrier (rs f s) ^ n, n, rfl⟩
  refine ⟨IsLocalization.mk' _ v r, ?_⟩
  have ha : IsUnit (algebraMap R (Sl f S s) (rs f s)) := by
    rw [IsScalarTower.algebraMap_apply R S (Sl f S s)]
    exact IsLocalization.Away.algebraMap_isUnit _
  set a := algebraMap R (Sl f S s) (rs f s)
  have h1 : locAwayψ N f S L h (IsLocalization.mk' _ v r) * a ^ n = y * a ^ n := by
    have h2 := congrArg (locAwayψ N f S L h)
      (IsLocalization.mk'_spec (Localization.Away (algebraMap R L.carrier (rs f s))) v r)
    rw [map_mul, locAwayψ_algebraMap, locAwayψ_algebraMap, hv, locS_algebraMap] at h2
    have h4 : L.ψ (r : L.carrier) = algebraMap R (Sl f S t) (rs f s) ^ n := by
      simp [r]
    rw [h4, map_pow, AlgHom.commutes] at h2
    rw [h2, ← hc]
    simp only [a, IsScalarTower.algebraMap_apply R S (Sl f S s)]
  exact (ha.pow n).mul_right_cancel h1

/-- The kernel of the reduction map `L_{r_s} → S_s` is the ideal `N L_{r_s}`. -/
theorem locAwayψ_ker {t s : Finset (Fin k)} (L : NilLift R N (Sl f S t)) (h : t ⊆ s) :
    RingHom.ker (locAwayψ N f S L h).toRingHom =
      N.map (algebraMap R (Localization.Away (algebraMap R L.carrier (rs f s)))) := by
  set Lr := Localization.Away (algebraMap R L.carrier (rs f s))
  apply le_antisymm
  · intro y hy
    obtain ⟨⟨v, ⟨_, n, rfl⟩⟩, rfl⟩ :=
      IsLocalization.mk'_surjective (Submonoid.powers (algebraMap R L.carrier (rs f s))) y
    set r : Submonoid.powers (algebraMap R L.carrier (rs f s)) :=
      ⟨algebraMap R L.carrier (rs f s) ^ n, n, rfl⟩
    show IsLocalization.mk' Lr v r ∈ _
    have hspec := IsLocalization.mk'_spec
      (M := Submonoid.powers (algebraMap R L.carrier (rs f s))) Lr v r
    have hy0 : locAwayψ N f S L h (IsLocalization.mk' Lr v r) = 0 := hy
    have hv0 : locS f S h (L.ψ v) = 0 := by
      rw [← locAwayψ_algebraMap N f S L h, ← hspec, map_mul, hy0, zero_mul]
    obtain ⟨m, hm⟩ := exists_pow_smul_eq_zero_of_locS f S h _ hv0
    have hmem : rs f s ^ m • v ∈ N.map (algebraMap R L.carrier) := by
      rw [← L.ker, RingHom.mem_ker]
      show L.ψ (rs f s ^ m • v) = 0
      rw [map_smul, hm]
    have hmem' : algebraMap L.carrier Lr (rs f s ^ m • v) ∈ N.map (algebraMap R Lr) := by
      have := Ideal.mem_map_of_mem (algebraMap L.carrier Lr) hmem
      rwa [Ideal.map_map, ← IsScalarTower.algebraMap_eq] at this
    have hunit : IsUnit (algebraMap R Lr (rs f s ^ (m + n))) := by
      have := (IsLocalization.Away.algebraMap_isUnit (S := Lr)
        (algebraMap R L.carrier (rs f s))).pow (m + n)
      rwa [← map_pow, ← map_pow, ← IsScalarTower.algebraMap_apply] at this
    have heq : IsLocalization.mk' Lr v r * algebraMap R Lr (rs f s ^ (m + n)) =
        algebraMap L.carrier Lr (rs f s ^ m • v) := by
      rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply, ← hspec, pow_add, map_mul]
      simp only [r, IsScalarTower.algebraMap_apply R L.carrier Lr, map_pow]
      ring
    have : IsLocalization.mk' Lr v r =
        algebraMap L.carrier Lr (rs f s ^ m • v) * ((hunit.unit⁻¹ : Lrˣ) : Lr) := by
      rw [← heq, mul_assoc, IsUnit.mul_val_inv, mul_one]
    rw [this]
    exact Ideal.mul_mem_right _ _ hmem'
  · rw [Ideal.map_le_iff_le_comap]
    intro n hn
    rw [Ideal.mem_comap, RingHom.mem_ker]
    show locAwayψ N f S L h (algebraMap R _ n) = 0
    have hn' : L.ψ (algebraMap R L.carrier n) = 0 := by
      have : algebraMap R L.carrier n ∈ RingHom.ker L.ψ.toRingHom := by
        rw [L.ker]
        exact Ideal.mem_map_of_mem _ hn
      exact this
    rw [AlgHom.commutes, ← AlgHom.commutes (locS f S h), ← AlgHom.commutes L.ψ, hn', map_zero]

/-- **A lift of `S_t`, localized at `r_s` for `t ⊆ s`, is a lift of `S_s`.** -/
noncomputable abbrev NilLift.locAway {t s : Finset (Fin k)} (L : NilLift R N (Sl f S t))
    (h : t ⊆ s) : NilLift R N (Sl f S s) where
  carrier := Localization.Away (algebraMap R L.carrier (rs f s))
  ψ := locAwayψ N f S L h
  surj := locAwayψ_surjective N f S L h
  ker := locAwayψ_ker N f S L h

end LocAway

/-! ### Multiplication by `N` through an identification of the reduction -/

section ThetaE

variable {X : Type u} [CommRing X] [Algebra R X]
  {B : Type u} [CommRing B] [Algebra R B]
  (lam : X ≃ₐ[R] B ⧸ N.map (algebraMap R B))

/-- The multiplication `X ⊗[R] N → B`, `x ⊗ n ↦ n · b` for a lift `b` of `lam x`. -/
noncomputable def thetaE : X ⊗[R] N →ₗ[R] B := theta N hN lam.toAlgHom

/-- `thetaE` sends `x ⊗ n` to `n • b` for any `b : B` reducing to `lam x`. -/
theorem thetaE_tmul (x : X) (n : N) (b : B) (hb : Ideal.Quotient.mk _ b = lam x) :
    thetaE N hN lam (x ⊗ₜ n) = (n : R) • b :=
  theta_tmul N hN _ x n b hb

/-- `thetaE` takes values in the ideal `N B`. -/
theorem thetaE_mem (z : X ⊗[R] N) : thetaE N hN lam z ∈ N.map (algebraMap R B) :=
  theta_mem N hN _ z

/-- `thetaE` is injective when `B` is flat over `R`. -/
theorem thetaE_injective [Module.Flat R B] : Function.Injective (thetaE N hN lam) := by
  have h : thetaE N hN lam = multT N hN B ∘ₗ (lam.toLinearEquiv.rTensor N).toLinearMap := rfl
  rw [h, LinearMap.coe_comp]
  exact (multT_injective N hN B).comp (lam.toLinearEquiv.rTensor N).injective

/-- Every element of `N B` lies in the image of `thetaE`. -/
theorem exists_thetaE_eq (y : B) (hy : y ∈ N.map (algebraMap R B)) :
    ∃ z, thetaE N hN lam z = y := by
  obtain ⟨z, rfl⟩ := exists_multT_eq N hN B y hy
  refine ⟨(lam.toLinearEquiv.rTensor N).symm z, ?_⟩
  show multT N hN B ((lam.toLinearEquiv.rTensor N) ((lam.toLinearEquiv.rTensor N).symm z)) = _
  rw [LinearEquiv.apply_symm_apply]

/-- `thetaE (x • z) = b * thetaE z` for any `b : B` reducing to `lam x`. -/
theorem thetaE_smul_mul (x : X) (z : X ⊗[R] N) (b : B) (hb : Ideal.Quotient.mk _ b = lam x) :
    thetaE N hN lam (x • z) = b * thetaE N hN lam z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x' n =>
    rw [TensorProduct.smul_tmul', smul_eq_mul]
    exact theta_mul N hN lam.toAlgHom x x' n b hb
  | add y z hy hz => rw [smul_add, map_add, map_add, hy, hz, mul_add]

/-- `thetaE (c • z) = b * thetaE z` for `c : S` and any `b : B` reducing to the image of `c` under
`lam`. -/
theorem thetaE_smul [Algebra S X] [IsScalarTower R S X] (c : S) (z : X ⊗[R] N) (b : B)
    (hb : Ideal.Quotient.mk _ b = lam (algebraMap S X c)) :
    thetaE N hN lam (c • z) = b * thetaE N hN lam z := by
  rw [← thetaE_smul_mul N hN lam _ z b hb, algebraMap_smul]

end ThetaE

/-! ### The defect of two lifts of the same map -/

section Defect

/-- Elements with the same image under the reduction map of a lift differ by an element of `N L`. -/
private theorem sub_mem_map_of_psi_eq {T : Type u} [CommRing T] [Algebra R T] (L : NilLift R N T)
    {w w' : L.carrier} (h : L.ψ w = L.ψ w') : w - w' ∈ N.map (algebraMap R L.carrier) := by
  rw [← L.ker, RingHom.mem_ker]
  show L.ψ (w - w') = 0
  rw [map_sub, h, sub_self]

variable {X : Type u} [CommRing X] [Algebra R X] [Algebra S X] [IsScalarTower R S X]
  {B : Type u} [CommRing B] [Algebra R B] [Module.Flat R B]
  (lam : X ≃ₐ[R] B ⧸ N.map (algebraMap R B))
  {s : Finset (Fin k)} (L : NilLift R N (Sl f S s)) (μ : Sl f S s →ₐ[R] X)

omit [Module.Flat R B] in
include hN in
/-- Two algebra maps `L → B` lifting the same map `L → B ⧸ N B` differ on `N L` by zero. -/
theorem sub_eq_zero_of_mem (a b : L.carrier →ₐ[R] B)
    (hab : ∀ w, Ideal.Quotient.mk (N.map (algebraMap R B)) (a w) =
      Ideal.Quotient.mk (N.map (algebraMap R B)) (b w))
    {x : L.carrier} (hx : x ∈ N.map (algebraMap R L.carrier)) : a x - b x = 0 := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨n, hn, rfl⟩ := hy
    rw [AlgHom.commutes, AlgHom.commutes, sub_self]
  | zero => simp
  | add x y _ _ hx hy =>
    rw [map_add, map_add, add_sub_add_comm, hx, hy, add_zero]
  | smul c x hxN hx =>
    rw [smul_eq_mul, map_mul, map_mul]
    have hc : a c - b c ∈ N.map (algebraMap R B) := Ideal.Quotient.eq.mp (hab c)
    have hx' : a x ∈ N.map (algebraMap R B) := by
      have key : (N.map (algebraMap R L.carrier)).map a.toRingHom = N.map (algebraMap R B) := by
        rw [Ideal.map_map]
        congr 1
        exact RingHom.ext a.commutes
      rw [← key]
      exact Ideal.mem_map_of_mem a.toRingHom (show x ∈ N.map (algebraMap R L.carrier) from hxN)
    have h0 : (a c - b c) * a x = 0 := by
      have : (a c - b c) * a x ∈ N.map (algebraMap R B) ^ 2 := by
        rw [pow_two]
        exact Ideal.mul_mem_mul hc hx'
      rwa [map_sq_eq_bot N hN B] at this
    calc a c * a x - b c * b x = (a c - b c) * a x + b c * (a x - b x) := by ring
      _ = 0 := by rw [h0, hx, mul_zero, add_zero]

variable (hμ : ∀ v : S, μ (algebraMap S _ v) = algebraMap S X v)

/-- The difference of two lifts of the same map only depends on the reduction of the argument. -/
private theorem sub_eq_sub_of_psi_eq_aux (hN : N ^ 2 = ⊥) {B' : Type u} [CommRing B']
    [Algebra R B'] (a b : L.carrier →ₐ[R] B')
    (hab : ∀ w, Ideal.Quotient.mk (N.map (algebraMap R B')) (a w) =
      Ideal.Quotient.mk (N.map (algebraMap R B')) (b w))
    {w w' : L.carrier} (h : L.ψ w = L.ψ w') : a w - b w = a w' - b w' := by
  have h0 := sub_eq_zero_of_mem N hN f S L a b hab (sub_mem_map_of_psi_eq N L h)
  rw [map_sub, map_sub] at h0
  linear_combination h0

/-- The value of the defect at `v ∈ S`: the preimage under `thetaE` of `a w - b w` for any lift
`w` of `v`. -/
noncomputable def defectFun (a b : L.carrier →ₐ[R] B)
    (ha : ∀ w, Ideal.Quotient.mk _ (a w) = lam (μ (L.ψ w)))
    (hb : ∀ w, Ideal.Quotient.mk _ (b w) = lam (μ (L.ψ w))) (v : S) : X ⊗[R] N :=
  Classical.choose (exists_thetaE_eq N hN lam
    (a (Classical.choose (L.surj (algebraMap S _ v))) -
      b (Classical.choose (L.surj (algebraMap S _ v))))
    (Ideal.Quotient.eq.mp ((ha _).trans (hb _).symm)))

omit [Algebra S X] [IsScalarTower R S X] [Module.Flat R B] in
/-- `thetaE` sends `defectFun a b v` to `a w - b w` for any `w : L` with `ψ w` the image of `v`. -/
theorem thetaE_defectFun (a b : L.carrier →ₐ[R] B)
    (ha : ∀ w, Ideal.Quotient.mk _ (a w) = lam (μ (L.ψ w)))
    (hb : ∀ w, Ideal.Quotient.mk _ (b w) = lam (μ (L.ψ w))) (v : S) (w : L.carrier)
    (hw : L.ψ w = algebraMap S _ v) :
    thetaE N hN lam (defectFun N hN f S lam L μ a b ha hb v) = a w - b w := by
  rw [defectFun, Classical.choose_spec (exists_thetaE_eq N hN lam _
    (Ideal.Quotient.eq.mp ((ha _).trans (hb _).symm)))]
  set w₀ := Classical.choose (L.surj (algebraMap S _ v))
  have hw₀ : L.ψ w₀ = algebraMap S _ v := Classical.choose_spec (L.surj (algebraMap S _ v))
  linear_combination sub_eq_sub_of_psi_eq_aux N f S L hN a b
    (fun w ↦ (ha w).trans (hb w).symm) (hw₀.trans hw.symm)

/-- **The defect of two lifts.** If `a, b : L → B` both reduce to `lam ∘ μ ∘ ψ`, their difference
is a derivation of `S` with values in `X ⊗[R] N`, read through `thetaE`. -/
noncomputable def defect (a b : L.carrier →ₐ[R] B)
    (ha : ∀ w, Ideal.Quotient.mk _ (a w) = lam (μ (L.ψ w)))
    (hb : ∀ w, Ideal.Quotient.mk _ (b w) = lam (μ (L.ψ w))) :
    Derivation R S (X ⊗[R] N) where
  toFun := defectFun N hN f S lam L μ a b ha hb
  map_add' v v' := by
    obtain ⟨w, hw⟩ := L.surj (algebraMap S _ v)
    obtain ⟨w', hw'⟩ := L.surj (algebraMap S _ v')
    apply thetaE_injective N hN lam
    rw [map_add, thetaE_defectFun N hN f S lam L μ a b ha hb v w hw,
      thetaE_defectFun N hN f S lam L μ a b ha hb v' w' hw',
      thetaE_defectFun N hN f S lam L μ a b ha hb (v + v') (w + w')
        (by rw [map_add, hw, hw', map_add]), map_add, map_add]
    ring
  map_smul' c v := by
    obtain ⟨w, hw⟩ := L.surj (algebraMap S _ v)
    apply thetaE_injective N hN lam
    rw [map_smul, thetaE_defectFun N hN f S lam L μ a b ha hb v w hw,
      thetaE_defectFun N hN f S lam L μ a b ha hb (c • v) (c • w)
        (by rw [map_smul, hw, Algebra.smul_def, Algebra.smul_def c v, map_mul,
          ← IsScalarTower.algebraMap_apply]), map_smul, map_smul, smul_sub, RingHom.id_apply]
  map_one_eq_zero' := by
    apply thetaE_injective N hN lam
    rw [map_zero]
    change thetaE N hN lam (defectFun N hN f S lam L μ a b ha hb 1) = 0
    rw [thetaE_defectFun N hN f S lam L μ a b ha hb 1 1 (by rw [map_one, map_one]), map_one,
      map_one, sub_self]
  leibniz' v v' := by
    obtain ⟨w, hw⟩ := L.surj (algebraMap S _ v)
    obtain ⟨w', hw'⟩ := L.surj (algebraMap S _ v')
    apply thetaE_injective N hN lam
    change thetaE N hN lam (defectFun N hN f S lam L μ a b ha hb (v * v')) =
      thetaE N hN lam (v • defectFun N hN f S lam L μ a b ha hb v' +
        v' • defectFun N hN f S lam L μ a b ha hb v)
    rw [map_add, thetaE_smul N hN S lam v _ (a w) (by rw [ha, hw, hμ]),
      thetaE_smul N hN S lam v' _ (b w') (by rw [hb, hw', hμ]),
      thetaE_defectFun N hN f S lam L μ a b ha hb v w hw,
      thetaE_defectFun N hN f S lam L μ a b ha hb v' w' hw',
      thetaE_defectFun N hN f S lam L μ a b ha hb (v * v') (w * w')
        (by rw [map_mul, hw, hw', map_mul]), map_mul, map_mul]
    ring

/-- `thetaE` sends `defect a b v` to `a w - b w` for any `w : L` with `ψ w` the image of `v`. -/
theorem thetaE_defect (a b : L.carrier →ₐ[R] B)
    (ha : ∀ w, Ideal.Quotient.mk _ (a w) = lam (μ (L.ψ w)))
    (hb : ∀ w, Ideal.Quotient.mk _ (b w) = lam (μ (L.ψ w))) (v : S) (w : L.carrier)
    (hw : L.ψ w = algebraMap S _ v) :
    thetaE N hN lam (defect N hN f S lam L μ hμ a b ha hb v) = a w - b w :=
  thetaE_defectFun N hN f S lam L μ a b ha hb v w hw

end Defect

/-! ### Calculus of defects -/

section DefectCalculus

variable {X : Type u} [CommRing X] [Algebra R X] [Algebra S X] [IsScalarTower R S X]
  {B : Type u} [CommRing B] [Algebra R B] [Module.Flat R B]
  (lam : X ≃ₐ[R] B ⧸ N.map (algebraMap R B))
  {s : Finset (Fin k)} (L : NilLift R N (Sl f S s)) (μ : Sl f S s →ₐ[R] X)
  (hμ : ∀ v : S, μ (algebraMap S _ v) = algebraMap S X v)

/-- Defects add up along a chain of three lifts. -/
theorem defect_add (a b c : L.carrier →ₐ[R] B)
    (ha : ∀ w, Ideal.Quotient.mk _ (a w) = lam (μ (L.ψ w)))
    (hb : ∀ w, Ideal.Quotient.mk _ (b w) = lam (μ (L.ψ w)))
    (hc : ∀ w, Ideal.Quotient.mk _ (c w) = lam (μ (L.ψ w))) :
    defect N hN f S lam L μ hμ a c ha hc =
      defect N hN f S lam L μ hμ a b ha hb + defect N hN f S lam L μ hμ b c hb hc := by
  ext v
  obtain ⟨w, hw⟩ := L.surj (algebraMap S _ v)
  apply thetaE_injective N hN lam
  rw [Derivation.add_apply, map_add, thetaE_defect N hN f S lam L μ hμ _ _ _ _ v w hw,
    thetaE_defect N hN f S lam L μ hμ _ _ _ _ v w hw,
    thetaE_defect N hN f S lam L μ hμ _ _ _ _ v w hw]
  ring

/-- The defect of a lift with itself is zero. -/
theorem defect_self (a : L.carrier →ₐ[R] B)
    (ha : ∀ w, Ideal.Quotient.mk _ (a w) = lam (μ (L.ψ w))) :
    defect N hN f S lam L μ hμ a a ha ha = 0 := by
  ext v
  obtain ⟨w, hw⟩ := L.surj (algebraMap S _ v)
  apply thetaE_injective N hN lam
  rw [thetaE_defect N hN f S lam L μ hμ _ _ _ _ v w hw, sub_self, Derivation.zero_apply, map_zero]

/-- Exchanging the two lifts negates the defect. -/
theorem defect_swap (a b : L.carrier →ₐ[R] B)
    (ha : ∀ w, Ideal.Quotient.mk _ (a w) = lam (μ (L.ψ w)))
    (hb : ∀ w, Ideal.Quotient.mk _ (b w) = lam (μ (L.ψ w))) :
    defect N hN f S lam L μ hμ b a hb ha = -defect N hN f S lam L μ hμ a b ha hb := by
  rw [eq_neg_iff_add_eq_zero, add_comm, ← defect_add, defect_self]

/-- **Postcomposition.** Composing both lifts with an algebra map `β : B → B'` compatible with
the identifications `lam`, `lam'` through `ν : X → X'` transports the defect along `ν ⊗ N`. -/
theorem defect_comp_left {X' : Type u} [CommRing X'] [Algebra R X'] [Algebra S X']
    [IsScalarTower R S X'] {B' : Type u} [CommRing B'] [Algebra R B'] [Module.Flat R B']
    (lam' : X' ≃ₐ[R] B' ⧸ N.map (algebraMap R B')) (ν : X →ₐ[R] X') (β : B →ₐ[R] B')
    (hν : ∀ x, redMap N β (lam x) = lam' (ν x))
    (hμ' : ∀ v : S, (ν.comp μ) (algebraMap S _ v) = algebraMap S X' v)
    (a b : L.carrier →ₐ[R] B)
    (ha : ∀ w, Ideal.Quotient.mk _ (a w) = lam (μ (L.ψ w)))
    (hb : ∀ w, Ideal.Quotient.mk _ (b w) = lam (μ (L.ψ w)))
    (ha' : ∀ w, Ideal.Quotient.mk _ ((β.comp a) w) = lam' ((ν.comp μ) (L.ψ w)))
    (hb' : ∀ w, Ideal.Quotient.mk _ ((β.comp b) w) = lam' ((ν.comp μ) (L.ψ w))) (v : S) :
    defect N hN f S lam' L (ν.comp μ) hμ' (β.comp a) (β.comp b) ha' hb' v =
      ν.toLinearMap.rTensor N (defect N hN f S lam L μ hμ a b ha hb v) := by
  obtain ⟨w, hw⟩ := L.surj (algebraMap S _ v)
  apply thetaE_injective N hN lam'
  have hnat : ∀ z, thetaE N hN lam' (ν.toLinearMap.rTensor N z) = β (thetaE N hN lam z) := by
    intro z
    rw [thetaE, thetaE, ← theta_comp N hN ν lam'.toAlgHom z]
    exact (theta_naturality N hN β lam.toAlgHom _ (by ext x; exact hν x) z).symm
  rw [hnat, thetaE_defect N hN f S lam' L (ν.comp μ) hμ' _ _ _ _ v w hw,
    thetaE_defect N hN f S lam L μ hμ _ _ _ _ v w hw, map_sub]
  rfl

/-- **Precomposition.** Precomposing both lifts with a map `κ : L₀ → L` of lifts, over a map
`τ : S_{s₀} → S_s` compatible with `S`, does not change the defect. -/
theorem defect_comp_right {s₀ : Finset (Fin k)} (L₀ : NilLift R N (Sl f S s₀))
    (τ : Sl f S s₀ →ₐ[R] Sl f S s) (hτ : ∀ v : S, τ (algebraMap S _ v) = algebraMap S _ v)
    (κ : L₀.carrier →ₐ[R] L.carrier) (hκ : ∀ w, L.ψ (κ w) = τ (L₀.ψ w))
    (hμ' : ∀ v : S, (μ.comp τ) (algebraMap S _ v) = algebraMap S X v)
    (a b : L.carrier →ₐ[R] B)
    (ha : ∀ w, Ideal.Quotient.mk _ (a w) = lam (μ (L.ψ w)))
    (hb : ∀ w, Ideal.Quotient.mk _ (b w) = lam (μ (L.ψ w)))
    (ha' : ∀ w, Ideal.Quotient.mk _ ((a.comp κ) w) = lam ((μ.comp τ) (L₀.ψ w)))
    (hb' : ∀ w, Ideal.Quotient.mk _ ((b.comp κ) w) = lam ((μ.comp τ) (L₀.ψ w))) :
    defect N hN f S lam L₀ (μ.comp τ) hμ' (a.comp κ) (b.comp κ) ha' hb' =
      defect N hN f S lam L μ hμ a b ha hb := by
  ext v
  obtain ⟨w, hw⟩ := L₀.surj (algebraMap S _ v)
  apply thetaE_injective N hN lam
  rw [thetaE_defect N hN f S lam L₀ (μ.comp τ) hμ' _ _ _ _ v w hw,
    thetaE_defect N hN f S lam L μ hμ _ _ _ _ v (κ w) (by rw [hκ, hw, hτ])]
  rfl

/-- **Vanishing.** If the defect of `a` and `b` is zero and `r_s` is invertible in `B`, then
`a = b`. -/
theorem eq_of_defect_eq_zero (hB : IsUnit (algebraMap R B (rs f s)))
    (a b : L.carrier →ₐ[R] B)
    (ha : ∀ w, Ideal.Quotient.mk _ (a w) = lam (μ (L.ψ w)))
    (hb : ∀ w, Ideal.Quotient.mk _ (b w) = lam (μ (L.ψ w)))
    (h : defect N hN f S lam L μ hμ a b ha hb = 0) : a = b := by
  ext w
  obtain ⟨n, c, hc⟩ := IsLocalization.Away.surj (algebraMap R S (rs f s)) (L.ψ w)
  obtain ⟨w', hw'⟩ := L.surj (algebraMap S _ c)
  have h0 : a w' - b w' = 0 := by
    rw [← thetaE_defect N hN f S lam L μ hμ a b ha hb c w' hw', h, Derivation.zero_apply,
      map_zero]
  have hmem := sub_mem_map_of_psi_eq N L (w := w * algebraMap R L.carrier (rs f s ^ n)) (w' := w')
    (by rw [map_mul, AlgHom.commutes, hw', ← hc, map_pow,
      IsScalarTower.algebraMap_apply R S (Sl f S s)])
  have h1 := sub_eq_zero_of_mem N hN f S L a b
    (fun w ↦ (ha w).trans (hb w).symm) hmem
  rw [map_sub, map_sub, map_mul, map_mul, AlgHom.commutes, AlgHom.commutes] at h1
  have h2 : (a w - b w) * algebraMap R B (rs f s ^ n) = 0 := by
    linear_combination h1 + h0
  have hu : IsUnit (algebraMap R B (rs f s ^ n)) := by
    rw [map_pow]
    exact hB.pow n
  exact sub_eq_zero.mp (hu.mul_left_eq_zero.mp h2)

end DefectCalculus

/-! ### Correcting a lift by a derivation -/

section Correct

variable {s : Finset (Fin k)} {X : Type u} [CommRing X] [Algebra R X] [Algebra S X]
  [IsScalarTower R S X] [Algebra (Sl f S s) X] [IsScalarTower R (Sl f S s) X]
  [IsScalarTower S (Sl f S s) X]
  {B : Type u} [CommRing B] [Algebra R B] [Module.Flat R B]
  (lam : X ≃ₐ[R] B ⧸ N.map (algebraMap R B)) (L : NilLift R N (Sl f S s))

omit [IsScalarTower R S X] in
/-- The structure map `S_s → X` sends the image of `v : S` in `S_s` to the image of `v` in `X`. -/
theorem algebraMap_toAlgHom_algebraMap (v : S) :
    (IsScalarTower.toAlgHom R (Sl f S s) X) (algebraMap S _ v) = algebraMap S X v := by
  rw [IsScalarTower.coe_toAlgHom', ← IsScalarTower.algebraMap_apply]

/-- **Every derivation is the defect of a correction.** Given a lift `a : L → B` of
`lam ∘ ψ` and a derivation `δ : S → X ⊗[R] N`, there is another lift `a'` with
`defect a' a = δ`: extend `δ` to `S_s`, push it into `N B` by `thetaE`, and add it to `a`. -/
theorem exists_defect_eq (a : L.carrier →ₐ[R] B)
    (ha : ∀ w, Ideal.Quotient.mk _ (a w) =
      lam ((IsScalarTower.toAlgHom R (Sl f S s) X) (L.ψ w)))
    (δ : Derivation R S (X ⊗[R] N)) :
    ∃ (a' : L.carrier →ₐ[R] B) (ha' : ∀ w, Ideal.Quotient.mk _ (a' w) =
        lam ((IsScalarTower.toAlgHom R (Sl f S s) X) (L.ψ w))),
      defect N hN f S lam L (IsScalarTower.toAlgHom R (Sl f S s) X)
        (algebraMap_toAlgHom_algebraMap f S) a' a ha' ha = δ := by
  obtain ⟨δ', hδ'⟩ := (bijective_compAlgebraMap_of_isLocalization R
    (Submonoid.powers (algebraMap R S (rs f s))) (Sl f S s) (X ⊗[R] N)).2 δ
  let : Algebra L.carrier B := a.toRingHom.toAlgebra
  have : IsScalarTower R L.carrier B := IsScalarTower.of_algebraMap_eq fun r ↦ (a.commutes r).symm
  let I : Ideal B := N.map (algebraMap R B)
  have hsmul : ∀ (w : L.carrier) (z : X ⊗[R] N),
      thetaE N hN lam (L.ψ w • z) = a w * thetaE N hN lam z := by
    intro w z
    rw [← algebraMap_smul X (L.ψ w) z]
    exact thetaE_smul_mul N hN lam _ z (a w) (by rw [ha]; rfl)
  let Δ : Derivation R L.carrier I :=
    { toFun := fun w ↦ ⟨thetaE N hN lam (δ' (L.ψ w)), thetaE_mem N hN lam _⟩
      map_add' := fun w w' ↦ Subtype.ext (by simp only [map_add, Submodule.coe_add])
      map_smul' := fun c w ↦ Subtype.ext (by
        show thetaE N hN lam (δ' (L.ψ (c • w))) = c • thetaE N hN lam (δ' (L.ψ w))
        rw [map_smul, Derivation.map_smul, map_smul])
      map_one_eq_zero' := Subtype.ext (by simp)
      leibniz' := fun w w' ↦ Subtype.ext (by
        show thetaE N hN lam (δ' (L.ψ (w * w'))) =
          a w * thetaE N hN lam (δ' (L.ψ w')) + a w' * thetaE N hN lam (δ' (L.ψ w))
        rw [map_mul, Derivation.leibniz, map_add, hsmul, hsmul]) }
  refine ⟨liftOfDerivationToSquareZero I (map_sq_eq_bot N hN B) Δ, fun w ↦ ?_, ?_⟩
  · rw [liftOfDerivationToSquareZero_apply, map_add,
      Ideal.Quotient.eq_zero_iff_mem.mpr (Δ w).prop, zero_add]
    exact ha w
  · ext v
    obtain ⟨w, hw⟩ := L.surj (algebraMap S _ v)
    apply thetaE_injective N hN lam
    rw [thetaE_defect N hN f S lam L _ _ _ _ _ _ v w hw, liftOfDerivationToSquareZero_apply]
    show thetaE N hN lam (δ' (L.ψ w)) + a w - a w = _
    rw [add_sub_cancel_right, hw, ← hδ']
    rfl

end Correct

/-! ### The identification `S_s ⊗[S] S^∧ ≅ H_s ⧸ N H_s` -/

section HSide

variable (H : Type u) [CommRing H] [Algebra R H]
  (e : (H ⧸ N.map (algebraMap R H)) ≃ₐ[R] Sh f S)

/-- The map `S_s ⊗[S] S^∧ → H_s ⧸ N H_s`, `x ⊗ y ↦ χ(x) λ(y)`. -/
noncomputable def lamXH (s : Finset (Fin k)) :
    Sl f S s ⊗[S] Sh f S →ₐ[R] Hl f H s ⧸ N.map (algebraMap R (Hl f H s)) := by
  letI : Algebra S (Hl f H s ⧸ N.map (algebraMap R (Hl f H s))) :=
    ((lamH N f S H e s).toRingHom.comp (algebraMap S (Sh f S))).toAlgebra
  haveI : IsScalarTower R S (Hl f H s ⧸ N.map (algebraMap R (Hl f H s))) :=
    IsScalarTower.of_algebraMap_eq fun r ↦ by
      change _ = lamH N f S H e s (algebraMap S (Sh f S) (algebraMap R S r))
      rw [← IsScalarTower.algebraMap_apply, AlgHom.commutes]
  let χ : Sl f S s →ₐ[S] Hl f H s ⧸ N.map (algebraMap R (Hl f H s)) :=
    { chi N f S H e s with
      commutes' := fun c ↦ chi_algebraMap N f S H e s c }
  let lamS : Sh f S →ₐ[S] Hl f H s ⧸ N.map (algebraMap R (Hl f H s)) :=
    { lamH N f S H e s with
      commutes' := fun c ↦ rfl }
  exact (Algebra.TensorProduct.productMap χ lamS).restrictScalars R

/-- `lamXH` sends `x ⊗ y` to `chi x * lamH y`. -/
theorem lamXH_tmul (s : Finset (Fin k)) (x : Sl f S s) (y : Sh f S) :
    lamXH N f S H e s (x ⊗ₜ y) = chi N f S H e s x * lamH N f S H e s y := rfl

/-- The `R`-linear map `S^∧ → S_s ⊗[S] S^∧`, `y ↦ 1 ⊗ y`, is a localization at the powers of
`r_s`. -/
theorem isLocalizedModule_includeRight (s : Finset (Fin k)) :
    IsLocalizedModule (Submonoid.powers (rs f s))
      ((TensorProduct.mk S (Sl f S s) (Sh f S) 1).restrictScalars R) := by
  have : IsLocalizedModule (Submonoid.powers (algebraMap R S (rs f s)))
      (TensorProduct.mk S (Sl f S s) (Sh f S) 1) :=
    (isLocalizedModule_iff_isBaseChange (Submonoid.powers (algebraMap R S (rs f s)))
      (Sl f S s) _).mpr (TensorProduct.isBaseChange S (Sh f S) (Sl f S s))
  exact IsLocalizedModule.restrictScalars_powers (rs f s) _

/-- The map `lamXH : S_s ⊗[S] S^∧ → H_s ⧸ N H_s` is bijective. -/
theorem lamXH_bijective (s : Finset (Fin k)) : Function.Bijective (lamXH N f S H e s) := by
  have := isLocalizedModule_includeRight f S s
  have := isLocalizedModule_lamH N f S H e s
  let E := IsLocalizedModule.linearEquiv (Submonoid.powers (rs f s))
    ((TensorProduct.mk S (Sl f S s) (Sh f S) 1).restrictScalars R)
    (lamH N f S H e s).toLinearMap
  have hE : (lamXH N f S H e s).toLinearMap = E.toLinearMap := by
    apply IsLocalizedModule.ext (Submonoid.powers (rs f s))
      ((TensorProduct.mk S (Sl f S s) (Sh f S) 1).restrictScalars R)
      (IsLocalizedModule.map_units (lamH N f S H e s).toLinearMap)
    refine LinearMap.ext fun y ↦ ?_
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe]
    rw [IsLocalizedModule.linearEquiv_apply]
    show lamXH N f S H e s (1 ⊗ₜ y) = _
    rw [lamXH_tmul, map_one, one_mul]
    rfl
  rw [show ⇑(lamXH N f S H e s) = ⇑E from congrArg DFunLike.coe hE]
  exact E.bijective

/-- The identification `S_s ⊗[S] S^∧ ≅ H_s ⧸ N H_s`. -/
noncomputable def lamXHEquiv (s : Finset (Fin k)) :
    Sl f S s ⊗[S] Sh f S ≃ₐ[R] Hl f H s ⧸ N.map (algebraMap R (Hl f H s)) :=
  AlgEquiv.ofBijective (lamXH N f S H e s) (lamXH_bijective N f S H e s)

/-- The equivalence `lamXHEquiv` acts as `lamXH`. -/
@[simp]
theorem lamXHEquiv_apply (s : Finset (Fin k)) (z : Sl f S s ⊗[S] Sh f S) :
    lamXHEquiv N f S H e s z = lamXH N f S H e s z := rfl

end HSide

/-! ### Naturality of `thetaE` -/

/-- For `β : B → B'` compatible with `lam`, `lam'` through `ν : X → X'`, `thetaE` intertwines
`ν ⊗ N` with `β`. -/
theorem thetaE_rTensor {X X' : Type u} [CommRing X] [Algebra R X] [CommRing X'] [Algebra R X']
    {B B' : Type u} [CommRing B] [Algebra R B] [CommRing B'] [Algebra R B']
    (lam : X ≃ₐ[R] B ⧸ N.map (algebraMap R B)) (lam' : X' ≃ₐ[R] B' ⧸ N.map (algebraMap R B'))
    (ν : X →ₐ[R] X') (β : B →ₐ[R] B') (hν : ∀ x, redMap N β (lam x) = lam' (ν x))
    (z : X ⊗[R] N) :
    thetaE N hN lam' (ν.toLinearMap.rTensor N z) = β (thetaE N hN lam z) := by
  rw [thetaE, thetaE, ← theta_comp N hN ν lam'.toAlgHom z]
  exact (theta_naturality N hN β lam.toAlgHom _ (by ext x; exact hν x) z).symm

include hN in
/-- The difference of two lifts of the same map only depends on the reduction of the argument. -/
theorem sub_eq_sub_of_psi_eq {s : Finset (Fin k)} (L : NilLift R N (Sl f S s)) {B : Type u}
    [CommRing B] [Algebra R B] [Module.Flat R B] (a b : L.carrier →ₐ[R] B)
    (hab : ∀ w, Ideal.Quotient.mk (N.map (algebraMap R B)) (a w) =
      Ideal.Quotient.mk (N.map (algebraMap R B)) (b w))
    {w w' : L.carrier} (h : L.ψ w = L.ψ w') : a w - b w = a w' - b w' := by
  exact sub_eq_sub_of_psi_eq_aux N f S L hN a b hab h

end Rig.SquareZeroLift

end
