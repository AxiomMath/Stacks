module

public import StacksFrontier.RingTheory.Rig.Algebraization.SquareZeroLiftSmoothChart
public import StacksFrontier.RingTheory.Rig.Algebraization.SquareZeroGlueDatum

/-!
# The glueing datum of the smooth square-zero lifting step

In the setting of `StacksFrontier.RingTheory.Rig.Algebraization.SquareZeroLiftData`, let `W i` be
lifts of the localizations `S_{f i}` across `R → R ⧸ N` which are formally smooth and flat over
`R`. This file builds from them the charts of a glueing datum
(`Rig.SquareZeroLift.GlueDatum`): the localizations `W_{i,s} = W_i[1/r_s]` for `i ∈ s`, their
restriction maps, maps `φ_{i,s} : W_{i,s} → H_s` lifting `χ`, and chart changes
`γ_{i,j} : W_{j,{i,j}} → W_{i,{i,j}}` lifting the identity of `S_{f_i f_j}`.

## Main definitions

* `Rig.SquareZeroLift.Wc`: the chart `W_{i,s} = W_i[1/r_s]`, a lift of `S_s` for `i ∈ s`.
* `Rig.SquareZeroLift.resW`: the restriction map `W_{i,t} → W_{i,s}` for `t ⊆ s`.
* `Rig.SquareZeroLift.locMap`: the localization `W_{j,s} → W_{i,s}` of a map `W_{j,t} → W_{i,t}`.
* `Rig.SquareZeroLift.locMapH`: the localization `W_{i,s} → H_s` of a map `W_{i,t} → H_t`.
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

/-! ### Charts -/

/-- The chart `W_{i,s} = W_i[1/r_s]`, a lift of `S_s` for `i ∈ s`. -/
noncomputable def Wc (i : Fin k) (s : Finset (Fin k)) (hi : i ∈ s) : NilLift R N (Sl f S s) :=
  (W i).locAway N f S (Finset.singleton_subset_iff.mpr hi)

/-- The carrier of `W_{i,s}` is the localization of `W_i` away from the image of `r_s`. -/
theorem Wc_carrier (i : Fin k) (s : Finset (Fin k)) (hi : i ∈ s) :
    (Wc N f S W i s hi).carrier = Localization.Away (algebraMap R (W i).carrier (rs f s)) := rfl

/-- The chart `W_{i,s}` is a `W_i`-algebra. -/
noncomputable instance algebra_Wc (i : Fin k) (s : Finset (Fin k)) (hi : i ∈ s) :
    Algebra (W i).carrier (Wc N f S W i s hi).carrier :=
  inferInstanceAs (Algebra (W i).carrier (Localization.Away (algebraMap R (W i).carrier (rs f s))))

/-- The algebra structures on `R → W_i → W_{i,s}` form a scalar tower. -/
instance isScalarTower_Wc (i : Fin k) (s : Finset (Fin k)) (hi : i ∈ s) :
    IsScalarTower R (W i).carrier (Wc N f S W i s hi).carrier :=
  inferInstanceAs
    (IsScalarTower R (W i).carrier (Localization.Away (algebraMap R (W i).carrier (rs f s))))

/-- The chart `W_{i,s}` is the localization of `W_i` away from the image of `r_s`. -/
instance isLocalization_Wc (i : Fin k) (s : Finset (Fin k)) (hi : i ∈ s) :
    IsLocalization.Away (algebraMap R (W i).carrier (rs f s)) (Wc N f S W i s hi).carrier :=
  inferInstanceAs
    (IsLocalization.Away (algebraMap R (W i).carrier (rs f s))
      (Localization.Away (algebraMap R (W i).carrier (rs f s))))

/-- If each `W_i` is flat over `R`, then so is each chart `W_{i,s}`. -/
instance flat_Wc [hW : ∀ i, Module.Flat R (W i).carrier] (i : Fin k) (s : Finset (Fin k))
    (hi : i ∈ s) : Module.Flat R (Wc N f S W i s hi).carrier := by
  change Module.Flat R (Localization.Away (algebraMap R (W i).carrier (rs f s)))
  infer_instance

/-- If each `W_i` is formally smooth over `R`, then so is each chart `W_{i,s}`. -/
instance formallySmooth_Wc [hW : ∀ i, Algebra.FormallySmooth R (W i).carrier] (i : Fin k)
    (s : Finset (Fin k)) (hi : i ∈ s) : Algebra.FormallySmooth R (Wc N f S W i s hi).carrier := by
  change Algebra.FormallySmooth R (Localization.Away (algebraMap R (W i).carrier (rs f s)))
  have : Algebra.FormallySmooth (W i).carrier
      (Localization.Away (algebraMap R (W i).carrier (rs f s))) :=
    Algebra.FormallySmooth.of_isLocalization
      (Submonoid.powers (algebraMap R (W i).carrier (rs f s)))
  exact Algebra.FormallySmooth.comp R (W i).carrier _

/-- For `t ⊆ s` and `i ∈ s`, the image of `r_t` in `W_{i,s}` is a unit. -/
theorem isUnit_Wc (i : Fin k) {t s : Finset (Fin k)} (h : t ⊆ s) (hi : i ∈ s) :
    IsUnit (algebraMap R (Wc N f S W i s hi).carrier (rs f t)) := by
  have h1 := IsLocalization.Away.isUnit_of_dvd
    (S := (Wc N f S W i s hi).carrier)
    (algebraMap R (W i).carrier (rs f s)) (map_dvd (algebraMap R (W i).carrier) (rs_dvd f h))
  rwa [← IsScalarTower.algebraMap_apply] at h1

/-- The map `W_i → W_{i,s}`. -/
noncomputable def toWc (i : Fin k) (s : Finset (Fin k)) (hi : i ∈ s) :
    (W i).carrier →ₐ[R] (Wc N f S W i s hi).carrier :=
  IsScalarTower.toAlgHom R (W i).carrier (Wc N f S W i s hi).carrier

/-- The reduction map of `W_{i,s}` composed with `W_i → W_{i,s}` is the reduction map of `W_i`
followed by the localization `S_{f_i} → S_s`. -/
theorem psi_toWc (i : Fin k) (s : Finset (Fin k)) (hi : i ∈ s) (w : (W i).carrier) :
    (Wc N f S W i s hi).ψ (toWc N f S W i s hi w) =
      locS f S (Finset.singleton_subset_iff.mpr hi) ((W i).ψ w) :=
  locAwayψ_algebraMap N f S (W i) _ w

/-- Two algebra maps out of a chart agreeing on `W_i` are equal. -/
theorem Wc_algHom_ext (i : Fin k) (s : Finset (Fin k)) (hi : i ∈ s) {B : Type*} [CommRing B]
    [Algebra R B] {a b : (Wc N f S W i s hi).carrier →ₐ[R] B}
    (h : ∀ w, a (toWc N f S W i s hi w) = b (toWc N f S W i s hi w)) : a = b := by
  have : a.toRingHom = b.toRingHom :=
    IsLocalization.ringHom_ext (Submonoid.powers (algebraMap R (W i).carrier (rs f s)))
      (RingHom.ext h)
  exact AlgHom.toRingHom_injective this

/-- The restriction map `W_{i,t} → W_{i,s}` for `t ⊆ s`. -/
noncomputable def resW (i : Fin k) {t s : Finset (Fin k)} (h : t ⊆ s) (hi : i ∈ t) :
    (Wc N f S W i t hi).carrier →ₐ[R] (Wc N f S W i s (h hi)).carrier :=
  IsLocalization.Away.liftAlgHom (algebraMap R (W i).carrier (rs f t))
    (f := toWc N f S W i s (h hi)) (by rw [AlgHom.commutes]; exact isUnit_Wc N f S W i h (h hi))

/-- The restriction `W_{i,t} → W_{i,s}` is compatible with the maps from `W_i`. -/
theorem resW_toWc (i : Fin k) {t s : Finset (Fin k)} (h : t ⊆ s) (hi : i ∈ t)
    (w : (W i).carrier) :
    resW N f S W i h hi (toWc N f S W i t hi w) = toWc N f S W i s (h hi) w := by
  simp [resW, toWc, IsLocalization.Away.liftAlgHom_apply, IsLocalization.Away.lift_eq]

/-- Restriction maps compose: `W_{i,t} → W_{i,s} → W_{i,w}` is the restriction
`W_{i,t} → W_{i,w}`. -/
theorem resW_resW (i : Fin k) {t s w : Finset (Fin k)} (h : t ⊆ s) (h' : s ⊆ w) (hi : i ∈ t)
    (v : (Wc N f S W i t hi).carrier) :
    resW N f S W i h' (h hi) (resW N f S W i h hi v) = resW N f S W i (h.trans h') hi v := by
  have : (resW N f S W i h' (h hi)).comp (resW N f S W i h hi) = resW N f S W i (h.trans h') hi :=
    Wc_algHom_ext N f S W i t hi fun w ↦ by
      rw [AlgHom.comp_apply, resW_toWc, resW_toWc, resW_toWc]
  exact AlgHom.congr_fun this v

/-- The restriction `W_{i,t} → W_{i,s}` lifts the localization `S_t → S_s`. -/
theorem psi_resW (i : Fin k) {t s : Finset (Fin k)} (h : t ⊆ s) (hi : i ∈ t)
    (v : (Wc N f S W i t hi).carrier) :
    (Wc N f S W i s (h hi)).ψ (resW N f S W i h hi v) = locS f S h ((Wc N f S W i t hi).ψ v) := by
  have : ((Wc N f S W i s (h hi)).ψ.comp (resW N f S W i h hi)) =
      (locS f S h).comp (Wc N f S W i t hi).ψ :=
    Wc_algHom_ext N f S W i t hi fun w ↦ by
      rw [AlgHom.comp_apply, AlgHom.comp_apply, resW_toWc, psi_toWc, psi_toWc, locS_locS]
  exact AlgHom.congr_fun this v

/-! ### Localizing maps between charts -/

section LocMap

variable {i j : Fin k} {t s : Finset (Fin k)} (h : t ⊆ s) (hi : i ∈ t) (hj : j ∈ t)

/-- The localization `W_{j,s} → W_{i,s}` of a map `W_{j,t} → W_{i,t}`, for `t ⊆ s`. -/
noncomputable def locMap (a : (Wc N f S W j t hj).carrier →ₐ[R] (Wc N f S W i t hi).carrier) :
    (Wc N f S W j s (h hj)).carrier →ₐ[R] (Wc N f S W i s (h hi)).carrier :=
  IsLocalization.Away.liftAlgHom (algebraMap R (W j).carrier (rs f s))
    (f := ((resW N f S W i h hi).comp a).comp (toWc N f S W j t hj))
    (by rw [AlgHom.commutes]; exact isUnit_Wc N f S W i (le_refl s) (h hi))

/-- On the image of `W_j`, the localization of `a` is `a` followed by restriction to `s`. -/
theorem locMap_toWc (a : (Wc N f S W j t hj).carrier →ₐ[R] (Wc N f S W i t hi).carrier)
    (w : (W j).carrier) :
    locMap N f S W h hi hj a (toWc N f S W j s (h hj) w) =
      resW N f S W i h hi (a (toWc N f S W j t hj w)) := by
  simp [locMap, toWc, IsLocalization.Away.liftAlgHom_apply, IsLocalization.Away.lift_eq]

/-- The localization of `a` commutes with the restriction maps from `t` to `s`. -/
theorem locMap_resW (a : (Wc N f S W j t hj).carrier →ₐ[R] (Wc N f S W i t hi).carrier)
    (v : (Wc N f S W j t hj).carrier) :
    locMap N f S W h hi hj a (resW N f S W j h hj v) = resW N f S W i h hi (a v) := by
  have : (locMap N f S W h hi hj a).comp (resW N f S W j h hj) = (resW N f S W i h hi).comp a :=
    Wc_algHom_ext N f S W j t hj fun w ↦ by
      rw [AlgHom.comp_apply, AlgHom.comp_apply, resW_toWc, locMap_toWc]
  exact AlgHom.congr_fun this v

/-- Localizing from `t` to `s` and then from `s` to `s'` is localizing from `t` to `s'`. -/
theorem locMap_locMap {s' : Finset (Fin k)} (h' : s ⊆ s')
    (a : (Wc N f S W j t hj).carrier →ₐ[R] (Wc N f S W i t hi).carrier)
    (v : (Wc N f S W j s' (h' (h hj))).carrier) :
    locMap N f S W h' (h hi) (h hj) (locMap N f S W h hi hj a) v =
      locMap N f S W (h.trans h') hi hj a v := by
  exact AlgHom.congr_fun (Wc_algHom_ext N f S W j s' _ fun w ↦ by
    rw [locMap_toWc, locMap_toWc, resW_resW, locMap_toWc]) v

/-- If `a : W_{j,t} → W_{i,t}` lifts the identity of `S_t`, then its localization lifts the
identity of `S_s`. -/
theorem psi_locMap (a : (Wc N f S W j t hj).carrier →ₐ[R] (Wc N f S W i t hi).carrier)
    (ha : ∀ v, (Wc N f S W i t hi).ψ (a v) = (Wc N f S W j t hj).ψ v)
    (v : (Wc N f S W j s (h hj)).carrier) :
    (Wc N f S W i s (h hi)).ψ (locMap N f S W h hi hj a v) = (Wc N f S W j s (h hj)).ψ v := by
  have : (Wc N f S W i s (h hi)).ψ.comp (locMap N f S W h hi hj a) =
      (Wc N f S W j s (h hj)).ψ :=
    Wc_algHom_ext N f S W j s _ fun w ↦ by
      rw [AlgHom.comp_apply, locMap_toWc, psi_resW, ha, psi_toWc, psi_toWc, locS_locS]
  exact AlgHom.congr_fun this v

/-- The localization of a composite `a ∘ b` is the composite of the localizations. -/
theorem locMap_comp {l : Fin k} (hl : l ∈ t)
    (a : (Wc N f S W j t hj).carrier →ₐ[R] (Wc N f S W i t hi).carrier)
    (b : (Wc N f S W l t hl).carrier →ₐ[R] (Wc N f S W j t hj).carrier)
    (v : (Wc N f S W l s (h hl)).carrier) :
    locMap N f S W h hi hl (a.comp b) v =
      locMap N f S W h hi hj a (locMap N f S W h hj hl b v) := by
  have : locMap N f S W h hi hl (a.comp b) =
      (locMap N f S W h hi hj a).comp (locMap N f S W h hj hl b) :=
    Wc_algHom_ext N f S W l s _ fun w ↦ by
      rw [AlgHom.comp_apply, locMap_toWc, locMap_toWc, AlgHom.comp_apply, locMap_resW]
  exact AlgHom.congr_fun this v

/-- The localization of the identity of `W_{i,t}` is the identity of `W_{i,s}`. -/
theorem locMap_id (v : (Wc N f S W i s (h hi)).carrier) :
    locMap N f S W h hi hi (AlgHom.id R _) v = v := by
  have : locMap N f S W h hi hi (AlgHom.id R _) = AlgHom.id R _ :=
    Wc_algHom_ext N f S W i s _ fun w ↦ by
      rw [locMap_toWc, AlgHom.id_apply, resW_toWc, AlgHom.id_apply]
  exact AlgHom.congr_fun this v

/-- The localization `W_{i,s} → H_s` of a map `W_{i,t} → H_t`, for `t ⊆ s`. -/
noncomputable def locMapH (φ : (Wc N f S W i t hi).carrier →ₐ[R] Hl f H t) :
    (Wc N f S W i s (h hi)).carrier →ₐ[R] Hl f H s :=
  IsLocalization.Away.liftAlgHom (algebraMap R (W i).carrier (rs f s))
    (f := ((((locH f H h).restrictScalars R).comp φ).comp (toWc N f S W i t hi)))
    (by rw [AlgHom.commutes]; exact isUnit_Hl f H s)

/-- On the image of `W_i`, the localization of `φ` is `φ` followed by `H_t → H_s`. -/
theorem locMapH_toWc (φ : (Wc N f S W i t hi).carrier →ₐ[R] Hl f H t) (w : (W i).carrier) :
    locMapH N f S H W h hi φ (toWc N f S W i s (h hi) w) =
      locH f H h (φ (toWc N f S W i t hi w)) := by
  simp [locMapH, toWc, IsLocalization.Away.liftAlgHom_apply, IsLocalization.Away.lift_eq]

/-- The localization of `φ` composed with the restriction `W_{i,t} → W_{i,s}` is `φ` followed by
`H_t → H_s`. -/
theorem locMapH_resW (φ : (Wc N f S W i t hi).carrier →ₐ[R] Hl f H t)
    (v : (Wc N f S W i t hi).carrier) :
    locMapH N f S H W h hi φ (resW N f S W i h hi v) = locH f H h (φ v) := by
  have : (locMapH N f S H W h hi φ).comp (resW N f S W i h hi) =
      ((locH f H h).restrictScalars R).comp φ :=
    Wc_algHom_ext N f S W i t hi fun w ↦ by
      rw [AlgHom.comp_apply, AlgHom.comp_apply, resW_toWc, locMapH_toWc]
      rfl
  exact AlgHom.congr_fun this v

/-- The localization of `φ ∘ a` is the localization of `φ` composed with that of `a`. -/
theorem locMapH_comp (a : (Wc N f S W j t hj).carrier →ₐ[R] (Wc N f S W i t hi).carrier)
    (φ : (Wc N f S W i t hi).carrier →ₐ[R] Hl f H t) (v : (Wc N f S W j s (h hj)).carrier) :
    locMapH N f S H W h hj (φ.comp a) v =
      locMapH N f S H W h hi φ (locMap N f S W h hi hj a v) := by
  have : locMapH N f S H W h hj (φ.comp a) =
      (locMapH N f S H W h hi φ).comp (locMap N f S W h hi hj a) :=
    Wc_algHom_ext N f S W j s _ fun w ↦ by
      rw [AlgHom.comp_apply, locMapH_toWc, locMap_toWc, locMapH_resW, AlgHom.comp_apply]
  exact AlgHom.congr_fun this v

/-- Localizing `φ` from `t` to `s` and then from `s` to `s'` is localizing it from `t` to `s'`. -/
theorem locMapH_locMapH {s' : Finset (Fin k)} (h' : s ⊆ s')
    (φ : (Wc N f S W i t hi).carrier →ₐ[R] Hl f H t) (v : (Wc N f S W i s' (h' (h hi))).carrier) :
    locMapH N f S H W h' (h hi) (locMapH N f S H W h hi φ) v =
      locMapH N f S H W (h.trans h') hi φ v := by
  exact AlgHom.congr_fun (Wc_algHom_ext N f S W i s' _ fun w ↦ by
    rw [locMapH_toWc, locMapH_toWc, locH_locH, locMapH_toWc]) v

/-- If `φ : W_{i,t} → H_t` lifts `χ_t`, then its localization `W_{i,s} → H_s` lifts `χ_s`. -/
theorem mk_locMapH (φ : (Wc N f S W i t hi).carrier →ₐ[R] Hl f H t)
    (hφ : ∀ v, Ideal.Quotient.mk _ (φ v) = chi N f S H e t ((Wc N f S W i t hi).ψ v))
    (v : (Wc N f S W i s (h hi)).carrier) :
    Ideal.Quotient.mk _ (locMapH N f S H W h hi φ v) =
      chi N f S H e s ((Wc N f S W i s (h hi)).ψ v) := by
  have : (Ideal.Quotient.mkₐ R (N.map (algebraMap R (Hl f H s)))).comp
      (locMapH N f S H W h hi φ) = (chi N f S H e s).comp (Wc N f S W i s (h hi)).ψ :=
    Wc_algHom_ext N f S W i s _ fun w ↦ by
      rw [AlgHom.comp_apply, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, locMapH_toWc,
        psi_toWc]
      change Ideal.Quotient.mk _ (((locH f H h).restrictScalars R) (φ (toWc N f S W i t hi w))) = _
      rw [← redMap_mk N, hφ, psi_toWc]
      have h1 := AlgHom.congr_fun (redMap_locH_chi N f S H e h)
        (locS f S (Finset.singleton_subset_iff.mpr hi) ((W i).ψ w))
      rw [AlgHom.comp_apply, AlgHom.comp_apply, locS_locS] at h1
      exact h1
  exact AlgHom.congr_fun this v

/-- The localization map `H_s → H_s` is the identity. -/
theorem locH_refl {s : Finset (Fin k)} (h : s ⊆ s) (x : Hl f H s) : locH f H h x = x := by
  have : locH f H h = AlgHom.id H (Hl f H s) :=
    IsLocalization.algHom_ext (Submonoid.powers (algebraMap R H (rs f s))) (by ext)
  exact AlgHom.congr_fun this x

/-- The restriction map `W_{i,s} → W_{i,s}` is the identity. -/
theorem resW_refl {i : Fin k} {s : Finset (Fin k)} (h : s ⊆ s) (hi : i ∈ s)
    (v : (Wc N f S W i s hi).carrier) : resW N f S W i h hi v = v := by
  have : resW N f S W i h hi = AlgHom.id R _ :=
    Wc_algHom_ext N f S W i s hi fun w ↦ by rw [resW_toWc, AlgHom.id_apply]
  exact AlgHom.congr_fun this v

/-- Localizing a map `W_{j,s} → W_{i,s}` from `s` to `s` returns the same map. -/
theorem locMap_refl {i j : Fin k} {s : Finset (Fin k)} (h : s ⊆ s) (hi : i ∈ s) (hj : j ∈ s)
    (a : (Wc N f S W j s hj).carrier →ₐ[R] (Wc N f S W i s hi).carrier) :
    locMap N f S W h hi hj a = a :=
  Wc_algHom_ext N f S W j s _ fun w ↦ by rw [locMap_toWc, resW_refl]

/-- Localizing a map `W_{i,s} → H_s` from `s` to `s` returns the same map. -/
theorem locMapH_refl {i : Fin k} {s : Finset (Fin k)} (h : s ⊆ s) (hi : i ∈ s)
    (φ : (Wc N f S W i s hi).carrier →ₐ[R] Hl f H s) : locMapH N f S H W h hi φ = φ :=
  Wc_algHom_ext N f S W i s _ fun w ↦ by rw [locMapH_toWc, locH_refl]

end LocMap

end Rig.SquareZeroLift

end
