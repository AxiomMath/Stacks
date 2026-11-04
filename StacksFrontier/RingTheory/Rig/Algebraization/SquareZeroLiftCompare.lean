module

public import StacksFrontier.RingTheory.Rig.Algebraization.SquareZeroLiftData

/-!
# Comparison of the square-zero ideals with localized modules

In the setting of `StacksFrontier.RingTheory.Rig.Algebraization.SquareZeroLiftData`, write
`P = S ⊗[R] N` and `P' = P ⊗[S] S^∧`. This file constructs the comparison maps
`μ_s : P_{r_s} → V_s` and `μ̂_s : P'_{r_s} → H_s`, induced by multiplication, and proves that
they are injective with image `N V_s` and `N H_s` (for `s` nonempty) and that they are
compatible with the transition maps, with the maps `ρ_s`, and with base change along
`S → S^∧`.

## Main definitions

* `Rig.SquareZeroLift.muV`: the comparison `P_{r_s} → V_s`.
* `Rig.SquareZeroLift.muH`: the comparison `P'_{r_s} → H_s`.
* `Rig.SquareZeroLift.muH0`: the multiplication `P' → H`.
-/

@[expose] public section

namespace Rig.SquareZeroLift

open TensorProduct Cech FormalGlueing

universe u

variable {R : Type u} [CommRing R] (N : Ideal R) (hN : N ^ 2 = ⊥)
variable {k : ℕ} (f : Fin k → R)
variable (S : Type u) [CommRing S] [Algebra R S]

/-- The `S`-module `P = S ⊗[R] N`. -/
abbrev PS := S ⊗[R] N

/-- The `S^∧`-module `P' = P ⊗[S] S^∧`. -/
abbrev PH := PS N S ⊗[S] Sh f S

/-- For an `S`-module `M`, the localization map `M → M_{r_s}`, viewed as an `R`-linear map, is a
localization at the powers of `r_s`. -/
theorem isLocalizedModule_cech (M : Type*) [AddCommGroup M] [Module S M] [Module R M]
    [IsScalarTower R S M] (s : Finset (Fin k)) :
    IsLocalizedModule (Submonoid.powers (rs f s))
      ((LocalizedModule.mkLinearMap (cechSub (gS f S) s) M).restrictScalars R) := by
  have h : cechSub (gS f S) s = Submonoid.powers (algebraMap R S (rs f s)) := by
    rw [cechSub, prod_gS]
  have : IsLocalizedModule (Submonoid.powers (algebraMap R S (rs f s)))
      (LocalizedModule.mkLinearMap (cechSub (gS f S) s) M) := h ▸ inferInstance
  exact IsLocalizedModule.restrictScalars_powers (rs f s) _

/-- The map `S → S_s`, viewed as an `R`-linear map, is a localization at the powers of `r_s`. -/
theorem isLocalizedModule_toAlgHom (s : Finset (Fin k)) :
    IsLocalizedModule (Submonoid.powers (rs f s))
      (IsScalarTower.toAlgHom R S (Sl f S s)).toLinearMap := by
  have : (IsScalarTower.toAlgHom R S (Sl f S s)).toLinearMap =
      (Algebra.linearMap S (Sl f S s)).restrictScalars R := rfl
  rw [this]
  exact IsLocalizedModule.restrictScalars_powers (rs f s) _

/-- The canonical identification `S^∧ ⊗[R] N ≅ P'`. -/
noncomputable def cancelH : Sh f S ⊗[R] N ≃ₗ[R] PH N f S :=
  ((AlgebraTensorModule.cancelBaseChange R S (Sh f S) (Sh f S) N).symm.restrictScalars R).trans
    ((TensorProduct.comm S (Sh f S) (PS N S)).restrictScalars R)

/-- The inverse of `cancelH` sends `(a ⊗ n) ⊗ x` to `(a x) ⊗ n`. -/
theorem cancelH_symm_tmul (a : S) (n : N) (x : Sh f S) :
    (cancelH N f S).symm ((a ⊗ₜ n) ⊗ₜ x) = (algebraMap S (Sh f S) a * x) ⊗ₜ n := by
  simp [cancelH, Algebra.smul_def, mul_comm]

variable (H : Type u) [CommRing H] [Algebra R H]
variable (e : (H ⧸ N.map (algebraMap R H)) ≃ₐ[R] Sh f S)

/-- The map `S^∧ → H_s ⧸ N H_s`, viewed as an `R`-linear map, is a localization at the powers of
`r_s`. -/
theorem isLocalizedModule_lamH (s : Finset (Fin k)) :
    IsLocalizedModule (Submonoid.powers (rs f s)) (lamH N f S H e s).toLinearMap := by
  have h1 := isLocalizedModule_redMap N (rs f s) (B := H) (Hl f H s)
  have : (lamH N f S H e s).toLinearMap =
      (redMap N (IsScalarTower.toAlgHom R H (Hl f H s))).toLinearMap ∘ₗ
        e.symm.toLinearEquiv.toLinearMap := rfl
  rw [this]
  infer_instance

/-- The localizations `H_s`, `s` nonempty, are flat over `R`. -/
theorem flat_Hl (hflat : ∀ i, Module.Flat R (Localization.Away (algebraMap R H (f i))))
    (s : Finset (Fin k)) (hs : s.Nonempty) : Module.Flat R (Hl f H s) := by
  obtain ⟨i, hi⟩ := hs
  have := hflat i
  let Hi := Localization.Away (algebraMap R H (f i))
  let Hii := Localization.Away (algebraMap H Hi (algebraMap R H (rs f (s.erase i))))
  have : IsLocalization.Away (algebraMap R H (f i) * algebraMap R H (rs f (s.erase i))) Hii :=
    IsLocalization.Away.mul' Hi Hii _ _
  have hprod : algebraMap R H (f i) * algebraMap R H (rs f (s.erase i)) =
      algebraMap R H (rs f s) := by
    rw [← map_mul, rs, rs, Finset.mul_prod_erase s f hi]
  rw [hprod] at this
  let φ : Hii ≃ₐ[H] Hl f H s :=
    IsLocalization.algEquiv (Submonoid.powers (algebraMap R H (rs f s))) Hii (Hl f H s)
  exact Module.Flat.of_linearEquiv ((φ.restrictScalars R).toLinearEquiv.symm)

/-- The multiplication `P' → H`. -/
noncomputable def muH0 : PH N f S →ₗ[R] H :=
  theta N hN e.symm.toAlgHom ∘ₗ (cancelH N f S).symm.toLinearMap

/-- The image of `P' → H` lies in `N H`. -/
theorem muH0_mem (y : PH N f S) : muH0 N hN f S H e y ∈ N.map (algebraMap R H) :=
  theta_mem N hN _ _

/-- Every element of `N H` is in the image of `P' → H`. -/
theorem exists_muH0_eq (h : H) (hh : h ∈ N.map (algebraMap R H)) :
    ∃ y, muH0 N hN f S H e y = h := by
  obtain ⟨z, rfl⟩ := exists_multT_eq N hN H h hh
  obtain ⟨z', rfl⟩ := (LinearEquiv.rTensor N e.symm.toLinearEquiv).surjective z
  refine ⟨cancelH N f S z', ?_⟩
  simp [muH0, theta]
  rfl

/-- The comparison `P'_{r_s} → H_s`. -/
noncomputable def muH (s : Finset (Fin k)) : cechMod (gS f S) (PH N f S) s →ₗ[R] Hl f H s :=
  haveI := isLocalizedModule_cech f S (PH N f S) s
  cmp N hN (rs f s) (isUnit_Hl f H s) (lamH N f S H e s)
    ((LocalizedModule.mkLinearMap (cechSub (gS f S) s) (PH N f S)).restrictScalars R ∘ₗ
      (cancelH N f S).toLinearMap)

/-- On the image of `y ∈ P'` in `P'_{r_s}`, `muH` is the image in `H_s` of `muH0 y`. -/
theorem muH_mk (s : Finset (Fin k)) (y : PH N f S) :
    muH N hN f S H e s (LocalizedModule.mkLinearMap _ _ y) =
      algebraMap H (Hl f H s) (muH0 N hN f S H e y) := by
  have := isLocalizedModule_cech f S (PH N f S) s
  have h := cmp_apply N hN (rs f s) (isUnit_Hl f H s) (lamH N f S H e s)
    ((LocalizedModule.mkLinearMap (cechSub (gS f S) s) (PH N f S)).restrictScalars R ∘ₗ
      (cancelH N f S).toLinearMap) ((cancelH N f S).symm y)
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply,
    LinearMap.restrictScalars_apply] at h
  rw [muH, h, muH0, LinearMap.comp_apply]
  exact (theta_naturality N hN (IsScalarTower.toAlgHom R H (Hl f H s)) _ _ rfl _).symm

/-- The map `P' → H` sends `(a ⊗ n) ⊗ x` to `n h` for any `h ∈ H` lifting `a x ∈ S^∧`. -/
theorem muH0_tmul (a : S) (n : N) (x : Sh f S) (h : H)
    (hh : Ideal.Quotient.mk _ h = e.symm (algebraMap S (Sh f S) a * x)) :
    muH0 N hN f S H e ((a ⊗ₜ n) ⊗ₜ x) = (n : R) • h := by
  rw [muH0, LinearMap.comp_apply, LinearEquiv.coe_coe, cancelH_symm_tmul]
  exact theta_tmul N hN _ _ n h hh

/-- If the localizations `H_{f_i}` are flat over `R`, then `P'_{r_s} → H_s` is injective for `s`
nonempty. -/
theorem muH_injective (hflat : ∀ i, Module.Flat R (Localization.Away (algebraMap R H (f i))))
    (s : Finset (Fin k)) (hs : s.Nonempty) : Function.Injective (muH N hN f S H e s) := by
  have := isLocalizedModule_cech f S (PH N f S) s
  have := isLocalizedModule_lamH N f S H e s
  have := flat_Hl f H hflat s hs
  exact cmp_injective N hN _ _ _ _

/-- The image of `P'_{r_s} → H_s` lies in `N H_s`. -/
theorem muH_mem (s : Finset (Fin k)) (y : cechMod (gS f S) (PH N f S) s) :
    muH N hN f S H e s y ∈ N.map (algebraMap R (Hl f H s)) := by
  have := isLocalizedModule_cech f S (PH N f S) s
  exact cmp_mem N hN _ _ _ _ y

/-- Every element of `N H_s` is in the image of `P'_{r_s} → H_s`. -/
theorem exists_muH_eq (s : Finset (Fin k)) (h : Hl f H s)
    (hh : h ∈ N.map (algebraMap R (Hl f H s))) : ∃ y, muH N hN f S H e s y = h := by
  have := isLocalizedModule_cech f S (PH N f S) s
  have := isLocalizedModule_lamH N f S H e s
  exact exists_cmp_eq N hN _ _ _ _ h hh

/-- An element of a localization of an `S`-module is, up to a power of `r_s`, the image of an
element of the module. -/
theorem exists_pow_smul_cech_eq_mk {M : Type*} [AddCommGroup M] [Module S M] [Module R M]
    [IsScalarTower R S M] (s : Finset (Fin k)) (m : cechMod (gS f S) M s) :
    ∃ (n : ℕ) (y : M), rs f s ^ n • m = LocalizedModule.mkLinearMap _ _ y := by
  have := isLocalizedModule_cech f S M s
  obtain ⟨⟨y, ⟨_, n, rfl⟩⟩, hy⟩ := IsLocalizedModule.surj (Submonoid.powers (rs f s))
    ((LocalizedModule.mkLinearMap (cechSub (gS f S) s) M).restrictScalars R) m
  exact ⟨n, y, by simpa [Submonoid.smul_def] using hy⟩

/-- Scalar multiplication by `r ∈ R` on an `R`-algebra `B` is injective when the image of `r` in
`B` is a unit. -/
theorem smul_injective_of_isUnit {B : Type*} [CommRing B] [Algebra R B] {r : R}
    (hr : IsUnit (algebraMap R B r)) : Function.Injective (fun b : B ↦ r • b) := by
  intro x y hxy
  simp only [Algebra.smul_def] at hxy
  exact hr.mul_left_cancel hxy

/-- For `s ⊆ t`, the element `r_s` is a unit in `H_t`. -/
theorem isUnit_Hl_of_subset {s t : Finset (Fin k)} (h : s ⊆ t) :
    IsUnit (algebraMap R (Hl f H t) (rs f s)) := by
  rw [IsScalarTower.algebraMap_apply R H (Hl f H t)]
  exact IsLocalization.Away.isUnit_of_dvd (algebraMap R H (rs f t)) (map_dvd _ (rs_dvd f h))

/-- The transition maps `H_s → H_t` are `R`-linear. -/
theorem locH_smul {s t : Finset (Fin k)} (h : s ⊆ t) (c : R) (x : Hl f H s) :
    locH f H h (c • x) = c • locH f H h x := by
  rw [Algebra.smul_def, Algebra.smul_def, map_mul]
  congr 1
  exact ((locH f H h).restrictScalars R).commutes c

/-- The maps `P'_{r_s} → H_s` commute with the transition maps `P'_{r_s} → P'_{r_t}` and
`H_s → H_t` for `s ⊆ t`. -/
theorem muH_cechι {s t : Finset (Fin k)} (h : s ⊆ t) (y : cechMod (gS f S) (PH N f S) s) :
    muH N hN f S H e t (cechι (gS f S) (PH N f S) h y) = locH f H h (muH N hN f S H e s y) := by
  obtain ⟨n, z, hz⟩ := exists_pow_smul_cech_eq_mk f S s y
  apply smul_injective_of_isUnit (r := rs f s ^ n)
    (by rw [map_pow]; exact (isUnit_Hl_of_subset f H h).pow n)
  simp only
  rw [← map_smul, ← LinearMap.map_smul_of_tower, hz, cechι_mk, muH_mk, ← locH_smul, ← map_smul,
    hz, muH_mk, locH_algebraMap]

/-- The inverse of `cancelH` sends `z ⊗ 1` to the base change of `z ∈ P` along `S → S^∧`. -/
theorem cancelH_symm_tmul_one (z : PS N S) :
    (cancelH N f S).symm (z ⊗ₜ 1) =
      (IsScalarTower.toAlgHom R S (Sh f S)).toLinearMap.rTensor N z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a n =>
    rw [cancelH_symm_tmul, mul_one]
    rfl
  | add x y hx hy => rw [TensorProduct.add_tmul, map_add, hx, hy, map_add]

/-- The map `P' → H` sends `z ⊗ 1` to `θ_λ z`, where `λ` is the composite `S → S^∧ ≅ H ⧸ N H`. -/
theorem muH0_tmul_one (z : PS N S) :
    muH0 N hN f S H e (z ⊗ₜ 1) =
      theta N hN (e.symm.toAlgHom.comp (IsScalarTower.toAlgHom R S (Sh f S))) z := by
  rw [muH0, LinearMap.comp_apply, LinearEquiv.coe_coe, cancelH_symm_tmul_one, theta_comp]

/-! ### The comparison maps for the lifts `V_s` -/

variable (L : ∀ s : Finset (Fin k), NilLift R N (Sl f S s))
variable (hL : ∀ s, s.Nonempty → Algebra.Etale R (L s).carrier)

include hN in
/-- For `s ⊆ t`, the element `r_s` is a unit in `V_t`. -/
theorem isUnit_V {s t : Finset (Fin k)} (h : s ⊆ t) :
    IsUnit (algebraMap R (L t).carrier (rs f s)) := by
  apply NilLift.isUnit N hN (L t)
  rw [AlgHom.commutes, IsScalarTower.algebraMap_apply R S (Sl f S t)]
  exact IsLocalization.Away.isUnit_of_dvd (algebraMap R S (rs f t)) (map_dvd _ (rs_dvd f h))

/-- The map `S → V_s ⧸ N V_s`, viewed as an `R`-linear map, is a localization at the powers of
`r_s`. -/
theorem isLocalizedModule_lam (s : Finset (Fin k)) :
    IsLocalizedModule (Submonoid.powers (rs f s)) (lam N f S L s).toLinearMap := by
  have := isLocalizedModule_toAlgHom f S s
  have : (lam N f S L s).toLinearMap = ((L s).qe N).symm.toLinearEquiv.toLinearMap ∘ₗ
      (IsScalarTower.toAlgHom R S (Sl f S s)).toLinearMap := rfl
  rw [this]
  infer_instance

/-- The comparison `P_{r_s} → V_s`. -/
noncomputable def muV (s : Finset (Fin k)) : cechMod (gS f S) (PS N S) s →ₗ[R] (L s).carrier :=
  haveI := isLocalizedModule_cech f S (PS N S) s
  cmp N hN (rs f s) (isUnit_V N hN f S L (le_refl s)) (lam N f S L s)
    ((LocalizedModule.mkLinearMap (cechSub (gS f S) s) (PS N S)).restrictScalars R)

/-- On the image of `z ∈ P` in `P_{r_s}`, `muV` is `θ_λ z` for `λ : S → V_s ⧸ N V_s`. -/
theorem muV_mk (s : Finset (Fin k)) (z : PS N S) :
    muV N hN f S L s (LocalizedModule.mkLinearMap _ _ z) = theta N hN (lam N f S L s) z := by
  have := isLocalizedModule_cech f S (PS N S) s
  exact cmp_apply N hN _ _ _ _ z

include hL in
/-- For `s` nonempty, the map `P_{r_s} → V_s` is injective. -/
theorem muV_injective (s : Finset (Fin k)) (hs : s.Nonempty) :
    Function.Injective (muV N hN f S L s) := by
  have := isLocalizedModule_cech f S (PS N S) s
  have := isLocalizedModule_lam N f S L s
  have := hL s hs
  exact cmp_injective N hN _ _ _ _

/-- The image of `P_{r_s} → V_s` lies in `N V_s`. -/
theorem muV_mem (s : Finset (Fin k)) (y : cechMod (gS f S) (PS N S) s) :
    muV N hN f S L s y ∈ N.map (algebraMap R (L s).carrier) := by
  have := isLocalizedModule_cech f S (PS N S) s
  exact cmp_mem N hN _ _ _ _ y

/-- Every element of `N V_s` is in the image of `P_{r_s} → V_s`. -/
theorem exists_muV_eq (s : Finset (Fin k)) (v : (L s).carrier)
    (hv : v ∈ N.map (algebraMap R (L s).carrier)) : ∃ y, muV N hN f S L s y = v := by
  have := isLocalizedModule_cech f S (PS N S) s
  have := isLocalizedModule_lam N f S L s
  exact exists_cmp_eq N hN _ _ _ _ v hv

/-- For `s ⊆ t` with `s` nonempty, reducing `σ_{s,t} : V_s → V_t` modulo `N` and composing with
`S → V_s ⧸ N V_s` gives `S → V_t ⧸ N V_t`. -/
theorem lam_sig {s t : Finset (Fin k)} (h : s ⊆ t) (hs : s.Nonempty) :
    (redMap N (sig N hN f S L hL h hs)).comp (lam N f S L s) = lam N f S L t := by
  ext x
  obtain ⟨v, hv⟩ := Ideal.Quotient.mk_surjective (lam N f S L s x)
  have hψ : (L s).ψ v = algebraMap S _ x := by
    rw [← (L s).qe_mk N, hv]
    simp [lam]
  rw [AlgHom.comp_apply, ← hv, redMap_mk, mk_sig, hψ, locS_algebraMap]
  rfl

/-- For `s` nonempty, reducing `ρ_s : V_s → H_s` modulo `N` and composing with `S → V_s ⧸ N V_s`
gives the composite `S → S^∧ → H_s ⧸ N H_s`. -/
theorem lam_rho (s : Finset (Fin k)) (hs : s.Nonempty) :
    (redMap N (rho N hN f S H e L hL s hs)).comp (lam N f S L s) =
      (lamH N f S H e s).comp (IsScalarTower.toAlgHom R S (Sh f S)) := by
  ext x
  obtain ⟨v, hv⟩ := Ideal.Quotient.mk_surjective (lam N f S L s x)
  have hψ : (L s).ψ v = algebraMap S _ x := by
    rw [← (L s).qe_mk N, hv]
    simp [lam]
  rw [AlgHom.comp_apply, ← hv, redMap_mk, mk_rho, hψ, chi_algebraMap]
  rfl

/-- The map `P_{r_s} → V_s` commutes with scalar multiplication by `R`. -/
theorem smul_muV (s : Finset (Fin k)) (c : R) (y : cechMod (gS f S) (PS N S) s) :
    muV N hN f S L s (c • y) = c • muV N hN f S L s y := map_smul _ _ _

/-- For `s ⊆ t` with `s` nonempty, the maps `P_{r_s} → V_s` commute with the transition maps
`P_{r_s} → P_{r_t}` and `σ_{s,t} : V_s → V_t`. -/
theorem muV_cechι {s t : Finset (Fin k)} (h : s ⊆ t) (hs : s.Nonempty)
    (y : cechMod (gS f S) (PS N S) s) :
    muV N hN f S L t (cechι (gS f S) (PS N S) h y) =
      sig N hN f S L hL h hs (muV N hN f S L s y) := by
  obtain ⟨n, z, hz⟩ := exists_pow_smul_cech_eq_mk f S s y
  apply smul_injective_of_isUnit (r := rs f s ^ n)
    (by rw [map_pow]; exact (isUnit_V N hN f S L h).pow n)
  simp only
  rw [← map_smul, ← LinearMap.map_smul_of_tower, hz, cechι_mk, muV_mk, ← map_smul, ← map_smul,
    hz, muV_mk, theta_naturality N hN _ _ _ (lam_sig N hN f S L hL h hs)]

/-- For `s` nonempty, the map `P_{r_s} → P'_{r_s}`, `z ↦ z ⊗ 1`, followed by `P'_{r_s} → H_s`
equals `P_{r_s} → V_s` followed by `ρ_s : V_s → H_s`. -/
theorem muH_unit_eq_rho_muV (s : Finset (Fin k)) (hs : s.Nonempty)
    (y : cechMod (gS f S) (PS N S) s) :
    muH N hN f S H e s
        (LocalizedModule.map (cechSub (gS f S) s)
          ((TensorProduct.mk S (PS N S) (Sh f S)).flip 1) y) =
      rho N hN f S H e L hL s hs (muV N hN f S L s y) := by
  obtain ⟨n, z, hz⟩ := exists_pow_smul_cech_eq_mk f S s y
  apply smul_injective_of_isUnit (r := rs f s ^ n)
    (by rw [map_pow]; exact (isUnit_Hl f H s).pow n)
  simp only
  rw [← map_smul, ← LinearMap.map_smul_of_tower, hz, ← map_smul, ← map_smul, hz, muV_mk]
  have h1 : LocalizedModule.map (cechSub (gS f S) s) ((TensorProduct.mk S (PS N S) (Sh f S)).flip 1)
      (LocalizedModule.mkLinearMap _ _ z) = LocalizedModule.mkLinearMap _ _ (z ⊗ₜ 1) := by
    simp [LocalizedModule.map_mk]
  rw [h1, muH_mk, muH0_tmul_one, theta_naturality N hN _ _ _ (lam_rho N hN f S H e L hL s hs)]
  exact theta_naturality N hN (IsScalarTower.toAlgHom R H (Hl f H s)) _ _ rfl z

end Rig.SquareZeroLift

end
