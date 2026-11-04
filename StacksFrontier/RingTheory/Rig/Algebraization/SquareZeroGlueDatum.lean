module

public import StacksFrontier.RingTheory.Rig.Algebraization.SquareZeroLiftCompare

/-!
# Glueing data for the square-zero lifting step

In the setting of `StacksFrontier.RingTheory.Rig.Algebraization.SquareZeroLiftData`, the ring of the
square-zero lifting step is glued from `S`, `H` and lifts `V_s` of the localizations
`S_s = S[1 / r_s]` across `R → R ⧸ N`, using transition maps `σ_{s,t} : V_s → V_t` and maps
`ρ_s : V_s → H_s`. When the `V_s` are étale over `R` these maps are unique
(`Rig.SquareZeroLift.sig`, `Rig.SquareZeroLift.rho`); in general they are extra data. A
`Rig.SquareZeroLift.GlueDatum` packages the lifts with such maps, satisfying the cocycle and
compatibility conditions, and the flatness of the `V_s` over `R`. This file records the
compatibilities of a glueing datum with the comparison maps `μ_s` and `μ̂_s`.

## Main definitions

* `Rig.SquareZeroLift.GlueDatum`: a glueing datum.
* `Rig.SquareZeroLift.etaleDatum`: the glueing datum of étale lifts.
-/

@[expose] public section

namespace Rig.SquareZeroLift

open TensorProduct Cech FormalGlueing

universe u

variable {R : Type u} [CommRing R] (N : Ideal R)
variable {k : ℕ} (f : Fin k → R)
variable (S : Type u) [CommRing S] [Algebra R S]
variable (H : Type u) [CommRing H] [Algebra R H]
variable (e : (H ⧸ N.map (algebraMap R H)) ≃ₐ[R] Sh f S)

/-- A glueing datum for the square-zero lifting step: lifts `V_s` of the localizations `S_s`
across `R → R ⧸ N`, flat over `R` for `s` nonempty, with transition maps `σ_{s,t} : V_s → V_t`
lifting `S_s → S_t` and satisfying the cocycle condition, and maps `ρ_s : V_s → H_s` lifting
`S_s → H_s ⧸ N H_s` and compatible with the transition maps. -/
structure GlueDatum where
  /-- The lifts `V_s` of the localizations `S_s`. -/
  L : ∀ s : Finset (Fin k), NilLift R N (Sl f S s)
  /-- The lifts `V_s`, `s` nonempty, are flat over `R`. -/
  flat : ∀ s, s.Nonempty → Module.Flat R (L s).carrier
  /-- The transition maps `σ_{s,t} : V_s → V_t`. -/
  sig : ∀ {s t : Finset (Fin k)}, s ⊆ t → s.Nonempty → (L s).carrier →ₐ[R] (L t).carrier
  psi_sig : ∀ {s t : Finset (Fin k)} (h : s ⊆ t) (hs : s.Nonempty) (v : (L s).carrier),
    (L t).ψ (sig h hs v) = locS f S h ((L s).ψ v)
  sig_sig : ∀ {s t w : Finset (Fin k)} (h : s ⊆ t) (h' : t ⊆ w) (hs : s.Nonempty)
    (v : (L s).carrier), sig h' (hs.mono h) (sig h hs v) = sig (h.trans h') hs v
  /-- The maps `ρ_s : V_s → H_s`. -/
  rho : ∀ s : Finset (Fin k), s.Nonempty → (L s).carrier →ₐ[R] Hl f H s
  mk_rho : ∀ (s : Finset (Fin k)) (hs : s.Nonempty) (v : (L s).carrier),
    Ideal.Quotient.mk _ (rho s hs v) = chi N f S H e s ((L s).ψ v)
  rho_sig : ∀ {s t : Finset (Fin k)} (h : s ⊆ t) (hs : s.Nonempty) (v : (L s).carrier),
    rho t (hs.mono h) (sig h hs v) = locH f H h (rho s hs v)

/-- The glueing datum of lifts which are étale over `R`, with the unique transition maps and
maps to the `H_s`. -/
noncomputable def etaleDatum (hN : N ^ 2 = ⊥) (L : ∀ s : Finset (Fin k), NilLift R N (Sl f S s))
    (hL : ∀ s, s.Nonempty → Algebra.Etale R (L s).carrier) : GlueDatum N f S H e where
  L := L
  flat s hs := haveI := hL s hs; inferInstance
  sig := sig N hN f S L hL
  psi_sig := psi_sig N hN f S L hL
  sig_sig := sig_sig N hN f S L hL
  rho := rho N hN f S H e L hL
  mk_rho := mk_rho N hN f S H e L hL
  rho_sig := rho_sig N hN f S H e L hL

namespace GlueDatum

variable {N f S H e} (D : GlueDatum N f S H e)

/-- The reduction modulo `N` of `σ_{s,t}(v)` is the image of the reduction of `v` under the
localization map `S_s → S_t`, transported along the identifications `V_t ⧸ N V_t ≃ S_t`. -/
theorem mk_sig {s t : Finset (Fin k)} (h : s ⊆ t) (hs : s.Nonempty) (v : (D.L s).carrier) :
    Ideal.Quotient.mk _ (D.sig h hs v) = ((D.L t).qe N).symm (locS f S h ((D.L s).ψ v)) := by
  rw [← D.psi_sig h hs v, ← (D.L t).qe_mk N, AlgEquiv.symm_apply_apply]

/-- The transition map `σ_{s,t}` sends `N V_s` into `N V_t`. -/
theorem sig_mem {s t : Finset (Fin k)} (h : s ⊆ t) (hs : s.Nonempty) {v : (D.L s).carrier}
    (hv : v ∈ N.map (algebraMap R (D.L s).carrier)) :
    D.sig h hs v ∈ N.map (algebraMap R (D.L t).carrier) := by
  rw [NilLift.mem_iff] at hv ⊢
  rw [D.psi_sig, hv, map_zero]

/-- The map `ρ_s` sends `N V_s` into `N H_s`. -/
theorem rho_mem (s : Finset (Fin k)) (hs : s.Nonempty) {v : (D.L s).carrier}
    (hv : v ∈ N.map (algebraMap R (D.L s).carrier)) :
    D.rho s hs v ∈ N.map (algebraMap R (Hl f H s)) := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, D.mk_rho]
  rw [NilLift.mem_iff] at hv
  rw [hv, map_zero]

/-- Every `lam x` lifts to some `v : V_s` whose `ψ` is the image of `x`. -/
private theorem exists_mk_eq_lam (s : Finset (Fin k)) (x : S) :
    ∃ v : (D.L s).carrier, Ideal.Quotient.mk _ v = lam N f S D.L s x ∧
      (D.L s).ψ v = algebraMap S _ x := by
  obtain ⟨v, hv⟩ := Ideal.Quotient.mk_surjective (lam N f S D.L s x)
  refine ⟨v, hv, ?_⟩
  rw [← (D.L s).qe_mk N, hv]
  simp [lam]

/-- The reduction of `σ_{s,t}` modulo `N` is compatible with the maps `lam` from `S_s` and
`S_t`. -/
theorem lam_sig {s t : Finset (Fin k)} (h : s ⊆ t) (hs : s.Nonempty) :
    (redMap N (D.sig h hs)).comp (lam N f S D.L s) = lam N f S D.L t := by
  ext x
  obtain ⟨v, hv, hψ⟩ := D.exists_mk_eq_lam s x
  rw [AlgHom.comp_apply, ← hv, redMap_mk, D.mk_sig, hψ, locS_algebraMap]
  rfl

/-- The reduction of `ρ_s` modulo `N`, composed with `lam` from `S_s`, agrees with `lamH`
composed with the algebra map `S → Sh f S`. -/
theorem lam_rho (s : Finset (Fin k)) (hs : s.Nonempty) :
    (redMap N (D.rho s hs)).comp (lam N f S D.L s) =
      (lamH N f S H e s).comp (IsScalarTower.toAlgHom R S (Sh f S)) := by
  ext x
  obtain ⟨v, hv, hψ⟩ := D.exists_mk_eq_lam s x
  rw [AlgHom.comp_apply, ← hv, redMap_mk, D.mk_rho, hψ, chi_algebraMap]
  rfl

variable (hN : N ^ 2 = ⊥)

/-- For `s` nonempty, the comparison map `μ_s = muV` into `V_s` is injective. -/
theorem muV_injective (s : Finset (Fin k)) (hs : s.Nonempty) :
    Function.Injective (muV N hN f S D.L s) := by
  have := isLocalizedModule_cech f S (PS N S) s
  have := isLocalizedModule_lam N f S D.L s
  have := D.flat s hs
  exact cmp_injective N hN _ _ _ _

/-- The comparison maps `μ_s = muV` commute with the Čech transition maps `cechι` and the
transition maps `σ_{s,t}`. -/
theorem muV_cechι {s t : Finset (Fin k)} (h : s ⊆ t) (hs : s.Nonempty)
    (y : cechMod (gS f S) (PS N S) s) :
    muV N hN f S D.L t (cechι (gS f S) (PS N S) h y) = D.sig h hs (muV N hN f S D.L s y) := by
  obtain ⟨n, z, hz⟩ := exists_pow_smul_cech_eq_mk f S s y
  apply smul_injective_of_isUnit (r := rs f s ^ n)
    (by rw [map_pow]; exact (isUnit_V N hN f S D.L h).pow n)
  simp only
  rw [← map_smul, ← LinearMap.map_smul_of_tower, hz, cechι_mk, muV_mk, ← map_smul, ← map_smul,
    hz, muV_mk, theta_naturality N hN _ _ _ (D.lam_sig h hs)]

/-- The comparison map `μ̂_s = muH`, precomposed with base change along `S → Sh f S`, equals `ρ_s`
composed with `μ_s = muV`. -/
theorem muH_unit_eq_rho_muV (s : Finset (Fin k)) (hs : s.Nonempty)
    (y : cechMod (gS f S) (PS N S) s) :
    muH N hN f S H e s
        (LocalizedModule.map (cechSub (gS f S) s)
          ((TensorProduct.mk S (PS N S) (Sh f S)).flip 1) y) =
      D.rho s hs (muV N hN f S D.L s y) := by
  obtain ⟨n, z, hz⟩ := exists_pow_smul_cech_eq_mk f S s y
  apply smul_injective_of_isUnit (r := rs f s ^ n)
    (by rw [map_pow]; exact (isUnit_Hl f H s).pow n)
  simp only
  rw [← map_smul, ← LinearMap.map_smul_of_tower, hz, ← map_smul, ← map_smul, hz, muV_mk]
  have h1 : LocalizedModule.map (cechSub (gS f S) s) ((TensorProduct.mk S (PS N S) (Sh f S)).flip 1)
      (LocalizedModule.mkLinearMap _ _ z) = LocalizedModule.mkLinearMap _ _ (z ⊗ₜ 1) := by
    simp [LocalizedModule.map_mk]
  rw [h1, muH_mk, muH0_tmul_one, theta_naturality N hN _ _ _ (D.lam_rho s hs)]
  exact theta_naturality N hN (IsScalarTower.toAlgHom R H (Hl f H s)) _ _ rfl z

end GlueDatum

end Rig.SquareZeroLift

end
