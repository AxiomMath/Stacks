module

public import StacksFrontier.RingTheory.Rig.Algebraization.SquareZeroGlueDatumRing
public import StacksFrontier.RingTheory.Rig.Algebraization.SquareZeroLiftSurj

/-!
# The ring glued from a glueing datum surjects onto `S`

For a glueing datum `D`, the projection `T → S` of the glued ring is surjective. Given `s ∈ S`,
choose lifts `h ∈ H` and `v_i ∈ V_i`; their defects on the overlaps form a cocycle of the
glueing complex of `P = S ⊗[R] N` for the flat map `S → S^∧`, which is a coboundary by
`FormalGlueing.glueingComplex_exact_two`; correcting the lifts by it gives a preimage of `s`.

## Main results

* `Rig.SquareZeroLift.GlueDatum.prS_surjective`: the projection `T → S` is surjective.
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

/-- For `p > 0`, the maps `muV` intertwine the differential of the glueing complex of `PS N S`
with the Čech differential of the family `XV N f S D.L`. -/
theorem muV_cechDiff (p : ℕ) (hp : 0 < p) (y : GlueingTerm (gS f S) (PS N S) p)
    (T : {s : Finset (Fin k) // s.card = p + 1}) :
    muV N hN f S D.L T.1 (glueingDifferential (gS f S) (PS N S) p y T) =
      cechDiff (XV N f S D.L) D.ιV p (fun s ↦ muV N hN f S D.L s.1 (y s)) T := by
  rw [glueingDifferential_eq_cechDiff]
  exact cechDiff_natural _ _ D.ιV (fun s ↦ (muV N hN f S D.L s).toAddMonoidHom) hp
    (fun s t h hs x ↦ by
      simp only [LinearMap.toAddMonoidHom_coe]
      rw [D.ιV_apply h hs]
      exact D.muV_cechι hN h hs x) y T

/-- The Čech differential of the family `XV N f S D.L` squares to zero in degree `1`. -/
theorem cechDiff_ιV_cechDiff (x : FamTerm (XV N f S D.L) 1) :
    cechDiff (XV N f S D.L) D.ιV 2 (cechDiff (XV N f S D.L) D.ιV 1 x) =
      0 :=
  cechDiff_cechDiff _ _ (fun s t w h h' hs x ↦ by
    rw [D.ιV_apply h hs, D.ιV_apply h' (hs.mono h),
      D.ιV_apply (h.trans h') hs, D.sig_sig]) x

variable (s₀ : S) (h₀ : H) (v₀ : FamTerm (XV N f S D.L) 1)

/-- If each `v₀ u` maps to `s₀` under `ψ`, then so does its image under `D.ιV h` in the lift over
any larger index set `t`. -/
theorem psi_ιV_v₀ (hv₀ : ∀ u : {s : Finset (Fin k) // s.card = 1},
      (D.L u.1).ψ (v₀ u) = algebraMap S (Sl f S u.1) s₀)
    (u : {s : Finset (Fin k) // s.card = 1}) {t : Finset (Fin k)} (h : u.1 ⊆ t) :
    (D.L t).ψ (D.ιV h (v₀ u)) = algebraMap S _ s₀ := by
  rw [D.ιV_apply h (nonempty_of_card_eq u), D.psi_sig, hv₀, locS_algebraMap]

/-- If `h₀` lifts `s₀` and each `v₀ u` lifts `s₀`, then the defect `D.rho u (v₀ u) - h₀` lies in
the extension of `N` to `Hl f H u`. -/
theorem defect_mem (hhb : e (Ideal.Quotient.mk _ h₀) = algebraMap S (Sh f S) s₀)
    (hv₀ : ∀ u : {s : Finset (Fin k) // s.card = 1},
      (D.L u.1).ψ (v₀ u) = algebraMap S (Sl f S u.1) s₀)
    (u : {s : Finset (Fin k) // s.card = 1}) :
    D.rho u.1 (nonempty_of_card_eq u) (v₀ u) - algebraMap H _ h₀ ∈
      N.map (algebraMap R (Hl f H u.1)) := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, D.mk_rho, hv₀, chi_algebraMap, sub_eq_zero]
  have : e.symm (algebraMap S (Sh f S) s₀) = Ideal.Quotient.mk _ h₀ := by
    rw [← hhb, AlgEquiv.symm_apply_apply]
  show redMap N _ (e.symm (algebraMap S (Sh f S) s₀)) = _
  rw [this, redMap_mk]
  rfl

/-- If each `v₀ u` lifts `s₀`, then every component of the Čech differential of `v₀` lies in the
extension of `N`. -/
theorem dd_mem (hv₀ : ∀ u : {s : Finset (Fin k) // s.card = 1},
      (D.L u.1).ψ (v₀ u) = algebraMap S (Sl f S u.1) s₀)
    (T : {s : Finset (Fin k) // s.card = 2}) :
    cechDiff (XV N f S D.L) D.ιV 1 v₀ T ∈ N.map (algebraMap R (D.L T.1).carrier) := by
  obtain ⟨u, v, hu, hv, hT⟩ := cechDiff_one_pair D.ιV v₀ T
  rw [NilLift.mem_iff, hT, map_sub, D.psi_ιV_v₀ s₀ v₀ hv₀,
    D.psi_ιV_v₀ s₀ v₀ hv₀, sub_self]

/-- A family `X` whose image under `muV` is the Čech differential of `v₀` is a cocycle of the
glueing complex of `PS N S`. -/
theorem cocycle_X (X : GlueingTerm (gS f S) (PS N S) 2)
    (hX : ∀ T : {s : Finset (Fin k) // s.card = 2},
      muV N hN f S D.L T.1 (X T) = cechDiff (XV N f S D.L) D.ιV 1 v₀ T) :
    glueingDifferential (gS f S) (PS N S) 2 X = 0 := by
  funext T
  apply D.muV_injective hN T.1 (nonempty_of_card_eq T)
  rw [D.muV_cechDiff hN 2 (by norm_num), Pi.zero_apply, map_zero, funext hX,
    D.cechDiff_ιV_cechDiff]
  rfl

/-- If `muV` maps `X` to the Čech differential of `v₀` and `muH` maps `Y` to the defects
`D.rho u (v₀ u) - h₀`, then the differential of `Y` equals the localization of `X`. -/
theorem compat_YX (hflat : ∀ i, Module.Flat R (Localization.Away (algebraMap R H (f i))))
    (X : GlueingTerm (gS f S) (PS N S) 2) (Y : GlueingTerm (gS f S) (PH N f S) 1)
    (hX : ∀ T : {s : Finset (Fin k) // s.card = 2},
      muV N hN f S D.L T.1 (X T) = cechDiff (XV N f S D.L) D.ιV 1 v₀ T)
    (hY : ∀ u : {s : Finset (Fin k) // s.card = 1}, muH N hN f S H e u.1 (Y u) =
      D.rho u.1 (nonempty_of_card_eq u) (v₀ u) - algebraMap H _ h₀) :
    glueingDifferential (gS f S) (PH N f S) 1 Y =
      localizationTensorMap (Sh f S) (gS f S) (PS N S) 2 X := by
  funext T
  apply muH_injective N hN f S H e hflat T.1 (nonempty_of_card_eq T)
  rw [muH_cechDiff N hN f S H e 1 Y T (by norm_num)]
  have h1 : muH N hN f S H e T.1 (localizationTensorMap (Sh f S) (gS f S) (PS N S) 2 X T) =
      D.rho T.1 (nonempty_of_card_eq T)
        (cechDiff (XV N f S D.L) D.ιV 1 v₀ T) := by
    rw [← hX]
    exact D.muH_unit_eq_rho_muV hN T.1 (nonempty_of_card_eq T) (X T)
  rw [h1, funext hY]
  obtain ⟨i, j, hij, hT⟩ := exists_sorted_pair T
  have hu : (singletonIndex i).1 ⊆ T.1 := by rw [hT]; simp
  have hv : (singletonIndex j).1 ⊆ T.1 := by rw [hT]; simp
  rw [cechDiff_one_apply _ (ιH f H) _ T hij hT _ _ rfl rfl hu hv,
    cechDiff_one_apply _ D.ιV v₀ T hij hT _ _ rfl rfl hu hv,
    D.ιV_apply _ (nonempty_of_card_eq _),
    D.ιV_apply _ (nonempty_of_card_eq _),
    map_sub (D.rho T.1 (nonempty_of_card_eq T)), D.rho_sig, D.rho_sig]
  simp only [ιH, AddMonoidHom.coe_coe, RingHom.toAddMonoidHom_eq_coe,
    AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_sub, locH_algebraMap]
  abel

/-- Correcting the lifts `h₀` and `v₀` by a preimage `(y₀, x)` of `(Y, X)` under `glueingBeta`
gives an element of `D.glued` lying over `s₀`. -/
theorem new_mem (hhb : e (Ideal.Quotient.mk _ h₀) = algebraMap S (Sh f S) s₀)
    (hv₀ : ∀ u : {s : Finset (Fin k) // s.card = 1},
      (D.L u.1).ψ (v₀ u) = algebraMap S (Sl f S u.1) s₀)
    (X : GlueingTerm (gS f S) (PS N S) 2) (Y : GlueingTerm (gS f S) (PH N f S) 1)
    (hX : ∀ T : {s : Finset (Fin k) // s.card = 2},
      muV N hN f S D.L T.1 (X T) = cechDiff (XV N f S D.L) D.ιV 1 v₀ T)
    (hY : ∀ u : {s : Finset (Fin k) // s.card = 1}, muH N hN f S H e u.1 (Y u) =
      D.rho u.1 (nonempty_of_card_eq u) (v₀ u) - algebraMap H _ h₀)
    (y₀ : PH N f S) (x : GlueingTerm (gS f S) (PS N S) 1)
    (hyx : glueingBeta (Sh f S) (gS f S) (PS N S) (y₀, x) = (Y, X)) :
    (s₀, h₀ + muH0 N hN f S H e y₀, fun u ↦ v₀ u + muV N hN f S D.L u.1 (x u)) ∈
      D.glued := by
  have hYx : ∀ u, Y u = LocalizedModule.mkLinearMap _ _ y₀ -
      LocalizedModule.map (cechSub (gS f S) u.1)
        ((TensorProduct.mk S (PS N S) (Sh f S)).flip 1) (x u) := by
    intro u
    exact (congrFun (congrArg Prod.fst hyx) u).symm
  have hXx : X = -glueingDifferential (gS f S) (PS N S) 1 x :=
    (congrArg Prod.snd hyx).symm
  rw [D.mem_glued]
  refine ⟨?_, fun u ↦ ?_, fun u ↦ ?_, ?_⟩
  · have : Ideal.Quotient.mk (N.map (algebraMap R H)) (muH0 N hN f S H e y₀) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (muH0_mem N hN f S H e y₀)
    simp only [map_add, this, add_zero, hhb]
  · have : (D.L u.1).ψ (muV N hN f S D.L u.1 (x u)) = 0 :=
      ((D.L u.1).mem_iff N _).mp (muV_mem N hN f S D.L u.1 (x u))
    simp only [map_add, this, add_zero, hv₀]
  · have h2 := hY u
    rw [hYx u, map_sub, muH_mk, D.muH_unit_eq_rho_muV hN u.1
      (nonempty_of_card_eq u)] at h2
    simp only [map_add]
    linear_combination -h2
  · funext T
    let w : FamTerm (XV N f S D.L) 1 := fun u ↦ muV N hN f S D.L u.1 (x u)
    have hw : (fun u : {s : Finset (Fin k) // s.card = 1} ↦ v₀ u + muV N hN f S D.L u.1 (x u)) =
        v₀ + w := rfl
    rw [hw, cechDiff_add, Pi.add_apply]
    have h3 : cechDiff (XV N f S D.L) D.ιV 1 w T =
        muV N hN f S D.L T.1 (glueingDifferential (gS f S) (PS N S) 1 x T) :=
      (D.muV_cechDiff hN 1 (by norm_num) x T).symm
    rw [h3, ← hX T, ← map_add, hXx, Pi.neg_apply, neg_add_cancel, map_zero]
    rfl

include hN in
/-- **The glued ring surjects onto `S`.** -/
theorem prS_surjective [IsNoetherianRing S]
    (hflat : ∀ i, Module.Flat R (Localization.Away (algebraMap R H (f i)))) :
    Function.Surjective D.prS := by
  classical
  intro s₀
  obtain ⟨hb, hhb⟩ := e.surjective (algebraMap S (Sh f S) s₀)
  obtain ⟨h₀, rfl⟩ := Ideal.Quotient.mk_surjective hb
  choose v₀ hv₀ using fun u : {s : Finset (Fin k) // s.card = 1} ↦
    (D.L u.1).surj (algebraMap S (Sl f S u.1) s₀)
  choose Y hY using fun u : {s : Finset (Fin k) // s.card = 1} ↦ exists_muH_eq N hN f S H e u.1 _
    (D.defect_mem s₀ h₀ v₀ hhb hv₀ u)
  choose X hX using fun T : {s : Finset (Fin k) // s.card = 2} ↦
    exists_muV_eq N hN f S D.L T.1 _ (D.dd_mem s₀ v₀ hv₀ T)
  obtain ⟨⟨y₀, x⟩, hyx⟩ := glueingComplex_exact_two S (Sh f S) (gS f S) (PS N S)
    (flat_Sh f S) (quotientMap_Sh_bijective f S) Y X
    (D.compat_YX hN h₀ v₀ hflat X Y hX hY)
    (D.cocycle_X hN v₀ X hX)
  exact ⟨⟨_, D.new_mem hN s₀ h₀ v₀ hhb hv₀ X Y hX hY y₀ x hyx⟩, rfl⟩

end Rig.SquareZeroLift.GlueDatum

end
