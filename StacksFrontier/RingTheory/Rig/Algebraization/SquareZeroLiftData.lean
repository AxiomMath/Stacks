module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Smooth.Flat
public import Mathlib.RingTheory.Localization.Away.Basic
public import StacksFrontier.RingTheory.Rig.Algebraization.SquareZeroLiftTheta
public import StacksFrontier.RingTheory.Rig.Algebraization.SquareZeroLiftCech

/-!
# The local data of the square-zero lifting step

Fix a ring `R`, an ideal `N ⊆ R` with `N ^ 2 = 0`, a family `f : Fin k → R`, an `R`-algebra `S`
killed by `N`, and an `R`-algebra `H` with an isomorphism `e : H ⧸ N H ≅ S^∧` onto the
`(f)`-adic completion of `S`. For a finite set `s` of indices write `r_s = ∏_{i ∈ s} f i`,
`S_s = S[1 / r_s]` and `H_s = H[1 / r_s]`.

Given lifts `V_s` of the `S_s` across `R → R ⧸ N`, étale over `R` when `s` is nonempty, this file
constructs the transition maps `σ_{s,t} : V_s → V_t` and the maps `ρ_s : V_s → H_s`, as the
unique lifts of `S_s → S_t` and of `S_s → H_s ⧸ N H_s`.

## Main definitions

* `Rig.SquareZeroLift.NilLift`: a lift of an `R`-algebra across `R → R ⧸ N`.
* `Rig.SquareZeroLift.sig`: the transition maps `σ_{s,t}`.
* `Rig.SquareZeroLift.rho`: the maps `ρ_s : V_s → H_s`.

## Main results

* `Rig.SquareZeroLift.sig_sig`: `σ_{t,w} ∘ σ_{s,t} = σ_{s,w}`.
* `Rig.SquareZeroLift.rho_sig`: `ρ_t ∘ σ_{s,t}` is `ρ_s` followed by `H_s → H_t`.
-/

@[expose] public section

namespace Rig.SquareZeroLift

open TensorProduct Cech FormalGlueing

universe u

/-- A lift of the `R`-algebra `C` across `R → R ⧸ N`: an `R`-algebra `V` with a surjection onto
`C` whose kernel is `N V`. -/
structure NilLift (R : Type u) [CommRing R] (N : Ideal R) (C : Type u) [CommRing C]
    [Algebra R C] where
  /-- The lifted algebra. -/
  carrier : Type u
  [commRing : CommRing carrier]
  [algebra : Algebra R carrier]
  /-- The reduction map. -/
  ψ : carrier →ₐ[R] C
  surj : Function.Surjective ψ
  ker : RingHom.ker ψ.toRingHom = N.map (algebraMap R carrier)

attribute [instance] NilLift.commRing NilLift.algebra

section General

variable {R : Type u} [CommRing R] (N : Ideal R) (hN : N ^ 2 = ⊥)

include hN in
/-- If `N ^ 2 = 0` then the ideal `N B` of an `R`-algebra `B` is nilpotent. -/
theorem isNilpotent_map (B : Type*) [CommRing B] [Algebra R B] :
    IsNilpotent (N.map (algebraMap R B)) :=
  ⟨2, by rw [← Ideal.map_pow, hN, Ideal.map_bot, Ideal.zero_eq_bot]⟩

include hN in
/-- If `N ^ 2 = 0` then `(N B) ^ 2 = 0` for every `R`-algebra `B`. -/
theorem map_sq_eq_bot (B : Type*) [CommRing B] [Algebra R B] :
    N.map (algebraMap R B) ^ 2 = ⊥ := by
  rw [← Ideal.map_pow, hN, Ideal.map_bot]

/-- The reduction of a lift is its target. -/
noncomputable def NilLift.qe {C : Type u} [CommRing C] [Algebra R C] (L : NilLift R N C) :
    (L.carrier ⧸ N.map (algebraMap R L.carrier)) ≃ₐ[R] C :=
  (Ideal.quotientEquivAlgOfEq R L.ker.symm).trans (Ideal.quotientKerAlgEquivOfSurjective L.surj)

/-- The isomorphism `NilLift.qe` sends the class of `v` to `ψ v`. -/
@[simp]
theorem NilLift.qe_mk {C : Type u} [CommRing C] [Algebra R C] (L : NilLift R N C)
    (v : L.carrier) : L.qe N (Ideal.Quotient.mk _ v) = L.ψ v := by
  simp only [NilLift.qe]
  rfl

/-- Two elements of a lift are congruent modulo `N V` if and only if they have the same
reduction. -/
theorem NilLift.mk_eq_mk_iff {C : Type u} [CommRing C] [Algebra R C] (L : NilLift R N C)
    (v w : L.carrier) :
    Ideal.Quotient.mk (N.map (algebraMap R L.carrier)) v = Ideal.Quotient.mk _ w ↔
      L.ψ v = L.ψ w := by
  rw [← L.qe_mk N, ← L.qe_mk N, (L.qe N).injective.eq_iff]

/-- An element of a lift lies in `N V` if and only if its reduction vanishes. -/
theorem NilLift.mem_iff {C : Type u} [CommRing C] [Algebra R C] (L : NilLift R N C)
    (v : L.carrier) : v ∈ N.map (algebraMap R L.carrier) ↔ L.ψ v = 0 := by
  rw [← L.ker]
  rfl

include hN in
/-- If `N ^ 2 = 0`, an element of a lift whose reduction is a unit is itself a unit. -/
theorem NilLift.isUnit {C : Type u} [CommRing C] [Algebra R C] (L : NilLift R N C)
    {v : L.carrier} (h : IsUnit (L.ψ v)) : IsUnit v := by
  apply isUnit_of_isUnit_quotient _ (map_sq_eq_bot N hN L.carrier)
  rw [← L.qe_mk N] at h
  simpa only [AlgEquiv.symm_apply_apply] using h.map (L.qe N).symm

/-- The reduction `B ⧸ N B → B_r ⧸ N B_r` of a localization is a localization. -/
theorem isLocalizedModule_redMap (r : R) {B : Type*} [CommRing B] [Algebra R B]
    (Br : Type*) [CommRing Br] [Algebra R Br] [Algebra B Br] [IsScalarTower R B Br]
    [IsLocalization.Away (algebraMap R B r) Br] :
    IsLocalizedModule (Submonoid.powers r)
      (redMap N (IsScalarTower.toAlgHom R B Br)).toLinearMap := by
  have hunit : ∀ n : ℕ, IsUnit (algebraMap R Br (r ^ n)) := fun n ↦ by
    rw [IsScalarTower.algebraMap_apply R B Br, map_pow, map_pow]
    exact (IsLocalization.Away.algebraMap_isUnit (algebraMap R B r)).pow n
  constructor
  · rintro ⟨_, n, rfl⟩
    apply isUnit_end_of_isUnit
    rw [IsScalarTower.algebraMap_apply R Br (Br ⧸ _)]
    exact (hunit n).map _
  · intro y
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨⟨b, ⟨_, n, rfl⟩⟩, hb⟩ := IsLocalization.surj (Submonoid.powers (algebraMap R B r)) z
    refine ⟨⟨Ideal.Quotient.mk _ b, ⟨r ^ n, n, rfl⟩⟩, ?_⟩
    have hb' : z * algebraMap R Br (r ^ n) = algebraMap B Br b := by
      rw [IsScalarTower.algebraMap_apply R B Br, map_pow]
      exact hb
    simp only [Submonoid.smul_def, AlgHom.toLinearMap_apply, redMap_mk,
      IsScalarTower.coe_toAlgHom', Algebra.smul_def]
    rw [IsScalarTower.algebraMap_apply R Br (Br ⧸ _), Ideal.Quotient.algebraMap_eq, ← map_mul,
      mul_comm, hb']
  · intro x₁ x₂ h
    obtain ⟨b₁, rfl⟩ := Ideal.Quotient.mk_surjective x₁
    obtain ⟨b₂, rfl⟩ := Ideal.Quotient.mk_surjective x₂
    simp only [AlgHom.toLinearMap_apply, redMap_mk, IsScalarTower.coe_toAlgHom'] at h
    have hmem : algebraMap B Br (b₁ - b₂) ∈
        (N.map (algebraMap R B)).map (algebraMap B Br) := by
      rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq, map_sub]
      exact Ideal.Quotient.eq.mp h
    obtain ⟨⟨⟨a, ha⟩, ⟨_, m, rfl⟩⟩, hm⟩ :=
      (IsLocalization.mem_map_algebraMap_iff (Submonoid.powers (algebraMap R B r)) Br).mp hmem
    simp only at hm
    rw [← map_mul] at hm
    obtain ⟨⟨_, c, rfl⟩, hc⟩ := (IsLocalization.eq_iff_exists
      (Submonoid.powers (algebraMap R B r)) Br).mp hm
    refine ⟨⟨r ^ (c + m), c + m, rfl⟩, ?_⟩
    simp only [Submonoid.smul_def, Algebra.smul_def]
    rw [IsScalarTower.algebraMap_apply R B (B ⧸ _), Ideal.Quotient.algebraMap_eq, ← map_mul,
      ← map_mul, Ideal.Quotient.eq, ← mul_sub]
    have : algebraMap R B (r ^ (c + m)) * (b₁ - b₂) =
        (algebraMap R B r) ^ c * ((b₁ - b₂) * algebraMap R B r ^ m) := by
      rw [map_pow]
      ring
    rw [this, hc]
    exact Ideal.mul_mem_left _ _ ha

/-- Two `R`-algebra maps out of a formally unramified algebra into `B` which agree modulo `N B`
agree. -/
private theorem apply_eq_of_mk_eq (hN : N ^ 2 = ⊥) {A B : Type*} [CommRing A] [Algebra R A]
    [Algebra.FormallyUnramified R A] [CommRing B] [Algebra R B] (f g : A →ₐ[R] B)
    (h : ∀ x, Ideal.Quotient.mk (N.map (algebraMap R B)) (f x) = Ideal.Quotient.mk _ (g x))
    (v : A) : f v = g v :=
  AlgHom.congr_fun (Algebra.FormallyUnramified.ext _ (isNilpotent_map N hN B) h) v

end General

variable {R : Type u} [CommRing R] (N : Ideal R) (hN : N ^ 2 = ⊥)
variable {k : ℕ} (f : Fin k → R)

/-- The product `r_s = ∏_{i ∈ s} f i`. -/
def rs (s : Finset (Fin k)) : R := ∏ i ∈ s, f i

/-- If `s ⊆ t` then `r_s` divides `r_t`. -/
theorem rs_dvd {s t : Finset (Fin k)} (h : s ⊆ t) : rs f s ∣ rs f t :=
  Finset.prod_dvd_prod_of_subset _ _ _ h

variable (S : Type u) [CommRing S] [Algebra R S]

/-- The localization `S_s = S[1 / r_s]`. -/
abbrev Sl (s : Finset (Fin k)) := Localization.Away (algebraMap R S (rs f s))

/-- The images of the `f i` in `S`. -/
def gS : Fin k → S := fun i ↦ algebraMap R S (f i)

/-- The product of the images in `S` of the `f i`, `i ∈ s`, is the image of `r_s`. -/
theorem prod_gS (s : Finset (Fin k)) : ∏ i ∈ s, gS f S i = algebraMap R S (rs f s) :=
  (map_prod (algebraMap R S) f s).symm

/-- The transition maps `S_s → S_t`. -/
noncomputable def locS {s t : Finset (Fin k)} (h : s ⊆ t) : Sl f S s →ₐ[R] Sl f S t :=
  (IsLocalization.Away.liftAlgHom (algebraMap R S (rs f s)) (f := Algebra.ofId S (Sl f S t))
    (IsLocalization.Away.isUnit_of_dvd _ (map_dvd _ (rs_dvd f h)))).restrictScalars R

/-- The transition map `S_s → S_t` is compatible with the localization maps from `S`. -/
@[simp]
theorem locS_algebraMap {s t : Finset (Fin k)} (h : s ⊆ t) (a : S) :
    locS f S h (algebraMap S _ a) = algebraMap S _ a := by
  simp [locS]

/-- The composite of the transition maps `S_s → S_t → S_w` is the transition map `S_s → S_w`. -/
theorem locS_locS {s t w : Finset (Fin k)} (h : s ⊆ t) (h' : t ⊆ w) (x : Sl f S s) :
    locS f S h' (locS f S h x) = locS f S (h.trans h') x := by
  have : ((locS f S h').comp (locS f S h)).toRingHom = (locS f S (h.trans h')).toRingHom :=
    IsLocalization.ringHom_ext (Submonoid.powers (algebraMap R S (rs f s)))
      (RingHom.ext fun a ↦ by simp)
  exact RingHom.congr_fun this x

variable (H : Type u) [CommRing H] [Algebra R H]

/-- The localization `H_s = H[1 / r_s]`. -/
abbrev Hl (s : Finset (Fin k)) := Localization.Away (algebraMap R H (rs f s))

/-- The transition maps `H_s → H_t`. -/
noncomputable def locH {s t : Finset (Fin k)} (h : s ⊆ t) : Hl f H s →ₐ[H] Hl f H t :=
  IsLocalization.Away.liftAlgHom (algebraMap R H (rs f s)) (f := Algebra.ofId H (Hl f H t))
    (IsLocalization.Away.isUnit_of_dvd _ (map_dvd _ (rs_dvd f h)))

/-- The transition map `H_s → H_t` is compatible with the localization maps from `H`. -/
@[simp]
theorem locH_algebraMap {s t : Finset (Fin k)} (h : s ⊆ t) (a : H) :
    locH f H h (algebraMap H _ a) = algebraMap H _ a := by
  simp [locH]

/-- The composite `H → H_s → H_t` is the localization map `H → H_t`, as `R`-algebra maps. -/
theorem locH_comp_toAlgHom {s t : Finset (Fin k)} (h : s ⊆ t) :
    ((locH f H h).restrictScalars R).comp (IsScalarTower.toAlgHom R H (Hl f H s)) =
      IsScalarTower.toAlgHom R H (Hl f H t) := by
  ext a
  simp

/-- The composite of the transition maps `H_s → H_t → H_w` is the transition map `H_s → H_w`. -/
theorem locH_locH {s t w : Finset (Fin k)} (h : s ⊆ t) (h' : t ⊆ w) (x : Hl f H s) :
    locH f H h' (locH f H h x) = locH f H (h.trans h') x := by
  have : (locH f H h').comp (locH f H h) = locH f H (h.trans h') :=
    IsLocalization.algHom_ext (Submonoid.powers (algebraMap R H (rs f s))) (by ext)
  exact AlgHom.congr_fun this x

/-- The completion `S^∧` of `S` along `(f)`. -/
abbrev Sh := AdicCompletion ((Ideal.span (Set.range f)).map (algebraMap R S)) S

variable (e : (H ⧸ N.map (algebraMap R H)) ≃ₐ[R] Sh f S)

/-- The reduction of the localization map `H → H_s`. -/
noncomputable def redH (s : Finset (Fin k)) :
    H ⧸ N.map (algebraMap R H) →ₐ[R] Hl f H s ⧸ N.map (algebraMap R (Hl f H s)) :=
  redMap N (IsScalarTower.toAlgHom R H (Hl f H s))

/-- The map `S^∧ → H_s ⧸ N H_s`. -/
noncomputable def lamH (s : Finset (Fin k)) :
    Sh f S →ₐ[R] Hl f H s ⧸ N.map (algebraMap R (Hl f H s)) :=
  (redH N f H s).comp e.symm.toAlgHom

/-- The element `r_s` is a unit in `H_s`. -/
theorem isUnit_Hl (s : Finset (Fin k)) : IsUnit (algebraMap R (Hl f H s) (rs f s)) := by
  rw [IsScalarTower.algebraMap_apply R H (Hl f H s)]
  exact IsLocalization.Away.algebraMap_isUnit _

/-- The image of `r_s` under `S → S^∧ → H_s ⧸ N H_s` is a unit. -/
theorem isUnit_lamH (s : Finset (Fin k)) :
    IsUnit (((lamH N f S H e s).comp (IsScalarTower.toAlgHom R S (Sh f S)))
      (algebraMap R S (rs f s))) := by
  rw [AlgHom.commutes]
  have h2 := (isUnit_Hl f H s).map (Ideal.Quotient.mkₐ R (N.map (algebraMap R (Hl f H s))))
  rwa [AlgHom.commutes] at h2

/-- The map `S_s → H_s ⧸ N H_s`. -/
noncomputable def chi (s : Finset (Fin k)) :
    Sl f S s →ₐ[R] Hl f H s ⧸ N.map (algebraMap R (Hl f H s)) :=
  IsLocalization.Away.liftAlgHom (algebraMap R S (rs f s))
    (f := (lamH N f S H e s).comp (IsScalarTower.toAlgHom R S (Sh f S)))
    (isUnit_lamH N f S H e s)

/-- On the image of `a ∈ S`, the map `S_s → H_s ⧸ N H_s` is given by `S → S^∧ → H_s ⧸ N H_s`. -/
@[simp]
theorem chi_algebraMap (s : Finset (Fin k)) (a : S) :
    chi N f S H e s (algebraMap S _ a) = lamH N f S H e s (algebraMap S (Sh f S) a) := by
  simp [chi, IsLocalization.Away.lift_eq]

/-- The maps `S_s → H_s ⧸ N H_s` commute with the transition maps `S_s → S_t` and the
reductions of `H_s → H_t`. -/
theorem redMap_locH_chi {s t : Finset (Fin k)} (h : s ⊆ t) :
    (redMap N ((locH f H h).restrictScalars R)).comp (chi N f S H e s) =
      (chi N f S H e t).comp (locS f S h) := by
  have key : ∀ a : S, redMap N ((locH f H h).restrictScalars R) (chi N f S H e s
      (algebraMap S _ a)) = chi N f S H e t (locS f S h (algebraMap S _ a)) := by
    intro a
    rw [chi_algebraMap, locS_algebraMap, chi_algebraMap]
    simp only [lamH, redH, AlgHom.comp_apply]
    obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (e.symm.toAlgHom (algebraMap S (Sh f S) a))
    rw [← hb, redMap_mk, redMap_mk, redMap_mk]
    simp
  exact AlgHom.coe_ringHom_injective <|
    IsLocalization.ringHom_ext (Submonoid.powers (algebraMap R S (rs f s))) (RingHom.ext key)

/-! ### The lifts and the maps between them -/

variable (L : ∀ s : Finset (Fin k), NilLift R N (Sl f S s))

/-- The map `S → V_s ⧸ N V_s`. -/
noncomputable def lam (s : Finset (Fin k)) :
    S →ₐ[R] (L s).carrier ⧸ N.map (algebraMap R (L s).carrier) :=
  ((L s).qe N).symm.toAlgHom.comp (IsScalarTower.toAlgHom R S (Sl f S s))

variable (hL : ∀ s, s.Nonempty → Algebra.Etale R (L s).carrier)

/-- The transition maps `σ_{s,t} : V_s → V_t`, the unique lifts of `S_s → S_t`. -/
noncomputable def sig {s t : Finset (Fin k)} (h : s ⊆ t) (hs : s.Nonempty) :
    (L s).carrier →ₐ[R] (L t).carrier :=
  haveI := hL s hs
  Algebra.FormallySmooth.lift _ (isNilpotent_map N hN _)
    (((L t).qe N).symm.toAlgHom.comp ((locS f S h).comp (L s).ψ))

/-- The reduction modulo `N V_t` of `σ_{s,t} v` corresponds to the image of `ψ v` in `S_t`. -/
theorem mk_sig {s t : Finset (Fin k)} (h : s ⊆ t) (hs : s.Nonempty) (v : (L s).carrier) :
    Ideal.Quotient.mk _ (sig N hN f S L hL h hs v) =
      ((L t).qe N).symm (locS f S h ((L s).ψ v)) := by
  have := hL s hs
  exact Algebra.FormallySmooth.mk_lift _ _ _ v

/-- The transition map `σ_{s,t}` lifts the transition map `S_s → S_t`. -/
theorem psi_sig {s t : Finset (Fin k)} (h : s ⊆ t) (hs : s.Nonempty) (v : (L s).carrier) :
    (L t).ψ (sig N hN f S L hL h hs v) = locS f S h ((L s).ψ v) := by
  rw [← (L t).qe_mk N, mk_sig, AlgEquiv.apply_symm_apply]

/-- The transition maps compose: `σ_{t,w} ∘ σ_{s,t} = σ_{s,w}`. -/
theorem sig_sig {s t w : Finset (Fin k)} (h : s ⊆ t) (h' : t ⊆ w) (hs : s.Nonempty)
    (v : (L s).carrier) :
    sig N hN f S L hL h' (hs.mono h) (sig N hN f S L hL h hs v) =
      sig N hN f S L hL (h.trans h') hs v := by
  have := hL s hs
  refine apply_eq_of_mk_eq N hN ((sig N hN f S L hL h' (hs.mono h)).comp (sig N hN f S L hL h hs))
    (sig N hN f S L hL (h.trans h') hs) (fun x ↦ ?_) v
  rw [AlgHom.comp_apply, (L w).mk_eq_mk_iff, psi_sig, psi_sig, psi_sig]
  exact locS_locS f S h h' _

/-- The transition map `σ_{s,t}` sends `N V_s` into `N V_t`. -/
theorem sig_mem {s t : Finset (Fin k)} (h : s ⊆ t) (hs : s.Nonempty) {v : (L s).carrier}
    (hv : v ∈ N.map (algebraMap R (L s).carrier)) :
    sig N hN f S L hL h hs v ∈ N.map (algebraMap R (L t).carrier) := by
  rw [NilLift.mem_iff] at hv ⊢
  rw [psi_sig, hv, map_zero]

/-- The maps `ρ_s : V_s → H_s`, the unique lifts of `S_s → H_s ⧸ N H_s`. -/
noncomputable def rho (s : Finset (Fin k)) (hs : s.Nonempty) : (L s).carrier →ₐ[R] Hl f H s :=
  haveI := hL s hs
  Algebra.FormallySmooth.lift _ (isNilpotent_map N hN _) ((chi N f S H e s).comp (L s).ψ)

/-- The map `ρ_s` lifts `S_s → H_s ⧸ N H_s`: the class of `ρ_s v` is the image of `ψ v`. -/
theorem mk_rho (s : Finset (Fin k)) (hs : s.Nonempty) (v : (L s).carrier) :
    Ideal.Quotient.mk _ (rho N hN f S H e L hL s hs v) = chi N f S H e s ((L s).ψ v) := by
  have := hL s hs
  exact Algebra.FormallySmooth.mk_lift _ _ _ v

/-- The maps `ρ` commute with the transition maps: `ρ_t ∘ σ_{s,t}` is `ρ_s` followed by
`H_s → H_t`. -/
theorem rho_sig {s t : Finset (Fin k)} (h : s ⊆ t) (hs : s.Nonempty) (v : (L s).carrier) :
    rho N hN f S H e L hL t (hs.mono h) (sig N hN f S L hL h hs v) =
      locH f H h (rho N hN f S H e L hL s hs v) := by
  have := hL s hs
  refine apply_eq_of_mk_eq N hN ((rho N hN f S H e L hL t (hs.mono h)).comp
    (sig N hN f S L hL h hs)) (((locH f H h).restrictScalars R).comp
    (rho N hN f S H e L hL s hs)) (fun x ↦ ?_) v
  rw [AlgHom.comp_apply, AlgHom.comp_apply, mk_rho, psi_sig]
  have h1 := AlgHom.congr_fun (redMap_locH_chi N f S H e h) ((L s).ψ x)
  rw [AlgHom.comp_apply, AlgHom.comp_apply] at h1
  rw [← h1, ← mk_rho N hN f S H e L hL s hs x]
  rfl

/-- The map `ρ_s` sends `N V_s` into `N H_s`. -/
theorem rho_mem (s : Finset (Fin k)) (hs : s.Nonempty) {v : (L s).carrier}
    (hv : v ∈ N.map (algebraMap R (L s).carrier)) :
    rho N hN f S H e L hL s hs v ∈ N.map (algebraMap R (Hl f H s)) := by
  rw [NilLift.mem_iff] at hv
  rw [← Ideal.Quotient.eq_zero_iff_mem, mk_rho, hv, map_zero]

end Rig.SquareZeroLift

end
