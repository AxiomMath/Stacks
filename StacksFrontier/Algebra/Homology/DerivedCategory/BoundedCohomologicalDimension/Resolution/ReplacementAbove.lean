module

public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedCohomologicalDimension.Resolution.Coresolution

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Resolutions by objects of bounded cohomological dimension: replacement above a degree

The replacement of all degrees `≥ m` by objects of `d`-value `0`, the reduction to finite
`d`-values, degreewise eventually constant replacement data, and the single step of the
descent on the greatest contribution `n + d (K.X n)`.

## Main definitions

* `DegreewiseECData`: a sequence of quasi-isomorphisms which is degreewise eventually constant.
* `XiDescent.stepC`, `XiDescent.stepF`: one step of the descent.

## Main results

* `exists_dZero_above`: a quasi-isomorphism making all degrees `≥ m` of `d`-value `0`.
* `exists_finite_d_qis`: a quasi-isomorphism to a complex with finite `d`-values.

## References

* [Stacks: Tag 07K6](https://stacks.math.columbia.edu/tag/07K6)
-/

open CategoryTheory CategoryTheory.Limits ZeroObject

namespace Stacks.BoundedCohomologicalDimension

variable {A : Type*} [Category A] [Abelian A]

namespace AboveConstruction

open ElemReplConstruction

/-- One elementary-replacement step at degree `n`: `L` itself if `d (L.X n) = 0`, and
otherwise the replacement complex `Kp` along a chosen embedding of `L.X n` into an object
of `d`-value `0`. -/
noncomputable def stepC (d : A → ℕ∞) (hd : BoundedCohomologicalDimension d)
    (L : CochainComplex A ℤ) (n : ℤ) : CochainComplex A ℤ :=
  if 0 < d (L.X n) then Kp L n (hd.embed (L.X n)).choose (hd.embed (L.X n)).choose_spec.choose
  else L

/-- The comparison map of one step. -/
noncomputable def stepF (d : A → ℕ∞) (hd : BoundedCohomologicalDimension d)
    (L : CochainComplex A ℤ) (n : ℤ) : L ⟶ stepC d hd L n :=
  if h0 : 0 < d (L.X n) then
    (fmap L n (hd.embed (L.X n)).choose (hd.embed (L.X n)).choose_spec.choose) ≫
      eqToHom
        (by
          unfold stepC; rw [ite_eq_left h0])
  else
    eqToHom
      (by
        unfold stepC; rw [ite_eq_right h0])

/-- Each step is a quasi-isomorphism. -/
theorem stepF_quasiIso (d : A → ℕ∞) (hd : BoundedCohomologicalDimension d) (L : CochainComplex A ℤ)
    (n : ℤ) : QuasiIso (stepF d hd L n) := by
  unfold stepF
  by_cases h0 : 0 < d (L.X n)
  · rw [dite_eq_left h0]
    have hc := (hd.embed (L.X n)).choose_spec.choose_spec
    have hq :
      QuasiIso (fmap L n (hd.embed (L.X n)).choose (hd.embed (L.X n)).choose_spec.choose) := by
      have :=
        elemReplBuild_quasiIso d L n (hd.embed (L.X n)).choose
          (hd.embed (L.X n)).choose_spec.choose hc.1
      simpa only [elemReplBuild] using this
    have := hq
    infer_instance
  · rw [dite_eq_right h0]; infer_instance

/-- Object freezing off the touched degrees. -/
theorem stepC_X_off (d : A → ℕ∞) (hd : BoundedCohomologicalDimension d) (L : CochainComplex A ℤ)
    (n j : ℤ) (h1 : j ≠ n) (h2 : j ≠ n + 1) : (stepC d hd L n).X j = L.X j := by
  unfold stepC
  by_cases h0 : 0 < d (L.X n)
  · rw [ite_eq_left h0]; exact XX_off L n _ _ j h1 h2
  · rw [ite_eq_right h0]

/-- The touched degree `n` is cleared to `d = 0`. -/
theorem stepC_dX_n (d : A → ℕ∞) (hd : BoundedCohomologicalDimension d) (L : CochainComplex A ℤ)
    (n : ℤ) : d ((stepC d hd L n).X n) = 0 := by
  unfold stepC
  by_cases h0 : 0 < d (L.X n)
  · rw [ite_eq_left h0]
    change d (XX L n _ _ n) = 0
    rw [XX_n]
    exact (hd.embed (L.X n)).choose_spec.choose_spec.2
  · rw [ite_eq_right h0]
    simpa only [not_lt, nonpos_iff_eq_zero] using h0

variable (d : A → ℕ∞) (hd : BoundedCohomologicalDimension d) (K : CochainComplex A ℤ) (m : ℤ)

/-- The recursive resolution sequence: `Kseq 0 = K`, and `Kseq (k+1)` clears degree
`m + k` of `Kseq k`. -/
noncomputable def Kseq : ℕ → CochainComplex A ℤ := fun k =>
  Nat.rec K (fun j prev => stepC d hd prev (m + (j : ℤ))) k

/-- The `0`-th stage is `K`. -/
@[simp]
lemma Kseq_zero : Kseq d hd K m 0 = K :=
  rfl

/-- The `(k + 1)`-st stage is `stepC` applied to the `k`-th stage at degree `m + k`. -/
lemma Kseq_succ (k : ℕ) : Kseq d hd K m (k + 1) = stepC d hd (Kseq d hd K m k) (m + (k : ℤ)) :=
  rfl

/-- The comparison map of the `k`-th stage. -/
noncomputable def Kstep (k : ℕ) : Kseq d hd K m k ⟶ Kseq d hd K m (k + 1) :=
  stepF d hd (Kseq d hd K m k) (m + (k : ℤ))

/-- Each stage comparison map `Kstep` is a quasi-isomorphism. -/
lemma Kstep_quasiIso (k : ℕ) : QuasiIso (Kstep d hd K m k) :=
  stepF_quasiIso d hd (Kseq d hd K m k) (m + (k : ℤ))

/-- Degree `j` is frozen by stage `k+1` whenever the step at stage `k` (degree `m+k`)
does not touch it, i.e. `j < m + k`. -/
lemma Kseq_X_succ_off (k : ℕ) (j : ℤ) (h : j < m + (k : ℤ)) :
    (Kseq d hd K m (k + 1)).X j = (Kseq d hd K m k).X j := by
  rw [Kseq_succ]
  exact stepC_X_off d hd (Kseq d hd K m k) (m + (k : ℤ)) j (by omega) (by omega)

/-- For `j < m + s` and `s ≤ t`, the objects `(Kseq t).X j` and `(Kseq s).X j` are equal. -/
lemma Kseq_X_stable (j : ℤ) (s t : ℕ) (hs : j < m + (s : ℤ)) (hst : s ≤ t) :
    (Kseq d hd K m t).X j = (Kseq d hd K m s).X j := by
  induction t with
  | zero =>
    obtain rfl : s = 0 := by omega
    rfl
  | succ t ih =>
    rcases Nat.lt_or_ge s (t + 1) with h | h
    · have hst' : s ≤ t := by omega
      rw [Kseq_X_succ_off d hd K m t j (by omega), ih hst']
    · have : s = t + 1 := by omega
      rw [this]

/-- The freezing stage of degree `j`: smallest `s` with `j < m + s` for `j ≥ m`
(namely `(j-m).toNat + 1`), and `0` for `j < m` (never touched). -/
def stage (m j : ℤ) : ℕ :=
  if m ≤ j then (j - m).toNat + 1 else 0

/-- Every degree `j` satisfies `j < m + stage m j`. -/
lemma stage_lt (m j : ℤ) : j < m + (stage m j : ℤ) := by
  unfold stage
  by_cases h : m ≤ j
  · rw [ite_eq_left h]; push_cast; omega
  · rw [ite_eq_right h]; push_cast; omega

/-- The freezing stage `stage m j` is monotone in `j`. -/
lemma stage_mono (m : ℤ) {j j' : ℤ} (h : j ≤ j') : stage m j ≤ stage m j' := by
  unfold stage
  by_cases hj : m ≤ j
  · rw [ite_eq_left hj, ite_eq_left (by omega)]; omega
  · rw [ite_eq_right hj]; omega

/-- Objects of the diagonal frozen complex. -/
noncomputable def PX (j : ℤ) : A :=
  (Kseq d hd K m (stage m j)).X j

/-- For any stage `s` past `j`'s freezing stage, `(Kseq s).X j = PX j`. -/
lemma Kseq_X_eq_PX (j : ℤ) (s : ℕ) (hs : stage m j ≤ s) :
    (Kseq d hd K m s).X j = PX d hd K m j := by
  unfold PX
  exact Kseq_X_stable d hd K m j (stage m j) s (stage_lt m j) hs

/-- Differential freezing for one step: off `{n-1, n, n+1}` the differential of
`stepC` is the differential of `L`, conjugated by the object-freezing identifications. -/
lemma stepC_d_off (L : CochainComplex A ℤ) (n j : ℤ) (hA : j ≠ n - 1) (hB : j ≠ n) (hC : j ≠ n + 1)
    (h1 : (stepC d hd L n).X j = L.X j) (h2 : L.X (j + 1) = (stepC d hd L n).X (j + 1)) :
    (stepC d hd L n).d j (j + 1) = eqToHom h1 ≫ L.d j (j + 1) ≫ eqToHom h2 := by
  revert h1 h2
  unfold stepC
  by_cases h0 : 0 < d (L.X n)
  · rw [ite_eq_left h0]
    intro h1 h2
    set M := (hd.embed (L.X n)).choose
    set ι := (hd.embed (L.X n)).choose_spec.choose
    change Kd L n M ι j (j + 1) = _
    rw [show Kd L n M ι j (j + 1) = dd L n M ι j ≫ eqToHom rfl from by
        unfold Kd; rw [dite_eq_left rfl]]
    unfold dd
    rw [dite_eq_right hA, dite_eq_right hB, dite_eq_right hC]
    simp only [eqToHom_refl, Category.comp_id]
  · rw [ite_eq_right h0]
    intro h1 h2
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

/-- Differential stability across stages: for `s ≤ t` with `j + 1 < m + s` (both `j` and
`j+1` past their differential-freezing point), the differential `d j (j+1)` of `Kseq t`
agrees with that of `Kseq s` up to the object-freezing identifications. -/
lemma Kseq_d_stable (j : ℤ) (s t : ℕ) (hs : j + 1 < m + (s : ℤ)) (hst : s ≤ t)
    (h1 : (Kseq d hd K m t).X j = (Kseq d hd K m s).X j)
    (h2 : (Kseq d hd K m s).X (j + 1) = (Kseq d hd K m t).X (j + 1)) :
    (Kseq d hd K m t).d j (j + 1) = eqToHom h1 ≫ (Kseq d hd K m s).d j (j + 1) ≫ eqToHom h2 := by
  induction t with
  | zero =>
    obtain rfl : s = 0 := by omega
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  | succ t ih =>
    rcases Nat.lt_or_ge s (t + 1) with hlt | hge
    · have hst' : s ≤ t := by omega
      have e1 : (Kseq d hd K m t).X j = (Kseq d hd K m s).X j :=
        Kseq_X_stable d hd K m j s t (by omega) hst'
      have e2 : (Kseq d hd K m s).X (j + 1) = (Kseq d hd K m t).X (j + 1) :=
        (Kseq_X_stable d hd K m (j + 1) s t (by omega) hst').symm
      have key :
        (Kseq d hd K m (t + 1)).d j (j + 1) =
          eqToHom (Kseq_X_succ_off d hd K m t j (by omega)) ≫
            (Kseq d hd K m t).d j (j + 1) ≫
            eqToHom (Kseq_X_succ_off d hd K m t (j + 1) (by omega)).symm := by
        exact
          stepC_d_off d hd (Kseq d hd K m t) (m + (t : ℤ)) j (by omega) (by omega) (by omega) _ _
      rw [key, ih hst' e1 e2]
      simp only [Category.assoc, eqToHom_trans, eqToHom_trans_assoc]
    · obtain rfl : s = t + 1 := by omega
      simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

/-- The successor differential of the diagonal complex, read off the common freezing
stage `stage m (j+1)`. -/
noncomputable def Pdsucc (j : ℤ) : PX d hd K m j ⟶ PX d hd K m (j + 1) :=
  eqToHom (Kseq_X_eq_PX d hd K m j (stage m (j + 1)) (stage_mono m (by omega))).symm ≫
    (Kseq d hd K m (stage m (j + 1))).d j (j + 1) ≫
    eqToHom (Kseq_X_eq_PX d hd K m (j + 1) (stage m (j + 1)) le_rfl)

/-- `Pdsucc` computed at any sufficiently large stage `s`. -/
lemma Pdsucc_eq (j : ℤ) (s : ℕ) (hs : stage m (j + 1) ≤ s) :
    Pdsucc d hd K m j =
      eqToHom (Kseq_X_eq_PX d hd K m j s (le_trans (stage_mono m (by omega)) hs)).symm ≫
        (Kseq d hd K m s).d j (j + 1) ≫ eqToHom (Kseq_X_eq_PX d hd K m (j + 1) s hs) := by
  unfold Pdsucc
  have hstab :=
    Kseq_d_stable d hd K m j (stage m (j + 1)) s (stage_lt m (j + 1)) hs
      (by
        rw [Kseq_X_eq_PX d hd K m j s (le_trans (stage_mono m (by omega)) hs),
          Kseq_X_eq_PX d hd K m j (stage m (j + 1)) (stage_mono m (by omega))])
      (by
        rw [Kseq_X_eq_PX d hd K m (j + 1) (stage m (j + 1)) le_rfl,
          Kseq_X_eq_PX d hd K m (j + 1) s hs])
  rw [hstab]
  simp only [Category.assoc, eqToHom_trans, eqToHom_trans_assoc]

/-- The full differential of the diagonal complex. -/
noncomputable def Pd (i j : ℤ) : PX d hd K m i ⟶ PX d hd K m j :=
  if h : j = i + 1 then Pdsucc d hd K m i ≫ eqToHom (by rw [h]) else 0

/-- Two consecutive differentials `Pd` compose to zero. -/
lemma Pd_dd (i j k : ℤ) (hij : (ComplexShape.up ℤ).Rel i j) (hjk : (ComplexShape.up ℤ).Rel j k) :
    Pd d hd K m i j ≫ Pd d hd K m j k = 0 := by
  simp only [ComplexShape.up_Rel] at hij hjk
  subst hij hjk
  unfold Pd
  rw [dite_eq_left rfl, dite_eq_left rfl]
  set s := stage m (i + 1 + 1) with hs_def
  have hsi1 : stage m (i + 1) ≤ s := stage_mono m (by omega)
  rw [Pdsucc_eq d hd K m i s hsi1, Pdsucc_eq d hd K m (i + 1) s le_rfl]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp, Category.comp_id,
    HomologicalComplex.d_comp_d, comp_zero]

/-- The diagonal frozen complex `K'`. -/
noncomputable def Pcomplex : CochainComplex A ℤ where
  X := PX d hd K m
  d := Pd d hd K m
  shape i j hij := by
    unfold Pd; rw [dite_eq_right]; intro h; apply hij; simp [ComplexShape.up_Rel]; omega
  d_comp_d' i j k hij hjk := Pd_dd d hd K m i j k hij hjk

/-- The objects of `Pcomplex d hd K m` are given by `PX`. -/
@[simp]
lemma Pcomplex_X (j : ℤ) : (Pcomplex d hd K m).X j = PX d hd K m j :=
  rfl

/-- Below the cut-off the diagonal complex is objectwise `K`. -/
lemma PX_below (j : ℤ) (h : j < m) : PX d hd K m j = K.X j := by
  unfold PX stage
  rw [ite_eq_right (by omega)]
  rfl

/-- At and above the cut-off the diagonal complex is `d`-acyclic. -/
lemma dPX_above (j : ℤ) (h : m ≤ j) : d (PX d hd K m j) = 0 := by
  unfold PX stage
  rw [ite_eq_left h]
  set k := (j - m).toNat with hk
  have hjk : j = m + (k : ℤ) := by
    rw [hk]; omega
  rw [Kseq_succ]
  rw [hjk]
  exact stepC_dX_n d hd (Kseq d hd K m k) (m + (k : ℤ))

/-- The composite comparison `K = Kseq 0 ⟶ Kseq s`. -/
noncomputable def Kcomp : (s : ℕ) → (K ⟶ Kseq d hd K m s)
  | 0 => 𝟙 K
  | (s + 1) => Kcomp s ≫ Kstep d hd K m s

/-- The composite comparison `Kcomp` is a quasi-isomorphism. -/
lemma Kcomp_quasiIso (s : ℕ) : QuasiIso (Kcomp d hd K m s) := by
  induction s with
  | zero =>
    unfold Kcomp; infer_instance
  | succ s ih =>
    unfold Kcomp
    have := ih
    have := Kstep_quasiIso d hd K m s
    exact quasiIso_comp _ _

/-- Off the touched degrees, the step comparison map is the freezing identification. -/
lemma stepF_f_off (L : CochainComplex A ℤ) (n j : ℤ) (hB : j ≠ n) (hC : j ≠ n + 1)
    (h : (stepC d hd L n).X j = L.X j) : (stepF d hd L n).f j = eqToHom h.symm := by
  unfold stepF
  by_cases h0 : 0 < d (L.X n)
  · rw [dite_eq_left h0]
    rw [HomologicalComplex.comp_f, HomologicalComplex.eqToHom_f]
    change ff L n _ _ j ≫ _ = _
    unfold ff
    rw [dite_eq_right hB, dite_eq_right hC]
    rw [eqToHom_trans]
  · rw [dite_eq_right h0]
    rw [HomologicalComplex.eqToHom_f]

/-- The composite comparison map is stable in each frozen degree. -/
lemma Kcomp_f_stable (j : ℤ) (s t : ℕ) (hs : j < m + (s : ℤ)) (hst : s ≤ t)
    (h : (Kseq d hd K m s).X j = (Kseq d hd K m t).X j) :
    (Kcomp d hd K m t).f j = (Kcomp d hd K m s).f j ≫ eqToHom h := by
  induction t with
  | zero =>
    obtain rfl : s = 0 := by omega
    simp only [eqToHom_refl, Category.comp_id]
  | succ t ih =>
    rcases Nat.lt_or_ge s (t + 1) with hlt | hge
    · have hst' : s ≤ t := by omega
      have e1 : (Kseq d hd K m s).X j = (Kseq d hd K m t).X j :=
        (Kseq_X_stable d hd K m j s t hs hst').symm
      change (Kcomp d hd K m t ≫ Kstep d hd K m t).f j = _
      rw [HomologicalComplex.comp_f, ih hst' e1]
      have hstepf :
        (Kstep d hd K m t).f j = eqToHom (Kseq_X_succ_off d hd K m t j (by omega)).symm := by
        unfold Kstep
        exact
          stepF_f_off d hd (Kseq d hd K m t) (m + (t : ℤ)) j (by omega) (by omega)
            (Kseq_X_succ_off d hd K m t j (by omega))
      rw [hstepf]
      simp only [Category.assoc, eqToHom_trans]
    · obtain rfl : s = t + 1 := by omega
      simp only [eqToHom_refl, Category.comp_id]

/-- The comparison chain map `g : K ⟶ K'` in each degree (before assembling). -/
noncomputable def gf (j : ℤ) : K.X j ⟶ PX d hd K m j :=
  (Kcomp d hd K m (stage m j)).f j ≫ eqToHom (Kseq_X_eq_PX d hd K m j (stage m j) le_rfl)

/-- `gf` computed at any sufficiently large stage. -/
lemma gf_eq (j : ℤ) (s : ℕ) (hs : stage m j ≤ s) :
    gf d hd K m j = (Kcomp d hd K m s).f j ≫ eqToHom (Kseq_X_eq_PX d hd K m j s hs) := by
  unfold gf
  have hstab :=
    Kcomp_f_stable d hd K m j (stage m j) s (stage_lt m j) hs
      (by rw [Kseq_X_eq_PX d hd K m j (stage m j) le_rfl, Kseq_X_eq_PX d hd K m j s hs])
  rw [hstab]
  simp only [Category.assoc, eqToHom_trans]

/-- The comparison map `gf` is a chain map. -/
lemma gf_comm (j : ℤ) :
    gf d hd K m j ≫ Pd d hd K m j (j + 1) = K.d j (j + 1) ≫ gf d hd K m (j + 1) := by
  set s := stage m (j + 1) with hs_def
  have hsj : stage m j ≤ s := stage_mono m (by omega)
  rw [gf_eq d hd K m j s hsj, gf_eq d hd K m (j + 1) s le_rfl]
  unfold Pd
  rw [dite_eq_left rfl, Pdsucc_eq d hd K m j s le_rfl]
  simp only [eqToHom_refl, Category.comp_id, Category.assoc, eqToHom_trans_assoc, Category.id_comp]
  exact (Kcomp d hd K m s).comm j (j + 1)

/-- The comparison chain map `g : K ⟶ K'`. -/
noncomputable def gmap : K ⟶ Pcomplex d hd K m where
  f := gf d hd K m
  comm' i j hij := by
    simp only [ComplexShape.up_Rel] at hij; subst hij
    exact gf_comm d hd K m i

/-- The windowed short complex of `Kseq s` at `[j-1, j, j+1]` is isomorphic to that of
`Pcomplex`, provided `s` freezes all three degrees (`stage m (j+1) ≤ s`). -/
noncomputable def scIso (j : ℤ) (s : ℕ) (hs : stage m (j + 1) ≤ s) :
    (HomologicalComplex.shortComplexFunctor' A (ComplexShape.up ℤ) (j - 1) j (j + 1)).obj
        (Kseq d hd K m s) ≅
      (HomologicalComplex.shortComplexFunctor' A (ComplexShape.up ℤ) (j - 1) j (j + 1)).obj
        (Pcomplex d hd K m) := by
  have hsm1 : stage m j ≤ s := le_trans (stage_mono m (by omega)) hs
  have hsm2 : stage m (j - 1) ≤ s := le_trans (stage_mono m (by omega)) hs
  refine
    ShortComplex.isoMk (eqToIso (Kseq_X_eq_PX d hd K m (j - 1) s hsm2))
      (eqToIso (Kseq_X_eq_PX d hd K m j s hsm1)) (eqToIso (Kseq_X_eq_PX d hd K m (j + 1) s hs)) ?_
      ?_
  · have hjj : (j - 1 + 1 : ℤ) = j := by ring
    change
      eqToHom (Kseq_X_eq_PX d hd K m (j - 1) s hsm2) ≫ Pd d hd K m (j - 1) j =
        (Kseq d hd K m s).d (j - 1) j ≫ eqToHom (Kseq_X_eq_PX d hd K m j s hsm1)
    unfold Pd
    rw [dite_eq_left (by omega)]
    rw [Pdsucc_eq d hd K m (j - 1) s
        (by
          rw [hjj]; exact hsm1)]
    simp only [eqToHom_trans, eqToHom_trans_assoc, Category.assoc, eqToHom_refl, Category.id_comp]
    have hd2 :
      (Kseq d hd K m s).d (j - 1) (j - 1 + 1) ≫
          eqToHom (show (Kseq d hd K m s).X (j - 1 + 1) = (Kseq d hd K m s).X j by rw [hjj]) =
        (Kseq d hd K m s).d (j - 1) j :=
      HomologicalComplex.d_comp_eqToHom _ (show (ComplexShape.up ℤ).Rel (j - 1) j by simp)
        (show (ComplexShape.up ℤ).Rel (j - 1) (j - 1 + 1) by simp)
    rw [← hd2, Category.assoc]
    simp only [eqToHom_trans]
  · change
      eqToHom (Kseq_X_eq_PX d hd K m j s hsm1) ≫ Pd d hd K m j (j + 1) =
        (Kseq d hd K m s).d j (j + 1) ≫ eqToHom (Kseq_X_eq_PX d hd K m (j + 1) s hs)
    unfold Pd
    rw [dite_eq_left rfl]
    rw [Pdsucc_eq d hd K m j s hs]
    simp only [eqToHom_trans_assoc, eqToHom_refl, Category.id_comp, Category.comp_id]

/-- The comparison map `gmap d hd K m` is a quasi-isomorphism. -/
theorem gmap_quasiIso : QuasiIso (gmap d hd K m) := by
  rw [quasiIso_iff]
  intro j
  rw [quasiIsoAt_iff' (gmap d hd K m) (j - 1) j (j + 1) (by simp) (by simp)]
  set s := stage m (j + 1) with hs_def
  have hsm1 : stage m j ≤ s := le_trans (stage_mono m (by omega)) le_rfl
  have hKcs : QuasiIsoAt (Kcomp d hd K m s) j := (quasiIso_iff _).mp (Kcomp_quasiIso d hd K m s) j
  rw [quasiIsoAt_iff' (Kcomp d hd K m s) (j - 1) j (j + 1) (by simp) (by simp)] at hKcs
  have := hKcs
  have hfact :
    (HomologicalComplex.shortComplexFunctor' A (ComplexShape.up ℤ) (j - 1) j (j + 1)).map
        (gmap d hd K m) =
      (HomologicalComplex.shortComplexFunctor' A (ComplexShape.up ℤ) (j - 1) j (j + 1)).map
          (Kcomp d hd K m s) ≫
        (scIso d hd K m j s le_rfl).hom := by
    apply ShortComplex.hom_ext
    · rw [ShortComplex.comp_τ₁]
      change gf d hd K m (j - 1) = (Kcomp d hd K m s).f (j - 1) ≫ _
      rw [gf_eq d hd K m (j - 1) s (le_trans (stage_mono m (by omega)) le_rfl)]
      congr 1
    · rw [ShortComplex.comp_τ₂]
      change gf d hd K m j = (Kcomp d hd K m s).f j ≫ _
      rw [gf_eq d hd K m j s hsm1]
      congr 1
    · rw [ShortComplex.comp_τ₃]
      change gf d hd K m (j + 1) = (Kcomp d hd K m s).f (j + 1) ≫ _
      rw [gf_eq d hd K m (j + 1) s le_rfl]
      congr 1
  rw [hfact]
  have : IsIso (scIso d hd K m j s le_rfl).hom := inferInstance
  infer_instance

end AboveConstruction

/-- For every `m`, there is a quasi-isomorphism `g : K ⟶ K'` with `d (K'.X n) = 0` for
`n ≥ m` and `d (K'.X n) = d (K.X n)` for `n < m`. -/
theorem exists_dZero_above (d : A → ℕ∞) (hd : BoundedCohomologicalDimension d)
    (K : CochainComplex A ℤ) (m : ℤ) :
    ∃ (K' : CochainComplex A ℤ) (g : K ⟶ K'),
      QuasiIso g ∧
        (∀ n : ℤ, m ≤ n → d (K'.X n) = 0) ∧ (∀ n : ℤ, n < m → d (K'.X n) = d (K.X n)) := by
  refine
    ⟨AboveConstruction.Pcomplex d hd K m, AboveConstruction.gmap d hd K m,
      AboveConstruction.gmap_quasiIso d hd K m, ?_, ?_⟩
  · intro n hn
    exact AboveConstruction.dPX_above d hd K m n hn
  · intro n hn
    exact congrArg d (AboveConstruction.PX_below d hd K m n hn)

/-- Under the growth hypothesis, there is a quasi-isomorphism `f : K ⟶ K'` such that
`d (K'.X n)` is finite for every `n` and `K'` still satisfies the growth hypothesis. -/
theorem exists_finite_d_qis (d : A → ℕ∞) (hd : BoundedCohomologicalDimension d)
    (K : CochainComplex A ℤ) (hK : TendsToNegInfty d K) :
    ∃ (K' : CochainComplex A ℤ) (f : K ⟶ K'),
      QuasiIso f ∧ (∀ n : ℤ, d (K'.X n) ≠ ⊤) ∧ TendsToNegInfty d K' := by
  obtain ⟨n₀, hn₀⟩ := hK 0
  obtain ⟨K', g, hg, habove, hbelow⟩ := exists_dZero_above d hd K (n₀ + 1)
  refine ⟨K', g, hg, ?_, ?_⟩
  · intro n
    by_cases hlt : n < n₀ + 1
    · rw [hbelow n hlt]
      obtain ⟨k, hk, _⟩ := hn₀ n (by omega)
      rw [hk]; exact (by simp : ((k : ℕ∞)) ≠ ⊤)
    · have hge : n₀ + 1 ≤ n := by omega
      rw [habove n hge]; exact (by norm_num : (0 : ℕ∞) ≠ ⊤)
  · intro N
    obtain ⟨nN, hnN⟩ := hK N
    refine ⟨min nN n₀, ?_⟩
    intro n hn
    have hlt : n < n₀ + 1 := by
      have : n ≤ n₀ := le_trans hn (min_le_right _ _)
      omega
    obtain ⟨k, hk, hkN⟩ := hnN n (le_trans hn (min_le_left _ _))
    exact ⟨k, by rw [hbelow n hlt, hk], hkN⟩

/-- An `ℕ`-indexed sequence of complexes starting at `K`, whose transition maps are
quasi-isomorphisms, which is degreewise eventually constant (in each degree `n` the
component maps are isomorphisms past some stage) and degreewise eventually `d`-acyclic
(in each degree `n` the `d`-value is `0` past some stage). -/
structure DegreewiseECData (d : A → ℕ∞) (K : CochainComplex A ℤ) where
  /-- The replacement sequence (`seq 0 = K`). -/
  seq : ℕ → CochainComplex A ℤ
  /-- `seq` starts at `K`. -/
  seq_zero : seq 0 = K
  /-- The comparison maps `seq j ⟶ seq (j+1)`. -/
  tr : ∀ j : ℕ, seq j ⟶ seq (j + 1)
  /-- Every comparison map is a quasi-isomorphism. -/
  tr_qis : ∀ j : ℕ, QuasiIso (tr j)
  /-- Degreewise eventual constancy: each degree `n` freezes past some stage `s` (the
  component map `(tr t).f n` is an isomorphism for `t ≥ s`). -/
  freeze : ∀ n : ℤ, ∃ s : ℕ, ∀ t : ℕ, s ≤ t → IsIso ((tr t).f n)
  /-- Degreewise eventual `d`-acyclicity: each degree `n` has `d = 0` past some stage. -/
  acyclic : ∀ n : ℤ, ∃ s : ℕ, ∀ t : ℕ, s ≤ t → d ((seq t).X n) = 0

/-- The contribution of degree `n`: the integer `n + (d (K.X n)).toNat`. -/
noncomputable def contrib (d : A → ℕ∞) (K : CochainComplex A ℤ) (n : ℤ) : ℤ :=
  n + ((d (K.X n)).toNat : ℤ)

/-- The set of contributions `contrib d K n` over the degrees `n` with `0 < d (K.X n)`. -/
def cvals (d : A → ℕ∞) (K : CochainComplex A ℤ) : Set ℤ :=
  {v | ∃ n : ℤ, 0 < d (K.X n) ∧ contrib d K n = v}

/-- Under the growth hypothesis, if every degree `n` with `0 < d (K.X n)` satisfies `n ≤ b`,
then `cvals d K` is bounded above. -/
theorem cvals_bddAbove (d : A → ℕ∞) (K : CochainComplex A ℤ) (hK : TendsToNegInfty d K) (b : ℤ)
    (hb : ∀ n, 0 < d (K.X n) → n ≤ b) : BddAbove (cvals d K) := by
  obtain ⟨n₀, hn₀⟩ := hK b
  apply BddAbove.mono (s := cvals d K) (t := Set.Iic b ∪ (contrib d K '' (Set.Icc (n₀ + 1) b)))
  · rintro v ⟨n, hpos, rfl⟩
    by_cases hn : n ≤ n₀
    · left
      obtain ⟨k, hk, hkb⟩ := hn₀ n hn
      simp only [Set.mem_Iic]
      unfold contrib
      rw [hk]
      simp only [ENat.toNat_natCast]
      exact hkb
    · right
      exact ⟨n, ⟨by omega, hb n hpos⟩, rfl⟩
  · exact bddAbove_Iic.union ((Set.finite_Icc _ _).image _).bddAbove

/-- A complex `K` is reduced if every `d (K.X n)` is finite, `K` satisfies the growth
hypothesis, and the degrees `n` with `0 < d (K.X n)` are bounded above. -/
structure Reduced (d : A → ℕ∞) (K : CochainComplex A ℤ) : Prop where
  /-- Every `d (K.X n)` is finite. -/
  fin : ∀ n : ℤ, d (K.X n) ≠ ⊤
  /-- `K` satisfies the growth hypothesis. -/
  growth : TendsToNegInfty d K
  /-- The degrees `n` with `0 < d (K.X n)` are bounded above. -/
  bddSupp : ∃ b : ℤ, ∀ n, 0 < d (K.X n) → n ≤ b

/-- `K` is active if some degree `n` has `0 < d (K.X n)`. -/
def active (d : A → ℕ∞) (K : CochainComplex A ℤ) : Prop :=
  ∃ n, 0 < d (K.X n)

/-- If `K` is active then `cvals d K` is nonempty. -/
theorem cvals_nonempty (d : A → ℕ∞) (K : CochainComplex A ℤ) (h : active d K) :
    (cvals d K).Nonempty := by
  obtain ⟨n, hn⟩ := h
  exact ⟨contrib d K n, n, hn, rfl⟩

/-- If `K` is reduced and active, then `cvals d K` has a greatest element. -/
theorem exists_xi (d : A → ℕ∞) (K : CochainComplex A ℤ) (hR : Reduced d K) (hact : active d K) :
    ∃ ξ : ℤ, ξ ∈ cvals d K ∧ ∀ v ∈ cvals d K, v ≤ ξ := by
  obtain ⟨b, hb⟩ := hR.bddSupp
  have hbdd := cvals_bddAbove d K hR.growth b hb
  obtain ⟨B, hB⟩ := hbdd
  obtain ⟨ξ, hξmem, hξmax⟩ :=
    Int.exists_greatest_of_bdd ⟨B, fun v hv => hB hv⟩ (cvals_nonempty d K hact)
  exact ⟨ξ, hξmem, hξmax⟩

/-- The set of degrees attaining the level `ξ`. -/
def attain (d : A → ℕ∞) (K : CochainComplex A ℤ) (ξ : ℤ) : Set ℤ :=
  {n | 0 < d (K.X n) ∧ contrib d K n = ξ}

/-- If `K` is reduced, then `attain d K ξ` is finite. -/
theorem attain_finite (d : A → ℕ∞) (K : CochainComplex A ℤ) (hR : Reduced d K) (ξ : ℤ) :
    (attain d K ξ).Finite := by
  apply Set.Finite.subset (ce_fiber_finite d K hR.growth ξ)
  intro n hn
  simp only [attain, Set.mem_ofPred_eq] at hn
  obtain ⟨hpos, hc⟩ := hn
  simp only [Set.mem_ofPred_eq]
  set k := (d (K.X n)).toNat with hkdef
  have hfin := hR.fin n
  have hdk : d (K.X n) = (k : ℕ∞) := by
    rw [hkdef]; exact (ENat.natCast_toNat hfin).symm
  refine ⟨?_, k, hdk, ?_⟩
  · unfold contrib at hc; omega
  · unfold contrib at hc; omega

/-- Given a quasi-isomorphism `g : K ⟶ K₀` and `DegreewiseECData d K₀`, there is
`DegreewiseECData d K`, obtained by prepending `g` to the sequence. -/
theorem ECData_prepend (d : A → ℕ∞) (K K₀ : CochainComplex A ℤ) (g : K ⟶ K₀) (hg : QuasiIso g)
    (D₀ : DegreewiseECData d K₀) : Nonempty (DegreewiseECData d K) := by
  classical
  refine ⟨?_⟩
  refine
    { seq := fun k => Nat.rec K (fun j _ => D₀.seq j) k
      seq_zero := rfl
      tr := fun j => ?_
      tr_qis := fun j => ?_
      freeze := fun n => ?_
      acyclic := fun n => ?_ }
  · match j with
    | 0 => exact g ≫ eqToHom D₀.seq_zero.symm
    | (k + 1) => exact D₀.tr k
  · match j with
    | 0 =>
      have := hg
      exact quasiIso_comp g (eqToHom D₀.seq_zero.symm)
    | (k + 1) => exact D₀.tr_qis k
  · obtain ⟨s, hs⟩ := D₀.freeze n
    exact ⟨s + 1, fun t ht => by cases t with | zero => omega | succ u => exact hs u (by omega)⟩
  · obtain ⟨s, hs⟩ := D₀.acyclic n
    exact ⟨s + 1, fun t ht => by cases t with | zero => omega | succ u => exact hs u (by omega)⟩

namespace XiDescent

open Classical in
/-- The least degree attaining the greatest contribution `xiOf d K`, when `K` is active and
reduced, and `0` otherwise. -/
noncomputable def nstar (d : A → ℕ∞) (K : CochainComplex A ℤ) : ℤ :=
  if h : active d K ∧ Reduced d K then
    (Set.exists_min_image (attain d K (exists_xi d K h.2 h.1).choose) id
        (attain_finite d K h.2 (exists_xi d K h.2 h.1).choose)
        ⟨(exists_xi d K h.2 h.1).choose_spec.1.choose,
          (exists_xi d K h.2 h.1).choose_spec.1.choose_spec.1,
          (exists_xi d K h.2 h.1).choose_spec.1.choose_spec.2⟩).choose
  else 0

open Classical in
/-- The greatest element of `cvals d K`, when `K` is active and reduced, and `0`
otherwise. -/
noncomputable def xiOf (d : A → ℕ∞) (K : CochainComplex A ℤ) : ℤ :=
  if h : active d K ∧ Reduced d K then (exists_xi d K h.2 h.1).choose else 0

/-- For `K` active and reduced, `xiOf d K` is the chosen greatest element of `cvals d K`. -/
lemma xiOf_eq (d : A → ℕ∞) (K : CochainComplex A ℤ) (hact : active d K) (hR : Reduced d K) :
    xiOf d K = (exists_xi d K hR hact).choose := by
  unfold xiOf; rw [dite_eq_left ⟨hact, hR⟩]

/-- For `K` active and reduced, `xiOf d K ∈ cvals d K`. -/
lemma xiOf_mem (d : A → ℕ∞) (K : CochainComplex A ℤ) (hact : active d K) (hR : Reduced d K) :
    xiOf d K ∈ cvals d K := by
  rw [xiOf_eq d K hact hR]; exact (exists_xi d K hR hact).choose_spec.1

/-- For `K` active and reduced, every element of `cvals d K` is at most `xiOf d K`. -/
lemma xiOf_max (d : A → ℕ∞) (K : CochainComplex A ℤ) (hact : active d K) (hR : Reduced d K) :
    ∀ v ∈ cvals d K, v ≤ xiOf d K := by
  rw [xiOf_eq d K hact hR]; exact (exists_xi d K hR hact).choose_spec.2

/-- `nstar d K` is the least degree attaining the chosen greatest contribution. -/
private lemma nstar_spec (d : A → ℕ∞) (K : CochainComplex A ℤ) (hact : active d K)
    (hR : Reduced d K) :
    nstar d K ∈ attain d K (exists_xi d K hR hact).choose ∧
      ∀ m ∈ attain d K (exists_xi d K hR hact).choose, nstar d K ≤ m := by
  unfold nstar
  rw [dite_eq_left ⟨hact, hR⟩]
  obtain ⟨n, hn⟩ := (exists_xi d K hR hact).choose_spec.1
  exact (Set.exists_min_image _ id (attain_finite d K hR _) ⟨n, hn⟩).choose_spec

/-- For `K` active and reduced, `nstar d K` attains the level `xiOf d K`. -/
lemma nstar_mem_attain (d : A → ℕ∞) (K : CochainComplex A ℤ) (hact : active d K)
    (hR : Reduced d K) : nstar d K ∈ attain d K (xiOf d K) := by
  rw [xiOf_eq d K hact hR]
  exact (nstar_spec d K hact hR).1

/-- For `K` active and reduced, `nstar d K` is the least degree attaining `xiOf d K`. -/
lemma nstar_min (d : A → ℕ∞) (K : CochainComplex A ℤ) (hact : active d K) (hR : Reduced d K) :
    ∀ m ∈ attain d K (xiOf d K), nstar d K ≤ m := by
  rw [xiOf_eq d K hact hR]
  exact (nstar_spec d K hact hR).2

/-- For `K` active and reduced, `nstar d K + 1 ≤ xiOf d K`. -/
lemma nstar_succ_le_xi (d : A → ℕ∞) (K : CochainComplex A ℤ) (hact : active d K)
    (hR : Reduced d K) : nstar d K + 1 ≤ xiOf d K := by
  obtain ⟨hpos, hc⟩ := nstar_mem_attain d K hact hR
  have htoNat : 1 ≤ (d (K.X (nstar d K))).toNat := by
    have hfin := hR.fin (nstar d K)
    rcases ENat.ne_top_iff_exists.mp hfin with ⟨k, hk⟩
    rw [← hk] at hpos ⊢
    simp only [ENat.toNat_natCast]
    rcases Nat.eq_zero_or_pos k with hk0 | hk0
    · subst hk0; simp at hpos
    · omega
  unfold contrib at hc
  omega

/-- For `K` active and reduced, `0 < d (K.X (nstar d K))`. -/
lemma nstar_pos (d : A → ℕ∞) (K : CochainComplex A ℤ) (hact : active d K) (hR : Reduced d K) :
    0 < d (K.X (nstar d K)) :=
  (nstar_mem_attain d K hact hR).1

open Classical in
/-- One descent step: the strengthened elementary replacement `elementary_replacement'` at
degree `nstar d K` when `K` is active and reduced, and `K` itself otherwise. -/
noncomputable def stepC (d : A → ℕ∞) (hd : BoundedCohomologicalDimension d)
    (K : CochainComplex A ℤ) : CochainComplex A ℤ :=
  if _ : active d K ∧ Reduced d K then (elementary_replacement' d hd K (nstar d K)).choose else K

open Classical in
/-- The transition map `K ⟶ stepC d hd K` of one descent step. -/
noncomputable def stepF (d : A → ℕ∞) (hd : BoundedCohomologicalDimension d)
    (K : CochainComplex A ℤ) : K ⟶ stepC d hd K :=
  if h : active d K ∧ Reduced d K then
    (elementary_replacement' d hd K (nstar d K)).choose_spec.choose ≫
      eqToHom
        (by
          unfold stepC; rw [dite_eq_left h])
  else
    eqToHom
      (by
        unfold stepC; rw [dite_eq_right h])

/-- The transition map of one descent step is a quasi-isomorphism. -/
lemma stepF_qis (d : A → ℕ∞) (hd : BoundedCohomologicalDimension d) (K : CochainComplex A ℤ) :
    QuasiIso (stepF d hd K) := by
  unfold stepF
  by_cases h : active d K ∧ Reduced d K
  · rw [dite_eq_left h]
    have := (elementary_replacement' d hd K (nstar d K)).choose_spec.choose_spec.1
    exact quasiIso_comp _ _
  · rw [dite_eq_right h]; infer_instance

/-- If `K` is not both active and reduced, every component of `stepF d hd K` is an
isomorphism. -/
lemma stepF_f_iso_inactive (d : A → ℕ∞) (hd : BoundedCohomologicalDimension d)
    (K : CochainComplex A ℤ) (h : ¬(active d K ∧ Reduced d K)) (m : ℤ) :
    IsIso ((stepF d hd K).f m) := by
  have :
    (stepF d hd K) =
      eqToHom
        (by
          unfold stepC; rw [dite_eq_right h]) := by
    unfold stepF; rw [dite_eq_right h]
  rw [this, HomologicalComplex.eqToHom_f]
  infer_instance

/-- For `m ∉ {nstar d K, nstar d K + 1}`, the object `(stepC d hd K).X m` equals `K.X m` and
the component `(stepF d hd K).f m` is an isomorphism. -/
lemma step_off (d : A → ℕ∞) (hd : BoundedCohomologicalDimension d) (K : CochainComplex A ℤ) (m : ℤ)
    (hm1 : m ≠ nstar d K) (hm2 : m ≠ nstar d K + 1) :
    (stepC d hd K).X m = K.X m ∧ IsIso ((stepF d hd K).f m) := by
  by_cases h : active d K ∧ Reduced d K
  · obtain ⟨hobj, hfeq⟩ :=
      (elementary_replacement' d hd K (nstar d K)).choose_spec.choose_spec.2.2.2.2 m hm1 hm2
    have hCeq : (stepC d hd K).X m = K.X m := by
      have : stepC d hd K = (elementary_replacement' d hd K (nstar d K)).choose := by
        unfold stepC; rw [dite_eq_left h]
      rw [this]; exact hobj
    refine ⟨hCeq, ?_⟩
    have hFeq :
      (stepF d hd K) =
        (elementary_replacement' d hd K (nstar d K)).choose_spec.choose ≫
          eqToHom
            (by
              unfold stepC; rw [dite_eq_left h]) := by
      unfold stepF; rw [dite_eq_left h]
    rw [hFeq, HomologicalComplex.comp_f, HomologicalComplex.eqToHom_f, hfeq, eqToHom_trans]
    infer_instance
  · refine ⟨?_, stepF_f_iso_inactive d hd K h m⟩
    unfold stepC
    rw [dite_eq_right h]

/-- For `K` active and reduced, if `m ∈ {nstar d K, nstar d K + 1}` then `m ≤ xiOf d K`. -/
lemma step_touch_forces (d : A → ℕ∞) (K : CochainComplex A ℤ) (hact : active d K)
    (hR : Reduced d K) (m : ℤ) (hm : m = nstar d K ∨ m = nstar d K + 1) : m ≤ xiOf d K := by
  have h := nstar_succ_le_xi d K hact hR
  rcases hm with hm | hm <;> omega

/-- If `K` is reduced, so is `stepC d hd K`. -/
lemma step_reduced (d : A → ℕ∞) (hd : BoundedCohomologicalDimension d) (K : CochainComplex A ℤ)
    (hR : Reduced d K) : Reduced d (stepC d hd K) := by
  unfold stepC
  by_cases h : active d K ∧ Reduced d K
  · rw [dite_eq_left h]
    set n := nstar d K with hn
    obtain ⟨f, hqis, hzero, hbnd, hoff, hoffobj⟩ :=
      Classical.choose_spec (elementary_replacement' d hd K n)
    change Reduced d (elementary_replacement' d hd K n).choose
    have hKpos : 0 < d (K.X n) := nstar_pos d K h.1 h.2
    obtain ⟨b, hb⟩ := hR.bddSupp
    have hnb : n ≤ b := hb n hKpos
    have hfin' : ∀ m : ℤ, d ((elementary_replacement' d hd K n).choose.X m) ≠ ⊤ := by
      intro m
      by_cases hm1 : m = n
      · subst hm1; rw [hzero]; norm_num
      · by_cases hm2 : m = n + 1
        · subst hm2
          intro htop
          rw [htop] at hbnd
          have hle : (⊤ : ℕ∞) ≤ max (d (K.X n) - 1) (d (K.X (n + 1))) := hbnd
          have hfa : d (K.X n) - 1 ≠ ⊤ := by
            rcases ENat.ne_top_iff_exists.mp (hR.fin n) with ⟨k, hk⟩
            rw [← hk, ← ENat.natCast_one, ← ENat.natCast_sub]; simp
          have hfb : d (K.X (n + 1)) ≠ ⊤ := hR.fin (n + 1)
          have hmax : max (d (K.X n) - 1) (d (K.X (n + 1))) ≠ ⊤ := by
            rcases max_cases (d (K.X n) - 1) (d (K.X (n + 1))) with ⟨he, _⟩ | ⟨he, _⟩
            · rw [he]; exact hfa
            · rw [he]; exact hfb
          rw [top_le_iff] at hle
          exact hmax hle
        · rw [hoff m hm1 hm2]; exact hR.fin m
    refine ⟨hfin', ?_, ?_⟩
    · intro N
      obtain ⟨n₀, hn₀⟩ := hR.growth N
      refine ⟨min n₀ (n - 1), fun p hp => ?_⟩
      have hpn0 : p ≤ n₀ := le_trans hp (min_le_left _ _)
      have hpn : p < n := lt_of_le_of_lt (le_trans hp (min_le_right _ _)) (by omega)
      obtain ⟨k, hk, hkN⟩ := hn₀ p hpn0
      refine ⟨k, ?_, hkN⟩
      rw [hoff p (by omega) (by omega)]; exact hk
    · refine ⟨max b (n + 1), fun p hppos => ?_⟩
      by_cases hp1 : p = n
      · subst hp1
        rw [hzero] at hppos; exact absurd hppos (lt_irrefl 0)
      · by_cases hp2 : p = n + 1
        · subst hp2; exact le_trans (le_max_right _ _) le_rfl
        · rw [hoff p hp1 hp2] at hppos
          exact le_trans (hb p hppos) (le_max_left _ _)
  · rw [dite_eq_right h]; exact hR
end XiDescent

end Stacks.BoundedCohomologicalDimension
