module

public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedCohomologicalDimension.Resolution.ReplacementAbove

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Resolutions by objects of bounded cohomological dimension: descent and freezing

The descent sequence on the greatest contribution `n + d (K.X n)`, which yields degreewise
eventually constant replacement data, and the limit complex of such data.

## Main results

* `exists_DegreewiseECData`: degreewise eventually constant replacement data exist.
* `DegreewiseECData_qis`: such data give a quasi-isomorphism to a complex of `d`-value `0`.
* `exists_dZero_qis`: the main result.

## References

* [Stacks: Tag 07K6](https://stacks.math.columbia.edu/tag/07K6)
-/

open CategoryTheory CategoryTheory.Limits ZeroObject

namespace Stacks.BoundedCohomologicalDimension

variable {A : Type*} [Category A] [Abelian A]

namespace XiDescent

/-- The descent sequence: `seqC 0 = K` and `seqC (k + 1) = stepC d hd (seqC k)`. -/
noncomputable def seqC (d : A → ℕ∞) (hd : BoundedCohomologicalDimension d)
    (K : CochainComplex A ℤ) : ℕ → CochainComplex A ℤ := fun k =>
  Nat.rec K (fun _ prev => stepC d hd prev) k

/-- The `0`-th stage of the descent sequence is `K`. -/
@[simp]
lemma seqC_zero (d : A → ℕ∞) (hd : BoundedCohomologicalDimension d) (K : CochainComplex A ℤ) :
    seqC d hd K 0 = K :=
  rfl

/-- The `(k + 1)`-st stage of the descent sequence is `stepC` of the `k`-th. -/
lemma seqC_succ (d : A → ℕ∞) (hd : BoundedCohomologicalDimension d) (K : CochainComplex A ℤ)
    (k : ℕ) : seqC d hd K (k + 1) = stepC d hd (seqC d hd K k) :=
  rfl

/-- If `K` is reduced, every stage of the descent sequence is reduced. -/
lemma seqC_reduced (d : A → ℕ∞) (hd : BoundedCohomologicalDimension d) (K : CochainComplex A ℤ)
    (hR : Reduced d K) (k : ℕ) : Reduced d (seqC d hd K k) := by
  induction k with
  | zero => exact hR
  | succ k ih =>
    rw [seqC_succ]; exact step_reduced d hd _ ih

/-- The transition map at stage `j`. -/
noncomputable def trF (d : A → ℕ∞) (hd : BoundedCohomologicalDimension d) (K : CochainComplex A ℤ)
    (j : ℕ) : seqC d hd K j ⟶ seqC d hd K (j + 1) :=
  stepF d hd (seqC d hd K j)

/-- Each transition map `trF` is a quasi-isomorphism. -/
lemma trF_qis (d : A → ℕ∞) (hd : BoundedCohomologicalDimension d) (K : CochainComplex A ℤ)
    (j : ℕ) : QuasiIso (trF d hd K j) :=
  stepF_qis d hd (seqC d hd K j)

/-- A positive finite `ℕ∞` value has `toNat` at least `1`. -/
private theorem one_le_toNat_of_pos {x : ℕ∞} (hx : x ≠ ⊤) (h : 0 < x) : 1 ≤ x.toNat := by
  lift x to ℕ using hx
  rw [ENat.toNat_natCast]; exact_mod_cast h

/-- The properties of one descent step at an active reduced complex, at the degree `nstar`. -/
private theorem step_spec (d : A → ℕ∞) (hd : BoundedCohomologicalDimension d)
    (K : CochainComplex A ℤ) (hact : active d K) (hR : Reduced d K) :
    d ((stepC d hd K).X (nstar d K)) = 0 ∧
      d ((stepC d hd K).X (nstar d K + 1)) ≤
        max (d (K.X (nstar d K)) - 1) (d (K.X (nstar d K + 1))) ∧
      ∀ m : ℤ, m ≠ nstar d K → m ≠ nstar d K + 1 → d ((stepC d hd K).X m) = d (K.X m) := by
  have hC : stepC d hd K = (elementary_replacement' d hd K (nstar d K)).choose := by
    unfold stepC; rw [dite_eq_left ⟨hact, hR⟩]
  rw [hC]
  obtain ⟨_, h1, h2, h3, _⟩ := (elementary_replacement' d hd K (nstar d K)).choose_spec.choose_spec
  exact ⟨h1, h2, h3⟩

/-- For `K` active and reduced with `stepC d hd K` active, one descent step does not increase
`xiOf`. -/
lemma step_xi_le (d : A → ℕ∞) (hd : BoundedCohomologicalDimension d) (K : CochainComplex A ℤ)
    (hact : active d K) (hR : Reduced d K) (hact' : active d (stepC d hd K)) :
    xiOf d (stepC d hd K) ≤ xiOf d K := by
  have hR' : Reduced d (stepC d hd K) := step_reduced d hd K hR
  obtain ⟨hzero, hbnd, hoffd⟩ := step_spec d hd K hact hR
  set n := nstar d K with hn
  obtain ⟨p, hppos, hpc⟩ := xiOf_mem d (stepC d hd K) hact' hR'
  rw [← hpc]
  obtain ⟨hnpos, hnc⟩ := nstar_mem_attain d K hact hR
  rw [← hn] at hnpos hnc
  have hn1 := one_le_toNat_of_pos (hR.fin n) hnpos
  by_cases hp1 : p = n
  · subst hp1; rw [hzero] at hppos; exact absurd hppos (lt_irrefl 0)
  · by_cases hp2 : p = n + 1
    · subst hp2
      have hfa : d (K.X n) - 1 ≠ ⊤ := by
        rcases ENat.ne_top_iff_exists.mp (hR.fin n) with ⟨k, hk⟩
        rw [← hk, ← ENat.natCast_one, ← ENat.natCast_sub]; simp
      have hfb : d (K.X (n + 1)) ≠ ⊤ := hR.fin (n + 1)
      have hmaxfin : max (d (K.X n) - 1) (d (K.X (n + 1))) ≠ ⊤ := by
        rcases max_cases (d (K.X n) - 1) (d (K.X (n + 1))) with ⟨he, _⟩ | ⟨he, _⟩
        · rw [he]; exact hfa
        · rw [he]; exact hfb
      have htle :
        (d ((stepC d hd K).X (n + 1))).toNat ≤ (max (d (K.X n) - 1) (d (K.X (n + 1)))).toNat :=
        ENat.toNat_le_toNat hbnd hmaxfin
      have htmax :
        (max (d (K.X n) - 1) (d (K.X (n + 1)))).toNat =
          max ((d (K.X n) - 1).toNat) ((d (K.X (n + 1))).toNat) := by
        rcases le_total (d (K.X n) - 1) (d (K.X (n + 1))) with hle' | hle'
        · rw [max_eq_right hle', max_eq_right (ENat.toNat_le_toNat hle' hfb)]
        · rw [max_eq_left hle', max_eq_left (ENat.toNat_le_toNat hle' hfa)]
      have htsub : (d (K.X n) - 1).toNat = (d (K.X n)).toNat - 1 := by
        rcases ENat.ne_top_iff_exists.mp (hR.fin n) with ⟨k, hk⟩
        rw [← hk]
        rw [show (1 : ℕ∞) = ((1 : ℕ) : ℕ∞) from rfl, ← ENat.natCast_sub, ENat.toNat_natCast,
          ENat.toNat_natCast]
      rw [htmax, htsub] at htle
      have hbranch1 : (n + 1) + (((d (K.X n)).toNat : ℤ) - 1) ≤ xiOf d K := by
        unfold contrib at hnc; omega
      have hbranch2 : (n + 1) + ((d (K.X (n + 1))).toNat : ℤ) ≤ xiOf d K := by
        by_cases hq : 0 < d (K.X (n + 1))
        · have hmemK : contrib d K (n + 1) ∈ cvals d K := ⟨n + 1, hq, rfl⟩
          have := xiOf_max d K hact hR _ hmemK
          unfold contrib at this; omega
        · have hz : d (K.X (n + 1)) = 0 := by simpa only [not_lt, nonpos_iff_eq_zero] using hq
          rw [hz]; simp only [ENat.toNat_zero, Nat.cast_zero, add_zero]
          have := nstar_succ_le_xi d K hact hR; omega
      unfold contrib
      rcases le_max_iff.mp htle with hh | hh <;> omega
    · have hdeq : d ((stepC d hd K).X p) = d (K.X p) := hoffd p hp1 hp2
      have hpposK : 0 < d (K.X p) := by
        rw [← hdeq]; exact hppos
      have hmemK : contrib d K p ∈ cvals d K := ⟨p, hpposK, rfl⟩
      have hcontrib : contrib d (stepC d hd K) p = contrib d K p := by
        unfold contrib; rw [hdeq]
      rw [hcontrib]
      exact xiOf_max d K hact hR _ hmemK

/-- If one descent step leaves `xiOf` unchanged, then it strictly increases `nstar`. -/
lemma step_min_increase (d : A → ℕ∞) (hd : BoundedCohomologicalDimension d)
    (K : CochainComplex A ℤ) (hact : active d K) (hR : Reduced d K)
    (hact' : active d (stepC d hd K)) (hxi : xiOf d (stepC d hd K) = xiOf d K) :
    nstar d K < nstar d (stepC d hd K) := by
  have hR' : Reduced d (stepC d hd K) := step_reduced d hd K hR
  obtain ⟨hzero, -, hoffd⟩ := step_spec d hd K hact hR
  set n := nstar d K with hn
  obtain ⟨hmpos, hmc⟩ := nstar_mem_attain d (stepC d hd K) hact' hR'
  set m := nstar d (stepC d hd K) with hm
  have hmn : m ≠ n := by
    intro he; rw [he, hzero] at hmpos; exact absurd hmpos (lt_irrefl 0)
  by_cases hmn1 : m = n + 1
  · rw [hmn1]; omega
  · have hdeq : d ((stepC d hd K).X m) = d (K.X m) := hoffd m hmn hmn1
    have hmposK : 0 < d (K.X m) := by
      rw [← hdeq]; exact hmpos
    have hcontribK : contrib d K m = xiOf d K := by
      have : contrib d (stepC d hd K) m = contrib d K m := by
        unfold contrib; rw [hdeq]
      rw [← this, hmc, hxi]
    have hmemK : m ∈ attain d K (xiOf d K) := ⟨hmposK, hcontribK⟩
    have hle := nstar_min d K hact hR m hmemK
    rw [← hn] at hle
    omega

/-- If a stage is inactive, the next stage equals it (the step is the identity). -/
lemma seqC_succ_eq_of_inactive (d : A → ℕ∞) (hd : BoundedCohomologicalDimension d)
    (K : CochainComplex A ℤ) (t : ℕ) (hin : ¬active d (seqC d hd K t)) :
    seqC d hd K (t + 1) = seqC d hd K t := by
  rw [seqC_succ]
  unfold stepC
  rw [dite_eq_right]
  rintro ⟨hact, _⟩
  exact hin hact

/-- Inactivity is absorbing: once a stage is inactive, all later stages equal it. -/
lemma seqC_inactive_stable (d : A → ℕ∞) (hd : BoundedCohomologicalDimension d)
    (K : CochainComplex A ℤ) (t : ℕ) (hin : ¬active d (seqC d hd K t)) :
    ∀ t' : ℕ, t ≤ t' → seqC d hd K t' = seqC d hd K t := by
  intro t' ht'
  induction t' with
  | zero =>
    obtain rfl : t = 0 := Nat.le_zero.mp ht'; rfl
  | succ u ih =>
    rcases Nat.lt_or_ge t (u + 1) with hlt | hge
    · have htu : t ≤ u := by omega
      have hinu : ¬active d (seqC d hd K u) := by
        rw [ih htu]; exact hin
      rw [seqC_succ_eq_of_inactive d hd K u hinu, ih htu]
    · obtain rfl : t = u + 1 := by omega
      rfl

/-- From any active stage `t` of the descent sequence, some later stage `s` is inactive or
has `xiOf` strictly smaller than at stage `t`. -/
lemma fixed_level_finite (d : A → ℕ∞) (hd : BoundedCohomologicalDimension d)
    (K : CochainComplex A ℤ) (hR : Reduced d K) :
    ∀ (M : ℕ) (t : ℕ),
      active d (seqC d hd K t) →
        (xiOf d (seqC d hd K t) - 1 - nstar d (seqC d hd K t)).toNat ≤ M →
        ∃ s : ℕ,
          t ≤ s ∧
            (¬active d (seqC d hd K s) ∨ xiOf d (seqC d hd K s) < xiOf d (seqC d hd K t)) := by
  intro M
  induction M with
  | zero =>
    intro t hact hmeas
    have hRt : Reduced d (seqC d hd K t) := seqC_reduced d hd K hR t
    by_cases hact' : active d (seqC d hd K (t + 1))
    · have hRt1 : Reduced d (seqC d hd K (t + 1)) := seqC_reduced d hd K hR (t + 1)
      rw [seqC_succ] at hact'
      have hle := step_xi_le d hd (seqC d hd K t) hact hRt hact'
      by_cases hlt : xiOf d (stepC d hd (seqC d hd K t)) < xiOf d (seqC d hd K t)
      · exact
          ⟨t + 1, by omega, by
            rw [seqC_succ]; exact Or.inr hlt⟩
      · have heq : xiOf d (stepC d hd (seqC d hd K t)) = xiOf d (seqC d hd K t) := by omega
        have hinc := step_min_increase d hd (seqC d hd K t) hact hRt hact' heq
        have hwin := nstar_succ_le_xi d (seqC d hd K t) hact hRt
        have hRt1' : Reduced d (stepC d hd (seqC d hd K t)) :=
          step_reduced d hd (seqC d hd K t) hRt
        have hwin1 := nstar_succ_le_xi d (stepC d hd (seqC d hd K t)) hact' hRt1'
        have hge0 : 0 ≤ xiOf d (seqC d hd K t) - 1 - nstar d (seqC d hd K t) := by omega
        have h0 : (xiOf d (seqC d hd K t) - 1 - nstar d (seqC d hd K t)).toNat = 0 := by omega
        have hexact : xiOf d (seqC d hd K t) - 1 - nstar d (seqC d hd K t) = 0 := by omega
        omega
    · exact ⟨t + 1, by omega, Or.inl hact'⟩
  | succ M ih =>
    intro t hact hmeas
    have hRt : Reduced d (seqC d hd K t) := seqC_reduced d hd K hR t
    by_cases hact' : active d (seqC d hd K (t + 1))
    · have hRt1 : Reduced d (seqC d hd K (t + 1)) := seqC_reduced d hd K hR (t + 1)
      have hact's : active d (stepC d hd (seqC d hd K t)) := by
        rw [← seqC_succ]; exact hact'
      have hle := step_xi_le d hd (seqC d hd K t) hact hRt hact's
      rw [← seqC_succ] at hle
      by_cases hlt : xiOf d (seqC d hd K (t + 1)) < xiOf d (seqC d hd K t)
      · exact ⟨t + 1, by omega, Or.inr hlt⟩
      · have heq : xiOf d (seqC d hd K (t + 1)) = xiOf d (seqC d hd K t) := by omega
        have heqs : xiOf d (stepC d hd (seqC d hd K t)) = xiOf d (seqC d hd K t) := by
          rw [← seqC_succ]; exact heq
        have hinc := step_min_increase d hd (seqC d hd K t) hact hRt hact's heqs
        rw [← seqC_succ] at hinc
        have hwin := nstar_succ_le_xi d (seqC d hd K t) hact hRt
        have hwin1 := nstar_succ_le_xi d (seqC d hd K (t + 1)) hact' hRt1
        have hmeas1 :
          (xiOf d (seqC d hd K (t + 1)) - 1 - nstar d (seqC d hd K (t + 1))).toNat ≤ M := by omega
        obtain ⟨s, hts, hs⟩ := ih (t + 1) hact' hmeas1
        refine ⟨s, by omega, ?_⟩
        rcases hs with hin | hlt'
        · exact Or.inl hin
        · exact Or.inr (by omega)
    · exact ⟨t + 1, by omega, Or.inl hact'⟩

/-- From any stage `t` that is inactive or has `xiOf ≤ L + j`, some later stage is inactive
or has `xiOf < L`. -/
lemma drive_below (d : A → ℕ∞) (hd : BoundedCohomologicalDimension d) (K : CochainComplex A ℤ)
    (hR : Reduced d K) (L : ℤ) :
    ∀ (j : ℕ) (t : ℕ),
      (active d (seqC d hd K t) → xiOf d (seqC d hd K t) ≤ L + j) →
        ∃ s : ℕ, t ≤ s ∧ (¬active d (seqC d hd K s) ∨ xiOf d (seqC d hd K s) < L) := by
  intro j
  induction j with
  | zero =>
    intro t ht
    by_cases hact : active d (seqC d hd K t)
    · have hRt : Reduced d (seqC d hd K t) := seqC_reduced d hd K hR t
      obtain ⟨s, hts, hs⟩ :=
        fixed_level_finite d hd K hR (xiOf d (seqC d hd K t) - 1 - nstar d (seqC d hd K t)).toNat t
          hact (le_refl _)
      refine ⟨s, hts, ?_⟩
      rcases hs with hin | hlt
      · exact Or.inl hin
      · have := ht hact; exact Or.inr (by omega)
    · exact ⟨t, le_refl _, Or.inl hact⟩
  | succ j ih =>
    intro t ht
    by_cases hact : active d (seqC d hd K t)
    · have hRt : Reduced d (seqC d hd K t) := seqC_reduced d hd K hR t
      by_cases hxle : xiOf d (seqC d hd K t) ≤ L + j
      · exact ih t (fun _ => hxle)
      · obtain ⟨s, hts, hs⟩ :=
          fixed_level_finite d hd K hR (xiOf d (seqC d hd K t) - 1 - nstar d (seqC d hd K t)).toNat
            t hact (le_refl _)
        rcases hs with hin | hlt
        · exact ⟨s, hts, Or.inl hin⟩
        · have htx := ht hact
          obtain ⟨s', hss', hs'⟩ := ih s (fun _ => by omega)
          exact ⟨s', by omega, hs'⟩
    · exact ⟨t, le_refl _, Or.inl hact⟩

/-- For every `L`, all sufficiently late stages of the descent sequence are inactive or have
`xiOf < L`. -/
lemma xi_eventually_below (d : A → ℕ∞) (hd : BoundedCohomologicalDimension d)
    (K : CochainComplex A ℤ) (hR : Reduced d K) (L : ℤ) :
    ∃ s : ℕ, ∀ t : ℕ, s ≤ t → ¬active d (seqC d hd K t) ∨ xiOf d (seqC d hd K t) < L := by
  by_cases h0 : active d (seqC d hd K 0)
  · set j : ℕ := (xiOf d (seqC d hd K 0) - L).toNat with hj
    have hstart : active d (seqC d hd K 0) → xiOf d (seqC d hd K 0) ≤ L + j := by
      intro _
      have : (0 : ℤ) ≤ xiOf d (seqC d hd K 0) - L ∨ xiOf d (seqC d hd K 0) - L < 0 := by omega
      omega
    obtain ⟨s, _, hs⟩ := drive_below d hd K hR L j 0 hstart
    refine ⟨s, ?_⟩
    intro t hst
    rcases hs with hin | hlt
    · left
      rw [seqC_inactive_stable d hd K s hin t hst]
      exact hin
    · have key : ∀ u : ℕ, s ≤ u → ¬active d (seqC d hd K u) ∨ xiOf d (seqC d hd K u) < L := by
        intro u hsu
        induction u with
        | zero =>
          obtain rfl : s = 0 := Nat.le_zero.mp hsu; exact Or.inr hlt
        | succ v ih =>
          rcases Nat.lt_or_ge s (v + 1) with hlt' | hge
          · have hsv : s ≤ v := by omega
            rcases ih hsv with hinv | hltv
            · left
              rw [seqC_succ_eq_of_inactive d hd K v hinv]
              exact hinv
            · by_cases hav1 : active d (seqC d hd K (v + 1))
              · right
                have hRv : Reduced d (seqC d hd K v) := seqC_reduced d hd K hR v
                by_cases hav : active d (seqC d hd K v)
                · have hav1s : active d (stepC d hd (seqC d hd K v)) := by
                    rw [← seqC_succ]; exact hav1
                  have hle := step_xi_le d hd (seqC d hd K v) hav hRv hav1s
                  rw [← seqC_succ] at hle; omega
                · exfalso
                  rw [seqC_succ_eq_of_inactive d hd K v hav] at hav1
                  exact hav hav1
              · exact Or.inl hav1
          · obtain rfl : s = v + 1 := by omega
            exact Or.inr hlt
      exact key t hst
  · refine ⟨0, ?_⟩
    intro t _
    left
    rw [seqC_inactive_stable d hd K 0 h0 t (Nat.zero_le t)]
    exact h0

/-- If each step from stage `s` on leaves the object in degree `n` unchanged, then
`(seqC t).X n = (seqC s).X n` for `t ≥ s`. -/
lemma seqC_X_stable_of_frozen (d : A → ℕ∞) (hd : BoundedCohomologicalDimension d)
    (K : CochainComplex A ℤ) (n : ℤ) (s : ℕ)
    (hstep : ∀ u : ℕ, s ≤ u → (stepC d hd (seqC d hd K u)).X n = (seqC d hd K u).X n) :
    ∀ t : ℕ, s ≤ t → (seqC d hd K t).X n = (seqC d hd K s).X n := by
  intro t hst
  induction t with
  | zero =>
    obtain rfl : s = 0 := Nat.le_zero.mp hst; rfl
  | succ t ih =>
    rcases Nat.lt_or_ge s (t + 1) with hlt | hge
    · have hst' : s ≤ t := by omega
      have hs2 : (seqC d hd K (t + 1)).X n = (seqC d hd K t).X n := by
        rw [seqC_succ]; exact hstep t hst'
      rw [hs2, ih hst']
    · obtain rfl : s = t + 1 := by omega
      rfl

/-- If `K` is reduced and inactive or has `xiOf d K < n`, one descent step does not change
degree `n`, up to an isomorphism. -/
private theorem step_off_of_late (d : A → ℕ∞) (hd : BoundedCohomologicalDimension d)
    (K : CochainComplex A ℤ) (hR : Reduced d K) (n : ℤ) (hn : ¬active d K ∨ xiOf d K < n) :
    (stepC d hd K).X n = K.X n ∧ IsIso ((stepF d hd K).f n) := by
  by_cases hact : active d K
  · have hbelow : xiOf d K < n := hn.resolve_left (not_not.mpr hact)
    exact step_off d hd K n
      (fun he => by have := step_touch_forces d K hact hR n (Or.inl he); omega)
      (fun he => by have := step_touch_forces d K hact hR n (Or.inr he); omega)
  · have hbad : ¬(active d K ∧ Reduced d K) := fun h => hact h.1
    refine ⟨?_, stepF_f_iso_inactive d hd K hbad n⟩
    unfold stepC; rw [dite_eq_right hbad]

/-- For `K` reduced, in each degree `n` the stages of the descent sequence eventually have
`d`-value `0`. -/
lemma acyclic' (d : A → ℕ∞) (hd : BoundedCohomologicalDimension d) (K : CochainComplex A ℤ)
    (hR : Reduced d K) (n : ℤ) : ∃ s : ℕ, ∀ t : ℕ, s ≤ t → d ((seqC d hd K t).X n) = 0 := by
  obtain ⟨s, hs⟩ := xi_eventually_below d hd K hR n
  have hstep : ∀ u : ℕ, s ≤ u → (stepC d hd (seqC d hd K u)).X n = (seqC d hd K u).X n :=
    fun u hu => (step_off_of_late d hd _ (seqC_reduced d hd K hR u) n (hs u hu)).1
  have hstable := seqC_X_stable_of_frozen d hd K n s hstep
  refine ⟨s, fun t ht => ?_⟩
  rw [show (seqC d hd K t).X n = (seqC d hd K s).X n from hstable t ht]
  by_contra hne0
  have hpos : 0 < d ((seqC d hd K s).X n) := zero_lt_iff.mpr hne0
  have hacts : active d (seqC d hd K s) := ⟨n, hpos⟩
  have hRs : Reduced d (seqC d hd K s) := seqC_reduced d hd K hR s
  have hbelow : xiOf d (seqC d hd K s) < n := (hs s le_rfl).resolve_left (not_not.mpr hacts)
  have hmemc : contrib d (seqC d hd K s) n ∈ cvals d (seqC d hd K s) := ⟨n, hpos, rfl⟩
  have hle := xiOf_max d (seqC d hd K s) hacts hRs _ hmemc
  have htoNat := one_le_toNat_of_pos (hRs.fin n) hpos
  unfold contrib at hle
  omega

/-- For `K` reduced, in each degree `n` the components of the transition maps of the descent
sequence are eventually isomorphisms. -/
lemma freeze' (d : A → ℕ∞) (hd : BoundedCohomologicalDimension d) (K : CochainComplex A ℤ)
    (hR : Reduced d K) (n : ℤ) : ∃ s : ℕ, ∀ t : ℕ, s ≤ t → IsIso ((trF d hd K t).f n) := by
  obtain ⟨s, hs⟩ := xi_eventually_below d hd K hR n
  refine ⟨s, fun t ht => ?_⟩
  exact (step_off_of_late d hd _ (seqC_reduced d hd K hR t) n (hs t ht)).2

/-- The descent sequence of a reduced complex `K`, as `DegreewiseECData d K`. -/
noncomputable def data (d : A → ℕ∞) (hd : BoundedCohomologicalDimension d) (K : CochainComplex A ℤ)
    (hR : Reduced d K) : DegreewiseECData d K
    where
  seq := seqC d hd K
  seq_zero := rfl
  tr := trF d hd K
  tr_qis := trF_qis d hd K
  freeze := freeze' d hd K hR
  acyclic := acyclic' d hd K hR

end XiDescent

/-- Every reduced complex `K` admits `DegreewiseECData d K`. -/
theorem exists_ECData_of_reduced (d : A → ℕ∞) (hd : BoundedCohomologicalDimension d)
    (K : CochainComplex A ℤ) (hR : Reduced d K) : Nonempty (DegreewiseECData d K) := by
  by_cases hact : active d K
  · exact ⟨XiDescent.data d hd K hR⟩
  · have hzero : ∀ n, d (K.X n) = 0 := by
      intro n
      by_contra h
      exact hact ⟨n, by positivity⟩
    refine
      ⟨{  seq := fun _ => K
          seq_zero := rfl
          tr := fun _ => 𝟙 K
          tr_qis := fun _ => inferInstance
          freeze := fun n => ⟨0, fun t _ => ?_⟩
          acyclic := fun n => ⟨0, fun t _ => hzero n⟩ }⟩
    show IsIso ((𝟙 K : K ⟶ K).f n)
    simp only [HomologicalComplex.id_f]
    infer_instance

/-- Under the growth hypothesis, if every `d (K.X n)` is finite then `K` admits
`DegreewiseECData d K`. -/
theorem exists_DegreewiseECData (d : A → ℕ∞) (hd : BoundedCohomologicalDimension d)
    (K : CochainComplex A ℤ) (hK : TendsToNegInfty d K) (hfin : ∀ n : ℤ, d (K.X n) ≠ ⊤) :
    Nonempty (DegreewiseECData d K) := by
  obtain ⟨K₀, g, hg, hzero, hagree⟩ := exists_dZero_above d hd K 0
  have hR : Reduced d K₀ := by
    refine ⟨?_, ?_, ⟨0, ?_⟩⟩
    · intro n
      by_cases hn : (0 : ℤ) ≤ n
      · rw [hzero n hn]; norm_num
      · rw [hagree n (by omega)]; exact hfin n
    · intro N
      obtain ⟨n₀, hn₀⟩ := hK N
      refine ⟨min n₀ (-1), ?_⟩
      intro n hn
      have hn0 : n < 0 := by
        have : n ≤ (-1 : ℤ) := le_trans hn (min_le_right _ _)
        omega
      have hnn₀ : n ≤ n₀ := le_trans hn (min_le_left _ _)
      obtain ⟨k, hk, hkN⟩ := hn₀ n hnn₀
      refine ⟨k, ?_, hkN⟩
      rw [hagree n hn0]; exact hk
    · intro n hpos
      by_contra hcon
      push Not at hcon
      rw [hzero n (by omega)] at hpos
      exact (lt_irrefl _ hpos)
  obtain ⟨D₀⟩ := exists_ECData_of_reduced d hd K₀ hR
  exact ECData_prepend d K K₀ g hg D₀

namespace DiagFreeze

variable {A : Type*} [Category A] [Abelian A]
variable (d : A → ℕ∞) (K : CochainComplex A ℤ) (D : DegreewiseECData d K)

/-- The chosen freeze stage for degree `n`: past it, the transition components at `n`
are isomorphisms. -/
noncomputable def fst (n : ℤ) : ℕ :=
  (D.freeze n).choose

/-- Past the freeze stage `fst d K D n`, the components `(D.tr t).f n` are isomorphisms. -/
lemma fst_spec (n : ℤ) (t : ℕ) (h : fst d K D n ≤ t) : IsIso ((D.tr t).f n) :=
  (D.freeze n).choose_spec t h

/-- The chosen acyclic stage for degree `n`. -/
noncomputable def acyc (n : ℤ) : ℕ :=
  (D.acyclic n).choose

/-- Past the acyclic stage `acyc d K D n`, the objects `(D.seq t).X n` have `d`-value `0`. -/
lemma acyc_spec (n : ℤ) (t : ℕ) (h : acyc d K D n ≤ t) : d ((D.seq t).X n) = 0 :=
  (D.acyclic n).choose_spec t h

/-- The definition stage for degree `n`: dominates both the freeze and acyclic stages. -/
noncomputable def S (n : ℤ) : ℕ :=
  fst d K D n ⊔ acyc d K D n

/-- The freeze stage is at most the definition stage. -/
lemma fst_le_S (n : ℤ) : fst d K D n ≤ S d K D n :=
  le_sup_left

/-- The acyclic stage is at most the definition stage. -/
lemma acyc_le_S (n : ℤ) : acyc d K D n ≤ S d K D n :=
  le_sup_right

/-- The freeze isomorphism between successive stages at degree `j`, for `u ≥ fst j`. -/
noncomputable def stepIso (j : ℤ) (u : ℕ) (hu : fst d K D j ≤ u) :
    (D.seq u).X j ≅ (D.seq (u + 1)).X j :=
  haveI := fst_spec d K D j u hu
  asIso ((D.tr u).f j)

/-- The forward map of `stepIso` is the component `(D.tr u).f j`. -/
lemma stepIso_hom (j : ℤ) (u : ℕ) (hu : fst d K D j ≤ u) :
    (stepIso d K D j u hu).hom = (D.tr u).f j :=
  rfl

/-- The freeze isomorphism `(seq s).X j ≅ (seq t).X j` for `fst j ≤ s ≤ t`. -/
noncomputable def seqIso (j : ℤ) (s t : ℕ) (hs : fst d K D j ≤ s) (hst : s ≤ t) :
    (D.seq s).X j ≅ (D.seq t).X j :=
  if h : s = t then eqToIso (by rw [h])
  else
    have hlt : s < t := lt_of_le_of_ne hst h
    have : t - 1 + 1 = t := by omega
    (seqIso j s (t - 1) hs (by omega)).trans
      (this ▸ stepIso d K D j (t - 1) (le_trans hs (by omega)))
termination_by t - s

/-- The freeze isomorphism from a stage to itself is the identity. -/
lemma seqIso_refl (j : ℤ) (s : ℕ) (hs : fst d K D j ≤ s) :
    seqIso d K D j s s hs le_rfl = Iso.refl _ := by
  rw [seqIso]; simp

/-- The freeze isomorphism to stage `t + 1` is the one to stage `t` followed by `stepIso`. -/
lemma seqIso_succ (j : ℤ) (s t : ℕ) (hs : fst d K D j ≤ s) (hst : s ≤ t) :
    seqIso d K D j s (t + 1) hs (by omega) =
      (seqIso d K D j s t hs hst).trans (stepIso d K D j t (le_trans hs hst)) := by
  conv_lhs => rw [seqIso]
  rw [dite_eq_right (by omega)]
  simp only []
  rfl

/-- The freeze isomorphisms compose: `seqIso s t ≪≫ seqIso t u = seqIso s u`. -/
lemma seqIso_trans (j : ℤ) (s t u : ℕ) (hs : fst d K D j ≤ s) (hst : s ≤ t) (htu : t ≤ u) :
    (seqIso d K D j s t hs hst).trans (seqIso d K D j t u (le_trans hs hst) htu) =
      seqIso d K D j s u hs (le_trans hst htu) := by
  induction u with
  | zero =>
    obtain rfl : t = 0 := by omega
    obtain rfl : s = 0 := by omega
    rw [seqIso_refl]; ext; simp
  | succ u ih =>
    rcases Nat.lt_or_ge t (u + 1) with hlt | hge
    · have htu' : t ≤ u := by omega
      rw [seqIso_succ d K D j t u (le_trans hs hst) htu',
        seqIso_succ d K D j s u hs (le_trans hst htu')]
      rw [← ih htu']
      ext; simp
    · obtain rfl : t = u + 1 := by omega
      rw [seqIso_refl]; ext; simp

/-- The objects of the diagonal frozen complex. -/
noncomputable def PX (j : ℤ) : A :=
  (D.seq (S d K D j)).X j

/-- The freeze iso from `PX j` to any sufficiently late stage. -/
noncomputable def PXiso (j : ℤ) (s : ℕ) (hs : S d K D j ≤ s) : PX d K D j ≅ (D.seq s).X j :=
  seqIso d K D j (S d K D j) s (fst_le_S d K D j) hs

/-- The freeze isomorphisms commute with the differentials `d j (j + 1)`. -/
lemma seqIso_d (j : ℤ) (s t : ℕ) (hs : fst d K D j ≤ s) (hs1 : fst d K D (j + 1) ≤ s)
    (hst : s ≤ t) :
    (seqIso d K D j s t hs hst).hom ≫ (D.seq t).d j (j + 1) =
      (D.seq s).d j (j + 1) ≫ (seqIso d K D (j + 1) s t hs1 hst).hom := by
  induction t with
  | zero =>
    obtain rfl : s = 0 := by omega
    rw [seqIso_refl, seqIso_refl]; simp
  | succ t ih =>
    rcases Nat.lt_or_ge s (t + 1) with hlt | hge
    · have hst' : s ≤ t := by omega
      rw [seqIso_succ d K D j s t hs hst', seqIso_succ d K D (j + 1) s t hs1 hst']
      simp only [Iso.trans_hom, Category.assoc, stepIso_hom]
      rw [(D.tr t).comm j (j + 1)]
      rw [← Category.assoc, ih hst', Category.assoc]
    · obtain rfl : s = t + 1 := by omega
      rw [seqIso_refl, seqIso_refl]; simp

/-- The successor differential of the diagonal complex, at the common stage `S j ⊔ S (j+1)`. -/
noncomputable def Pdsucc (j : ℤ) : PX d K D j ⟶ PX d K D (j + 1) :=
  (PXiso d K D j (S d K D j ⊔ S d K D (j + 1)) le_sup_left).hom ≫
    (D.seq (S d K D j ⊔ S d K D (j + 1))).d j (j + 1) ≫
    (PXiso d K D (j + 1) (S d K D j ⊔ S d K D (j + 1)) le_sup_right).inv

/-- `Pdsucc` computed at any stage `s` dominating both `S j` and `S (j+1)`. -/
lemma Pdsucc_eq (j : ℤ) (s : ℕ) (hsj : S d K D j ≤ s) (hsj1 : S d K D (j + 1) ≤ s) :
    Pdsucc d K D j =
      (PXiso d K D j s hsj).hom ≫ (D.seq s).d j (j + 1) ≫ (PXiso d K D (j + 1) s hsj1).inv := by
  unfold Pdsucc
  set s0 := max (S d K D j) (S d K D (j + 1)) with hs0
  have hs0le : s0 ≤ s := by
    rw [hs0]; exact sup_le hsj hsj1
  have hkey :=
    seqIso_d d K D j s0 s (le_trans (fst_le_S d K D j) le_sup_left)
      (le_trans (fst_le_S d K D (j + 1)) le_sup_right) hs0le
  have hP : ∀ (i : ℤ) (h0 : S d K D i ≤ s0) (h : S d K D i ≤ s),
      PXiso d K D i s h = (PXiso d K D i s0 h0).trans
        (seqIso d K D i s0 s (le_trans (fst_le_S d K D i) h0) hs0le) := by
    intro i h0 h
    unfold PXiso
    rw [seqIso_trans]
  rw [hP j le_sup_left hsj, hP (j + 1) le_sup_right hsj1]
  simp only [Iso.trans_hom, Iso.trans_inv, Category.assoc]
  rw [←
    Category.assoc (seqIso d K D j s0 s (le_trans (fst_le_S d K D j) le_sup_left) hs0le).hom
      ((D.seq s).d j (j + 1)),
    hkey]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rfl

/-- The full differential of the diagonal complex. -/
noncomputable def Pd (i j : ℤ) : PX d K D i ⟶ PX d K D j :=
  if h : j = i + 1 then Pdsucc d K D i ≫ eqToHom (by rw [h]) else 0

/-- `Pd i j` for `j = i + 1`, computed at any common late stage. -/
lemma Pd_succ_eq (i j : ℤ) (hj : j = i + 1) (s : ℕ) (hsi : S d K D i ≤ s) (hsj : S d K D j ≤ s) :
    Pd d K D i j = (PXiso d K D i s hsi).hom ≫ (D.seq s).d i j ≫ (PXiso d K D j s hsj).inv := by
  subst hj
  unfold Pd
  rw [dite_eq_left rfl]
  rw [Pdsucc_eq d K D i s hsi hsj]
  simp only [eqToHom_refl, Category.comp_id]

/-- Two consecutive differentials `Pd` compose to zero. -/
lemma Pd_dd (i j k : ℤ) (hij : (ComplexShape.up ℤ).Rel i j) (hjk : (ComplexShape.up ℤ).Rel j k) :
    Pd d K D i j ≫ Pd d K D j k = 0 := by
  simp only [ComplexShape.up_Rel] at hij hjk
  subst hij hjk
  unfold Pd
  rw [dite_eq_left rfl, dite_eq_left rfl]
  set s := S d K D i ⊔ S d K D (i + 1) ⊔ S d K D (i + 1 + 1) with hs_def
  have hsi : S d K D i ≤ s := le_trans le_sup_left le_sup_left
  have hsi1 : S d K D (i + 1) ≤ s := le_trans le_sup_right le_sup_left
  have hsi2 : S d K D (i + 1 + 1) ≤ s := le_sup_right
  rw [Pdsucc_eq d K D i s hsi hsi1, Pdsucc_eq d K D (i + 1) s hsi1 hsi2]
  simp only [Category.assoc, eqToHom_refl, Category.comp_id, Iso.inv_hom_id_assoc]
  rw [← Category.assoc ((D.seq s).d i (i + 1)) ((D.seq s).d (i + 1) (i + 1 + 1)),
    HomologicalComplex.d_comp_d, zero_comp, comp_zero]

/-- The diagonal frozen complex `L`. -/
noncomputable def Pcomplex : CochainComplex A ℤ where
  X := PX d K D
  d := Pd d K D
  shape i j hij := by
    unfold Pd; rw [dite_eq_right]; intro h; apply hij; simp [ComplexShape.up_Rel]; omega
  d_comp_d' i j k hij hjk := Pd_dd d K D i j k hij hjk

/-- The objects of `Pcomplex d K D` are given by `PX`. -/
@[simp]
lemma Pcomplex_X (j : ℤ) : (Pcomplex d K D).X j = PX d K D j :=
  rfl

/-- The diagonal complex is `d`-acyclic in every degree. -/
lemma dPX (j : ℤ) : d (PX d K D j) = 0 := by
  unfold PX
  exact acyc_spec d K D j (S d K D j) (acyc_le_S d K D j)

/-- The composite comparison `K ⟶ seq s`. -/
noncomputable def Kcomp : (s : ℕ) → (K ⟶ D.seq s)
  | 0 => eqToHom D.seq_zero.symm
  | (s + 1) => Kcomp s ≫ D.tr s

/-- The composite comparison `Kcomp` is a quasi-isomorphism. -/
lemma Kcomp_quasiIso (s : ℕ) : QuasiIso (Kcomp d K D s) := by
  induction s with
  | zero =>
    unfold Kcomp; infer_instance
  | succ s ih =>
    unfold Kcomp
    have := ih
    have := D.tr_qis s
    exact quasiIso_comp _ _

/-- The composite comparison map is stable in each frozen degree. -/
lemma Kcomp_f_stable (j : ℤ) (s t : ℕ) (hs : fst d K D j ≤ s) (hst : s ≤ t) :
    (Kcomp d K D t).f j = (Kcomp d K D s).f j ≫ (seqIso d K D j s t hs hst).hom := by
  induction t with
  | zero =>
    obtain rfl : s = 0 := by omega
    rw [seqIso_refl]; simp
  | succ t ih =>
    rcases Nat.lt_or_ge s (t + 1) with hlt | hge
    · have hst' : s ≤ t := by omega
      change (Kcomp d K D t ≫ D.tr t).f j = _
      rw [HomologicalComplex.comp_f, ih hst', seqIso_succ d K D j s t hs hst']
      simp only [Iso.trans_hom, Category.assoc, stepIso_hom]
    · obtain rfl : s = t + 1 := by omega
      rw [seqIso_refl]; simp

/-- The comparison chain map `g : K ⟶ L` in each degree. -/
noncomputable def gf (j : ℤ) : K.X j ⟶ PX d K D j :=
  (Kcomp d K D (S d K D j)).f j ≫ (PXiso d K D j (S d K D j) le_rfl).inv

/-- `gf` computed at any sufficiently late stage. -/
lemma gf_eq (j : ℤ) (s : ℕ) (hs : S d K D j ≤ s) :
    gf d K D j = (Kcomp d K D s).f j ≫ (PXiso d K D j s hs).inv := by
  unfold gf
  rw [Kcomp_f_stable d K D j (S d K D j) s (fst_le_S d K D j) hs]
  rw [Category.assoc]
  congr 1
  unfold PXiso
  rw [seqIso_refl]
  simp only [Iso.refl_inv]
  rw [Iso.hom_inv_id]

/-- The comparison map `gf` is a chain map. -/
lemma gf_comm (j : ℤ) : gf d K D j ≫ Pd d K D j (j + 1) = K.d j (j + 1) ≫ gf d K D (j + 1) := by
  set s := S d K D j ⊔ S d K D (j + 1) with hs_def
  have hsj : S d K D j ≤ s := le_sup_left
  have hsj1 : S d K D (j + 1) ≤ s := le_sup_right
  rw [gf_eq d K D j s hsj, gf_eq d K D (j + 1) s hsj1]
  unfold Pd
  rw [dite_eq_left rfl, Pdsucc_eq d K D j s hsj hsj1]
  simp only [eqToHom_refl, Category.comp_id, Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Category.assoc ((Kcomp d K D s).f j) ((D.seq s).d j (j + 1))]
  rw [(Kcomp d K D s).comm j (j + 1)]
  rw [Category.assoc]

/-- The comparison chain map `g : K ⟶ L`. -/
noncomputable def gmap : K ⟶ Pcomplex d K D where
  f := gf d K D
  comm' i j hij := by
    simp only [ComplexShape.up_Rel] at hij; subst hij
    exact gf_comm d K D i

/-- The windowed short complex of `seq s` at `[j-1, j, j+1]` is isomorphic to that of
`Pcomplex`, provided `s` freezes all three degrees. -/
noncomputable def scIso (j : ℤ) (s : ℕ) (hsm1 : S d K D (j - 1) ≤ s) (hsm : S d K D j ≤ s)
    (hsp1 : S d K D (j + 1) ≤ s) :
    (HomologicalComplex.shortComplexFunctor' A (ComplexShape.up ℤ) (j - 1) j (j + 1)).obj
        (D.seq s) ≅
      (HomologicalComplex.shortComplexFunctor' A (ComplexShape.up ℤ) (j - 1) j (j + 1)).obj
        (Pcomplex d K D) := by
  refine
    ShortComplex.isoMk (PXiso d K D (j - 1) s hsm1).symm (PXiso d K D j s hsm).symm
      (PXiso d K D (j + 1) s hsp1).symm ?_ ?_
  · change
      (PXiso d K D (j - 1) s hsm1).inv ≫ Pd d K D (j - 1) j =
        (D.seq s).d (j - 1) j ≫ (PXiso d K D j s hsm).inv
    rw [Pd_succ_eq d K D (j - 1) j (by ring) s hsm1 hsm]
    simp only [Iso.inv_hom_id_assoc]
  · change
      (PXiso d K D j s hsm).inv ≫ Pd d K D j (j + 1) =
        (D.seq s).d j (j + 1) ≫ (PXiso d K D (j + 1) s hsp1).inv
    rw [Pd_succ_eq d K D j (j + 1) rfl s hsm hsp1]
    simp only [Iso.inv_hom_id_assoc]

/-- The comparison map `gmap d K D` is a quasi-isomorphism. -/
theorem gmap_quasiIso : QuasiIso (gmap d K D) := by
  rw [quasiIso_iff]
  intro j
  rw [quasiIsoAt_iff' (gmap d K D) (j - 1) j (j + 1) (by simp) (by simp)]
  set s := S d K D (j - 1) ⊔ S d K D j ⊔ S d K D (j + 1) with hs_def
  have hsm1 : S d K D (j - 1) ≤ s := le_trans le_sup_left le_sup_left
  have hsm : S d K D j ≤ s := le_trans le_sup_right le_sup_left
  have hsp1 : S d K D (j + 1) ≤ s := le_sup_right
  have hKcs : QuasiIsoAt (Kcomp d K D s) j := (quasiIso_iff _).mp (Kcomp_quasiIso d K D s) j
  rw [quasiIsoAt_iff' (Kcomp d K D s) (j - 1) j (j + 1) (by simp) (by simp)] at hKcs
  have := hKcs
  have hfact :
    (HomologicalComplex.shortComplexFunctor' A (ComplexShape.up ℤ) (j - 1) j (j + 1)).map
        (gmap d K D) =
      (HomologicalComplex.shortComplexFunctor' A (ComplexShape.up ℤ) (j - 1) j (j + 1)).map
          (Kcomp d K D s) ≫
        (scIso d K D j s hsm1 hsm hsp1).hom := by
    apply ShortComplex.hom_ext
    · rw [ShortComplex.comp_τ₁]
      change gf d K D (j - 1) = (Kcomp d K D s).f (j - 1) ≫ _
      rw [gf_eq d K D (j - 1) s hsm1]
      rfl
    · rw [ShortComplex.comp_τ₂]
      change gf d K D j = (Kcomp d K D s).f j ≫ _
      rw [gf_eq d K D j s hsm]
      rfl
    · rw [ShortComplex.comp_τ₃]
      change gf d K D (j + 1) = (Kcomp d K D s).f (j + 1) ≫ _
      rw [gf_eq d K D (j + 1) s hsp1]
      rfl
  rw [hfact]
  have : IsIso (scIso d K D j s hsm1 hsm hsp1).hom := inferInstance
  infer_instance

end DiagFreeze

/-- If `K` admits `DegreewiseECData d K`, there is a quasi-isomorphism `f : K ⟶ L` with
`d (L.X n) = 0` for all `n`. -/
theorem DegreewiseECData_qis (d : A → ℕ∞) (K : CochainComplex A ℤ) (D : DegreewiseECData d K) :
    ∃ (L : CochainComplex A ℤ) (f : K ⟶ L), QuasiIso f ∧ ∀ n : ℤ, d (L.X n) = 0 := by
  refine
    ⟨DiagFreeze.Pcomplex d K D, DiagFreeze.gmap d K D, DiagFreeze.gmap_quasiIso d K D, fun n => ?_⟩
  rw [DiagFreeze.Pcomplex_X]
  exact DiagFreeze.dPX d K D n

/-- Under the growth hypothesis, if every `d (K.X n)` is finite then there is a
quasi-isomorphism `f : K ⟶ L` with `d (L.X n) = 0` for all `n`. -/
theorem exists_dZero_qis_of_finite (d : A → ℕ∞) (hd : BoundedCohomologicalDimension d)
    (K : CochainComplex A ℤ) (hK : TendsToNegInfty d K) (hfin : ∀ n : ℤ, d (K.X n) ≠ ⊤) :
    ∃ (L : CochainComplex A ℤ) (f : K ⟶ L), QuasiIso f ∧ ∀ n : ℤ, d (L.X n) = 0 := by
  obtain ⟨D⟩ := exists_DegreewiseECData d hd K hK hfin
  exact DegreewiseECData_qis d K D

/-- Under the growth hypothesis `TendsToNegInfty d K`, there is a quasi-isomorphism
`f : K ⟶ L` with `d (L.X n) = 0` for all `n`. -/
theorem exists_dZero_qis (d : A → ℕ∞) (hd : BoundedCohomologicalDimension d)
    (K : CochainComplex A ℤ) (hK : TendsToNegInfty d K) :
    ∃ (L : CochainComplex A ℤ) (f : K ⟶ L), QuasiIso f ∧ ∀ n : ℤ, d (L.X n) = 0 := by
  obtain ⟨K', f, hf, hfin, hK'⟩ := exists_finite_d_qis d hd K hK
  obtain ⟨L, g, hg, hL⟩ := exists_dZero_qis_of_finite d hd K' hK' hfin
  exact ⟨L, f ≫ g, quasiIso_comp f g, hL⟩

/-- Let `A` be an abelian category and `d : Ob(A) → ℕ∞` a function satisfying the
bounded cohomological dimension hypotheses. Let `K•` be a cochain complex with
`n + d(K^n) → -∞` as `n → -∞`. Then there exists a complex `L•` together with a
quasi-isomorphism `K• → L•` such that `d(L^n) = 0` for all `n ∈ ℤ`. -/
@[stacks 07K6]
alias main_theorem_07k6 := Stacks.BoundedCohomologicalDimension.exists_dZero_qis

end Stacks.BoundedCohomologicalDimension
