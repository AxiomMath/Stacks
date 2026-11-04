module

public import StacksFrontier.RingTheory.Cech.Cohomology
public import StacksFrontier.RingTheory.Localization.Glueing.FormalGlueingComplex
import all StacksFrontier.RingTheory.Localization.Glueing.FormalGlueingComplex

/-!
# Exactness of the glueing complex at its fourth term

Let `R → S` be a ring map, `f = (f₁, …, f_t)` a finite family in `R` and `M` an `R`-module. The
glueing complex of `M` (`FormalGlueing.glueingAlpha`, `FormalGlueing.glueingBeta`,
`FormalGlueing.glueingGamma`) is continued here by its fourth map

`(∏ i < j, (M ⊗[R] S)_{f i f j}) × ∏ M_{f i f j f k} →
  (∏ (M ⊗[R] S)_{f i f j f k}) × ∏ M_{f i f j f k f l}`,
`(y, x) ↦ (d y + x ⊗ 1, d x)`,

and it is shown that the complex is exact at its fourth term as soon as `R → S` is flat and
induces an isomorphism `R / I ≅ S / IS` for `I = (f₁, …, f_t)`.

The proof is the one of `FormalGlueing.glueingComplex_exact_third`, one degree up. It needs two
facts about the alternating Čech differential `FormalGlueing.glueingDifferential` in arbitrary
degree, which are obtained by comparing it with the differential `Cech.cechD` of the extended
alternating Čech complex `Cech.cechComplex` (a direct sum instead of a product over the finitely
many index sets): its square vanishes (`Cech.cechD_comp_cechD`), and its cohomology is killed
by powers of every `f i` (Tag 0G6K, through the null homotopy of Tag 0G6J).

## Main definitions

* `FormalGlueing.glueingDelta`: the fourth map of the glueing complex.

## Main results

* `FormalGlueing.glueingDifferential_eq_cechD`: the glueing differential is the Čech differential
  `Cech.cechD`, read on products.
* `FormalGlueing.glueingDifferential_comp_glueingDifferential`: `d ∘ d = 0` in every degree.
* `FormalGlueing.exists_pow_smul_eq_glueingDifferential_of_glueingDifferential_eq_zero`: a power
  of each `f i` turns a cocycle of positive degree into a coboundary.
* `FormalGlueing.glueingDelta_comp_glueingGamma`: the third and fourth maps compose to zero.
* `FormalGlueing.glueingComplex_exact_fourth`: exactness at the fourth term.

## Implementation notes

The signs of the glueing complex alternate as in a total complex: the second component of
`FormalGlueing.glueingBeta` is `-d`, the first component of `FormalGlueing.glueingGamma` is
`d y - x ⊗ 1`, and so the first component of `FormalGlueing.glueingDelta` is `d y + x ⊗ 1`.

## References

* [Stacks Project, Tag 05EK](https://stacks.math.columbia.edu/tag/05EK)
* [Stacks Project, Tag 0G6K](https://stacks.math.columbia.edu/tag/0G6K)
-/

@[expose] public section

namespace FormalGlueing

open CategoryTheory TensorProduct Cech

universe u v w

/-! ### The glueing differential in arbitrary degree -/

section Differential

variable {R : Type u} [CommRing R] {r : ℕ} (f : Fin r → R) (M : Type w) [AddCommGroup M]
  [Module R M]

/-- Restricting the component, at an index set equal to `s`, of an element of the summand
indexed by `s`. -/
private theorem cechι_of_apply_of_eq {p : ℕ} (s t : {s : Finset (Fin r) // s.card = p})
    (hts : t = s) {U : Finset (Fin r)} (htU : t.1 ⊆ U) (hsU : s.1 ⊆ U) (y : cechMod f M s.1) :
    cechι f M htU
        (DirectSum.of (fun s : {s : Finset (Fin r) // s.card = p} ↦ cechMod f M s.1) s y t) =
      cechι f M hsU y := by
  subst hts
  rw [DirectSum.of_eq_same]

/-- The components of the glueing differential, with the restriction maps written on the
erased index sets. -/
private theorem glueingDifferential_apply_eraseIndex (p : ℕ) (x : GlueingTerm f M p)
    (T : {s : Finset (Fin r) // s.card = p + 1}) :
    glueingDifferential f M p x T =
      ∑ k ∈ T.1.attach, cechSign T.1 k •
        cechι f M (show (eraseIndex p T k).1 ⊆ T.1 from Finset.erase_subset _ _)
          (x (eraseIndex p T k)) :=
  glueingDifferential_apply f M p x T

/-- Every term of the glueing complex is the family of components of an element of the
corresponding direct sum. -/
theorem exists_coe_eq_glueingTerm (p : ℕ) (z : GlueingTerm f M p) :
    ∃ x : cechTerm f M p, (fun s ↦ x s) = z :=
  ⟨DFinsupp.equivFunOnFintype.symm z, DFinsupp.equivFunOnFintype.apply_symm_apply z⟩

/-- **The glueing differential is the Čech differential.** Read on the families of components,
the differential `Cech.cechD` of the extended alternating Čech complex is the glueing
differential. -/
theorem glueingDifferential_eq_cechD (p : ℕ) (x : cechTerm f M p) :
    glueingDifferential f M p (fun s ↦ x s) = fun T ↦ cechD f M p x T := by
  classical
  induction x using DirectSum.induction_on with
  | zero =>
    have h : (fun s ↦ (0 : cechTerm f M p) s) = 0 := funext fun s ↦ rfl
    rw [h, map_zero, map_zero]
    exact funext fun T ↦ rfl
  | add x y hx hy =>
    have h : (fun s ↦ (x + y) s) = (fun s ↦ x s) + (fun s ↦ y s) :=
      funext fun s ↦ DirectSum.add_apply x y s
    rw [h, map_add, hx, hy, map_add]
    funext T
    exact (DirectSum.add_apply (cechD f M p x) (cechD f M p y) T).symm
  | of s y =>
    funext T
    rw [glueingDifferential_apply_eraseIndex, ← DirectSum.lof_eq_of R, cechD_lof,
      DirectSum.sum_apply]
    simp only [DirectSum.lof_eq_of, DirectSum.smul_apply]
    obtain ⟨T, hT⟩ := T
    by_cases hsT : s.1 ⊆ T
    · obtain ⟨k₀, hk₀, rfl⟩ := Finset.exists_eq_insert_iff.mpr ⟨hsT, by rw [s.2, hT]⟩
      rw [Finset.sum_eq_single_of_mem ⟨k₀, Finset.mem_insert_self _ _⟩ (Finset.mem_attach _ _),
        Finset.sum_eq_single_of_mem ⟨k₀, Finset.mem_compl.mpr hk₀⟩ (Finset.mem_attach _ _)]
      · rw [cechι_of_apply_of_eq f M s
          (eraseIndex p ⟨insert k₀ s.1, hT⟩ ⟨k₀, Finset.mem_insert_self _ _⟩)
          (Subtype.ext (Finset.erase_insert hk₀)) _ (Finset.subset_insert k₀ s.1),
          DirectSum.of_eq_same]
        exact congrArg (· • cechι f M (Finset.subset_insert k₀ s.1) y) (cechSign_insert k₀ s.1)
      · rintro ⟨i, hi⟩ - hik
        have hne : (⟨insert k₀ s.1, hT⟩ : {s : Finset (Fin r) // s.card = p + 1}) ≠
            ⟨insert i s.1, by
              rw [Finset.card_insert_of_notMem (by simpa using Finset.mem_compl.1 hi), s.2]⟩ := by
          intro h
          have h' : insert k₀ s.1 = insert i s.1 := congrArg Subtype.val h
          have hk : k₀ ∈ insert i s.1 := by
            rw [← h']; exact Finset.mem_insert_self _ _
          rcases Finset.mem_insert.mp hk with hk | hk
          · exact hik (Subtype.ext hk.symm)
          · exact hk₀ hk
        rw [DirectSum.of_eq_of_ne _ _ _ hne]
        exact zsmul_zero _
      · rintro ⟨k, hk⟩ - hkk
        have hne : eraseIndex p ⟨insert k₀ s.1, hT⟩ ⟨k, hk⟩ ≠ s := by
          intro h
          have hks : k ∈ s.1 :=
            (Finset.mem_insert.mp hk).resolve_left fun hk' ↦ hkk (Subtype.ext hk')
          have h' : (insert k₀ s.1).erase k = s.1 := congrArg Subtype.val h
          rw [← h'] at hks
          exact (Finset.notMem_erase k _) hks
        rw [DirectSum.of_eq_of_ne _ _ _ hne, map_zero]
        exact zsmul_zero _
    · rw [Finset.sum_eq_zero, Finset.sum_eq_zero]
      · rintro ⟨i, hi⟩ -
        have hne : (⟨T, hT⟩ : {s : Finset (Fin r) // s.card = p + 1}) ≠
            ⟨insert i s.1, by
              rw [Finset.card_insert_of_notMem (by simpa using Finset.mem_compl.1 hi), s.2]⟩ := by
          intro h
          have h' : T = insert i s.1 := congrArg Subtype.val h
          exact hsT (by rw [h']; exact Finset.subset_insert _ _)
        rw [DirectSum.of_eq_of_ne _ _ _ hne]
        exact zsmul_zero _
      · rintro k -
        have hne : eraseIndex p ⟨T, hT⟩ k ≠ s := by
          intro h
          have h' : T.erase k = s.1 := congrArg Subtype.val h
          exact hsT (by rw [← h']; exact Finset.erase_subset _ _)
        rw [DirectSum.of_eq_of_ne _ _ _ hne, map_zero]
        exact zsmul_zero _

/-- **`d ∘ d = 0` for the glueing complex.** The Čech differentials of the glueing complex
compose to zero in every degree. -/
theorem glueingDifferential_comp_glueingDifferential (p : ℕ) :
    glueingDifferential f M (p + 1) ∘ₗ glueingDifferential f M p = 0 := by
  refine LinearMap.ext fun z ↦ ?_
  obtain ⟨x, rfl⟩ := exists_coe_eq_glueingTerm f M p z
  rw [LinearMap.comp_apply, glueingDifferential_eq_cechD, glueingDifferential_eq_cechD,
    ← LinearMap.comp_apply (cechD f M (p + 1)), cechD_comp_cechD, LinearMap.zero_apply]
  exact funext fun T ↦ DirectSum.zero_apply T

/-- **Čech cocycles are power torsion modulo coboundaries.** A cocycle of positive degree of the
extended alternating Čech complex becomes a coboundary after multiplication by a power of any
`f i`. -/
theorem exists_pow_smul_eq_cechD_of_cechD_eq_zero (p : ℕ) (x : cechTerm f M (p + 1))
    (hx : cechD f M (p + 1) x = 0) (i : Fin r) :
    ∃ (n : ℕ) (w : cechTerm f M p), f i ^ n • x = cechD f M p w := by
  let K := cechComplex f M
  let S := K.sc' p (p + 1) (p + 2)
  have hd (q : ℕ) : (K.d q (q + 1)).hom = cechD f M q := by
    rw [cechComplex_d]
    rfl
  have hg : S.g.hom = cechD f M (p + 1) := hd (p + 1)
  have hf : S.f.hom = cechD f M p := hd p
  have hxK : (x : S.X₂) ∈ LinearMap.ker S.g.hom := by
    show S.g.hom x = 0
    exact (LinearMap.congr_fun hg x).trans hx
  let e := ((K.homologyIsoSc' p (p + 1) (p + 2) (by simp) (by simp)).trans
    S.moduleCatHomologyIso).toLinearEquiv
  let q : LinearMap.ker S.g.hom ⧸ LinearMap.range S.moduleCatToCycles :=
    Submodule.Quotient.mk ⟨x, hxK⟩
  let eZ := (K.extendHomologyIso ComplexShape.embeddingUpNat (j := p + 1)
    (j' := ((p + 1 : ℕ) : ℤ)) (by simp)).toLinearEquiv
  obtain ⟨n, -, hnZ⟩ := (cechComplex_homology_torsion_support_vanishes f M
    ((p + 1 : ℕ) : ℤ)).2.1 i (eZ.symm (e.symm q))
  have h1 : (f i ^ n • ⟨x, hxK⟩ : LinearMap.ker S.g.hom) ∈
      LinearMap.range S.moduleCatToCycles := by
    refine (Submodule.Quotient.mk_eq_zero _).mp ?_
    rw [Submodule.Quotient.mk_smul]
    exact e.symm.injective ((e.symm.map_smul (f i ^ n) q).trans (eZ.symm.injective
      ((eZ.symm.map_smul (f i ^ n) (e.symm q)).trans (hnZ.trans eZ.symm.map_zero.symm))
        |>.trans e.symm.map_zero.symm))
  obtain ⟨w, hw⟩ := h1
  exact ⟨n, w, (congrArg Subtype.val hw).symm.trans (LinearMap.congr_fun hf w)⟩

/-- **Glueing cocycles are power torsion modulo coboundaries.** A cocycle of positive degree of
the glueing complex becomes a coboundary after multiplication by a power of any `f i`. -/
theorem exists_pow_smul_eq_glueingDifferential_of_glueingDifferential_eq_zero (p : ℕ)
    (z : GlueingTerm f M (p + 1)) (hz : glueingDifferential f M (p + 1) z = 0) (i : Fin r) :
    ∃ (n : ℕ) (w : GlueingTerm f M p), f i ^ n • z = glueingDifferential f M p w := by
  obtain ⟨x, rfl⟩ := exists_coe_eq_glueingTerm f M (p + 1) z
  have hx : cechD f M (p + 1) x = 0 := by
    refine DFinsupp.ext fun T ↦ ?_
    rw [DirectSum.zero_apply]
    exact congrFun ((glueingDifferential_eq_cechD f M (p + 1) x).symm.trans hz) T
  obtain ⟨n, w, hw⟩ := exists_pow_smul_eq_cechD_of_cechD_eq_zero f M p x hx i
  refine ⟨n, fun s ↦ w s, ?_⟩
  rw [glueingDifferential_eq_cechD, ← hw]
  exact funext fun s ↦ (DirectSum.smul_apply (f i ^ n) x s).symm

end Differential

/-- The cohomology of the glueing complex in positive degree is power torsion for the ideal
generated by `f`. -/
theorem isIPowerTorsion_cohomologyModule_glueingDifferential {R : Type u} [CommRing R] {r : ℕ}
    (f : Fin r → R) (M : Type u) [AddCommGroup M] [Module R M] (p : ℕ) :
    IsIPowerTorsion R
      (cohomologyModule (glueingDifferential f M p) (glueingDifferential f M (p + 1)))
      (Ideal.span (Set.range f)) := by
  intro c
  obtain ⟨⟨z, hz⟩, rfl⟩ := Submodule.mkQ_surjective _ c
  apply exists_pow_annihilator_of_generators
  intro i
  obtain ⟨n, w, hw⟩ :=
    exists_pow_smul_eq_glueingDifferential_of_glueingDifferential_eq_zero f M p z hz i
  refine ⟨n, ?_⟩
  rw [← map_smul]
  exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨w, hw.symm⟩

/-! ### The fourth map of the glueing complex -/

/-- The fourth map of the glueing complex,
`(∏ i < j, (M ⊗[R] S)_{f i f j}) × ∏ M_{f i f j f k} →
  (∏ (M ⊗[R] S)_{f i f j f k}) × ∏ M_{f i f j f k f l}`:
its first component is `(y, x) ↦ d y + x ⊗ 1` and its second component is `(y, x) ↦ d x`. -/
public noncomputable def glueingDelta {R : Type u} [CommRing R] (S : Type v) [CommRing S]
    [Algebra R S] {r : ℕ} (f : Fin r → R) (M : Type w) [AddCommGroup M] [Module R M] :
    GlueingTerm f (TensorProduct R M S) 2 × GlueingTerm f M 3 →ₗ[R]
      GlueingTerm f (TensorProduct R M S) 3 × GlueingTerm f M 4 :=
  LinearMap.prod
    ((glueingDifferential f (TensorProduct R M S) 2).comp
        (LinearMap.fst R (GlueingTerm f (TensorProduct R M S) 2) (GlueingTerm f M 3)) +
      (localizationTensorMap S f M 3).comp
        (LinearMap.snd R (GlueingTerm f (TensorProduct R M S) 2) (GlueingTerm f M 3)))
    ((glueingDifferential f M 3).comp
      (LinearMap.snd R (GlueingTerm f (TensorProduct R M S) 2) (GlueingTerm f M 3)))

/-- The third and fourth maps of the glueing complex compose to zero. -/
public theorem glueingDelta_comp_glueingGamma {R : Type u} [CommRing R] (S : Type v)
    [CommRing S] [Algebra R S] {r : ℕ} (f : Fin r → R) (M : Type w) [AddCommGroup M]
    [Module R M] :
    glueingDelta S f M ∘ₗ glueingGamma S f M = 0 := by
  refine LinearMap.ext fun ⟨y, x⟩ ↦ Prod.ext ?_ ?_
  · show glueingDifferential f (M ⊗[R] S) (1 + 1)
        (glueingDifferential f (M ⊗[R] S) 1 y - localizationTensorMap S f M (1 + 1) x) +
      localizationTensorMap S f M (2 + 1) (glueingDifferential f M 2 x) = 0
    rw [localizationTensorMap_differential, map_sub,
      ← LinearMap.comp_apply (glueingDifferential f (M ⊗[R] S) (1 + 1)),
      glueingDifferential_comp_glueingDifferential, LinearMap.zero_apply, zero_sub,
      neg_add_cancel]
  · show glueingDifferential f M (2 + 1) (glueingDifferential f M 2 x) = 0
    rw [← LinearMap.comp_apply, glueingDifferential_comp_glueingDifferential,
      LinearMap.zero_apply]

/-- **Exactness of the glueing complex at its fourth term.** If `R → S` is flat and induces an
isomorphism modulo the ideal generated by `f`, then every element killed by the fourth map of the
glueing complex of `M` is in the image of its third map. -/
public theorem glueingComplex_exact_fourth
    (R : Type u) (S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    {r : ℕ} (f : Fin r → R) (M : Type u) [AddCommGroup M] [Module R M]
    (hflat : Module.Flat R S)
    (hq : Function.Bijective
      (Ideal.quotientMap
        ((Ideal.span (Set.range f)).map (algebraMap R S))
        (algebraMap R S) Ideal.le_comap_map))
    (y : GlueingTerm f (TensorProduct R M S) 2) (x : GlueingTerm f M 3)
    (h : glueingDelta S f M (y, x) = 0) :
    ∃ z : GlueingTerm f (TensorProduct R M S) 1 × GlueingTerm f M 2,
      glueingGamma S f M z = (y, x) := by
  set I := Ideal.span (Set.range f)
  have h₁ : glueingDifferential f (M ⊗[R] S) 2 y + localizationTensorMap S f M 3 x = 0 :=
    congrArg Prod.fst h
  have h₂ : glueingDifferential f M 3 x = 0 := congrArg Prod.snd h
  let e₁ := glueingTermTensorEquiv f M S 1
  let e₂ := glueingTermTensorEquiv f M S 2
  let e₃ := glueingTermTensorEquiv f M S 3
  have hx : x ⊗ₜ[R] (1 : S) ∈ LinearMap.range ((glueingDifferential f M 2).rTensor S) := by
    refine ⟨e₂.symm (-y), e₃.injective ?_⟩
    show glueingTermTensorEquiv f M S (2 + 1) _ = glueingTermTensorEquiv f M S (2 + 1) _
    rw [glueingTermTensorEquiv_differential, LinearEquiv.apply_symm_apply, map_neg,
      glueingTermTensorEquiv_unit_deg]
    exact neg_eq_iff_add_eq_zero.mpr h₁
  obtain ⟨w, hw⟩ := mem_range_of_tmul_one_mem_range_rTensor I hflat hq
    (glueingDifferential_comp_glueingDifferential f M 2)
    (isIPowerTorsion_cohomologyModule_glueingDifferential f M 2) h₂ hx
  have hy' : (glueingDifferential f M 2).rTensor S
      (e₂.symm (y + localizationTensorMap S f M 2 w)) = 0 := by
    apply e₃.injective
    show glueingTermTensorEquiv f M S (2 + 1) _ = glueingTermTensorEquiv f M S (2 + 1) 0
    rw [glueingTermTensorEquiv_differential, LinearEquiv.apply_symm_apply, map_add,
      ← localizationTensorMap_differential, hw, map_zero]
    exact h₁
  obtain ⟨v, hv, t, ht⟩ := exists_eq_tmul_one_add_of_rTensor_eq_zero I hflat hq
    (glueingDifferential_comp_glueingDifferential f M 1)
    (isIPowerTorsion_cohomologyModule_glueingDifferential f M 1) hy'
  have ht' : glueingDifferential f (M ⊗[R] S) 1 (e₁ t) =
      y + localizationTensorMap S f M 2 w - localizationTensorMap S f M 2 v := by
    rw [← glueingTermTensorEquiv_differential, ht, map_sub, LinearEquiv.apply_symm_apply,
      glueingTermTensorEquiv_unit_deg]
  refine ⟨(e₁ t, w - v), Prod.ext ?_ ?_⟩
  · show glueingDifferential f (M ⊗[R] S) 1 (e₁ t) - localizationTensorMap S f M 2 (w - v) = y
    rw [ht', map_sub]
    abel
  · show glueingDifferential f M 2 (w - v) = x
    rw [map_sub, hv, sub_zero, hw]

end FormalGlueing
