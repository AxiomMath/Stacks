module

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.HomotopyCategory.KProjective
public import Mathlib.Algebra.Homology.Double
public import Mathlib.RingTheory.Localization.Away.Basic


@[expose] public noncomputable section

universe u v


open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

/-- The differential in the standard countable free resolution of `A[1/f]`. -/
public noncomputable def telescopeDifferential (A : Type u) [CommRing A] (f : A) :
    (ℕ →₀ A) →ₗ[A] (ℕ →₀ A) :=
  Finsupp.linearCombination A fun n ↦
    Finsupp.single n 1 - Finsupp.single (n + 1) f

public theorem telescopeDifferential_single (A : Type u) [CommRing A]
    (f coefficient : A) (index : ℕ) :
    telescopeDifferential A f (Finsupp.single index coefficient) =
      Finsupp.single index coefficient - Finsupp.single (index + 1) (f * coefficient) := by
  classical
  rw [telescopeDifferential, Finsupp.linearCombination_single]
  rw [smul_sub]
  congr 1 <;> ext n <;> simp [mul_comm]

public def powerDenominator (A : Type u) [CommRing A] (f : A) (n : ℕ) :
    Submonoid.powers f :=
  ⟨f ^ n, (Submonoid.mem_powers_iff (f ^ n) f).2 ⟨n, rfl⟩⟩

/-- The augmentation in the standard countable free resolution of `A[1/f]`. -/
public noncomputable def telescopeAugmentation (A : Type u) [CommRing A] (f : A) :
    (ℕ →₀ A) →ₗ[A] Localization.Away f :=
  Finsupp.linearCombination A fun n ↦
    IsLocalization.mk' (Localization.Away f) 1 (powerDenominator A f n)

public theorem telescopeAugmentation_single (A : Type u) [CommRing A]
    (f coefficient : A) (index : ℕ) :
    telescopeAugmentation A f (Finsupp.single index coefficient) =
      IsLocalization.mk' (Localization.Away f) coefficient
        (powerDenominator A f index) := by
  classical
  rw [telescopeAugmentation, Finsupp.linearCombination_single]
  exact IsLocalization.smul_mk'_one coefficient (powerDenominator A f index)

public theorem telescopeDifferential_apply_zero (A : Type u) [CommRing A]
    (f : A) (x : ℕ →₀ A) : telescopeDifferential A f x 0 = x 0 := by
  classical
  induction x using Finsupp.induction with
  | zero => simp
  | @single_add p a x hp ha ih =>
      rw [map_add, Finsupp.add_apply, ih, telescopeDifferential_single]
      simp [Finsupp.single_apply]

public theorem telescopeDifferential_apply_succ (A : Type u) [CommRing A]
    (f : A) (x : ℕ →₀ A) (n : ℕ) :
    telescopeDifferential A f x (n + 1) = x (n + 1) - f * x n := by
  classical
  induction x using Finsupp.induction with
  | zero => simp
  | @single_add p a x hp ha ih =>
      change (telescopeDifferential A f (Finsupp.single p a + x)) (n + 1) = _
      rw [congrArg (fun z : ℕ →₀ A => z (n + 1))
        ((telescopeDifferential A f).map_add (Finsupp.single p a) x)]
      change (telescopeDifferential A f (Finsupp.single p a)) (n + 1) +
        (telescopeDifferential A f x) (n + 1) = _
      rw [ih, telescopeDifferential_single]
      simp only [Finsupp.sub_apply, Finsupp.single_apply]
      split_ifs <;> simp_all [mul_add, sub_eq_add_neg, add_comm]

public theorem telescopeAugmentation_surjective (A : Type u) [CommRing A] (f : A) :
    Function.Surjective (telescopeAugmentation A f) := by
  intro z
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers f) z
  obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff (s : A) f).1 s.property
  have hs : s = powerDenominator A f n := Subtype.ext hn.symm
  rw [hs]
  exact ⟨Finsupp.single n a, telescopeAugmentation_single A f a n⟩

public theorem telescopeAugmentation_comp_differential
    (A : Type u) [CommRing A] (f : A) (x : ℕ →₀ A) :
    telescopeAugmentation A f (telescopeDifferential A f x) = 0 := by
  classical
  induction x using Finsupp.induction with
  | zero => simp
  | @single_add n a x hn ha ih =>
      rw [map_add, telescopeDifferential_single,
        (telescopeAugmentation A f).map_add, (telescopeAugmentation A f).map_sub,
        telescopeAugmentation_single, telescopeAugmentation_single, ih, add_zero]
      apply sub_eq_zero.mpr
      rw [IsLocalization.mk'_eq_iff_eq]
      simp [powerDenominator, pow_succ, mul_assoc, mul_comm]
      ring

public theorem telescopeDifferential_injective (A : Type u) [CommRing A] (f : A) :
    Function.Injective (telescopeDifferential A f) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro x hx
  ext n
  induction n with
  | zero => simpa [telescopeDifferential_apply_zero] using DFunLike.congr_fun hx 0
  | succ n ih => simpa [telescopeDifferential_apply_succ, ih] using DFunLike.congr_fun hx (n + 1)

public theorem telescope_shift_range (A : Type u) [CommRing A]
    (f coefficient : A) (index length : ℕ) :
    Finsupp.single index coefficient -
        Finsupp.single (index + length) (f ^ length * coefficient) ∈
      LinearMap.range (telescopeDifferential A f) := by
  classical
  induction length with
  | zero => simp
  | succ length ih =>
      have hsingle := telescopeDifferential_single A f (f ^ length * coefficient)
        (index + length)
      convert (LinearMap.range (telescopeDifferential A f)).add_mem ih ⟨_, hsingle⟩ using 1
      ext n
      simp only [Finsupp.add_apply, Finsupp.sub_apply, Finsupp.single_apply]
      split_ifs <;> (try omega) <;> ring_nf

public theorem telescope_collect_range (A : Type u) [CommRing A]
    (f : A) (coefficients : ℕ →₀ A) (bound : ℕ)
    (hbound : ∀ index ∈ coefficients.support, index ≤ bound) :
    coefficients - Finsupp.single bound
        (coefficients.sum fun index coefficient => f ^ (bound - index) * coefficient) ∈
      LinearMap.range (telescopeDifferential A f) := by
  classical
  induction coefficients using Finsupp.induction with
  | zero => simp
  | @single_add index coefficient coefficients hindex hcoeff ih =>
      have hcindex : coefficients index = 0 := by
        simpa [Finsupp.mem_support_iff] using hindex
      have hib : index ≤ bound := hbound index (by
        rw [Finsupp.mem_support_iff]
        simp [hcindex, hcoeff])
      have hcb : ∀ i ∈ coefficients.support, i ≤ bound := by
        intro i hi
        apply hbound i
        rw [Finsupp.mem_support_iff] at hi ⊢
        by_cases hii : i = index
        · subst i
          simp [hcindex, hcoeff]
        · simpa [Finsupp.single_apply, hii] using hi
      have hs := telescope_shift_range A f coefficient index (bound - index)
      rw [Nat.add_sub_of_le hib] at hs
      have hi := ih hcb
      have hr := (LinearMap.range (telescopeDifferential A f)).add_mem hs hi
      have hsum : (Finsupp.single index coefficient + coefficients).sum
          (fun i c => f ^ (bound - i) * c) =
          f ^ (bound - index) * coefficient +
            coefficients.sum (fun i c => f ^ (bound - i) * c) := by
        rw [Finsupp.sum_add_index]
        · rw [Finsupp.sum_single_index]
          simp
        · intro i hi
          simp
        · intro i hi x y
          simp [mul_add]
      rw [hsum]
      simpa [sub_eq_add_neg, add_assoc,
        add_left_comm, add_comm] using hr

public theorem telescope_kernel_le_range (A : Type u) [CommRing A] (f : A) :
    LinearMap.ker (telescopeAugmentation A f) ≤
      LinearMap.range (telescopeDifferential A f) := by
  classical
  intro coefficients hkernel
  let bound := coefficients.support.sup id
  let weighted := coefficients.sum fun index coefficient =>
    f ^ (bound - index) * coefficient
  have hbound : ∀ index ∈ coefficients.support, index ≤ bound := by
    intro index hindex
    exact Finset.le_sup (f := id) hindex
  have hcollect := telescope_collect_range A f coefficients bound hbound
  obtain ⟨preimage, hpreimage⟩ := hcollect
  have hsingleAug : telescopeAugmentation A f
      (Finsupp.single bound weighted) = 0 := by
    have hdiff := telescopeAugmentation_comp_differential A f preimage
    rw [hpreimage, map_sub] at hdiff
    rw [LinearMap.mem_ker] at hkernel
    simpa [hkernel] using hdiff
  rw [telescopeAugmentation_single] at hsingleAug
  obtain ⟨denominator, hdenominator⟩ :=
    (IsLocalization.mk'_eq_zero_iff weighted (powerDenominator A f bound)).1 hsingleAug
  obtain ⟨length, hlength⟩ :=
    (Submonoid.mem_powers_iff (denominator : A) f).1 denominator.property
  have hzero : f ^ length * weighted = 0 := by
    simpa [hlength] using hdenominator
  have hsingle := telescope_shift_range A f weighted bound length
  simp only [hzero, Finsupp.single_zero, sub_zero] at hsingle
  have hadd := (LinearMap.range (telescopeDifferential A f)).add_mem
    (⟨preimage, hpreimage⟩ : coefficients - Finsupp.single bound weighted ∈
      LinearMap.range (telescopeDifferential A f)) hsingle
  simpa [sub_add_cancel] using hadd

public theorem telescope_range_eq_kernel (A : Type u) [CommRing A] (f : A) :
    LinearMap.range (telescopeDifferential A f) =
      LinearMap.ker (telescopeAugmentation A f) := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    rw [LinearMap.mem_ker]
    exact telescopeAugmentation_comp_differential A f x
  · exact telescope_kernel_le_range A f

/-- Exactness of the standard countable free presentation of `A[1/f]`. -/
public theorem telescopeResolution_exact (A : Type u) [CommRing A] (f : A) :
    Function.Injective (telescopeDifferential A f) ∧
      LinearMap.range (telescopeDifferential A f) =
        LinearMap.ker (telescopeAugmentation A f) ∧
      Function.Surjective (telescopeAugmentation A f) :=
  ⟨telescopeDifferential_injective A f, telescope_range_eq_kernel A f,
    telescopeAugmentation_surjective A f⟩

public noncomputable def telescopeResolution (A : Type u) [CommRing A] (f : A) :
    CochainComplex (ModuleCat.{u} A) ℤ :=
  HomologicalComplex.double (ModuleCat.ofHom (telescopeDifferential A f))
    (show (ComplexShape.up ℤ).Rel (-1) 0 by simp)

public noncomputable def telescopeResolutionAugmentation
    (A : Type u) [CommRing A] (f : A) :
    telescopeResolution A f ⟶
      (CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj
        (ModuleCat.of A (Localization.Away f)) :=
  HomologicalComplex.mkHomFromDouble
    (show (ComplexShape.up ℤ).Rel (-1) 0 by simp) (by omega : (-1 : ℤ) ≠ 0)
    0 (ModuleCat.ofHom (telescopeAugmentation A f))
    (by
      simp only [zero_comp]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      exact (telescopeAugmentation_comp_differential A f x).symm)
    (by
      intro i hi
      exact comp_zero)

set_option backward.isDefEq.respectTransparency false in
public theorem telescopeResolutionAugmentation_quasiIso
    (ring : Type u) [CommRing ring] (element : ring) :
    QuasiIso (telescopeResolutionAugmentation ring element) := by
  apply (quasiIso_iff _).2
  intro degree
  by_cases degree_zero : degree = 0
  · subst degree
    rw [quasiIsoAt_iff' _ (-1) 0 1 (by simp) (by simp)]
    let comparison := (HomologicalComplex.shortComplexFunctor' (ModuleCat ring)
      (ComplexShape.up ℤ) (-1) 0 1).map (telescopeResolutionAugmentation ring element)
    change ShortComplex.QuasiIso comparison
    have source_d : (telescopeResolution ring element).d 0 1 = 0 :=
      HomologicalComplex.double_d_eq_zero₀ _ _ 0 1 (by norm_num)
    have target_in : (((CochainComplex.singleFunctor (ModuleCat ring) 0).obj
        (ModuleCat.of ring (Localization.Away element))).d (-1) 0) = 0 := rfl
    have target_out : (((CochainComplex.singleFunctor (ModuleCat ring) 0).obj
        (ModuleCat.of ring (Localization.Away element))).d 0 1) = 0 := rfl
    apply (ShortComplex.quasiIso_iff_of_zeros' comparison source_d target_in target_out).2
    constructor
    · rw [ShortComplex.moduleCat_exact_iff]
      intro cycle cycle_zero
      let firstIso := HomologicalComplex.doubleXIso₀
        (ModuleCat.ofHom (telescopeDifferential ring element))
        (show (ComplexShape.up ℤ).Rel (-1) 0 by simp)
      let secondIso := HomologicalComplex.doubleXIso₁
        (ModuleCat.ofHom (telescopeDifferential ring element))
        (show (ComplexShape.up ℤ).Rel (-1) 0 by simp) (by omega : (-1 : ℤ) ≠ 0)
      change (telescopeResolutionAugmentation ring element).f 0 cycle = 0 at cycle_zero
      rw [telescopeResolutionAugmentation, HomologicalComplex.mkHomFromDouble_f₁] at cycle_zero
      change telescopeAugmentation ring element (secondIso.hom cycle) = 0 at cycle_zero
      obtain ⟨preimage, preimage_eq⟩ :=
        (show secondIso.hom cycle ∈ LinearMap.range (telescopeDifferential ring element) from by
          rw [telescope_range_eq_kernel]
          exact cycle_zero)
      refine ⟨firstIso.inv preimage, ?_⟩
      change (telescopeResolution ring element).d (-1) 0 (firstIso.inv preimage) = cycle
      have differential_eq : (telescopeResolution ring element).d (-1) 0 =
          firstIso.hom ≫ ModuleCat.ofHom (telescopeDifferential ring element) ≫ secondIso.inv :=
        HomologicalComplex.double_d _ _ (by omega)
      rw [differential_eq]
      change secondIso.inv (telescopeDifferential ring element
        (firstIso.hom (firstIso.inv preimage))) = cycle
      have cancel_first : firstIso.hom (firstIso.inv preimage) = preimage := by
        exact ConcreteCategory.congr_hom firstIso.inv_hom_id preimage
      rw [cancel_first, preimage_eq]
      exact ConcreteCategory.congr_hom secondIso.hom_inv_id cycle
    · change Epi ((telescopeResolutionAugmentation ring element).f 0)
      rw [telescopeResolutionAugmentation, HomologicalComplex.mkHomFromDouble_f₁]
      have : Epi (ModuleCat.ofHom (telescopeAugmentation ring element)) :=
        (ModuleCat.epi_iff_surjective _).2 (telescopeAugmentation_surjective ring element)
      infer_instance
  · apply (quasiIsoAt_iff_exactAt' _ degree
      (HomologicalComplex.ExactAt.of_isZero
        (HomologicalComplex.isZero_single_obj_X _ _ _ _ degree_zero))).2
    by_cases degree_neg_one : degree = -1
    · subst degree
      rw [HomologicalComplex.exactAt_iff' _ (-2) (-1) 0 (by simp) (by simp)]
      apply (ShortComplex.exact_iff_mono _ ?_).2
      · change Mono ((telescopeResolution ring element).d (-1) 0)
        rw [telescopeResolution, HomologicalComplex.double_d _ _ (by omega)]
        have : Mono (ModuleCat.ofHom (telescopeDifferential ring element)) :=
          (ModuleCat.mono_iff_injective _).2 (telescopeDifferential_injective ring element)
        infer_instance
      · change (telescopeResolution ring element).d (-2) (-1) = 0
        exact HomologicalComplex.double_d_eq_zero₀ _
          (show (ComplexShape.up ℤ).Rel (-1) 0 by simp) (-2) (-1) (by norm_num)
    · exact HomologicalComplex.ExactAt.of_isZero
        (HomologicalComplex.isZero_double_X _ _ degree degree_neg_one degree_zero)

public noncomputable def freeHomProductEquiv
    (ring : Type u) [CommRing ring] (target : Type v)
    [AddCommGroup target] [Module ring target] :
    ((ℕ →₀ ring) →ₗ[ring] target) ≃ₗ[ring] (ℕ → target) where
  toFun linear index := linear (Finsupp.single index 1)
  invFun sequence := Finsupp.linearCombination ring sequence
  left_inv linear := by
    apply Finsupp.lhom_ext
    intro index coefficient
    simp only [Finsupp.linearCombination_single]
    rw [← map_smul]
    congr 1
    ext other
    simp
  right_inv sequence := by
    funext index
    simp only [Finsupp.linearCombination_single, one_smul]
  map_add' left right := rfl
  map_smul' coefficient linear := rfl

public theorem freeHomProductEquiv_precompose_telescope
    (ring : Type u) [CommRing ring] (target : Type v)
    [AddCommGroup target] [Module ring target]
    (element : ring) (linear : (ℕ →₀ ring) →ₗ[ring] target) (index : ℕ) :
    freeHomProductEquiv ring target (linear.comp (telescopeDifferential ring element)) index =
      freeHomProductEquiv ring target linear index -
        element • freeHomProductEquiv ring target linear (index + 1) := by
  change linear (telescopeDifferential ring element (Finsupp.single index 1)) = _
  rw [telescopeDifferential_single, mul_one, map_sub]
  change _ - linear (Finsupp.single (index + 1) element) =
    _ - element • linear (Finsupp.single (index + 1) 1)
  congr 1
  rw [← map_smul]
  congr 1
  ext other
  simp
