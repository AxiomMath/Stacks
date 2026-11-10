module

public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import StacksFrontier.AlgebraicGeometry.Crystalline.Examples.AffineSpaceDeRhamTopCoefficients

/-!
# The top cohomology of the completed de Rham complex of affine space

In the setup of the example of [Stacks, Tag 07LK], for `r > 0` variables, this module proves the
conclusions (3) and (4) of the source for the top cohomology `H^r` of the complex
`D → Ω¹_D → ⋯ → Ω^r_D` of `Crystalline.AffineSpaceCrystallineSetup.deRhamComplexNat`:

* `Crystalline.AffineSpaceCrystallineSetup.infinite_homology_top`: `H^r` is infinite;
* `Crystalline.AffineSpaceCrystallineSetup.not_isTorsion_homology_top`: `H^r` is not a torsion
  abelian group (`not_isTorsion_int_homology_top`: not a torsion `ℤ`-module);
* `Crystalline.AffineSpaceCrystallineSetup.not_isHausdorff_homology_top`: `H^r` is not separated
  for the `p`-adic topology; explicitly
  (`Crystalline.AffineSpaceCrystallineSetup.exists_ne_zero_forall_eq_pow_nsmul_homology_top`) it
  has a nonzero element divisible by every power of `p`.

## The argument

Since `Ω^{r+1}_D = 0`, a class in `H^r` is the class of a form in `Ω^r_D` modulo the image of
`d : Ω^{r-1}_D → Ω^r_D` (`exists_homologyClass_top`).  Writing `m(N) = (N, …, N)` for the
diagonal multi-index and `dx = dx_1 ∧ ⋯ ∧ dx_r`, the coefficient of
`x^{m(p^k - 1)} dx` of an exact form is divisible by `p^k`, and for each exact form even by
`p^{k+1}` for all but finitely many `k`
(`StacksFrontier.AlgebraicGeometry.Crystalline.Examples.AffineSpaceDeRhamTopCoefficients`).  Then:

* `ω = ∑_{e ≥ 0} p^e x^{m(p^{2e} - 1)} dx` has non-torsion class: if `n ω = d y` then comparing
  coefficients at `x^{m(p^{2e} - 1)} dx` makes `p^{2e}` divide `n p^e`, so `p^e ∣ n` for all `e`;
  the multiples of its class are pairwise distinct, so `H^r` is infinite.
* `η = ∑_{e ≥ 0} p^e x^{m(p^e - 1)} dx` has class divisible by every `p^t`, its partial sums
  being exact — `p^e x^{m(p^e - 1)} dx = d(x_1^{p^e} x_2^{p^e - 1} ⋯ x_r^{p^e - 1}
  dx_2 ∧ ⋯ ∧ dx_r)` — and is not exact, since its coefficient at `x^{m(p^e - 1)} dx` is exactly
  `p^e`.

These are the source's own `ω` and `η` for `r = 1`, the case treated by the two term complex of
`StacksFrontier.AlgebraicGeometry.Crystalline.Examples.AffineLineDeRhamCohomology`.

## References

* [Stacks Project, Tag 07LK](https://stacks.math.columbia.edu/tag/07LK)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace Crystalline

namespace AffineSpaceCrystallineSetup

variable (T : AffineSpaceCrystallineSetup)

/-! ### Differentials of polynomials and of polynomial forms -/

/-- The differential of (the image in `D` of) a polynomial is `∑_k (∂f/∂x_k) dx_k`. -/
public theorem differential_algebraMap_eq_sum (f : T.P) :
    T.differential (algebraMap T.P T.D f) =
      ∑ k, algebraMap T.P T.D (MvPolynomial.pderiv k f) • T.coordinateDifferential k := by
  classical
  induction f using MvPolynomial.induction_on with
  | C a =>
    have hC : algebraMap T.P T.D (MvPolynomial.C a) = algebraMap T.A T.D a := by
      rw [show (MvPolynomial.C a : T.P) = algebraMap T.A T.P a from rfl]
      exact (IsScalarTower.algebraMap_apply T.A T.P T.D a).symm
    rw [hC, T.differential_algebraMap]
    simp
  | add f g hf hg =>
    rw [map_add, T.differential_add, hf, hg, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [map_add, map_add, add_smul]
  | mul_X f i hf =>
    have h1 : ∀ k, algebraMap T.P T.D (MvPolynomial.pderiv k (f * MvPolynomial.X i)) •
        T.coordinateDifferential k =
        (if i = k then algebraMap T.P T.D f • T.coordinateDifferential k else 0) +
          algebraMap T.P T.D (MvPolynomial.X i) •
            (algebraMap T.P T.D (MvPolynomial.pderiv k f) • T.coordinateDifferential k) := by
      intro k
      rw [Derivation.leibniz, MvPolynomial.pderiv_X, smul_eq_mul, smul_eq_mul, map_add, map_mul,
        map_mul, add_smul]
      by_cases hk : i = k
      · subst hk
        simp [mul_smul]
      · simp [hk, mul_smul]
    rw [Finset.sum_congr rfl fun k _ ↦ h1 k, Finset.sum_add_distrib, Finset.sum_ite_eq,
      ite_eq_left (Finset.mem_univ _), ← Finset.smul_sum, ← hf, map_mul, T.differential_mul]
    rfl

/-- The de Rham differential of `g dx_{σ(1)} ∧ ⋯ ∧ dx_{σ(s)}` is
`dg ∧ dx_{σ(1)} ∧ ⋯ ∧ dx_{σ(s)}`. -/
public theorem deRhamDifferential_smul_wedgeCoordinates {s : ℕ} (g : T.D)
    (σ : Fin s → Fin T.r) :
    T.deRhamDifferential s (g • T.wedgeCoordinates σ) =
      (exteriorPower.ιMulti T.D (s + 1)
        (Matrix.vecCons (T.differential g) (T.coordinateDifferential ∘ σ)) :
          T.forms (s + 1)) := by
  have hgen := (dividedPowerDeRhamComplex (A := T.A)
    T.completedDividedPowers).differential_generator s
      (Fin.cons g fun j ↦ algebraMap T.P T.D (MvPolynomial.X (σ j)))
  simp only [Fin.cons_zero, Fin.cons_succ] at hgen
  have hfun : (fun j : Fin (s + 1) ↦ dividedPowerDifferential (A := T.A)
      T.completedDividedPowers
      ((Fin.cons g fun j ↦ algebraMap T.P T.D (MvPolynomial.X (σ j)) :
        Fin (s + 1) → T.D) j)) =
      Matrix.vecCons (T.differential g) (T.coordinateDifferential ∘ σ) := by
    funext j
    refine Fin.cases ?_ (fun j ↦ ?_) j
    · rfl
    · simp only [Fin.cons_succ, Matrix.cons_val_succ, Function.comp_apply]
      rfl
  rwa [hfun] at hgen

/-! ### The top wedge -/

variable {s : ℕ} (hs : T.r = s + 1)

/-- The top wedge `dx_1 ∧ ⋯ ∧ dx_r` in `Ω^r_{D/A,δ}`, for `r = s + 1`. -/
public def topWedge : T.forms (s + 1) := T.wedgeCoordinates (Fin.cast hs.symm)

/-- The top functional reads `g` off `g dx_1 ∧ ⋯ ∧ dx_r`. -/
public theorem topFunctional_smul_topWedge (g : T.D) :
    T.topFunctional hs (g • T.topWedge hs) = g := by
  rw [map_smul, topWedge, wedgeCoordinates, topFunctional_ιMulti]
  have h1 : (Matrix.of fun j l ↦ T.coordinateFunctional (Fin.cast hs.symm l)
      ((T.coordinateDifferential ∘ Fin.cast hs.symm) j)) = 1 := by
    ext j l
    simp only [Matrix.of_apply, Function.comp_apply,
      coordinateFunctional_coordinateDifferential, Matrix.one_apply, Fin.cast_inj]
  rw [h1, Matrix.det_one, smul_eq_mul, mul_one]

/-- The top coefficients of `f dx_1 ∧ ⋯ ∧ dx_r`, for a polynomial `f`, are the coefficients
of `f`. -/
public theorem topCoeffForms_smul_topWedge (m : Fin T.r →₀ ℕ) (f : T.P) :
    T.topCoeffForms hs m (algebraMap T.P T.D f • T.topWedge hs) = f.coeff m := by
  rw [topCoeffForms_apply, topFunctional_smul_topWedge, monomialCoeff_algebraMap]

/-- The image in `D` of the monomial `x^m`. -/
public def monomialD (m : Fin T.r →₀ ℕ) : T.D :=
  algebraMap T.P T.D (MvPolynomial.monomial m 1)

/-- The map `P → D` commutes with the scalars of `𝐙_p`. -/
public theorem algebraMap_smul_polynomial (a : T.A) (f : T.P) :
    algebraMap T.P T.D (a • f) = a • algebraMap T.P T.D f := by
  rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply, ← Algebra.smul_def]

/-- The differential of `x_1^{N+1} x_2^N ⋯ x_r^N dx_2 ∧ ⋯ ∧ dx_r` is
`(N + 1) x_1^N ⋯ x_r^N dx_1 ∧ ⋯ ∧ dx_r`. -/
public theorem deRhamDifferential_monomial_smul_wedgeCoordinates (N : ℕ) :
    T.deRhamDifferential s
      (T.monomialD (T.diagMonomial N + Finsupp.single (Fin.cast hs.symm 0) 1) •
        T.wedgeCoordinates (Fin.cast hs.symm ∘ Fin.succ)) =
      ((N + 1 : ℕ) : T.A) • (T.monomialD (T.diagMonomial N) • T.topWedge hs) := by
  classical
  rw [deRhamDifferential_smul_wedgeCoordinates, monomialD, differential_algebraMap_eq_sum]
  have hupd : ∀ v : T.differentials,
      (exteriorPower.ιMulti T.D (s + 1)
        (Matrix.vecCons v (T.coordinateDifferential ∘ Fin.cast hs.symm ∘ Fin.succ)) :
          T.forms (s + 1)) =
        exteriorPower.ιMulti T.D (s + 1) (Function.update
          (Matrix.vecCons 0 (T.coordinateDifferential ∘ Fin.cast hs.symm ∘ Fin.succ)) 0 v) := by
    intro v
    rw [Matrix.vecCons, Matrix.vecCons, Fin.update_cons_zero]
  rw [hupd, AlternatingMap.map_update_sum, Finset.sum_eq_single (Fin.cast hs.symm 0)]
  · rw [AlternatingMap.map_update_smul, ← hupd]
    have hcons : Matrix.vecCons (T.coordinateDifferential (Fin.cast hs.symm 0))
        (T.coordinateDifferential ∘ Fin.cast hs.symm ∘ Fin.succ) =
          T.coordinateDifferential ∘ Fin.cast hs.symm := by
      rw [← Fin.cons_self_tail (T.coordinateDifferential ∘ Fin.cast hs.symm)]
      rfl
    have hpd : MvPolynomial.pderiv (Fin.cast hs.symm 0)
        (MvPolynomial.monomial (T.diagMonomial N + Finsupp.single (Fin.cast hs.symm 0) 1)
          (1 : T.A)) = ((N + 1 : ℕ) : T.A) • MvPolynomial.monomial (T.diagMonomial N) 1 := by
      rw [MvPolynomial.pderiv_monomial, add_tsub_cancel_right, MvPolynomial.smul_monomial,
        smul_eq_mul, mul_one, one_mul]
      simp
    rw [hcons, hpd, algebraMap_smul_polynomial]
    change ((((N + 1 : ℕ) : T.A) • T.monomialD (T.diagMonomial N)) • T.topWedge hs :
      T.forms (s + 1)) = _
    exact smul_assoc _ _ _
  · intro k _ hk
    rw [AlternatingMap.map_update_smul, ← hupd]
    have hne : Fin.cast hs k ≠ 0 := by
      intro h
      apply hk
      rw [← h]
      rfl
    obtain ⟨j, hj⟩ := Fin.exists_succ_eq.mpr hne
    have hk' : Fin.cast hs.symm j.succ = k := by
      rw [hj]
      rfl
    have heq : Matrix.vecCons (T.coordinateDifferential k)
        (T.coordinateDifferential ∘ Fin.cast hs.symm ∘ Fin.succ) 0 =
        Matrix.vecCons (T.coordinateDifferential k)
          (T.coordinateDifferential ∘ Fin.cast hs.symm ∘ Fin.succ) j.succ := by
      rw [Matrix.cons_val_zero, Matrix.cons_val_succ, Function.comp_apply, Function.comp_apply,
        hk']
    have hz := (exteriorPower.ιMulti T.D (s + 1)).map_eq_zero_of_eq _ heq
      (Fin.succ_ne_zero j).symm
    rw [hz, smul_zero]
  · exact fun h ↦ absurd (Finset.mem_univ _) h

/-! ### Two power series of top forms -/

/-- Membership in the `t`-th step of the `a`-adic filtration: being a multiple of `a^t`. -/
private lemma mem_span_pow_smul_top_iff {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (a : R) (t : ℕ) (x : M) :
    x ∈ (Ideal.span {a} ^ t • (⊤ : Submodule R M)) ↔ ∃ v, a ^ t • v = x := by
  rw [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
    Submodule.mem_smul_pointwise_iff_exists]
  simp

/-- A `p`-adic integer divisible by every power of `p` vanishes. -/
public theorem eq_zero_of_forall_pow_dvd {a : T.A} (h : ∀ t, (T.p : T.A) ^ t ∣ a) : a = 0 := by
  refine IsHausdorff.haus (inferInstance : IsHausdorff T.baseIdeal T.A) a fun t ↦ ?_
  obtain ⟨c, hc⟩ := h t
  rw [SModEq.zero, hc]
  exact T.pow_mul_mem_baseIdeal_pow_smul t c

/-- An element of `Ω^i_D` whose level `t` is the class of `ω` is `ω` up to `p^t`. -/
public theorem eq_ofForms_add_pow_smul_of_eval (i : ℕ) (ξ : T.completedForms i) (t : ℕ)
    (ω : T.forms i) (h : AdicCompletion.eval T.baseIdeal (T.forms i) t ξ =
      Submodule.Quotient.mk ω) :
    ∃ ξ' : T.completedForms i, ξ = T.ofForms i ω + (T.p : T.A) ^ t • ξ' := by
  have hmem : (show AdicCompletion T.baseIdeal (T.forms i) from ξ) -
      AdicCompletion.of T.baseIdeal (T.forms i) ω ∈
      (T.baseIdeal ^ t • ⊤ : Submodule T.A (AdicCompletion T.baseIdeal (T.forms i))) := by
    rw [AdicCompletion.pow_smul_top_eq_ker_eval (Submodule.fg_span_singleton _),
      LinearMap.mem_ker, map_sub, AdicCompletion.eval_of, h, Submodule.mkQ_apply, sub_self]
  obtain ⟨ξ', hξ'⟩ := (mem_span_pow_smul_top_iff _ _ _).mp hmem
  exact ⟨ξ', eq_add_of_sub_eq' hξ'.symm⟩

/-- The partial sums `∑_{e < t} p^e x^{m(a(e))} dx_1 ∧ ⋯ ∧ dx_r`. -/
public def seriesPartial (a : ℕ → ℕ) (t : ℕ) : T.forms (s + 1) :=
  ∑ e ∈ Finset.range t,
    (T.p : T.A) ^ e • (T.monomialD (T.diagMonomial (a e)) • T.topWedge hs)

/-- The partial sums form a `p`-adic Cauchy sequence. -/
public theorem seriesPartial_cauchy (a : ℕ → ℕ) (t : ℕ) :
    T.seriesPartial hs a t ≡ T.seriesPartial hs a (t + 1)
      [SMOD (T.baseIdeal ^ t • (⊤ : Submodule T.A (T.forms (s + 1))))] := by
  rw [SModEq.sub_mem, seriesPartial, seriesPartial, Finset.sum_range_succ, sub_add_eq_sub_sub,
    sub_self, zero_sub, neg_mem_iff]
  exact (mem_span_pow_smul_top_iff _ _ _).mpr ⟨_, rfl⟩

/-- The power series `∑_{e ≥ 0} p^e x^{m(a(e))} dx_1 ∧ ⋯ ∧ dx_r` in `Ω^r_D`. -/
public def series (a : ℕ → ℕ) : T.completedForms (s + 1) :=
  AdicCompletion.mk T.baseIdeal (T.forms (s + 1))
    (AdicCompletion.AdicCauchySequence.mk (I := T.baseIdeal) (M := T.forms (s + 1))
      (T.seriesPartial hs a) (T.seriesPartial_cauchy hs a))

/-- The series is its `t`-th partial sum up to `p^t`. -/
public theorem exists_series_eq (a : ℕ → ℕ) (t : ℕ) :
    ∃ ξ' : T.completedForms (s + 1),
      T.series hs a = T.ofForms (s + 1) (T.seriesPartial hs a t) + (T.p : T.A) ^ t • ξ' :=
  T.eq_ofForms_add_pow_smul_of_eval (s + 1) _ t _ rfl

/-- The coefficients of the partial sums. -/
public theorem topCoeffForms_seriesPartial {a : ℕ → ℕ} (ha : Function.Injective a) {e t : ℕ}
    (het : e < t) :
    T.topCoeffForms hs (T.diagMonomial (a e)) (T.seriesPartial hs a t) = (T.p : T.A) ^ e := by
  classical
  rw [seriesPartial, map_sum, Finset.sum_eq_single_of_mem e (Finset.mem_range.mpr het)]
  · rw [map_smul, monomialD, topCoeffForms_smul_topWedge, MvPolynomial.coeff_monomial,
      ite_eq_left rfl, smul_eq_mul, mul_one]
  · intro j _ hj
    rw [map_smul, monomialD, topCoeffForms_smul_topWedge, MvPolynomial.coeff_monomial,
      ite_eq_right, smul_zero]
    intro h
    exact hj (ha (T.diagMonomial_injective (Fin.cast hs.symm 0) h))

/-- **The coefficient of `x^{m(a(e))} dx_1 ∧ ⋯ ∧ dx_r` in the series is `p^e`.** -/
public theorem topCoeff_series {a : ℕ → ℕ} (ha : Function.Injective a) (e : ℕ) :
    T.topCoeff hs (T.diagMonomial (a e)) (T.series hs a) = (T.p : T.A) ^ e := by
  rw [← sub_eq_zero]
  refine T.eq_zero_of_forall_pow_dvd fun t ↦ ?_
  obtain ⟨ξ', hξ'⟩ := T.exists_series_eq hs a (max t (e + 1))
  rw [hξ', map_add, map_smul, topCoeff_ofForms,
    T.topCoeffForms_seriesPartial hs ha (Nat.lt_of_lt_of_le (Nat.lt_succ_self e)
      (le_max_right t (e + 1))), add_sub_cancel_left, smul_eq_mul]
  exact (pow_dvd_pow _ (le_max_left t (e + 1))).mul_right _

/-- The partial sums of `η = ∑_{e ≥ 0} p^e x^{m(p^e - 1)} dx_1 ∧ ⋯ ∧ dx_r` are exact. -/
public theorem seriesPartial_eta_eq (t : ℕ) :
    T.seriesPartial hs (fun e ↦ T.p ^ e - 1) t =
      T.deRhamDifferential s (∑ e ∈ Finset.range t,
        T.monomialD (T.diagMonomial (T.p ^ e - 1) + Finsupp.single (Fin.cast hs.symm 0) 1) •
          T.wedgeCoordinates (Fin.cast hs.symm ∘ Fin.succ)) := by
  rw [map_sum, seriesPartial]
  refine Finset.sum_congr rfl fun e _ ↦ ?_
  rw [deRhamDifferential_monomial_smul_wedgeCoordinates (hs := hs),
    Nat.sub_add_cancel (Nat.one_le_pow _ _ (Fact.out : T.p.Prime).pos)]
  push_cast
  rfl

/-! ### The top cohomology as a cokernel -/

include hs in
/-- **The top cohomology is the cokernel of `d : Ω^{r-1}_D → Ω^r_D`**: there is a surjective
additive map `Ω^r_D → H^r` whose kernel is the image of `d`, the term `Ω^{r+1}_D` being zero. -/
public theorem exists_surjective_homologyClass_top :
    ∃ π : T.completedForms (s + 1) →+ T.deRhamComplexNat.homology T.r,
      Function.Surjective π ∧
        ∀ x, π x = 0 ↔ x ∈ LinearMap.range (T.completedDifferential s) := by
  cases T with
  | mk p r =>
  change r = s + 1 at hs
  subst hs
  set T : AffineSpaceCrystallineSetup := ⟨p, s + 1⟩ with hT
  let K := T.deRhamComplexNat
  let S := K.sc' s (s + 1) (s + 2)
  let E : K.homology (s + 1) ≅
      AddCommGrpCat.of ((AddMonoidHom.ker S.g.hom) ⧸ AddMonoidHom.range S.abToCycles) :=
    K.homologyIsoSc' s (s + 1) (s + 2) (CochainComplex.prev_nat_succ s)
      (CochainComplex.next ℕ (s + 1)) ≪≫ S.abHomologyIso
  have : Subsingleton S.X₃ := T.subsingleton_completedForms (show T.r < s + 2 by simp [hT])
  let incl : S.X₂ →+ AddMonoidHom.ker S.g.hom :=
    (AddMonoidHom.id _).codRestrict _ fun x ↦ AddMonoidHom.mem_ker.mpr (Subsingleton.elim _ _)
  refine ⟨E.inv.hom.comp ((QuotientAddGroup.mk' _).comp incl), fun z ↦ ?_, fun x ↦ ?_⟩
  · obtain ⟨⟨x, hx⟩, hxz⟩ := QuotientAddGroup.mk_surjective (E.hom z)
    refine ⟨x, ?_⟩
    have hincl : incl x = ⟨x, hx⟩ := Subtype.ext rfl
    have h1 : (QuotientAddGroup.mk' _ (incl x) :
        (AddMonoidHom.ker S.g.hom) ⧸ AddMonoidHom.range S.abToCycles) = E.hom z := by
      rwa [hincl, QuotientAddGroup.mk'_apply]
    change E.inv.hom (QuotientAddGroup.mk' _ (incl x)) = z
    rw [h1, ← ConcreteCategory.comp_apply, Iso.hom_inv_id]
    rfl
  constructor
  · intro hx
    have h0 : (QuotientAddGroup.mk' _ (incl x) :
        (AddMonoidHom.ker S.g.hom) ⧸ AddMonoidHom.range S.abToCycles) = 0 := by
      have := congrArg E.hom.hom hx
      rwa [map_zero, AddMonoidHom.comp_apply, ← ConcreteCategory.comp_apply,
        Iso.inv_hom_id] at this
    rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff] at h0
    obtain ⟨y, hy⟩ := h0
    exact ⟨y, (T.deRhamComplexNat_d s y).symm.trans (congrArg Subtype.val hy)⟩
  · rintro ⟨y, rfl⟩
    have h0 : (QuotientAddGroup.mk' _ (incl (T.completedDifferential s y)) :
        (AddMonoidHom.ker S.g.hom) ⧸ AddMonoidHom.range S.abToCycles) = 0 := by
      rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]
      exact ⟨y, Subtype.ext (T.deRhamComplexNat_d s y)⟩
    exact (congrArg E.inv.hom h0).trans (map_zero _)

include hs in
/-- **The top cohomology is the cokernel of `d : Ω^{r-1}_D → Ω^r_D`**: there is an additive map
`Ω^r_D → H^r` whose kernel is the image of `d`, the term `Ω^{r+1}_D` being zero. -/
public theorem exists_homologyClass_top :
    ∃ π : T.completedForms (s + 1) →+ T.deRhamComplexNat.homology T.r,
      ∀ x, π x = 0 ↔ x ∈ LinearMap.range (T.completedDifferential s) :=
  (T.exists_surjective_homologyClass_top hs).imp fun _ h ↦ h.2

/-! ### Conclusions (3) and (4) for the top cohomology -/

/-- The exponents `p^e - 1` of the source's `η` are pairwise distinct. -/
public theorem injective_eta : Function.Injective fun e : ℕ ↦ T.p ^ e - 1 := by
  have hp : T.p.Prime := Fact.out
  intro a b h
  have h1 : 1 ≤ T.p ^ a := Nat.one_le_pow _ _ hp.pos
  have h2 : 1 ≤ T.p ^ b := Nat.one_le_pow _ _ hp.pos
  have h3 : T.p ^ a = T.p ^ b := by
    simp only at h
    omega
  exact Nat.pow_right_injective hp.two_le h3

/-- The exponents `p^{2e} - 1` of the source's `ω`. -/
private lemma injective_omega : Function.Injective fun e : ℕ ↦ T.p ^ (2 * e) - 1 :=
  T.injective_eta.comp (mul_right_injective₀ two_ne_zero)

/-- **No nonzero multiple of `ω = ∑_{e ≥ 0} p^e x^{m(p^{2e} - 1)} dx_1 ∧ ⋯ ∧ dx_r` is exact.** -/
public theorem nsmul_series_omega_notMem_range {n : ℕ} (hn : n ≠ 0) :
    n • T.series hs (fun e ↦ T.p ^ (2 * e) - 1) ∉ LinearMap.range (T.completedDifferential s) := by
  have hp : T.p.Prime := Fact.out
  rintro ⟨y, hy⟩
  have hp0 : ∀ k : ℕ, ((T.p : T.A) ^ k) ≠ 0 := fun k ↦
    pow_ne_zero _ (Nat.cast_ne_zero.mpr hp.ne_zero)
  have key : ∀ e : ℕ, (T.p : T.A) ^ e ∣ (n : T.A) := by
    intro e
    have h1 := T.pow_dvd_topCoeff_completedDifferential hs y (2 * e)
    rw [hy, map_nsmul, T.topCoeff_series hs (T.injective_omega) e, nsmul_eq_mul,
      two_mul, pow_add] at h1
    exact (mul_dvd_mul_iff_right (hp0 e)).mp h1
  exact hn (Nat.cast_eq_zero.mp (T.eq_zero_of_forall_pow_dvd key))

/-- **`η = ∑_{e ≥ 0} p^e x^{m(p^e - 1)} dx_1 ∧ ⋯ ∧ dx_r` is not exact.** -/
public theorem series_eta_notMem_range :
    T.series hs (fun e ↦ T.p ^ e - 1) ∉ LinearMap.range (T.completedDifferential s) := by
  have hp : T.p.Prime := Fact.out
  rintro ⟨y, hy⟩
  obtain ⟨B, hB⟩ := T.exists_pow_succ_dvd_topCoeff_completedDifferential hs y
  have h1 := hB B le_rfl
  rw [hy, T.topCoeff_series hs (T.injective_eta) B, pow_succ] at h1
  have hp0 : ((T.p : T.A) ^ B) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr hp.ne_zero)
  exact PadicInt.p_nonunit (p := T.p)
    (isUnit_of_dvd_one (by rwa [← mul_dvd_mul_iff_left hp0, mul_one]))

/-- The class of `η` is divisible by `p^t` for every `t`. -/
public theorem exists_series_eta_eq_add (t : ℕ) :
    ∃ x ∈ LinearMap.range (T.completedDifferential s), ∃ ξ : T.completedForms (s + 1),
      T.series hs (fun e ↦ T.p ^ e - 1) = x + (T.p ^ t) • ξ := by
  obtain ⟨ξ', hξ'⟩ := T.exists_series_eq hs (fun e ↦ T.p ^ e - 1) t
  refine ⟨T.ofForms (s + 1) (T.seriesPartial hs (fun e ↦ T.p ^ e - 1) t),
    ⟨T.ofForms s (∑ e ∈ Finset.range t,
      T.monomialD (T.diagMonomial (T.p ^ e - 1) + Finsupp.single (Fin.cast hs.symm 0) 1) •
        T.wedgeCoordinates (Fin.cast hs.symm ∘ Fin.succ)), ?_⟩, ξ', ?_⟩
  · rw [T.completedDifferential_ofForms, ← T.seriesPartial_eta_eq hs t]
  · rw [hξ', ← Nat.cast_smul_eq_nsmul T.A, Nat.cast_pow]

/-- `r > 0` is `r = s + 1` for some `s`. -/
private lemma exists_eq_succ (hr : 0 < T.r) : ∃ s, T.r = s + 1 := ⟨T.r - 1, by omega⟩

/-- **Conclusion (3) of [Stacks, Tag 07LK] for the displayed complex, second clause.**  For
`r > 0` the top cohomology `H^r` of the completed de Rham complex `D → Ω¹_D → ⋯ → Ω^r_D` of
`D = 𝐙_p[x_1, …, x_r]^∧` is not a torsion abelian group: the class of
`ω = ∑_{e ≥ 0} p^e x_1^{p^{2e} - 1} ⋯ x_r^{p^{2e} - 1} dx_1 ∧ ⋯ ∧ dx_r` has infinite order. -/
public theorem not_isTorsion_homology_top (hr : 0 < T.r) :
    ¬ IsAddTorsion (T.deRhamComplexNat.homology T.r) := by
  obtain ⟨s, hs⟩ := T.exists_eq_succ hr
  obtain ⟨π, hπ⟩ := T.exists_homologyClass_top hs
  intro htor
  obtain ⟨n, hn, hzero⟩ :=
    isOfFinAddOrder_iff_nsmul_eq_zero.mp (htor (π (T.series hs fun e ↦ T.p ^ (2 * e) - 1)))
  rw [← map_nsmul, hπ] at hzero
  exact T.nsmul_series_omega_notMem_range hs hn.ne' hzero

/-- `Crystalline.AffineSpaceCrystallineSetup.not_isTorsion_homology_top`, phrased with torsion
for the `ℤ`-module structure: for `r > 0` the top cohomology `H^r` of the completed de Rham
complex of `D = 𝐙_p[x_1, …, x_r]^∧` is not a torsion `ℤ`-module. -/
public theorem not_isTorsion_int_homology_top (hr : 0 < T.r) :
    ¬ Module.IsTorsion ℤ (T.deRhamComplexNat.homology T.r) :=
  fun h ↦ T.not_isTorsion_homology_top hr (isAddTorsion_iff_isTorsion_int.mpr h)

/-- **Conclusion (3) of [Stacks, Tag 07LK] for the displayed complex, first clause.**  For
`r > 0` the top cohomology `H^r` of the completed de Rham complex `D → Ω¹_D → ⋯ → Ω^r_D` of
`D = 𝐙_p[x_1, …, x_r]^∧` is infinite: the multiples of the class of
`ω = ∑_{e ≥ 0} p^e x_1^{p^{2e} - 1} ⋯ x_r^{p^{2e} - 1} dx_1 ∧ ⋯ ∧ dx_r` are pairwise
distinct. -/
public theorem infinite_homology_top (hr : 0 < T.r) :
    Infinite (T.deRhamComplexNat.homology T.r) :=
  not_finite_iff_infinite.mp fun _ ↦
    T.not_isTorsion_homology_top hr fun x ↦ isOfFinAddOrder_of_finite x

/-- **Conclusion (4) of [Stacks, Tag 07LK] for the displayed complex, explicitly.**  For `r > 0`
the top cohomology `H^r` of the completed de Rham complex `D → Ω¹_D → ⋯ → Ω^r_D` of
`D = 𝐙_p[x_1, …, x_r]^∧` has a nonzero element divisible by every power of `p`: the class of
`η = ∑_{e ≥ 0} p^e x_1^{p^e - 1} ⋯ x_r^{p^e - 1} dx_1 ∧ ⋯ ∧ dx_r`. -/
public theorem exists_ne_zero_forall_eq_pow_nsmul_homology_top (hr : 0 < T.r) :
    ∃ x : T.deRhamComplexNat.homology T.r, x ≠ 0 ∧ ∀ t : ℕ, ∃ y, x = (T.p ^ t) • y := by
  obtain ⟨s, hs⟩ := T.exists_eq_succ hr
  obtain ⟨π, hπ⟩ := T.exists_homologyClass_top hs
  refine ⟨π (T.series hs fun e ↦ T.p ^ e - 1), fun h ↦ ?_, fun t ↦ ?_⟩
  · exact T.series_eta_notMem_range hs ((hπ _).mp h)
  · obtain ⟨z, hz, ξ, hξ⟩ := T.exists_series_eta_eq_add hs t
    refine ⟨π ξ, ?_⟩
    rw [hξ, map_add, (hπ z).mpr hz, zero_add, map_nsmul]

/-- **Conclusion (4) of [Stacks, Tag 07LK] for the displayed complex.**  For `r > 0` the top
cohomology `H^r` of the completed de Rham complex `D → Ω¹_D → ⋯ → Ω^r_D` of
`D = 𝐙_p[x_1, …, x_r]^∧` is not separated for the `p`-adic topology: the class of
`η = ∑_{e ≥ 0} p^e x_1^{p^e - 1} ⋯ x_r^{p^e - 1} dx_1 ∧ ⋯ ∧ dx_r` is nonzero and lies in
`p^t H^r` for every `t`. -/
public theorem not_isHausdorff_homology_top (hr : 0 < T.r) :
    ¬ IsHausdorff (Ideal.span {(T.p : ℤ)}) (T.deRhamComplexNat.homology T.r) := by
  obtain ⟨x, hx, hdiv⟩ := T.exists_ne_zero_forall_eq_pow_nsmul_homology_top hr
  intro hhaus
  refine hx (hhaus.haus x fun t ↦ SModEq.zero.mpr ?_)
  obtain ⟨y, hy⟩ := hdiv t
  rw [hy]
  exact (mem_span_pow_smul_top_iff _ _ _).mpr ⟨y, by rw [← Nat.cast_pow, natCast_zsmul]⟩

end AffineSpaceCrystallineSetup

end Crystalline

end
