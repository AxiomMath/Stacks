module

public import StacksFrontier.RingTheory.Koszul.Blowup
public import StacksFrontier.RingTheory.Koszul.BlowupRelations
public import StacksFrontier.RingTheory.Koszul.Homotopy
public import StacksFrontier.RingTheory.Koszul.Quasiregular
public import StacksFrontier.RingTheory.AffineBlowup.ModelComparison
public import StacksFrontier.RingTheory.CompleteIntersection.FieldGlobalToRingMap

@[expose] public section

/-!
# The blowup relations of an `H₁`-regular sequence are Koszul-regular

Let `A` be a Noetherian ring and `f₀, f₁, …, f_r` an `H₁`-regular sequence in `A`. The affine
blowup algebra `A[I/f₀]`, `I = (f₀, …, f_r)`, is the quotient of `P = A[X₁, …, X_r]` by the
*blowup relations* `h_j = f₀ X_j - f_j` (Stacks 0BIQ,
`Koszul.exists_affineBlowup_algEquiv_mvPolynomial_quotient_of_isH1Regular`). This file proves
that the relations `h₁, …, h_r` form a Koszul-regular sequence in `P`, which is what makes the
blowup of a regular immersion a local complete intersection morphism (the first sentence of the
proof of Stacks 0FVA).

The proof is local on `Spec P`. At a prime `Q` of `P`:

* if `f₀ ∉ Q`, a power of `f₀` annihilates the positive Koszul homology of `h`
  (`Koszul.exists_pow_smul_koszul_homology_eq_zero`), and `f₀` becomes a unit in `P_Q`;
* if some `h_j ∉ Q`, the ideal `(h)` annihilates the Koszul homology (Stacks 0663), and `h_j`
  becomes a unit in `P_Q`;
* otherwise `f₀, h₁, …, h_r` all lie in the maximal ideal of the Noetherian local ring `P_Q`,
  where they form an `H₁`-regular, hence regular sequence (Stacks 0BIQ's claim,
  `Koszul.isH1Regular_relationSequence`, and Stacks 09CC); a permutation of a regular sequence
  in a Noetherian local ring is regular, so `h₁, …, h_r, f₀` is regular and its initial segment
  `h₁, …, h_r` is (weakly) regular, hence Koszul-regular in `P_Q`.

## Main results

* `Koszul.isKoszulRegular_algebraMap_of_pow_smul_homology_eq_zero`: a sequence whose positive
  Koszul homology is killed by a power of an element becomes Koszul-regular in any flat algebra
  in which that element is a unit.
* `Koszul.isKoszulRegular_blowupRelations`: the blowup relations of an `H₁`-regular sequence in a
  Noetherian ring are Koszul-regular.
* `Koszul.isLocalCompleteIntersection_algebraMap_affineBlowup`: consequently the structure map
  `A ⟶ A[I/f₀]` of the affine blowup algebra is a local complete intersection homomorphism
  (Stacks 07D0).
* `Koszul.affineBlowupQuotientAlgEquiv` and `Koszul.smooth_quotientMap_affineBlowup`: modulo `I`
  the affine blowup algebra is the polynomial ring `(A/I)[X₁, …, X_r]`, so the exceptional
  divisor of the chart is smooth over the centre.

## References

* [Stacks Project, Tag 0BIQ](https://stacks.math.columbia.edu/tag/0BIQ)
* [Stacks Project, Tag 0FVA](https://stacks.math.columbia.edu/tag/0FVA)
* [Stacks Project, Tag 0663](https://stacks.math.columbia.edu/tag/0663)
-/

open CategoryTheory
open scoped TensorProduct

namespace Koszul

universe u

/-- **Koszul regularity after inverting an annihilator of the homology.** If a power of `t`
annihilates every positive Koszul homology module of `h` over `P`, then `h` is Koszul-regular in
every flat `P`-algebra in which `t` is a unit. -/
theorem isKoszulRegular_algebraMap_of_pow_smul_homology_eq_zero {P : Type u} [CommRing P]
    {r : ℕ} (h : Fin r → P) (t : P) (c : ℕ)
    (hc : ∀ i : ℕ, 1 ≤ i → ∀ x : (seqComplex h).homology i, t ^ c • x = 0)
    (S : Type u) [CommRing S] [Algebra P S] [Module.Flat P S] (ht : IsUnit (algebraMap P S t)) :
    IsKoszulRegular fun j => algebraMap P S (h j) := by
  refine (isKoszulRegularOn_self_iff _).1 ?_
  refine isKoszulRegularOn_of_linearEquiv _ (TensorProduct.AlgebraTensorModule.rid P S S) ?_
  intro i hi
  rw [ModuleCat.isZero_iff_subsingleton]
  obtain ⟨e⟩ := KoszulC.homology_baseChange_linearEquiv (S := S) h P i
  refine e.toEquiv.subsingleton_congr.2 ?_
  refine (TensorProduct.congr (LinearEquiv.refl P S)
    (homologySelfIso h i).toLinearEquiv).toEquiv.subsingleton_congr.2 ⟨fun x y => ?_⟩
  have hzero : ∀ z : S ⊗[P] (seqComplex h).homology i, z = 0 := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => rfl
    | add z₁ z₂ h₁ h₂ => rw [h₁, h₂, add_zero]
    | tmul s m =>
      obtain ⟨u, hu⟩ := ht.pow c
      have hs : s = (s * ↑u⁻¹) * algebraMap P S (t ^ c) := by
        rw [map_pow, ← hu, mul_assoc, Units.inv_mul, mul_one]
      rw [hs, mul_comm, ← Algebra.smul_def, TensorProduct.smul_tmul,
        hc i (Nat.one_le_iff_ne_zero.2 hi) m, TensorProduct.tmul_zero]
  rw [hzero x, hzero y]

/-- **The blowup relations of an `H₁`-regular sequence are Koszul-regular.** Let `A` be a
Noetherian ring and `f₀, f₁, …, f_r` an `H₁`-regular sequence in `A`. Then the relations
`f₀ X_j - f_j`, `j = 1, …, r`, which cut out the affine blowup algebra `A[I/f₀]` in
`A[X₁, …, X_r]` (Stacks 0BIQ), form a Koszul-regular sequence. -/
theorem isKoszulRegular_blowupRelations {A : Type u} [CommRing A] [IsNoetherianRing A] {r : ℕ}
    (f : Fin (r + 1) → A) (hf : IsH1Regular f) :
    IsKoszulRegular fun j : Fin r =>
      MvPolynomial.C (f 0) * MvPolynomial.X j - MvPolynomial.C (f j.succ) := by
  set h : Fin r → MvPolynomial (Fin r) A := fun j =>
    MvPolynomial.C (f 0) * MvPolynomial.X j - MvPolynomial.C (f j.succ)
  refine isKoszulRegular_of_forall_localization_prime h fun Q _ => ?_
  have hflat : Module.Flat (MvPolynomial (Fin r) A) (Localization.AtPrime Q) :=
    IsLocalization.flat _ Q.primeCompl
  have hunit : ∀ t ∉ Q, IsUnit (algebraMap (MvPolynomial (Fin r) A) (Localization.AtPrime Q) t) :=
    fun t ht => IsLocalization.map_units (Localization.AtPrime Q) (⟨t, ht⟩ : Q.primeCompl)
  by_cases h0 : MvPolynomial.C (f 0) ∈ Q
  · by_cases hJ : ∀ j, h j ∈ Q
    · -- every member lies in the maximal ideal of `P_Q`: regular sequence argument
      let g : Fin (r + 1) → MvPolynomial (Fin r) A := Fin.cases (MvPolynomial.C (f 0)) h
      let g' : Fin (r + 1) → Localization.AtPrime Q :=
        fun j => algebraMap (MvPolynomial (Fin r) A) (Localization.AtPrime Q) (g j)
      have hg' : IsH1Regular g' := isH1Regular_map_of_flat g (isH1Regular_relationSequence f hf)
      have hmem : ∀ j, g' j ∈ IsLocalRing.maximalIdeal (Localization.AtPrime Q) := by
        intro j
        rw [← Localization.AtPrime.map_eq_maximalIdeal]
        exact Ideal.mem_map_of_mem _ (Fin.cases h0 hJ j)
      have hreg : RingTheory.Sequence.IsRegular (Localization.AtPrime Q) (List.ofFn g') :=
        ((regular_koszulRegular_h1Regular_quasiRegular_tfae
          (M := Localization.AtPrime Q) g' hmem).2.out 1 3).2 hg'
      have hperm : (List.ofFn g').Perm
          ((List.ofFn fun j : Fin r => g' j.succ) ++ [g' 0]) := by
        rw [List.ofFn_succ]
        exact List.perm_append_singleton _ _ |>.symm
      have hweak : RingTheory.Sequence.IsWeaklyRegular (Localization.AtPrime Q)
          (List.ofFn fun j : Fin r => g' j.succ) :=
        ((RingTheory.Sequence.isWeaklyRegular_append_iff _ _ _).1
          (IsLocalRing.isRegular_of_perm hreg hperm).toIsWeaklyRegular).1
      exact (isKoszulRegularOn_self_iff _).1
        ((isKoszulRegularOn_and_isKoszulRegular_of_regular
          (M := Localization.AtPrime Q)).1 hweak)
    · -- some member is a unit in `P_Q`, and it annihilates the Koszul homology
      push Not at hJ
      obtain ⟨j, hj⟩ := hJ
      refine isKoszulRegular_algebraMap_of_pow_smul_homology_eq_zero h (h j) 1 (fun i _ x => ?_)
        (Localization.AtPrime Q) (hunit _ hj)
      rw [pow_one]
      exact Module.mem_annihilator.1
        ((koszulSeq_smul_nullHomotopic_and_span_le_annihilator h).2 i
          (Ideal.subset_span ⟨j, rfl⟩)) x
  · -- `f₀` is a unit in `P_Q`, and a power of it annihilates the Koszul homology
    obtain ⟨c, hc⟩ := exists_pow_smul_koszul_homology_eq_zero (f 0) (fun j : Fin r => f j.succ)
    exact isKoszulRegular_algebraMap_of_pow_smul_homology_eq_zero h _ c hc
      (Localization.AtPrime Q) (hunit _ h0)

/-- **The affine blowup algebra of an `H₁`-regular sequence is a local complete intersection.**
For `f₀, f₁, …, f_r` an `H₁`-regular sequence in a Noetherian ring `A`, with `I = (f₀, …, f_r)`,
the structure map `A ⟶ A[I/f₀]` is a local complete intersection homomorphism (Stacks 07D0): by
Stacks 0BIQ, `A[I/f₀] ≅ A[X₁, …, X_r]/(f₀ X_j - f_j)`, and the relations are Koszul-regular
(`Koszul.isKoszulRegular_blowupRelations`). -/
theorem isLocalCompleteIntersection_algebraMap_affineBlowup {A : Type u} [CommRing A]
    [IsNoetherianRing A] {r : ℕ} (f : Fin (r + 1) → A) (hf : IsH1Regular f) :
    (algebraMap A (affineBlowup (Ideal.span (Set.range f)) (f 0))).IsLocalCompleteIntersection := by
  rw [affineBlowup_eq_affineBlowupAlgebra, ← affineBlowupAlgebraAway_eq_affineBlowupAlgebra]
  obtain ⟨e⟩ := exists_affineBlowup_algEquiv_mvPolynomial_quotient_of_isH1Regular f hf
  set J : Ideal (MvPolynomial (Fin r) A) := Ideal.span
    (Set.range fun i : Fin r => MvPolynomial.C (f 0) * MvPolynomial.X i - MvPolynomial.C (f i.succ))
  let p : MvPolynomial (Fin r) A →ₐ[A] affineBlowupAlgebraAway (Ideal.span (Set.range f)) (f 0) :=
    e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ A J)
  have hp : Function.Surjective p :=
    e.symm.surjective.comp (Ideal.Quotient.mkₐ_surjective A J)
  have hker : RingHom.ker p.toRingHom = J := by
    ext x
    simp only [RingHom.mem_ker, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    show e.symm (Ideal.Quotient.mk J x) = 0 ↔ x ∈ J
    rw [map_eq_zero_iff _ e.symm.injective, Ideal.Quotient.eq_zero_iff_mem]
  rw [RingHom.IsLocalCompleteIntersection, _root_.toAlgebra_algebraMap]
  refine ⟨RingHom.finiteType_algebraMap.mpr (Algebra.FiniteType.of_surjective p hp),
    r, p, hp, ?_⟩
  rw [hker]
  exact isKoszulRegularIdeal_span_range _ (isKoszulRegular_blowupRelations f hf)

/-- **Modulo the centre, the affine blowup algebra is a polynomial ring.** For `f₀, …, f_r`
`H₁`-regular in `A` and `I = (f₀, …, f_r)`, the quotient `A[I/f₀]/I·A[I/f₀]` is
`(A/I)[X₁, …, X_r]`, as `A`-algebras: by Stacks 0BIQ it is `A[X]/(J + I·A[X])` with
`J = (f₀ X_j - f_j) ⊆ I·A[X]`. -/
noncomputable def affineBlowupQuotientAlgEquiv {A : Type u} [CommRing A] {r : ℕ}
    (f : Fin (r + 1) → A) (hf : IsH1Regular f) :
    (affineBlowup (Ideal.span (Set.range f)) (f 0) ⧸
        (Ideal.span (Set.range f)).map
          (algebraMap A (affineBlowup (Ideal.span (Set.range f)) (f 0)))) ≃ₐ[A]
      MvPolynomial (Fin r) (A ⧸ Ideal.span (Set.range f)) := by
  set I := Ideal.span (Set.range f)
  set J : Ideal (MvPolynomial (Fin r) A) := Ideal.span
    (Set.range fun i : Fin r => MvPolynomial.C (f 0) * MvPolynomial.X i - MvPolynomial.C (f i.succ))
  have hB : affineBlowup I (f 0) = affineBlowupAlgebraAway I (f 0) := by
    rw [affineBlowup_eq_affineBlowupAlgebra, ← affineBlowupAlgebraAway_eq_affineBlowupAlgebra]
  let e : affineBlowup I (f 0) ≃ₐ[A] MvPolynomial (Fin r) A ⧸ J :=
    (Subalgebra.equivOfEq _ _ hB).trans
      (Classical.choice (exists_affineBlowup_algEquiv_mvPolynomial_quotient_of_isH1Regular f hf))
  have hJ : J ≤ I.map (MvPolynomial.C : A →+* MvPolynomial (Fin r) A) := by
    refine Ideal.span_le.2 ?_
    rintro _ ⟨i, rfl⟩
    exact Ideal.sub_mem _
      (Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨0, rfl⟩)))
      (Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨i.succ, rfl⟩))
  refine (Ideal.quotientEquivAlg _ ((I.map (MvPolynomial.C : A →+* MvPolynomial (Fin r) A)).map
      (Ideal.Quotient.mkₐ A J)) e ?_).trans ?_
  · change Ideal.map (Ideal.Quotient.mk J) (Ideal.map MvPolynomial.C I) = _
    rw [Ideal.map_map, Ideal.map_map]
    congr 1
    ext x
    change Ideal.Quotient.mk J (MvPolynomial.C x) = e (algebraMap A _ x)
    rw [AlgEquiv.commutes]
    rfl
  refine (DoubleQuot.quotQuotEquivQuotSupₐ A J _).trans ?_
  refine (Ideal.quotientEquivAlgOfEq A (sup_eq_right.2 hJ)).trans ?_
  exact (MvPolynomial.quotientEquivQuotientMvPolynomial I).symm

/-- **The chart of the exceptional divisor is smooth over the centre.** For `f₀, …, f_r`
`H₁`-regular in `A` and `I = (f₀, …, f_r)`, the map `A/I ⟶ A[I/f₀]/I·A[I/f₀]` induced by the
structure map is smooth: by `Koszul.affineBlowupQuotientAlgEquiv` it is the inclusion of the
constants into the polynomial ring `(A/I)[X₁, …, X_r]`. -/
theorem smooth_quotientMap_affineBlowup {A : Type u} [CommRing A] {r : ℕ}
    (f : Fin (r + 1) → A) (hf : IsH1Regular f) :
    (Ideal.quotientMap ((Ideal.span (Set.range f)).map
        (algebraMap A (affineBlowup (Ideal.span (Set.range f)) (f 0))))
      (algebraMap A (affineBlowup (Ideal.span (Set.range f)) (f 0)))
      Ideal.le_comap_map).Smooth := by
  set Ψ := affineBlowupQuotientAlgEquiv f hf
  have hfac : Ideal.quotientMap ((Ideal.span (Set.range f)).map
        (algebraMap A (affineBlowup (Ideal.span (Set.range f)) (f 0))))
      (algebraMap A (affineBlowup (Ideal.span (Set.range f)) (f 0))) Ideal.le_comap_map =
      (Ψ.symm.toRingEquiv.toRingHom).comp MvPolynomial.C := by
    refine Ideal.Quotient.ringHom_ext (RingHom.ext fun a => ?_)
    simp only [RingHom.comp_apply, Ideal.quotientMap_mk, RingEquiv.toRingHom_eq_coe,
      RingEquiv.coe_toRingHom, AlgEquiv.coe_ringEquiv]
    refine (Ψ.symm_apply_eq.2 ?_).symm
    show MvPolynomial.C (Ideal.Quotient.mk _ a) = Ψ (algebraMap A _ a)
    rw [AlgEquiv.commutes]
    rfl
  rw [hfac]
  refine RingHom.Smooth.comp ?_ (RingHom.Smooth.of_bijective Ψ.symm.bijective)
  exact (RingHom.smooth_algebraMap (R := A ⧸ Ideal.span (Set.range f))
    (S := MvPolynomial (Fin r) (A ⧸ Ideal.span (Set.range f)))).2 ⟨inferInstance, inferInstance⟩

end Koszul

end
