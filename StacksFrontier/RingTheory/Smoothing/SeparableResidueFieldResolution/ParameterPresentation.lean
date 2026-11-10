module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.Ring.FinitePresentation
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.Ring.FinitePresentation
public import StacksFrontier.FieldTheory.Separable.Defs
public import StacksFrontier.FieldTheory.Separable.TFAE
public import StacksFrontier.RingTheory.Smooth.FieldExtensionCompleteIntersectionColimit
public import StacksFrontier.RingTheory.CompleteIntersection.RingMap.Criteria
public import StacksFrontier.RingTheory.CompleteIntersection.Smooth
public import StacksFrontier.RingTheory.Flat.RegularSequence
public import StacksFrontier.RingTheory.Ideal.RadicalMaximalQuotient
public import StacksFrontier.RingTheory.MvPolynomial.RegularRing
public import StacksFrontier.RingTheory.RegularLocalRing.Basic
public import StacksFrontier.RingTheory.Smooth.Localization
public import StacksFrontier.RingTheory.Smoothing.DesingularizationLifting
public import StacksFrontier.RingTheory.Smoothing.ImprovingPresentations
public import StacksFrontier.RingTheory.Smoothing.IndSmooth
public import StacksFrontier.RingTheory.Smoothing.LiftingProblem
public import StacksFrontier.RingTheory.Smoothing.LiftingResolutionsFromEighthPowers
public import StacksFrontier.RingTheory.Smoothing.LocalSmoothingSituation
public import StacksFrontier.RingTheory.Smoothing.ParametersWithPowersInIdeal
public import StacksFrontier.RingTheory.Smoothing.SingularIdealFactorization
public import StacksFrontier.RingTheory.Smoothing.SingularIdeals
public import StacksFrontier.RingTheory.Smoothing.SpreadingOutResolutions
public import StacksFrontier.RingTheory.Smoothing.StablyFreeStrictlyStandardPowers
public import StacksFrontier.RingTheory.Smoothing.StandardnessConditions
public import StacksFrontier.RingTheory.Smoothing.ZeroDimensionalResolution

/-!
# Parameter presentations for resolving a local smoothing situation

Auxiliary constructions for the resolution of a local smoothing situation `k → A → Λ ⊃ q` with
`Λ_q` regular and `κ(q)/k` separable: the `A`-algebra `A[x_i, z_{ij}]/(x_iⁿ - Σ z_{ij} a_j)`
and its charts, the formal smoothness of its localizations at the parameters, resolution over a
smooth base, stability of annihilators under powers, power containments at minimal primes, and
regular sequences of parameters.

## References

* [Stacks Project, Tag 07FE](https://stacks.math.columbia.edu/tag/07FE)
-/

@[expose] public section

namespace Stacks.Smoothing

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u v w u' v' t

private abbrev parameterPresentationPolynomial (A : Type*) [CommRing A]
    (d r : ℕ) := MvPolynomial (Fin d ⊕ (Fin d × Fin r)) A

private noncomputable def parameterPresentationRelation {A : Type*} [CommRing A]
    {d r : ℕ} (n : ℕ) (a : Fin r → A) (i : Fin d) :
    parameterPresentationPolynomial A d r :=
  MvPolynomial.X (Sum.inl i) ^ n -
    ∑ j, MvPolynomial.C (a j) * MvPolynomial.X (Sum.inr (i, j))

private noncomputable def parameterPresentationIdeal {A : Type*} [CommRing A]
    {d r : ℕ} (n : ℕ) (a : Fin r → A) :
    Ideal (parameterPresentationPolynomial A d r) :=
  Ideal.span (Set.range (parameterPresentationRelation n a))

private abbrev parameterChartVariables (d r : ℕ) (j : Fin r) :=
  Fin d ⊕ (Fin d × {l : Fin r // l ≠ j})

private noncomputable def parameterChartValue {K : Type*} [CommRing K]
    {d r : ℕ} (n : ℕ) (b : Fin r → K) (j : Fin r) (i : Fin d) :
    MvPolynomial (parameterChartVariables d r j) K :=
  MvPolynomial.C (Ring.inverse (b j)) *
    (MvPolynomial.X (Sum.inl i) ^ n -
      ∑ l : {l : Fin r // l ≠ j},
        MvPolynomial.C (b l.1) * MvPolynomial.X (Sum.inr (i, l)))

private noncomputable def parameterChartSubstitution {K : Type*} [CommRing K]
    {d r : ℕ} (n : ℕ) (b : Fin r → K) (j : Fin r) :
    (Fin d ⊕ (Fin d × Fin r)) → MvPolynomial (parameterChartVariables d r j) K :=
  fun x => match x with
    | Sum.inl i => MvPolynomial.X (Sum.inl i)
    | Sum.inr (i, l) => if h : l = j then parameterChartValue n b j i
        else MvPolynomial.X (Sum.inr (i, ⟨l, h⟩))

private noncomputable def parameterChartForwardHom {K : Type*} [CommRing K]
    {d r : ℕ} (n : ℕ) (b : Fin r → K) (j : Fin r) :
    MvPolynomial (Fin d ⊕ (Fin d × Fin r)) K →ₐ[K]
      MvPolynomial (parameterChartVariables d r j) K :=
  MvPolynomial.aeval (parameterChartSubstitution n b j)

private lemma sum_eq_add_sum_ne {ι M : Type*} [Fintype ι] [DecidableEq ι] [AddCommMonoid M]
    (j : ι) (f : ι → M) : ∑ i, f i = f j + ∑ i : {i // i ≠ j}, f i.1 := by
  classical
  simpa only [Fintype.sum_unique, (default : {i // i = j}).property] using
    (Fintype.sum_subtype_add_sum_subtype (fun i => i = j) f).symm

private lemma parameterChartForward_relation {K : Type*} [CommRing K]
    {d r : ℕ} (n : ℕ) (b : Fin r → K) (j : Fin r)
    (hj : IsUnit (b j)) (i : Fin d) :
    parameterChartForwardHom n b j (parameterPresentationRelation n b i) = 0 := by
  classical
  rw [parameterChartForwardHom, parameterPresentationRelation, map_sub, map_pow, map_sum]
  simp only [map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_X]
  rw [sum_eq_add_sum_ne j]
  have hne (l : {l : Fin r // l ≠ j}) :
      parameterChartSubstitution n b j (Sum.inr (i, l.1)) =
        MvPolynomial.X (Sum.inr (i, l)) := by
    simp [parameterChartSubstitution, l.property]
  simp_rw [hne]
  simp only [parameterChartSubstitution, dite_true]
  simp only [parameterChartValue, MvPolynomial.algebraMap_eq]
  rw [← mul_assoc, ← map_mul, Ring.mul_inverse_cancel _ hj, map_one, one_mul]
  ring

private noncomputable def parameterChartForward {K : Type*} [CommRing K]
    {d r : ℕ} (n : ℕ) (b : Fin r → K) (j : Fin r) (hj : IsUnit (b j)) :
    (parameterPresentationPolynomial K d r ⧸ parameterPresentationIdeal n b) →ₐ[K]
      MvPolynomial (parameterChartVariables d r j) K :=
  Ideal.Quotient.liftₐ _ (parameterChartForwardHom n b j) (by
    intro p hp
    apply RingHom.mem_ker.mp
    apply (Ideal.span_le.mpr ?_ : parameterPresentationIdeal n b ≤
      RingHom.ker (parameterChartForwardHom n b j).toRingHom) hp
    rintro _ ⟨i, rfl⟩
    exact parameterChartForward_relation n b j hj i)

private noncomputable def parameterChartBackward {K : Type*} [CommRing K]
    {d r : ℕ} (n : ℕ) (b : Fin r → K) (j : Fin r) :
    MvPolynomial (parameterChartVariables d r j) K →ₐ[K]
      (parameterPresentationPolynomial K d r ⧸ parameterPresentationIdeal n b) :=
  MvPolynomial.aeval fun x => Ideal.Quotient.mk _ (MvPolynomial.X
    (match x with
    | Sum.inl i => Sum.inl i
    | Sum.inr (i, l) => Sum.inr (i, l.1)))

private lemma parameterPresentation_mk_relation {K : Type*} [CommRing K]
    {d r : ℕ} (n : ℕ) (b : Fin r → K) (i : Fin d) :
    Ideal.Quotient.mk (parameterPresentationIdeal n b)
      (parameterPresentationRelation n b i) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨i, rfl⟩)

/-- In the parameter presentation, `xᵢⁿ` is the sum `Σ aⱼ zᵢⱼ`. -/
private lemma parameterPresentation_mk_pow_eq_sum {A : Type*} [CommRing A]
    {d r : ℕ} (n : ℕ) (a : Fin r → A) (i : Fin d) :
    Ideal.Quotient.mk (parameterPresentationIdeal (d := d) n a) (MvPolynomial.X (Sum.inl i)) ^ n =
      ∑ j, algebraMap A (parameterPresentationPolynomial A d r ⧸ parameterPresentationIdeal n a)
        (a j) * Ideal.Quotient.mk _ (MvPolynomial.X (Sum.inr (i, j))) := by
  have hC (x : A) : Ideal.Quotient.mk (parameterPresentationIdeal (d := d) n a)
      (MvPolynomial.C x) = algebraMap A _ x := by
    rw [IsScalarTower.algebraMap_apply A (parameterPresentationPolynomial A d r) _,
      MvPolynomial.algebraMap_eq]
    rfl
  have h := parameterPresentation_mk_relation n a i
  change Ideal.Quotient.mk _ (parameterPresentationRelation n a i) = 0 at h
  simpa only [parameterPresentationRelation, map_sub, map_pow, map_sum, map_mul,
    sub_eq_zero, hC] using h

private lemma parameterChartForward_mk {K : Type*} [CommRing K]
    {d r : ℕ} (n : ℕ) (b : Fin r → K) (j : Fin r) (hj : IsUnit (b j))
    (p : parameterPresentationPolynomial K d r) :
    parameterChartForward n b j hj (Ideal.Quotient.mk _ p) =
      parameterChartForwardHom n b j p := rfl

private lemma parameterChartForward_comp_backward {K : Type*} [CommRing K]
    {d r : ℕ} (n : ℕ) (b : Fin r → K) (j : Fin r) (hj : IsUnit (b j)) :
    (parameterChartForward (d := d) n b j hj).comp (parameterChartBackward n b j) =
      AlgHom.id K _ := by
  classical
  apply MvPolynomial.algHom_ext
  intro x
  change parameterChartForward n b j hj
    (parameterChartBackward n b j (MvPolynomial.X x)) = MvPolynomial.X x
  rw [parameterChartBackward, MvPolynomial.aeval_X, parameterChartForward_mk,
    parameterChartForwardHom, MvPolynomial.aeval_X]
  rcases x with i | ⟨i, l⟩
  · rfl
  · simp [parameterChartSubstitution, l.property]

private lemma parameterChartBackward_comp_forward {K : Type*} [CommRing K]
    {d r : ℕ} (n : ℕ) (b : Fin r → K) (j : Fin r) (hj : IsUnit (b j)) :
    (parameterChartBackward (d := d) n b j).comp (parameterChartForward n b j hj) =
      AlgHom.id K _ := by
  classical
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro x
  change parameterChartBackward n b j
    (parameterChartForward n b j hj (Ideal.Quotient.mk _ (MvPolynomial.X x))) =
      Ideal.Quotient.mk _ (MvPolynomial.X x)
  rw [parameterChartForward_mk, parameterChartForwardHom, MvPolynomial.aeval_X]
  rcases x with i | ⟨i, l⟩
  · simp [parameterChartSubstitution, parameterChartBackward]
  · by_cases hl : l = j
    · subst l
      let Q := parameterPresentationPolynomial K d r ⧸ parameterPresentationIdeal n b
      let mk := Ideal.Quotient.mk (parameterPresentationIdeal (d := d) n b)
      have hrel := parameterPresentation_mk_pow_eq_sum n b i
      rw [sum_eq_add_sum_ne j] at hrel
      simp only [parameterChartSubstitution, dite_true, parameterChartValue,
        map_mul, map_sub, map_pow, map_sum, parameterChartBackward,
        MvPolynomial.aeval_C, MvPolynomial.aeval_X]
      change algebraMap K Q (Ring.inverse (b j)) *
        (mk (MvPolynomial.X (Sum.inl i)) ^ n -
          ∑ l : {l // l ≠ j}, algebraMap K Q (b l.1) *
            mk (MvPolynomial.X (Sum.inr (i, l.1)))) = _
      rw [hrel, add_sub_cancel_right, ← mul_assoc, ← map_mul,
        Ring.inverse_mul_cancel _ hj, map_one, one_mul]
    · simp [parameterChartBackward, parameterChartSubstitution, hl]

private noncomputable def parameterChartEquiv {K : Type*} [CommRing K]
    {d r : ℕ} (n : ℕ) (b : Fin r → K) (j : Fin r) (hj : IsUnit (b j)) :
    (parameterPresentationPolynomial K d r ⧸ parameterPresentationIdeal n b) ≃ₐ[K]
      MvPolynomial (parameterChartVariables d r j) K :=
  AlgEquiv.ofAlgHom (parameterChartForward n b j hj) (parameterChartBackward n b j)
    (parameterChartForward_comp_backward n b j hj)
    (parameterChartBackward_comp_forward n b j hj)

private lemma formallySmooth_polynomial_over_parameters
    {k K ι κ : Type*} [CommRing k] [CommRing K] [Algebra k K]
    [Algebra.FormallySmooth k K]
    [Algebra (MvPolynomial ι k) (MvPolynomial (ι ⊕ κ) K)]
    [IsScalarTower k (MvPolynomial ι k) (MvPolynomial (ι ⊕ κ) K)]
    (hX : ∀ i, algebraMap (MvPolynomial ι k) (MvPolynomial (ι ⊕ κ) K)
      (MvPolynomial.X i) = MvPolynomial.X (Sum.inl i)) :
    Algebra.FormallySmooth (MvPolynomial ι k) (MvPolynomial (ι ⊕ κ) K) := by
  classical
  let R := MvPolynomial ι k
  let P := MvPolynomial (ι ⊕ κ) K
  apply Algebra.FormallySmooth.of_comp_surjective
  intro D _ _ I hI φ
  let : Algebra k D := ((algebraMap R D).comp (algebraMap k R)).toAlgebra
  let : IsScalarTower k R D := IsScalarTower.of_algebraMap_eq' rfl
  obtain ⟨ψ, hψ⟩ := Algebra.FormallySmooth.comp_surjective k K I hI
    ((φ.restrictScalars k).comp (IsScalarTower.toAlgHom k K P))
  choose z hz using (fun i : κ => Ideal.Quotient.mk_surjective
    (φ (MvPolynomial.X (Sum.inr i))))
  let v : ι ⊕ κ → D := Sum.elim (fun i => algebraMap R D (MvPolynomial.X i)) z
  let ψP : P →ₐ[k] D :=
    { MvPolynomial.eval₂Hom ψ.toRingHom v with
      commutes' := fun x => by
        change MvPolynomial.eval₂Hom ψ.toRingHom v (algebraMap k P x) = _
        rw [IsScalarTower.algebraMap_apply k K P, MvPolynomial.algebraMap_eq,
          MvPolynomial.eval₂Hom_C]
        exact ψ.commutes x }
  have hc : ψP.comp (IsScalarTower.toAlgHom k R P) =
      IsScalarTower.toAlgHom k R D := by
    apply MvPolynomial.algHom_ext
    intro i
    change ψP (algebraMap R P (MvPolynomial.X i)) = algebraMap R D (MvPolynomial.X i)
    rw [hX]
    exact MvPolynomial.eval₂Hom_X' _ _ _
  let ψR : P →ₐ[R] D :=
    { ψP.toRingHom with commutes' := fun x => AlgHom.congr_fun hc x }
  refine ⟨ψR, ?_⟩
  apply AlgHom.toRingHom_injective
  apply MvPolynomial.ringHom_ext
  · intro x
    change Ideal.Quotient.mk I
      (MvPolynomial.eval₂Hom ψ.toRingHom v (MvPolynomial.C x)) = _
    rw [MvPolynomial.eval₂Hom_C]
    exact AlgHom.congr_fun hψ x
  · intro i
    change Ideal.Quotient.mk I
      (MvPolynomial.eval₂Hom ψ.toRingHom v (MvPolynomial.X i)) = _
    rw [MvPolynomial.eval₂Hom_X']
    rcases i with i | i
    · change Ideal.Quotient.mk I (algebraMap R D (MvPolynomial.X i)) =
        φ (MvPolynomial.X (Sum.inl i))
      rw [← hX, φ.commutes, Ideal.Quotient.mk_algebraMap]
    · exact hz i

private lemma exists_parameterLocalizationEquiv
    {A : Type*} [CommRing A] {d r : ℕ} (n : ℕ) (a : Fin r → A) (j : Fin r) :
    let B := parameterPresentationPolynomial A d r ⧸ parameterPresentationIdeal n a
    ∃ e : Localization.Away (algebraMap A B (a j)) ≃ₐ[A]
        MvPolynomial (parameterChartVariables d r j) (Localization.Away (a j)),
      ∀ i : Fin d, e (algebraMap B (Localization.Away (algebraMap A B (a j)))
        (Ideal.Quotient.mk _ (MvPolynomial.X (Sum.inl i)))) =
          MvPolynomial.X (Sum.inl i) := by
  classical
  let P := parameterPresentationPolynomial A d r
  let I : Ideal P := parameterPresentationIdeal n a
  let B := P ⧸ I
  let Aj := Localization.Away (a j)
  let c : Fin r → Aj := fun l => algebraMap A Aj (a l)
  let Pj := parameterPresentationPolynomial Aj d r
  let : Algebra P Pj := MvPolynomial.algebraMvPolynomial
  have : IsLocalization
      ((Submonoid.powers (a j)).map (MvPolynomial.C : A →+* P)) Pj :=
    MvPolynomial.isLocalization (Submonoid.powers (a j)) Aj
  let J : Ideal Pj := I.map (algebraMap P Pj)
  let Q := Pj ⧸ J
  let bj : B := algebraMap A B (a j)
  have hsub : Algebra.algebraMapSubmonoid B
      ((Submonoid.powers (a j)).map (MvPolynomial.C : A →+* P)) =
      Submonoid.powers bj := by
    simp only [Algebra.algebraMapSubmonoid, Submonoid.map_powers]
    rfl
  have : IsLocalization (Submonoid.powers bj) Q := by
    rw [← hsub]
    infer_instance
  let e : Localization.Away bj ≃ₐ[B] Q :=
    IsLocalization.algEquiv (Submonoid.powers bj) _ _
  have hAQ (x : A) : algebraMap A Q x =
      algebraMap B Q (algebraMap A B x) := by
    change Ideal.Quotient.mk J (MvPolynomial.C (algebraMap A Aj x)) =
      algebraMap B Q (Ideal.Quotient.mk I (MvPolynomial.C x))
    rw [Ideal.Quotient.algebraMap_quotient_map_quotient]
    change _ = Ideal.Quotient.mk J (MvPolynomial.map (algebraMap A Aj) (MvPolynomial.C x))
    rw [MvPolynomial.map_C]
  let eA : Localization.Away bj ≃ₐ[A] Q :=
    AlgEquiv.ofRingEquiv (f := e.toRingEquiv) (by
      intro x
      change e (algebraMap A (Localization.Away bj) x) = algebraMap A Q x
      rw [IsScalarTower.algebraMap_apply A B (Localization.Away bj),
        e.commutes, ← hAQ])
  have hJ : J = parameterPresentationIdeal n c := by
    dsimp [J, I, parameterPresentationIdeal]
    rw [Ideal.map_span, ← Set.range_comp]
    congr 2
    funext i
    change MvPolynomial.map (algebraMap A Aj) (parameterPresentationRelation n a i) =
      parameterPresentationRelation n c i
    simp [parameterPresentationRelation, c]
  let eQ : Q ≃ₐ[Aj] (Pj ⧸ parameterPresentationIdeal n c) :=
    Ideal.quotientEquivAlgOfEq Aj hJ
  let ec := parameterChartEquiv (d := d) n c j
    (IsLocalization.Away.algebraMap_isUnit (a j))
  refine ⟨eA.trans ((eQ.trans ec).restrictScalars A), fun i => ?_⟩
  change ec (eQ (e (algebraMap B (Localization.Away bj)
    (Ideal.Quotient.mk I (MvPolynomial.X (Sum.inl i)))))) = _
  rw [e.commutes, Ideal.Quotient.algebraMap_quotient_map_quotient]
  change ec (eQ (Ideal.Quotient.mk J
    (MvPolynomial.map (algebraMap A Aj) (MvPolynomial.X (Sum.inl i))))) = _
  rw [MvPolynomial.map_X]
  change parameterChartForward n c j (IsLocalization.Away.algebraMap_isUnit (a j))
    (Ideal.Quotient.mk _ (MvPolynomial.X (Sum.inl i))) = _
  rw [parameterChartForward_mk, parameterChartForwardHom, MvPolynomial.aeval_X]
  rfl

private noncomputable def parameterLocalizationEquiv
    {A : Type*} [CommRing A] {d r : ℕ} (n : ℕ) (a : Fin r → A) (j : Fin r) :
    let B := parameterPresentationPolynomial A d r ⧸ parameterPresentationIdeal n a
    Localization.Away (algebraMap A B (a j)) ≃ₐ[A]
      MvPolynomial (parameterChartVariables d r j) (Localization.Away (a j)) :=
  (exists_parameterLocalizationEquiv n a j).choose

private lemma parameterLocalizationEquiv_X
    {A : Type*} [CommRing A] {d r : ℕ} (n : ℕ) (a : Fin r → A) (j : Fin r)
    (i : Fin d) :
    let B := parameterPresentationPolynomial A d r ⧸ parameterPresentationIdeal n a
    parameterLocalizationEquiv n a j
      (algebraMap B (Localization.Away (algebraMap A B (a j)))
        (Ideal.Quotient.mk _ (MvPolynomial.X (Sum.inl i)))) =
      MvPolynomial.X (Sum.inl i) :=
  (exists_parameterLocalizationEquiv n a j).choose_spec i

private lemma formallySmooth_parameter_localization
    {k A : Type*} [Field k] [CommRing A] [Algebra k A]
    {d r : ℕ} (n : ℕ) (a : Fin r → A) (j : Fin r)
    [Algebra (MvPolynomial (Fin d) k)
      (parameterPresentationPolynomial A d r ⧸ parameterPresentationIdeal n a)]
    [IsScalarTower k (MvPolynomial (Fin d) k)
      (parameterPresentationPolynomial A d r ⧸ parameterPresentationIdeal n a)]
    (hX : ∀ i : Fin d, algebraMap (MvPolynomial (Fin d) k)
      (parameterPresentationPolynomial A d r ⧸ parameterPresentationIdeal n a)
      (MvPolynomial.X i) = Ideal.Quotient.mk _ (MvPolynomial.X (Sum.inl i)))
    [Algebra.Smooth k (Localization.Away (a j))] :
    let B := parameterPresentationPolynomial A d r ⧸ parameterPresentationIdeal n a
    Algebra.FormallySmooth (MvPolynomial (Fin d) k)
      (Localization.Away (algebraMap A B (a j))) := by
  let R := MvPolynomial (Fin d) k
  let B := parameterPresentationPolynomial A d r ⧸ parameterPresentationIdeal n a
  let L := Localization.Away (algebraMap A B (a j))
  let T := MvPolynomial (parameterChartVariables d r j) (Localization.Away (a j))
  let e : L ≃ₐ[A] T := parameterLocalizationEquiv n a j
  let : Algebra R T := (e.toRingHom.comp (algebraMap R L)).toAlgebra
  have : IsScalarTower k R T := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    change algebraMap k T x = e (algebraMap R L (algebraMap k R x))
    rw [← IsScalarTower.algebraMap_apply k R L]
    exact ((e.restrictScalars k).commutes x).symm
  have heX (i : Fin d) : algebraMap R T (MvPolynomial.X i) =
      MvPolynomial.X (Sum.inl i) := by
    change e (algebraMap R L (MvPolynomial.X i)) = _
    rw [IsScalarTower.algebraMap_apply R B L, hX]
    exact parameterLocalizationEquiv_X n a j i
  have : Algebra.FormallySmooth R T := formallySmooth_polynomial_over_parameters heX
  let eR : L ≃ₐ[R] T := { e.toRingEquiv with commutes' := fun _ => rfl }
  exact Algebra.FormallySmooth.of_equiv eR.symm

private lemma mem_singularIdeal_of_smooth_away
    {R B : Type*} [CommRing R] [CommRing B] [Algebra R B] {b : B}
    (h : Algebra.Smooth R (Localization.Away b)) : b ∈ Stacks.Smoothing.singularIdeal R B := by
  rw [Stacks.Smoothing.singularIdeal, PrimeSpectrum.mem_vanishingIdeal]
  intro q hq
  by_contra hb
  exact hq ⟨b, hb, h⟩

private lemma smooth_away_of_mem_singularIdeal
    {R B : Type*} [CommRing R] [CommRing B] [Algebra R B]
    [Algebra.FinitePresentation R B] {b : B} (hb : b ∈ Stacks.Smoothing.singularIdeal R B) :
    Algebra.Smooth R (Localization.Away b) :=
  smooth_localization_away_of_mem_singularIdeal R B hb

private lemma smooth_parameter_away
    {k A : Type*} [Field k] [CommRing A] [Algebra k A]
    {d r : ℕ} (n : ℕ) (a : Fin r → A)
    [Algebra (MvPolynomial (Fin d) k)
      (parameterPresentationPolynomial A d r ⧸ parameterPresentationIdeal n a)]
    [IsScalarTower k (MvPolynomial (Fin d) k)
      (parameterPresentationPolynomial A d r ⧸ parameterPresentationIdeal n a)]
    [Algebra.FinitePresentation (MvPolynomial (Fin d) k)
      (parameterPresentationPolynomial A d r ⧸ parameterPresentationIdeal n a)]
    (hX : ∀ i : Fin d, algebraMap (MvPolynomial (Fin d) k)
      (parameterPresentationPolynomial A d r ⧸ parameterPresentationIdeal n a)
      (MvPolynomial.X i) = Ideal.Quotient.mk _ (MvPolynomial.X (Sum.inl i)))
    (ha : ∀ j, Algebra.Smooth k (Localization.Away (a j))) (i : Fin d) :
    let B := parameterPresentationPolynomial A d r ⧸ parameterPresentationIdeal n a
    Algebra.Smooth (MvPolynomial (Fin d) k)
      (Localization.Away (algebraMap (MvPolynomial (Fin d) k) B (MvPolynomial.X i))) := by
  let R := MvPolynomial (Fin d) k
  let B := parameterPresentationPolynomial A d r ⧸ parameterPresentationIdeal n a
  have hmem (j : Fin r) : algebraMap A B (a j) ∈ Stacks.Smoothing.singularIdeal R B := by
    have := ha j
    apply mem_singularIdeal_of_smooth_away
    exact ⟨formallySmooth_parameter_localization n a j hX, inferInstance⟩
  apply smooth_away_of_mem_singularIdeal
  apply Stacks.Smoothing.singularIdeal_isRadical R B
  refine ⟨n, ?_⟩
  rw [hX]
  rw [parameterPresentation_mk_pow_eq_sum n a i]
  apply Ideal.sum_mem
  intro j hj
  exact Ideal.mul_mem_right _ _ (hmem j)

private lemma singularIdeal_le_of_smooth_base
    {k R B : Type*} [CommRing k] [CommRing R] [CommRing B]
    [Algebra k R] [Algebra k B] [Algebra R B] [IsScalarTower k R B]
    [Algebra.Smooth k R] [Algebra.FinitePresentation R B] :
    Stacks.Smoothing.singularIdeal R B ≤ Stacks.Smoothing.singularIdeal k B := by
  intro b hb
  have : Algebra.Smooth R (Localization.Away b) :=
    smooth_away_of_mem_singularIdeal hb
  exact mem_singularIdeal_of_smooth_away
    (Algebra.Smooth.comp k R (Localization.Away b))

/-- Radicals of extended ideals are monotone along an intermediate algebra. -/
private lemma radical_map_le_radical_map_of_map_le {A C Λ : Type*} [CommRing A] [CommRing C]
    [CommRing Λ] [Algebra A C] [Algebra A Λ] [Algebra C Λ] [IsScalarTower A C Λ]
    {I : Ideal A} {J : Ideal C} (h : Ideal.map (algebraMap A C) I ≤ J) :
    (Ideal.map (algebraMap A Λ) I).radical ≤ (Ideal.map (algebraMap C Λ) J).radical := by
  apply Ideal.radical_mono
  rw [IsScalarTower.algebraMap_eq A C Λ, ← Ideal.map_map]
  exact Ideal.map_mono h

private lemma canBeResolved_of_smooth_base
    {k R : Type u} {A C : Type v} {Λ : Type w}
    [CommRing k] [CommRing R] [CommRing A] [CommRing C] [CommRing Λ]
    [Algebra k R] [Algebra k A] [Algebra k C] [Algebra k Λ]
    [Algebra R C] [Algebra R Λ] [Algebra A C] [Algebra A Λ] [Algebra C Λ]
    [IsScalarTower k R C] [IsScalarTower k R Λ]
    [IsScalarTower k A C] [IsScalarTower k A Λ]
    [IsScalarTower k C Λ] [IsScalarTower R C Λ] [IsScalarTower A C Λ]
    [Algebra.Smooth k R] (q : Ideal Λ)
    (hAC : Ideal.map (algebraMap A C) (Stacks.Smoothing.singularIdeal k A) ≤
      Stacks.Smoothing.singularIdeal R C)
    (h : CanBeResolved R C Λ q) :
    CanBeResolved k A Λ q := by
  obtain ⟨D, hD, hRD, hCD, hDΛ, hRCD, hCDΛ, hRDΛ, hfp, hsing, hq⟩ := h
  let := hD
  let := hRD
  let := hCD
  let := hDΛ
  let := hRCD
  let := hCDΛ
  let := hRDΛ
  let := hfp
  let : Algebra k D := ((algebraMap R D).comp (algebraMap k R)).toAlgebra
  let : IsScalarTower k R D := IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra A D := ((algebraMap C D).comp (algebraMap A C)).toAlgebra
  let : IsScalarTower A C D := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower k C D := IsScalarTower.of_algebraMap_eq fun x => by
    change algebraMap R D (algebraMap k R x) = algebraMap C D (algebraMap k C x)
    rw [IsScalarTower.algebraMap_apply k R C, ← IsScalarTower.algebraMap_apply R C D]
  have : IsScalarTower k A D := IsScalarTower.of_algebraMap_eq fun x => by
    rw [IsScalarTower.algebraMap_apply k C D,
      IsScalarTower.algebraMap_apply k A C,
      IsScalarTower.algebraMap_apply A C D]
  have : IsScalarTower A D Λ := IsScalarTower.of_algebraMap_eq fun x => by
    rw [IsScalarTower.algebraMap_apply A C Λ,
      IsScalarTower.algebraMap_apply A C D,
      ← IsScalarTower.algebraMap_apply C D Λ]
  have : IsScalarTower k D Λ := IsScalarTower.of_algebraMap_eq fun x => by
    rw [IsScalarTower.algebraMap_apply k R Λ,
      IsScalarTower.algebraMap_apply k R D,
      ← IsScalarTower.algebraMap_apply R D Λ]
  have hCDsing : (Ideal.map (algebraMap C Λ) (Stacks.Smoothing.singularIdeal R C)).radical ≤
      (Ideal.map (algebraMap D Λ) (Stacks.Smoothing.singularIdeal k D)).radical :=
    hsing.trans (Ideal.radical_mono (Ideal.map_mono singularIdeal_le_of_smooth_base))
  refine ⟨D, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance,
    Algebra.FinitePresentation.trans k R D, ?_, ?_⟩
  · exact (radical_map_le_radical_map_of_map_le hAC).trans hCDsing
  · intro hle
    apply hq
    exact (Ideal.radical_mono
      (Ideal.map_mono singularIdeal_le_of_smooth_base)).trans hle

private lemma map_singularIdeal_le_of_algEquiv
    {R B D : Type*} [CommRing R] [CommRing B] [CommRing D]
    [Algebra R B] [Algebra R D] [Algebra.FinitePresentation R B]
    (e : B ≃ₐ[R] D) :
    Ideal.map e.toRingHom (Stacks.Smoothing.singularIdeal R B) ≤
      Stacks.Smoothing.singularIdeal R D := by
  apply Ideal.map_le_iff_le_comap.mpr
  intro b hb
  change e b ∈ Stacks.Smoothing.singularIdeal R D
  have : Algebra.Smooth R (Localization.Away b) := smooth_away_of_mem_singularIdeal hb
  apply mem_singularIdeal_of_smooth_away
  exact Algebra.Smooth.of_equiv
    (IsLocalization.algEquivOfAlgEquiv (Localization.Away b) (Localization.Away (e b))
      e (by exact Submonoid.map_powers e b))

private lemma canBeResolved_of_singularIdeal_not_le
    {R : Type u} {A : Type v} {Λ : Type w}
    [CommRing R] [CommRing A] [CommRing Λ]
    [Algebra R A] [Algebra R Λ] [Algebra A Λ] [IsScalarTower R A Λ]
    [Algebra.FinitePresentation R A] (q : Ideal Λ)
    (h : ¬ (Ideal.map (algebraMap A Λ)
      (Stacks.Smoothing.singularIdeal R A)).radical ≤ q) :
    CanBeResolved R A Λ q := by
  let D := ULift.{max u w} A
  let : Algebra D Λ := ULift.algebra' A Λ
  have : IsScalarTower A D Λ := ⟨fun a d l => smul_assoc a d.down l⟩
  have : IsScalarTower R D Λ := ⟨fun a d l => smul_assoc a d.down l⟩
  have hAD : Ideal.map (algebraMap A D) (Stacks.Smoothing.singularIdeal R A) ≤
      Stacks.Smoothing.singularIdeal R D :=
    map_singularIdeal_le_of_algEquiv (ULift.algEquiv.symm : A ≃ₐ[R] D)
  have hADΛ : (Ideal.map (algebraMap A Λ) (Stacks.Smoothing.singularIdeal R A)).radical ≤
      (Ideal.map (algebraMap D Λ) (Stacks.Smoothing.singularIdeal R D)).radical :=
    radical_map_le_radical_map_of_map_le hAD
  refine ⟨D, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance,
    Algebra.FinitePresentation.equiv (ULift.algEquiv.symm : A ≃ₐ[R] D), hADΛ,
    fun hle => h (hADΛ.trans hle)⟩

private lemma exists_parameter_presentation_map
    {A : Type*} {Λ : Type*} [CommRing A] [CommRing Λ]
    [Algebra A Λ] {d r : ℕ} (n : ℕ) (a : Fin r → A)
    (coeff : Fin d → Fin r → Λ) (π : Fin d → Λ)
    (hcoeff : ∀ i, ∑ j, coeff i j * algebraMap A Λ (a j) = π i ^ n) :
    ∃ φ : (parameterPresentationPolynomial A d r ⧸
        parameterPresentationIdeal (d := d) (r := r) n a) →ₐ[A] Λ,
      (∀ i, φ (Ideal.Quotient.mk _ (MvPolynomial.X (Sum.inl i))) = π i) ∧
      (∀ i j, φ (Ideal.Quotient.mk _ (MvPolynomial.X (Sum.inr (i, j)))) =
        coeff i j) := by
  let P := parameterPresentationPolynomial A d r
  let J := parameterPresentationIdeal (d := d) (r := r) n a
  let ev : P →ₐ[A] Λ := MvPolynomial.aeval (fun x : Fin d ⊕ (Fin d × Fin r) =>
    match x with
    | Sum.inl i => π i
    | Sum.inr ij => coeff ij.1 ij.2)
  have hrel (i : Fin d) : ev (parameterPresentationRelation n a i) = 0 := by
    have hx (j : Fin d) : ev (MvPolynomial.X (Sum.inl j)) = π j := by
      dsimp [ev]
      exact MvPolynomial.aeval_X _ _
    have hz (j : Fin d) (l : Fin r) :
        ev (MvPolynomial.X (Sum.inr (j, l))) = coeff j l := by
      dsimp [ev]
      exact MvPolynomial.aeval_X _ _
    have hc (l : Fin r) : ev (MvPolynomial.C (a l)) = algebraMap A Λ (a l) := by
      dsimp [ev]
      exact MvPolynomial.aeval_C _ _
    calc
      ev (parameterPresentationRelation n a i) =
          π i ^ n - ∑ j, algebraMap A Λ (a j) * coeff i j := by
        rw [parameterPresentationRelation, map_sub, map_pow, map_sum]
        simp only [map_mul, hx, hz, hc]
      _ = 0 := by
        rw [← hcoeff i]
        have hs : (∑ j, coeff i j * algebraMap A Λ (a j)) =
            ∑ j, algebraMap A Λ (a j) * coeff i j := by
          apply Finset.sum_congr rfl
          intro j hj
          ring
        rw [hs]
        ring
  have hJ : J ≤ RingHom.ker ev.toRingHom := by
    dsimp [J, parameterPresentationIdeal]
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact RingHom.mem_ker.mpr (hrel i)
  refine ⟨Ideal.Quotient.liftₐ J ev (fun x hx => RingHom.mem_ker.mp (hJ hx)), ?_, ?_⟩
  · intro i
    change (Ideal.Quotient.lift J ev.toRingHom _)
      (Ideal.Quotient.mk J (MvPolynomial.X (Sum.inl i))) = _
    rw [Ideal.Quotient.lift_mk]
    exact MvPolynomial.aeval_X _ _
  · intro i j
    change (Ideal.Quotient.lift J ev.toRingHom _)
      (Ideal.Quotient.mk J (MvPolynomial.X (Sum.inr (i, j)))) = _
    rw [Ideal.Quotient.lift_mk]
    exact MvPolynomial.aeval_X _ _

private lemma mul_pow_add_eq_zero_iff {R : Type*} [CommRing R] {t : R}
    (h : ∀ x : R, x * t = 0 ↔ x * t ^ 2 = 0) (x : R) (m n : ℕ) :
    x * t ^ (m + 1) = 0 ↔ x * t ^ (m + n + 1) = 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hstep := mul_pow_succ_eq_zero_iff h x (m + n)
    simpa [Nat.add_assoc] using ih.trans hstep

private lemma mul_pow_succ_eq_zero_iff_double {R : Type*} [CommRing R] {t : R}
    (h : ∀ x : R, x * t = 0 ↔ x * t ^ 2 = 0) (x : R) (n : ℕ) :
    x * t ^ (n + 1) = 0 ↔ x * t ^ ((n + 1) * 2) = 0 := by
  have hpow := mul_pow_add_eq_zero_iff h x n (n + 1)
  have hexp : n + (n + 1) + 1 = (n + 1) * 2 := by omega
  simpa [hexp] using hpow

private lemma mul_pow_pos_eq_zero_iff_double {R : Type*} [CommRing R] {t : R}
    (h : ∀ x : R, x * t = 0 ↔ x * t ^ 2 = 0) (x : R) {c : ℕ}
    (hc : 0 < c) :
    x * t ^ c = 0 ↔ x * t ^ (2 * c) = 0 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : c ≠ 0)
  simpa [Nat.mul_comm] using mul_pow_succ_eq_zero_iff_double h x n

private lemma mul_pow_pos_eq_zero_iff_double_pow {R : Type*} [CommRing R] {t : R}
    (h : ∀ x : R, x * t = 0 ↔ x * t ^ 2 = 0) (x : R) {c : ℕ}
    (hc : 0 < c) :
    x * t ^ c = 0 ↔ x * (t ^ c) ^ 2 = 0 := by
  simpa [pow_two, pow_mul, Nat.mul_comm] using
    (mul_pow_pos_eq_zero_iff_double h x hc)

private lemma quotient_ann_stable_pow
    {R : Type*} [CommRing R] (I : Ideal R) (t : R)
    (h : ∀ x : R ⧸ I,
      x * Ideal.Quotient.mk I t = 0 ↔
        x * (Ideal.Quotient.mk I t) ^ 2 = 0)
    {c : ℕ} (hc : 0 < c) (x : R ⧸ I) :
    x * Ideal.Quotient.mk I (t ^ c) = 0 ↔
      x * (Ideal.Quotient.mk I (t ^ c)) ^ 2 = 0 := by
  simpa only [map_pow] using
    (mul_pow_pos_eq_zero_iff_double_pow (R := R ⧸ I)
      (t := Ideal.Quotient.mk I t) h x hc)

/-- Equality of the annihilator of an element with that of its square, from the elementwise
form in which it is produced here. -/
theorem annihilator_span_singleton_eq_sq_of_forall {T : Type*} [CommRing T] (t : T)
    (h : ∀ x : T, x * t = 0 ↔ x * t ^ 2 = 0) :
    (Submodule.span T {t}).annihilator = (Submodule.span T {t ^ 2}).annihilator := by
  rw [SetLike.ext_iff]
  simpa only [Submodule.mem_annihilator_span_singleton, smul_eq_mul] using h

private lemma mem_minimalPrimes_of_isMinimalPrime {R : Type*} [CommRing R]
    {I q : Ideal R} (h : I.IsMinimalPrime q) : q ∈ I.minimalPrimes := by
  exact h

private lemma exists_pos_pow_le_of_le_radical_fg {R : Type*} [CommSemiring R]
    {I J : Ideal R} (hIJ : I ≤ J.radical) (hIFG : I.FG) :
    ∃ n : ℕ, 0 < n ∧ I ^ n ≤ J := by
  obtain ⟨n, hn⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hIJ hIFG
  refine ⟨n + 1, Nat.zero_lt_succ n, ?_⟩
  exact (Ideal.pow_le_pow_right (by omega : n ≤ n + 1)).trans hn

private lemma exists_power_containment_at_minimalPrime
    {R : Type*} [CommRing R] [IsNoetherianRing R]
    (I q : Ideal R) [q.IsPrime] (hIq : q ∈ I.minimalPrimes) :
    ∃ n : ℕ, 0 < n ∧
      Ideal.map (algebraMap R (Localization.AtPrime q)) (q ^ n) ≤
        Ideal.map (algebraMap R (Localization.AtPrime q)) I := by
  let L := Localization.AtPrime q
  have hrad : (I.map (algebraMap R L)).radical = q.map (algebraMap R L) :=
    IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes (q := q) (A := L) I hIq
  have hmax : q.map (algebraMap R L) = IsLocalRing.maximalIdeal L :=
    IsLocalization.AtPrime.map_eq_maximalIdeal q L
  have hfg : (IsLocalRing.maximalIdeal L).FG :=
    (IsLocalRing.maximalIdeal L).fg_of_isNoetherianRing
  obtain ⟨n, hn, hpow⟩ := exists_pos_pow_le_of_le_radical_fg
    (I := IsLocalRing.maximalIdeal L) (J := I.map (algebraMap R L))
    (by rw [← hmax]; exact hrad.symm.le) hfg
  refine ⟨n, hn, ?_⟩
  rw [Ideal.map_pow, hmax]
  exact hpow

private lemma exists_nat_eq_ringKrullDim {R : Type*} [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R] :
    ∃ d : ℕ, ringKrullDim R = (d : WithBot ℕ∞) := by
  have hnonneg : (0 : WithBot ℕ∞) ≤ ringKrullDim R :=
    (zero_le_ringKrullDim_iff_nontrivial (R := R)).mpr inferInstance
  have hbot : ringKrullDim R ≠ ⊥ := by
    intro h
    rw [h] at hnonneg
    simp at hnonneg
  cases hx : ringKrullDim R with
  | bot => exact (hbot hx).elim
  | coe x =>
    cases x with
    | top => exact (ringKrullDim_ne_top hx).elim
    | coe d => exact ⟨d, by simp⟩

private lemma polynomial_idealOfVars_eq_ker_constantCoeff
    {R ι : Type*} [CommRing R] :
    MvPolynomial.idealOfVars ι R = RingHom.ker MvPolynomial.constantCoeff := by
  classical
  ext p
  change p ∈ Ideal.span (Set.range MvPolynomial.X) ↔ _
  rw [← Set.image_univ, MvPolynomial.mem_ideal_span_X_image,
    RingHom.mem_ker, MvPolynomial.constantCoeff_eq]
  simp only [Set.mem_univ, true_and]
  constructor
  · intro h
    by_contra h0
    obtain ⟨i, hi⟩ := h 0 (MvPolynomial.mem_support_iff.mpr h0)
    exact hi rfl
  · intro h m hm
    by_contra hn
    have hm0 : m = 0 := by
      ext i
      by_contra hi
      exact hn ⟨i, hi⟩
    subst m
    exact (MvPolynomial.mem_support_iff.mp hm) h

private lemma polynomial_idealOfVars_isMaximal
    {k ι : Type*} [Field k] : (MvPolynomial.idealOfVars ι k).IsMaximal := by
  rw [polynomial_idealOfVars_eq_ker_constantCoeff]
  apply RingHom.ker_isMaximal_of_surjective
  intro x
  exact ⟨MvPolynomial.C x, MvPolynomial.constantCoeff_C ι x⟩

private lemma isRegular_of_span_eq_maximalIdeal
    {T : Type*} [CommRing T] [IsRegularLocalRing T] {d : ℕ}
    (π : Fin d → T)
    (hspan : Ideal.span (Set.range π) = IsLocalRing.maximalIdeal T)
    (hd : ringKrullDim T = d) :
    RingTheory.Sequence.IsRegular T (List.ofFn π) := by
  have hlist : Ideal.ofList (List.ofFn π) = IsLocalRing.maximalIdeal T := by
    rw [← hspan]
    unfold Ideal.ofList
    congr 1
    ext x
    simp
  have hlength : (List.ofFn π).length = (IsLocalRing.maximalIdeal T).spanFinrank := by
    rw [List.length_ofFn]
    have h := (IsRegularLocalRing.spanFinrank_maximalIdeal (R := T)).trans hd
    exact_mod_cast h.symm
  exact (IsRegularLocalRing.isRegular_and_isRegularLocalRing_quotient_and_isMaximalCohenMacaulay
    T).1 _ hlist hlength |>.1

private lemma isRegular_localized_parameters
    {Λ : Type*} [CommRing Λ] (q : Ideal Λ) [q.IsPrime]
    [IsRegularLocalRing (Localization.AtPrime q)] {d : ℕ} (π : Fin d → Λ)
    (hspan : Ideal.map (algebraMap Λ (Localization.AtPrime q))
      (Ideal.span (Set.range π)) = Ideal.map (algebraMap Λ (Localization.AtPrime q)) q)
    (hd : ringKrullDim (Localization.AtPrime q) = d) :
    RingTheory.Sequence.IsRegular (Localization.AtPrime q)
      (List.ofFn fun i => algebraMap Λ (Localization.AtPrime q) (π i)) := by
  apply isRegular_of_span_eq_maximalIdeal _ _ hd
  rwa [Ideal.map_span, ← Set.range_comp,
    IsLocalization.AtPrime.map_eq_maximalIdeal q (Localization.AtPrime q)] at hspan

end Stacks.Smoothing

end
