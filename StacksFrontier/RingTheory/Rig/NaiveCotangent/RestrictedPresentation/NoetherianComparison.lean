module

public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Homology.DoubleExtend
public import StacksFrontier.RingTheory.RestrictedPowerSeries
public import StacksFrontier.RingTheory.Rig.FiniteType
public import StacksFrontier.RingTheory.Rig.NaiveCotangent
public import StacksFrontier.RingTheory.Rig.NaiveCotangent.PresentationIndependence
public import StacksFrontier.Topology.Algebra.AdicTopology.AdmissibleRings
public import StacksFrontier.RingTheory.Rig.NaiveCotangent.RestrictedPresentation.Construction

/-!
# Comparison of the restricted complex with Equation 0AJR

The closures of extended ideals forming a basis of neighbourhoods of `0` in `A{x_i}`, the
continuity of linear maps out of polynomials for the defining topology, the Taylor remainder
of a polynomial, and maps of two-term complexes; then the identification, for an ideal of
definition of a Noetherian `A`, of the complex of Tag 0GBX with the one of Equation 0AJR, and
its independence of the ideal of definition. Part of
`StacksFrontier.RingTheory.Rig.NaiveCotangent.RestrictedPresentation`.
-/

@[expose] public noncomputable section

open CategoryTheory
open ComplexShape (upIntRelNegOneZero)

universe u v

namespace Rig

open TopologicalRing

attribute [local implicit_reducible] Algebra.Extension.ofSurjective
  AdicFiniteTypeAlgebra.of

section Comparison

variable {A : Type u} [CommRing A] [TopologicalSpace A]
  {B : Type v} [CommRing B] [TopologicalSpace B] [Algebra A B]

open RestrictedPowerSeriesPresentation

private def denseImageIdealClosure
    {R S : Type*} [CommRing R] [CommRing S] [TopologicalSpace S] [IsTopologicalRing S]
    (f : R →+* S) (hf : DenseRange f) (J : Ideal R) : Ideal S :=
  let N := (J.toAddSubgroup.map f.toAddMonoidHom).topologicalClosure
  { N with
    smul_mem' := by
      intro a z hz
      change a * z ∈ N
      have hc : IsClosed (N : Set S) := AddSubgroup.isClosed_topologicalClosure _
      apply isClosed_property hf (hc.preimage (continuous_id.mul continuous_const)) _ a
      intro r
      apply (closure_minimal ?_ (hc.preimage (continuous_const.mul continuous_id))) hz
      rintro _ ⟨y, hy, rfl⟩
      exact subset_closure ⟨r * y, J.mul_mem_left r hy, f.map_mul r y⟩ }

private theorem denseImageIdealClosure_coe
    {R S : Type*} [CommRing R] [CommRing S] [TopologicalSpace S] [IsTopologicalRing S]
    (f : R →+* S) (hf : DenseRange f) (J : Ideal R) :
    (denseImageIdealClosure f hf J : Set S) = closure (f '' (J : Set R)) := rfl

private def restrictedIdealClosure
    {A : Type*} [CommRing A] [TopologicalSpace A] (σ : Type*) (J : Ideal A) :
    Ideal (RestrictedPowerSeries A σ) := by
  let : UniformSpace (MvPolynomial σ A) := restrictedPolynomialUniformSpace A σ
  exact denseImageIdealClosure (polynomialToRestrictedPowerSeries A σ)
    UniformSpace.Completion.denseRange_coe (J.map MvPolynomial.C)

private theorem restrictedIdealClosure_mem_nhds
    {A : Type*} [CommRing A] [TopologicalSpace A] (σ : Type*) (J : Ideal A)
    (hJ : IsOpen (J : Set A)) :
    (restrictedIdealClosure σ J : Set (RestrictedPowerSeries A σ)) ∈ nhds 0 := by
  let : TopologicalSpace (MvPolynomial σ A) := restrictedPolynomialTopology A σ
  let : UniformSpace (MvPolynomial σ A) := restrictedPolynomialUniformSpace A σ
  exact UniformSpace.Completion.isDenseInducing_coe.closure_image_mem_nhds
    ((restrictedPolynomialRingFilterBasis A σ).toAddGroupFilterBasis
      |>.nhds_zero_hasBasis.mem_of_mem ⟨⟨J, hJ⟩, rfl⟩)

private theorem restrictedIdealClosure_basis
    {A : Type*} [CommRing A] [TopologicalSpace A] (σ : Type*) :
    (nhds (0 : RestrictedPowerSeries A σ)).HasBasis
      (fun J : Ideal A => IsOpen (J : Set A))
      (fun J => (restrictedIdealClosure σ J : Set (RestrictedPowerSeries A σ))) := by
  let : TopologicalSpace (MvPolynomial σ A) := restrictedPolynomialTopology A σ
  let : UniformSpace (MvPolynomial σ A) := restrictedPolynomialUniformSpace A σ
  refine ⟨fun U => ⟨fun hU => ?_, fun ⟨J, hJ, hJU⟩ =>
    Filter.mem_of_superset (restrictedIdealClosure_mem_nhds σ J hJ) hJU⟩⟩
  obtain ⟨V, hV, hVc, hVU⟩ := exists_mem_nhds_isClosed_subset hU
  have hpre : (polynomialToRestrictedPowerSeries A σ) ⁻¹' V ∈
      nhds (0 : MvPolynomial σ A) :=
    (UniformSpace.Completion.continuous_coe (α := MvPolynomial σ A)).continuousAt hV
  obtain ⟨W, hW, hWV⟩ :=
    (restrictedPolynomialRingFilterBasis A σ).toAddGroupFilterBasis
      |>.nhds_zero_hasBasis.mem_iff.mp hpre
  rcases hW with ⟨J, rfl⟩
  refine ⟨J.1, J.2, ?_⟩
  show closure ((polynomialToRestrictedPowerSeries A σ) ''
    (J.1.map (MvPolynomial.C : A →+* MvPolynomial σ A) : Set _)) ⊆ U
  exact (closure_minimal (Set.image_subset_iff.mpr hWV) hVc).trans hVU

/-- Two continuous maps from `A{x_σ}` to a Hausdorff space agree if they agree on polynomials. -/
private theorem funext_of_polynomialToRestrictedPowerSeries
    {A : Type*} [CommRing A] [TopologicalSpace A] {σ : Type*} {X : Type*} [TopologicalSpace X]
    [T2Space X] {f g : RestrictedPowerSeries A σ → X} (hf : Continuous f) (hg : Continuous g)
    (h : ∀ p, f (polynomialToRestrictedPowerSeries A σ p) =
      g (polynomialToRestrictedPowerSeries A σ p)) : f = g := by
  let : UniformSpace (MvPolynomial σ A) := restrictedPolynomialUniformSpace A σ
  exact UniformSpace.Completion.denseRange_coe.equalizer hf hg (funext h)

/-- An additive map out of polynomials is continuous for the defining topology as soon as, for
each basic neighbourhood ideal, some open ideal of coefficients has its monomials mapped into it. -/
private theorem continuous_restrictedPolynomialTopology_of_monomial
    {A T σ ι : Type*} [CommRing A] [TopologicalSpace A] [CommRing T] [TopologicalSpace T]
    [IsTopologicalAddGroup T] {p : ι → Prop} {K : ι → Ideal T}
    (hb : (nhds (0 : T)).HasBasis p fun i => (K i : Set T)) (g : MvPolynomial σ A →+ T)
    (h : ∀ i, p i → ∃ J : Ideal A, IsOpen (J : Set A) ∧
      ∀ d, ∀ a ∈ J, g (MvPolynomial.monomial d a) ∈ K i) :
    @Continuous _ _ (restrictedPolynomialTopology A σ) _ g := by
  let : TopologicalSpace (MvPolynomial σ A) := restrictedPolynomialTopology A σ
  let : IsTopologicalRing (MvPolynomial σ A) := restrictedPolynomialIsTopologicalRing A σ
  apply continuous_of_tendsto_nhds_zero g
  apply ((restrictedPolynomialRingFilterBasis A σ).toAddGroupFilterBasis
    |>.nhds_zero_hasBasis.tendsto_iff hb).mpr
  intro i hi
  obtain ⟨J, hJ, hg⟩ := h i hi
  refine ⟨(J.map (MvPolynomial.C : A →+* MvPolynomial σ A) : Set _), ⟨⟨J, hJ⟩, rfl⟩, ?_⟩
  intro q hq
  change g q ∈ K i
  have hcoeff := MvPolynomial.mem_map_C_iff.mp hq
  rw [← MvPolynomial.support_sum_monomial_coeff q, map_sum]
  exact (K i).sum_mem fun d _ => hg d _ (hcoeff d)

theorem continuous_restrictedPolynomialLinearMap
    {A : Type*} [CommRing A] [TopologicalSpace A] {σ τ : Type*}
    (F : MvPolynomial σ A →ₗ[A] RestrictedPowerSeries A τ) :
    @Continuous _ _ (restrictedPolynomialTopology A σ) _ F := by
  refine continuous_restrictedPolynomialTopology_of_monomial (restrictedIdealClosure_basis τ)
    F.toAddMonoidHom fun J hJ => ⟨J, hJ, fun d a ha => ?_⟩
  have ha' : coeffToRestrictedPowerSeries A τ a ∈ restrictedIdealClosure τ J :=
    subset_closure ⟨MvPolynomial.C a, Ideal.mem_map_of_mem _ ha, rfl⟩
  have hm : MvPolynomial.monomial d a = a • MvPolynomial.monomial d (1 : A) := by
    rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  change F _ ∈ _
  rw [hm, map_smul, Algebra.smul_def]
  exact (restrictedIdealClosure τ J).mul_mem_right _ ha'

section

open MvPolynomial

private theorem eval_eq_add_pderiv_of_square_zero
    {A S σ : Type*} [CommRing A] [CommRing S] [Algebra A S] [Fintype σ]
    (x y : σ → S) (h : ∀ i j, (x i - y i) * (x j - y j) = 0)
    (p : MvPolynomial σ A) :
    aeval x p = aeval y p + ∑ i, aeval y (pderiv i p) * (x i - y i) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq =>
      simp only [map_add, hp, hq, add_mul, Finset.sum_add_distrib]
      ring
  | mul_X p k hp =>
      have hX (i : σ) : aeval y (pderiv i (X k : MvPolynomial σ A)) =
          if i = k then 1 else 0 := by
        by_cases hi : i = k <;> simp [pderiv_X, hi]
      simp only [map_mul, aeval_X, pderiv_mul, map_add, hX, mul_ite,
        mul_one, mul_zero, add_mul, ite_mul, zero_mul,
        Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      rw [hp]
      have hz : (∑ i, aeval y (pderiv i p) * (x i - y i)) * (x k - y k) = 0 := by
        rw [Finset.sum_mul]
        apply Finset.sum_eq_zero
        intro i hi
        rw [mul_assoc, h, mul_zero]
      have he : ∑ i, aeval y (pderiv i p) * y k * (x i - y i) =
          (∑ i, aeval y (pderiv i p) * (x i - y i)) * y k := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      rw [he]
      linear_combination hz

private theorem taylor_remainder_mem_sq
    {A S σ : Type*} [CommRing A] [CommRing S] [Algebra A S] [Fintype σ]
    (I : Ideal S) (x y : σ → S) (h : ∀ i, x i - y i ∈ I)
    (p : MvPolynomial σ A) :
    aeval x p - aeval y p - ∑ i, aeval y (pderiv i p) * (x i - y i) ∈ I ^ 2 := by
  let q := Ideal.Quotient.mkₐ A (I ^ 2)
  have hq (z : σ → S) (f : MvPolynomial σ A) :
      q (aeval z f) = aeval (fun i => q (z i)) f := by
    have he : q.comp (aeval z) = aeval (fun i => q (z i)) := by
      ext i
      simp
    exact DFunLike.congr_fun he f
  apply (Ideal.Quotient.eq_zero_iff_mem).mp
  show q _ = 0
  simp only [map_sub, map_sum, map_mul, hq]
  have hxy : ∀ i j, (q (x i) - q (y i)) * (q (x j) - q (y j)) = 0 := by
    intro i j
    rw [← map_sub, ← map_sub, ← map_mul]
    exact (Ideal.Quotient.eq_zero_iff_mem).mpr
      (by simpa only [pow_two] using Ideal.mul_mem_mul (h i) (h j))
  rw [eval_eq_add_pderiv_of_square_zero _ _ hxy]
  abel

theorem exists_taylor_remainder_linearMap
    (A σ : Type*) [CommRing A] [Fintype σ] :
    ∃ L : MvPolynomial σ A →ₗ[A] (σ × σ → MvPolynomial (σ ⊕ σ) A),
      ∀ p : MvPolynomial σ A,
        aeval (fun i => X (Sum.inl i)) p - aeval (fun i => X (Sum.inr i)) p -
          ∑ i, aeval (fun i => X (Sum.inr i)) (pderiv i p) *
            (X (Sum.inl i) - X (Sum.inr i)) =
          ∑ ij : σ × σ, L p ij * (X (Sum.inl ij.1) - X (Sum.inr ij.1)) *
            (X (Sum.inl ij.2) - X (Sum.inr ij.2)) := by
  classical
  let T := MvPolynomial (σ ⊕ σ) A
  let x : σ → T := fun i => X (Sum.inl i)
  let y : σ → T := fun i => X (Sum.inr i)
  let d : σ → T := fun i => x i - y i
  let v : σ × σ → T := fun ij => d ij.1 * d ij.2
  let I := Ideal.span (Set.range d)
  let U := Ideal.span (Set.range v)
  have hIU : I ^ 2 = U := by
    rw [pow_two, Ideal.span_mul_span]
    congr 1
    ext z
    constructor
    · rintro ⟨a, ⟨i, rfl⟩, b, ⟨j, rfl⟩, rfl⟩
      exact ⟨(i, j), rfl⟩
    · rintro ⟨⟨i, j⟩, rfl⟩
      exact ⟨d i, ⟨i, rfl⟩, d j, ⟨j, rfl⟩, rfl⟩
  let E : MvPolynomial σ A →ₗ[A] T :=
    (aeval x).toLinearMap - (aeval y).toLinearMap -
      ∑ i, d i • ((aeval y).toLinearMap.comp (pderiv i).toLinearMap)
  have hE (p : MvPolynomial σ A) : E p =
      aeval x p - aeval y p - ∑ i, aeval y (pderiv i p) * d i := by
    simp [E, mul_comm]
  have hEU (p : MvPolynomial σ A) : E p ∈ U := by
    rw [hE, ← hIU]
    exact taylor_remainder_mem_sq I x y (fun i => Ideal.subset_span ⟨i, rfl⟩) p
  let F : (σ × σ → T) →ₗ[A] T :=
    ∑ ij, v ij • (LinearMap.proj ij : (σ × σ → T) →ₗ[T] T).restrictScalars A
  have hF (c : σ × σ → T) : F c = ∑ ij, c ij * v ij := by
    simp [F, mul_comm]
  have hFU (c : σ × σ → T) : F c ∈ U := by
    rw [hF]
    exact U.sum_mem fun ij _ => U.mul_mem_left _ (Ideal.subset_span ⟨ij, rfl⟩)
  let F' := F.codRestrict (U.restrictScalars A) hFU
  have hsurj : Function.Surjective F' := by
    intro z
    obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp z.2
    exact ⟨c, Subtype.ext ((hF c).trans hc)⟩
  obtain ⟨L, hL⟩ :=
    Module.projective_lifting_property F' (E.codRestrict (U.restrictScalars A) hEU) hsurj
  refine ⟨L, fun p => ?_⟩
  have he := congrArg Subtype.val (DFunLike.congr_fun hL p)
  change F (L p) = E p at he
  rw [hE, hF] at he
  exact he.symm.trans (Finset.sum_congr rfl fun ij _ => mul_assoc _ _ _ |>.symm)

end

open HomologicalComplex

def doubleMap {C : Type*} [Category C] [Preadditive C] [Limits.HasZeroObject C]
    {X₀ X₁ Y₀ Y₁ : C} (d : X₀ ⟶ X₁) (e : Y₀ ⟶ Y₁)
    (a : X₀ ⟶ Y₀) (b : X₁ ⟶ Y₁) (hab : a ≫ e = d ≫ b) :
    double d upIntRelNegOneZero ⟶
      double e upIntRelNegOneZero :=
  mkHomFromDouble upIntRelNegOneZero (by norm_num)
    (a ≫ (doubleXIso₀ e upIntRelNegOneZero).inv)
    (b ≫ (doubleXIso₁ e upIntRelNegOneZero (by norm_num)).inv)
    (by
      rw [double_d e upIntRelNegOneZero (by norm_num)]
      simpa using congrArg
        (fun k => k ≫ (doubleXIso₁ e
          upIntRelNegOneZero (by norm_num)).inv) hab)
    (by intro k hk; rw [double_d_eq_zero₀ _ _ _ _ (by norm_num)]; simp)

end Comparison

/-! ### Comparison with the Noetherian construction of Equation 0AJR -/

open HomologicalComplex

private def cotangentMapOfAlgHom
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (P Q : Algebra.Extension R S) (f : P.Ring →ₐ[R] Q.Ring)
    (hf : ∀ x, algebraMap Q.Ring S (f x) = algebraMap P.Ring S x) :
    P.Cotangent →ₗ[S] Q.Cotangent :=
  Algebra.Extension.Cotangent.map
    { toRingHom := f.toRingHom
      toRingHom_algebraMap := f.commutes
      algebraMap_toRingHom := hf }

private theorem cotangentMapOfAlgHom_mk
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (P Q : Algebra.Extension R S) (f : P.Ring →ₐ[R] Q.Ring)
    (hf : ∀ x, algebraMap Q.Ring S (f x) = algebraMap P.Ring S x) (x : P.ker) :
    cotangentMapOfAlgHom P Q f hf (Algebra.Extension.Cotangent.mk x) =
      Algebra.Extension.Cotangent.mk ⟨f x.1, by
        change algebraMap Q.Ring S (f x.1) = 0
        rw [hf]; exact x.2⟩ :=
  Algebra.Extension.Cotangent.map_mk _ x

private def extensionCotangentEquivOfAlgEquiv
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (P Q : Algebra.Extension R S) (e : P.Ring ≃ₐ[R] Q.Ring)
    (he : ∀ x, algebraMap Q.Ring S (e x) = algebraMap P.Ring S x) :
    P.Cotangent ≃ₗ[S] Q.Cotangent :=
  { cotangentMapOfAlgHom P Q e.toAlgHom he with
    invFun := cotangentMapOfAlgHom Q P e.symm.toAlgHom (fun y =>
      (he (e.symm y)).symm.trans
        (congrArg (algebraMap Q.Ring S) (e.apply_symm_apply y)))
    left_inv := by
      intro x
      obtain ⟨z, rfl⟩ := Algebra.Extension.Cotangent.mk_surjective x
      change Algebra.Extension.Cotangent.mk
        ⟨e.symm (e z.1), by simpa only [e.symm_apply_apply] using z.2⟩ =
          Algebra.Extension.Cotangent.mk z
      congr 1
      exact Subtype.ext (e.symm_apply_apply z.1)
    right_inv := by
      intro x
      obtain ⟨z, rfl⟩ := Algebra.Extension.Cotangent.mk_surjective x
      change Algebra.Extension.Cotangent.mk
        ⟨e (e.symm z.1), by simpa only [e.apply_symm_apply] using z.2⟩ =
          Algebra.Extension.Cotangent.mk z
      congr 1
      exact Subtype.ext (e.apply_symm_apply z.1) }

private def doubleIso {C : Type*} [Category C] [Preadditive C] [Limits.HasZeroObject C]
    {X₀ X₁ Y₀ Y₁ : C} (d : X₀ ⟶ X₁) (e : Y₀ ⟶ Y₁)
    (a : X₀ ≅ Y₀) (b : X₁ ≅ Y₁) (hab : a.hom ≫ e = d ≫ b.hom) :
    double d upIntRelNegOneZero ≅
      double e upIntRelNegOneZero where
  hom := doubleMap d e a.hom b.hom hab
  inv := doubleMap e d a.inv b.inv (by
    simpa using (congrArg (fun f => a.inv ≫ f ≫ b.inv) hab).symm)
  hom_inv_id := by
    apply from_double_hom_ext <;> simp [doubleMap]
  inv_hom_id := by
    apply from_double_hom_ext <;> simp [doubleMap]

section Noetherian

variable {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [IsLinearTopology A A] [IsNoetherianRing A]

open RestrictedPowerSeriesPresentation

omit [IsTopologicalRing A] [IsLinearTopology A A] [IsNoetherianRing A] in
private theorem restrictedPowerSeries_isLinearTopology (σ : Type*) :
    @IsLinearTopology (RestrictedPowerSeries A σ) (RestrictedPowerSeries A σ)
      _ _ Semiring.toModule _ := by
  let : Module (RestrictedPowerSeries A σ) (RestrictedPowerSeries A σ) := Semiring.toModule
  exact @IsLinearTopology.mk_of_hasBasis _ _ _ _ Semiring.toModule
    _ _ _ _ _ _ _ _ (restrictedIdealClosure_basis (A := A) σ)

omit [IsNoetherianRing A] in
private theorem continuous_restrictedCoefficients (σ : Type*) :
    Continuous (algebraMap A (RestrictedPowerSeries A σ)) := by
  apply continuous_of_tendsto_nhds_zero (coeffToRestrictedPowerSeries A σ).toAddMonoidHom
  apply (IsLinearTopology.hasBasis_open_ideal.tendsto_iff
    (restrictedIdealClosure_basis σ)).mpr
  intro J hJ
  refine ⟨J, hJ, ?_⟩
  intro a ha
  exact subset_closure ⟨MvPolynomial.C a, Ideal.mem_map_of_mem _ ha, rfl⟩

omit [IsTopologicalRing A] [IsLinearTopology A A] [IsNoetherianRing A] in
private theorem restrictedPowerSeries_isComplete (σ : Type*) :
    TopologicalRing.IsComplete (RestrictedPowerSeries A σ) := by
  let : UniformSpace (MvPolynomial σ A) := restrictedPolynomialUniformSpace A σ
  let : IsUniformAddGroup (MvPolynomial σ A) :=
    (restrictedPolynomialRingFilterBasis A σ).toAddGroupFilterBasis.isUniformAddGroup
  let : IsUniformAddGroup (RestrictedPowerSeries A σ) :=
    inferInstanceAs (IsUniformAddGroup (UniformSpace.Completion (MvPolynomial σ A)))
  refine ⟨inferInstance, ?_⟩
  rw [IsUniformAddGroup.rightUniformSpace_eq]
  infer_instance

omit [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A] [IsNoetherianRing A] in
private theorem restrictedLimit_t2 (I : Ideal A) (σ : Type*) :
    T2Space (_root_.RestrictedPowerSeries I σ) := by
  let : ∀ n : ℕ, TopologicalSpace (MvPolynomial σ (A ⧸ I ^ n)) := fun _ => ⊥
  let : ∀ n : ℕ, DiscreteTopology (MvPolynomial σ (A ⧸ I ^ n)) := fun _ => ⟨rfl⟩
  exact inferInstanceAs (T2Space (↑(_root_.RestrictedPowerSeries.inverseLimitSubring I σ)))

omit [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A] [IsNoetherianRing A] in
private theorem restrictedLimit_basis (I : Ideal A) (σ : Type*) (hI : I.FG) :
    (nhds (0 : _root_.RestrictedPowerSeries I σ)).HasBasis (fun _ : ℕ => True)
      (fun n => ((I.map (algebraMap A
          (AdicCompletion (I.map (MvPolynomial.C : A →+* MvPolynomial σ A))
            (MvPolynomial σ A))) ^ n).comap
        (_root_.RestrictedPowerSeries.adicCompletionEquiv I σ).toRingHom : Set _)) := by
  let T := AdicCompletion (I.map (MvPolynomial.C : A →+* MvPolynomial σ A))
    (MvPolynomial σ A)
  let : TopologicalSpace T :=
    _root_.RestrictedPowerSeries.polynomialCompletionAdicTopology I σ
  have hf := _root_.RestrictedPowerSeries.isHomeomorph_adicCompletionEquiv I σ hI
  rw [hf.isInducing.nhds_eq_comap, map_zero]
  exact (I.map (algebraMap A T)).hasBasis_nhds_zero_adic.comap _

omit [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A] [IsNoetherianRing A] in
private theorem restrictedLimit_isLinearTopology (I : Ideal A) (σ : Type*) (hI : I.FG) :
    IsLinearTopology (_root_.RestrictedPowerSeries I σ)
      (_root_.RestrictedPowerSeries I σ) :=
  IsLinearTopology.mk_of_hasBasis _ (restrictedLimit_basis I σ hI)

omit [IsLinearTopology A A] [IsNoetherianRing A] in
private theorem continuous_restrictedLimitCoefficients
    {I : Ideal A} (hI : _root_.IsAdic I) (hIFG : I.FG) (σ : Type*) :
    Continuous (algebraMap A (_root_.RestrictedPowerSeries I σ)) := by
  apply continuous_of_tendsto_nhds_zero (algebraMap A
    (_root_.RestrictedPowerSeries I σ)).toAddMonoidHom
  apply (hI.hasBasis_nhds_zero.tendsto_iff
    (restrictedLimit_basis I σ hIFG)).mpr
  intro n hn
  refine ⟨n, trivial, ?_⟩
  intro a ha
  show _root_.RestrictedPowerSeries.adicCompletionAlgEquiv I σ
    (algebraMap A _ a) ∈ (I.map (algebraMap A
      (AdicCompletion (I.map (MvPolynomial.C : A →+* MvPolynomial σ A))
        (MvPolynomial σ A)))) ^ n
  rw [AlgEquiv.commutes, ← Ideal.map_pow]
  exact Ideal.mem_map_of_mem _ ha

omit [IsTopologicalRing A] [IsLinearTopology A A] [IsNoetherianRing A] in
private theorem continuous_polynomialAlgHom_of_linearTopology
    {T : Type*} [CommRing T] [TopologicalSpace T] [IsTopologicalRing T]
    [IsLinearTopology T T] [Algebra A T]
    (hAT : Continuous (algebraMap A T)) {σ : Type*} (f : MvPolynomial σ A →ₐ[A] T) :
    @Continuous _ _ (restrictedPolynomialTopology A σ) _ f := by
  refine continuous_restrictedPolynomialTopology_of_monomial IsLinearTopology.hasBasis_open_ideal
    f.toRingHom.toAddMonoidHom fun J hJ => ⟨J.comap (algebraMap A T), hJ.preimage hAT,
      fun d a ha => ?_⟩
  change f _ ∈ J
  rw [MvPolynomial.monomial_eq, map_mul, MvPolynomial.C_eq_algebraMap, f.commutes]
  exact J.mul_mem_right _ ha

omit [IsTopologicalRing A] [IsLinearTopology A A] [IsNoetherianRing A] in
private theorem exists_continuous_restrictedExtension
    {T : Type*} [CommRing T] [TopologicalSpace T] [IsTopologicalRing T]
    [IsLinearTopology T T] [Algebra A T]
    (hAT : Continuous (algebraMap A T)) (hT : TopologicalRing.IsComplete T)
    {σ : Type*} (f : MvPolynomial σ A →ₐ[A] T) :
    ∃ F : RestrictedPowerSeries A σ →ₐ[A] T, Continuous F ∧
      ∀ p, F (polynomialToRestrictedPowerSeries A σ p) = f p := by
  let : UniformSpace (MvPolynomial σ A) := restrictedPolynomialUniformSpace A σ
  let : IsUniformAddGroup (MvPolynomial σ A) :=
    (restrictedPolynomialRingFilterBasis A σ).toAddGroupFilterBasis.isUniformAddGroup
  let : UniformSpace T := IsTopologicalAddGroup.rightUniformSpace T
  let : IsUniformAddGroup T := isUniformAddGroup_of_addCommGroup
  let : CompleteSpace T := hT.2
  let : T2Space T := hT.1
  have hf := continuous_polynomialAlgHom_of_linearTopology hAT f
  let E := UniformSpace.Completion.extensionHom f.toRingHom hf
  have hp (p : MvPolynomial σ A) :
      E (polynomialToRestrictedPowerSeries A σ p) = f p :=
    UniformSpace.Completion.extensionHom_coe f.toRingHom hf p
  let F : RestrictedPowerSeries A σ →ₐ[A] T :=
    { E with commutes' := fun a => (hp (MvPolynomial.C a)).trans (f.commutes a) }
  exact ⟨F, UniformSpace.Completion.continuous_extension, hp⟩

omit [IsNoetherianRing A] in
private theorem exists_restrictedLimitAlgEquiv {I : Ideal A}
    (hI : _root_.IsAdic I) (hIFG : I.FG) (σ : Type*) :
    ∃ e : RestrictedPowerSeries A σ ≃ₐ[A] _root_.RestrictedPowerSeries I σ,
      Continuous e ∧ Continuous e.symm ∧ ∀ p : MvPolynomial σ A,
        e (polynomialToRestrictedPowerSeries A σ p) =
          _root_.RestrictedPowerSeries.polynomialAlgHom I σ p := by
  -- The module structure of `A{x_σ}` over itself has to be supplied in the shape that
  -- `IsLinearTopology` asks for: the ring structure is transported from a completion by a
  -- tactic proof, so instance synthesis cannot identify the `AddCommMonoid` obtained through
  -- `Semiring` with the one obtained through `AddCommGroup`.
  let instAcg : AddCommGroup (RestrictedPowerSeries A σ) := inferInstance
  let instMod : @Module (RestrictedPowerSeries A σ) (RestrictedPowerSeries A σ)
      inferInstance instAcg.toAddCommMonoid := Semiring.toModule
  let instLin : @IsLinearTopology (RestrictedPowerSeries A σ) (RestrictedPowerSeries A σ)
      inferInstance instAcg instMod inferInstance :=
    restrictedPowerSeries_isLinearTopology σ
  let : IsLinearTopology (_root_.RestrictedPowerSeries I σ)
      (_root_.RestrictedPowerSeries I σ) := restrictedLimit_isLinearTopology I σ hIFG
  let : T2Space (_root_.RestrictedPowerSeries I σ) := restrictedLimit_t2 I σ
  let S := RestrictedPowerSeries A σ
  let T := _root_.RestrictedPowerSeries I σ
  have hT : TopologicalRing.IsComplete T := ⟨inferInstance,
    _root_.RestrictedPowerSeries.limitCompleteSpace I σ⟩
  let pS : MvPolynomial σ A →ₐ[A] S :=
    { toRingHom := polynomialToRestrictedPowerSeries A σ, commutes' := fun _ => rfl }
  let pT := _root_.RestrictedPowerSeries.polynomialAlgHom I σ
  obtain ⟨F, hFc, hFp⟩ := exists_continuous_restrictedExtension
    (continuous_restrictedLimitCoefficients hI hIFG σ) hT pT
  obtain ⟨G, ⟨hGc, hGp⟩, hGu⟩ := _root_.RestrictedPowerSeries.existsUnique_continuousAlgHom_extends
    (fun n : ℕ => I ^ n) (fun _ _ h => Ideal.pow_le_pow_right h)
    (isAdic_iff.mp hI).1 (isAdic_iff.mp hI).2
    (continuous_restrictedCoefficients σ) (restrictedPowerSeries_isComplete σ) pS
  have hGF : G.comp F = AlgHom.id A S := by
    apply DFunLike.ext'
    refine funext_of_polynomialToRestrictedPowerSeries (hGc.comp hFc) continuous_id fun p => ?_
    change G (F (polynomialToRestrictedPowerSeries A σ p)) = _
    rw [hFp]
    exact DFunLike.congr_fun hGp p
  obtain ⟨H, hH, hHu⟩ := _root_.RestrictedPowerSeries.existsUnique_continuousAlgHom_extends
    (fun n : ℕ => I ^ n) (fun _ _ h => Ideal.pow_le_pow_right h)
    (isAdic_iff.mp hI).1 (isAdic_iff.mp hI).2
    (continuous_restrictedLimitCoefficients hI hIFG σ) hT pT
  have hFG : F.comp G = AlgHom.id A T := by
    apply (hHu _ ⟨hFc.comp hGc, ?_⟩).trans (hHu _ ⟨continuous_id, rfl⟩).symm
    rw [AlgHom.comp_assoc, hGp]
    exact DFunLike.ext _ _ hFp
  let e : S ≃ₐ[A] T :=
    { F with
      invFun := G
      left_inv := DFunLike.congr_fun hGF
      right_inv := DFunLike.congr_fun hFG }
  exact ⟨e, hFc, hGc, hFp⟩

/-- The agreement, for an ideal of definition `I` of a Noetherian `A`, of the complex of Tag
0GBX with the completed naive cotangent complex of Equation 0AJR. The source's reason is that
`A{x₁, …, x_r}` and `A[x₁, …, x_r]̂ ` are the same topological ring (Tag 0AL0), so that a
presentation of one kind is a presentation of the other with the same variables and the same
ideal; `ringEquiv`, `variableCount_eq` and `commutes` record exactly that, and the remaining
fields pin the resulting isomorphism of complexes. -/
public structure NoetherianPresentationComparison
    {I : Ideal A} {C : Type v} [CommRing C] [Algebra A C] [TopologicalSpace C]
    {P : RestrictedPowerSeriesPresentation A C}
    (K : RestrictedNaiveCotangentComplex P)
    (hc : IsAdicComplete (I.map (algebraMap A C)) C)
    [Algebra.FiniteType (A ⧸ I) (C ⧸ I.map (algebraMap A C))]
    (Q : CompletedPolynomialPresentation I (AdicFiniteTypeAlgebra.of C hc)) where
  /-- The identification `A{x₁, …, x_r} = A[x₁, …, x_r]̂ ` of Tag 0AL0. -/
  ringEquiv : P.ring ≃ₐ[A] Q.completedPolynomialRing
  /-- The two presentations use the same variables. -/
  variableCount_eq : P.variableCount = Q.variableCount
  /-- The two presentations have the same surjection onto `B`. -/
  commutes : Q.toAlgHom.comp ringEquiv.toAlgHom = P.toAlgHom
  /-- The resulting isomorphism of complexes. -/
  equiv : HomotopyEquiv K.cochainComplex
    (Rig.completedNaiveCotangentComplex (AdicFiniteTypeAlgebra.of C hc) Q).cochainComplex
  /-- In degree `-1` it is induced by `ringEquiv` on conormal classes. -/
  conormal_mk : ∀ g : P.extension.ker,
    equiv.hom.f (-1)
        (K.degreeNegOneIso.inv (ULift.up (Algebra.Extension.Cotangent.mk g))) =
      (Rig.completedNaiveCotangentComplex
          (AdicFiniteTypeAlgebra.of C hc) Q).degreeNegOneIso.inv
        (ULift.up (Algebra.Extension.Cotangent.mk ⟨ringEquiv g.1, by
          change Q.toAlgHom (ringEquiv g.1) = 0
          rw [show Q.toAlgHom (ringEquiv g.1) = (Q.toAlgHom.comp ringEquiv.toAlgHom) g.1 from rfl,
            commutes]
          exact g.2⟩))
  /-- In degree `0` it is the identity on the shared set of variables. -/
  free_apply : ∀ v : Fin P.variableCount → C,
    equiv.hom.f 0 (K.degreeZeroIso.inv (ULift.up v)) =
      (Rig.completedNaiveCotangentComplex
          (AdicFiniteTypeAlgebra.of C hc) Q).degreeZeroIso.inv
        (ULift.up fun j => v (Fin.cast variableCount_eq.symm j))

/-- **Stacks Project, Tag 0GBX.** When `A` is Noetherian and `I` is an ideal of definition for
its topology, the complex of Tag 0GBX reproduces the completed naive cotangent complex of
`B` over `(A, I)` defined by Equation 0AJR. -/
@[stacks 0GBX "agreement with Equation 0AJR"]
public theorem exists_noetherianPresentationComparison
    {I : Ideal A} (_hI : TopologicalRing.IsIdealOfDefinition I) (hIadic : _root_.IsAdic I)
    {C : Type v} [CommRing C] [Algebra A C] [TopologicalSpace C] [IsTopologicalRing C]
    [IsLinearTopology C C]
    (hc : IsAdicComplete (I.map (algebraMap A C)) C)
    [Algebra.FiniteType (A ⧸ I) (C ⧸ I.map (algebraMap A C))]
    (P : RestrictedPowerSeriesPresentation A C) :
    ∃ Q : CompletedPolynomialPresentation I (AdicFiniteTypeAlgebra.of C hc),
      Nonempty (NoetherianPresentationComparison (restrictedNaiveCotangentComplex P) hc Q)  := by
  let T := AdicCompletion (I.map (MvPolynomial.C : A →+*
    MvPolynomial (Fin P.variableCount) A)) (MvPolynomial (Fin P.variableCount) A)
  let : TopologicalSpace T :=
    _root_.RestrictedPowerSeries.polynomialCompletionLimitTopology I
      (Fin P.variableCount)
  let K := restrictedNaiveCotangentComplex P
  obtain ⟨e₀, he₀, he₀', he₀p⟩ := exists_restrictedLimitAlgEquiv hIadic
    (IsNoetherian.noetherian I) (Fin P.variableCount)
  let e : P.ring ≃ₐ[A] T := e₀.trans
    (_root_.RestrictedPowerSeries.adicCompletionAlgEquiv I (Fin P.variableCount))
  have hec : Continuous e :=
    (_root_.RestrictedPowerSeries.adicCompletionHomeomorph I
      (Fin P.variableCount)).continuous.comp he₀
  let : T2Space (_root_.RestrictedPowerSeries I (Fin P.variableCount)) :=
    restrictedLimit_t2 I (Fin P.variableCount)
  let : T2Space T :=
    (_root_.RestrictedPowerSeries.adicCompletionHomeomorph I
      (Fin P.variableCount)).t2Space
  have hep (p : MvPolynomial (Fin P.variableCount) A) :
      e (polynomialToRestrictedPowerSeries A (Fin P.variableCount) p) =
        algebraMap (MvPolynomial (Fin P.variableCount) A) T p := by
    show _root_.RestrictedPowerSeries.adicCompletionAlgEquiv I
      (Fin P.variableCount) (e₀ (polynomialToRestrictedPowerSeries A _ p)) = _
    rw [he₀p]
    exact _root_.RestrictedPowerSeries.adicCompletionEquiv_polynomialRingHom I _ p
  let f : T →ₐ[A] C := P.toAlgHom.comp e.symm.toAlgHom
  have hf : Function.Surjective f := P.toAlgHom_surjective.comp e.symm.surjective
  let Q : CompletedPolynomialPresentation I (AdicFiniteTypeAlgebra.of C hc) :=
    ⟨P.variableCount, RingHom.ker f.toRingHom, Ideal.quotientKerAlgEquivOfSurjective hf⟩
  have hQ (x : T) : Q.toAlgHom x = f x :=
    Ideal.quotientKerAlgEquivOfSurjective_mk hf x
  have he (x : P.ring) : Q.toAlgHom (e x) = P.toAlgHom x := by
    rw [hQ]
    exact congrArg P.toAlgHom (e.symm_apply_apply x)
  let L := Rig.completedNaiveCotangentComplex (AdicFiniteTypeAlgebra.of C hc) Q
  have hd (i : Fin P.variableCount) (x : P.ring) :
      L.partialDeriv i (e x) = e (K.partialDeriv i x) := by
    have heq : (fun y => L.partialDeriv i (e y)) = (fun y => e (K.partialDeriv i y)) := by
      refine funext_of_polynomialToRestrictedPowerSeries
        ((L.partialDeriv_continuous i).comp hec) (hec.comp (K.partialDeriv_continuous i))
        fun p => ?_
      rw [hep, L.partialDeriv_polynomial, K.partialDeriv_polynomial, hep]
    exact congrFun heq x
  let m : P.extension.Cotangent ≃ₗ[C] Q.extension.Cotangent :=
    extensionCotangentEquivOfAlgEquiv P.extension Q.extension e he
  have hm (g : P.extension.ker) : m (Algebra.Extension.Cotangent.mk g) =
      Algebra.Extension.Cotangent.mk ⟨e g.1, (he g.1).trans g.2⟩ :=
    cotangentMapOfAlgHom_mk P.extension Q.extension e.toAlgHom he g
  have hdm : L.differential.comp m.toLinearMap = K.differential := by
    refine LinearMap.ext fun x => ?_
    obtain ⟨g, rfl⟩ := Algebra.Extension.Cotangent.mk_surjective x
    show L.differential (m (Algebra.Extension.Cotangent.mk g)) = _
    rw [hm, L.differential_mk, K.differential_mk g]
    funext i
    exact (congrArg Q.toAlgHom (hd i g.1)).trans (he _)
  let a : ModuleCat.of C (RestrictedNaiveCotangentComplex.LiftedCotangent (P := P)) ≅
      ModuleCat.of C (Rig.CompletedNaiveCotangentComplex.LiftedCotangent (P := Q)) :=
    (ULift.moduleEquiv.trans (m.trans ULift.moduleEquiv.symm)).toModuleIso
  let d : ULift.{v} P.extension.Cotangent →ₗ[C] ULift.{u} (Fin P.variableCount → C) :=
    K.liftedDifferential
  let d' : ULift.{v} Q.extension.Cotangent →ₗ[C] ULift.{u} (Fin P.variableCount → C) :=
    L.liftedDifferential
  have hab : a.hom ≫ ModuleCat.ofHom d' = ModuleCat.ofHom d ≫ 𝟙 _ := by
    refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    show ULift.up (L.differential (m x.down)) = ULift.up (K.differential x.down)
    exact congrArg ULift.up (DFunLike.congr_fun hdm x.down)
  let E : K.cochainComplex ≅ L.cochainComplex :=
    doubleIso (ModuleCat.ofHom d) (ModuleCat.ofHom d') a (Iso.refl _) hab
  refine ⟨Q, ⟨{ ringEquiv := e, variableCount_eq := rfl
                commutes := AlgHom.ext he
                equiv := HomotopyEquiv.ofIso E
                conormal_mk := ?_, free_apply := ?_ }⟩⟩
  · intro g
    show (doubleMap (ModuleCat.ofHom d) (ModuleCat.ofHom d') a.hom (𝟙 _) hab).f (-1) _ = _
    simp only [doubleMap, mkHomFromDouble_f₀]
    show L.degreeNegOneIso.inv (a.hom
      (K.degreeNegOneIso.hom (K.degreeNegOneIso.inv (ULift.up _)))) = _
    rw [Iso.inv_hom_id_apply]
    show L.degreeNegOneIso.inv (ULift.up (m (Algebra.Extension.Cotangent.mk g))) = _
    rw [hm]
  · intro v
    show (doubleMap (ModuleCat.ofHom d) (ModuleCat.ofHom d') a.hom (𝟙 _) hab).f 0 _ = _
    simp only [doubleMap, mkHomFromDouble_f₁]
    show L.degreeZeroIso.inv (K.degreeZeroIso.hom
      (K.degreeZeroIso.inv (ULift.up v))) = _
    rw [Iso.inv_hom_id_apply]
    rfl


/-- **Stacks Project, Tag 0GBX.** For `A` an adic Noetherian topological ring, the completed
naive cotangent complex of Equation 0AJR is independent of the choice of the ideal of
definition `I ⊆ A`: both are the complex of Tag 0GBX, which is built from the topology of `A`
alone. -/
@[stacks 0GBX "independence of the ideal of definition", sga "6 0 4.4" "partial"]
public theorem nonempty_homotopyEquiv_of_idealOfDefinition
    {I I' : Ideal A}
    (hI : TopologicalRing.IsIdealOfDefinition I) (hIadic : _root_.IsAdic I)
    (hI' : TopologicalRing.IsIdealOfDefinition I') (hIadic' : _root_.IsAdic I')
    {C : Type v} [CommRing C] [Algebra A C] [TopologicalSpace C] [IsTopologicalRing C]
    [IsLinearTopology C C]
    (hc : IsAdicComplete (I.map (algebraMap A C)) C)
    [Algebra.FiniteType (A ⧸ I) (C ⧸ I.map (algebraMap A C))]
    (hc' : IsAdicComplete (I'.map (algebraMap A C)) C)
    [Algebra.FiniteType (A ⧸ I') (C ⧸ I'.map (algebraMap A C))]
    (P : RestrictedPowerSeriesPresentation A C)
    (Q : CompletedPolynomialPresentation I (AdicFiniteTypeAlgebra.of C hc))
    (Q' : CompletedPolynomialPresentation I' (AdicFiniteTypeAlgebra.of C hc')) :
    Nonempty (HomotopyEquiv
      (Rig.completedNaiveCotangentComplex (AdicFiniteTypeAlgebra.of C hc) Q).cochainComplex
      (Rig.completedNaiveCotangentComplex
        (AdicFiniteTypeAlgebra.of C hc') Q').cochainComplex) := by
  obtain ⟨Q₀, ⟨c₀⟩⟩ := exists_noetherianPresentationComparison hI hIadic hc P
  obtain ⟨Q₀', ⟨c₀'⟩⟩ := exists_noetherianPresentationComparison hI' hIadic' hc' P
  obtain ⟨e⟩ := completedNaiveCotangentComplex_homotopyEquiv I
    (AdicFiniteTypeAlgebra.of C hc) Q Q₀
  obtain ⟨e'⟩ := completedNaiveCotangentComplex_homotopyEquiv I'
    (AdicFiniteTypeAlgebra.of C hc') Q₀' Q'
  exact ⟨(e.trans c₀.equiv.symm).trans (c₀'.equiv.trans e')⟩

end Noetherian


end Rig

end
