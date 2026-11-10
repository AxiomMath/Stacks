module

public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.Localization.Basic
public import Mathlib.RingTheory.Localization.Finiteness
public import Mathlib.RingTheory.Localization.Integer
public import Mathlib.RingTheory.MvPolynomial.Localization
public import Mathlib.RingTheory.Smooth.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Smoothing.BaseChangeOfPresentation
public import StacksFrontier.RingTheory.Smoothing.SpreadingOutResolutions
public import StacksFrontier.RingTheory.Smoothing.StandardSmoothPresentation
public import StacksFrontier.RingTheory.Smoothing.StandardSmoothRetract

/-!
# Clearing denominators and rescaling variables for a delocalized smooth factorization

Auxiliary lemmas for `Stacks.Smoothing.exists_factorization_isElementaryStandard` (Stacks 07F4):
the tail index of a presentation and the second standard condition, clearing denominators from
memberships, vanishing and elements over a localization, diagonal rescaling of polynomial
variables, the determinant convention for the pre-submersive Jacobian, and the kernel of
evaluation at constants.
-/

@[expose] public section

namespace Stacks.Smoothing

def presentationTailIndex {m c : ℕ} (hcm : c ≤ m)
    (j : Fin (m - c)) : Fin m :=
  Fin.cast (by omega : c + (m - c) = m) (Fin.natAdd c j)

private theorem presentationTailIndex_eq_mk {m c : ℕ} (hcm : c ≤ m)
    (j : Fin (m - c)) :
    presentationTailIndex hcm j = ⟨c + j.1, by omega⟩ := by
  apply Fin.ext
  simp [presentationTailIndex]

theorem standardCond2_of_mul_mem
    {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (P : Presentation R A) (a : A) (c : ℕ) (hcm : c ≤ P.m)
    (p₀ : MvPolynomial (Fin P.n) R) (hp₀ : P.IsLift a p₀)
    (hmul : ∀ j : Fin (P.m - c),
      p₀ * P.f (presentationTailIndex hcm j) ∈
        P.firstRelIdeal c hcm + P.relIdeal ^ 2) :
    P.StandardCond2 a c hcm := by
  intro j p hp
  rw [← presentationTailIndex_eq_mk hcm j]
  have hmk : Ideal.Quotient.mk (P.relIdeal) p =
      Ideal.Quotient.mk (P.relIdeal) p₀ := by
    have h := P.iso.symm.injective (by simpa [Presentation.lift] using hp.trans hp₀.symm)
    change Ideal.Quotient.mk (Ideal.span (Set.range P.f)) p =
      Ideal.Quotient.mk (Ideal.span (Set.range P.f)) p₀
    simpa only [Ideal.Quotient.mkₐ_eq_mk] using h
  have hdiff : p - p₀ ∈ P.relIdeal := Ideal.Quotient.eq.mp hmk
  have htail : P.f (presentationTailIndex hcm j) ∈ P.relIdeal :=
    Ideal.subset_span ⟨presentationTailIndex hcm j, rfl⟩
  have hprod : (p - p₀) * P.f (presentationTailIndex hcm j) ∈ P.relIdeal ^ 2 := by
    rw [pow_two]
    exact Ideal.mul_mem_mul hdiff htail
  rw [show p * P.f (presentationTailIndex hcm j) = p₀ * P.f (presentationTailIndex hcm j) +
    (p - p₀) * P.f (presentationTailIndex hcm j) by ring]
  exact Ideal.add_mem _ (hmul j) (by rw [Ideal.add_eq_sup]; exact Submodule.mem_sup_right hprod)

/-- Clear denominators from a membership in a finitely generated ideal of a
localized polynomial ring.  The extra multiplier in the conclusion accounts
for possible `S`-torsion in the coefficient ring. -/
theorem exists_localization_multiple_mem_span
    {R Rₛ : Type*} [CommRing R] [CommRing Rₛ] (S : Submonoid R)
    [Algebra R Rₛ] [IsLocalization S Rₛ]
    {n m : ℕ} (f : Fin m → MvPolynomial (Fin n) R)
    (p : MvPolynomial (Fin n) R)
    (hp : MvPolynomial.map (algebraMap R Rₛ) p ∈
      Ideal.span (Set.range (fun i => MvPolynomial.map (algebraMap R Rₛ) (f i)))) :
    ∃ s : S, MvPolynomial.C (s : R) * p ∈ Ideal.span (Set.range f) := by
  classical
  let P := MvPolynomial (Fin n) R
  let Pₛ := MvPolynomial (Fin n) Rₛ
  let : Algebra P Pₛ :=
    MvPolynomial.algebraMvPolynomial (σ := Fin n)
  let : IsLocalization (S.map MvPolynomial.C) Pₛ :=
    MvPolynomial.isLocalization S Rₛ
  have hp' : MvPolynomial.map (algebraMap R Rₛ) p ∈
      Submodule.span Pₛ (Set.range (fun i =>
        MvPolynomial.map (algebraMap R Rₛ) (f i))) := hp
  obtain ⟨s, hs⟩ := multiple_mem_span_of_mem_localization_span
    (R := MvPolynomial (Fin n) R)
    (M := S.map MvPolynomial.C) (R' := Pₛ) (N := Pₛ)
    (s := Set.range (fun i => MvPolynomial.map (algebraMap R Rₛ) (f i)))
    (x := MvPolynomial.map (algebraMap R Rₛ) p) hp'
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun P).mp hs
  let q : MvPolynomial (Fin n) R := ∑ i, a i * f i
  have hmap (x : P) : MvPolynomial.map (algebraMap R Rₛ) x = algebraMap P Pₛ x := by
    rw [MvPolynomial.algebraMap_def]
  have hq : algebraMap P Pₛ q = algebraMap P Pₛ (s : P) * algebraMap P Pₛ p := by
    calc
      algebraMap P Pₛ q = ∑ i, algebraMap P Pₛ (a i) * algebraMap P Pₛ (f i) := by
        simp [q]
      _ = ∑ i, a i • MvPolynomial.map (algebraMap R Rₛ) (f i) :=
        Finset.sum_congr rfl fun _ _ => rfl
      _ = (s : P) • MvPolynomial.map (algebraMap R Rₛ) p := ha
      _ = algebraMap P Pₛ (s : P) * algebraMap P Pₛ p := by
        simp [Algebra.smul_def, hmap]
  obtain ⟨s₀, hs₀, hsval⟩ := (Submonoid.mem_map.mp s.2)
  have hzero : algebraMap P Pₛ (MvPolynomial.C (s₀ : R) * p - q) = 0 := by
    have hcoef : algebraMap P Pₛ (MvPolynomial.C (s₀ : R)) =
        algebraMap P Pₛ (s : P) := congrArg (algebraMap P Pₛ) hsval
    rw [map_sub, map_mul, hq, hcoef]
    ring
  obtain ⟨t, ht⟩ :=
    (IsLocalization.map_eq_zero_iff (S.map MvPolynomial.C) Pₛ _).mp hzero
  obtain ⟨t₀, ht₀, htT⟩ := Submonoid.mem_map.mp t.2
  have hmulzero : MvPolynomial.C (t₀ : R) *
      (MvPolynomial.C (s₀ : R) * p - q) = 0 := by
    simpa [htT] using ht
  have hrewrite : MvPolynomial.C ((t₀ : R) * (s₀ : R)) * p =
      MvPolynomial.C (t₀ : R) * q := by
    rw [map_mul]
    linear_combination hmulzero
  refine ⟨⟨t₀, ht₀⟩ * ⟨s₀, hs₀⟩, ?_⟩
  change MvPolynomial.C (t₀ * s₀) * p ∈ Ideal.span (Set.range f)
  rw [hrewrite]
  apply Ideal.mul_mem_left
  change (∑ i : Fin m, a i * f i) ∈ Ideal.span (Set.range f)
  exact Ideal.sum_mem _ fun i hi =>
    Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)

/-- Clear the denominators in a finite family of ideal memberships at once. -/
theorem exists_localization_multiple_mem_span_family
    {R Rₛ : Type*} [CommRing R] [CommRing Rₛ] (S : Submonoid R)
    [Algebra R Rₛ] [IsLocalization S Rₛ]
    {n k : ℕ} (f : Fin k → MvPolynomial (Fin n) R)
    {m : ℕ} (p : Fin m → MvPolynomial (Fin n) R)
    (hp : ∀ i, MvPolynomial.map (algebraMap R Rₛ) (p i) ∈
      Ideal.span (Set.range (fun j => MvPolynomial.map (algebraMap R Rₛ) (f j)))) :
    ∃ s : S, ∀ i, MvPolynomial.C (s : R) * p i ∈ Ideal.span (Set.range f) := by
  classical
  choose s hs using fun i : Fin m =>
    exists_localization_multiple_mem_span S f (p i) (hp i)
  let t : S := ⟨∏ i : Fin m, (s i : R),
    S.prod_mem (fun i hi => (s i).property)⟩
  refine ⟨t, ?_⟩
  intro i
  let u : R := ∏ j ∈ Finset.univ.erase i, (s j : R)
  have hprod : (t : R) = (s i : R) * u := by
    dsimp [t, u]
    rw [← Finset.prod_erase_mul Finset.univ (fun j : Fin m => (s j : R))
      (Finset.mem_univ i)]
    ring
  have hfactor : MvPolynomial.C (t : R) * p i =
      MvPolynomial.C (u) * (MvPolynomial.C (s i : R) * p i) := by
    rw [hprod, map_mul]
    ring
  rw [hfactor]
  exact Ideal.mul_mem_left _ _ (hs i)

/-- If an element dies after localizing a target algebra, some denominator from
the base already annihilates it in the original target. -/
theorem exists_localization_multiple_eq_zero
    {R T Tₛ : Type*} [CommRing R] [CommRing T] [CommRing Tₛ]
    (S : Submonoid R) [Algebra R T] [Algebra T Tₛ]
    [IsLocalization (S.map (algebraMap R T)) Tₛ]
    (x : T) (hx : algebraMap T Tₛ x = 0) :
    ∃ s : S, algebraMap R T (s : R) * x = 0 := by
  obtain ⟨u, hu⟩ :=
    (IsLocalization.map_eq_zero_iff (S.map (algebraMap R T)) Tₛ x).mp hx
  obtain ⟨s, hs, hsu⟩ := Submonoid.mem_map.mp u.2
  refine ⟨⟨s, hs⟩, ?_⟩
  simpa [hsu] using hu

/-- Clear a denominator in a localized element of the target algebra. -/
theorem exists_localization_multiple_target
    {R Λ Λₛ : Type*} [CommRing R] [CommRing Λ] [CommRing Λₛ]
    (S : Submonoid R) [Algebra R Λ] [Algebra R Λₛ] [Algebra Λ Λₛ]
    [IsScalarTower R Λ Λₛ] [IsLocalization (S.map (algebraMap R Λ)) Λₛ]
    (x : Λₛ) :
    ∃ s : S, ∃ a : Λ, algebraMap Λ Λₛ a = algebraMap R Λₛ (s : R) * x := by
  obtain ⟨t, ht⟩ := IsLocalization.exists_integer_multiple
    (S.map (algebraMap R Λ)) (S := Λₛ) x
  change ∃ a : Λ, algebraMap Λ Λₛ a = (t : Λ) • x at ht
  obtain ⟨a, ha⟩ := ht
  obtain ⟨s, hs, hst⟩ := Submonoid.mem_map.mp t.2
  have ha' : algebraMap Λ Λₛ a = algebraMap Λ Λₛ (t : Λ) * x := by
    simpa [Algebra.smul_def] using ha
  refine ⟨⟨s, hs⟩, a, ?_⟩
  calc
    algebraMap Λ Λₛ a = algebraMap Λ Λₛ (t : Λ) * x := ha'
    _ = algebraMap Λ Λₛ (algebraMap R Λ s) * x := by rw [hst]
    _ = algebraMap R Λₛ s * x := by
      rw [IsScalarTower.algebraMap_apply R Λ Λₛ s]

/-- Partial derivatives commute with diagonal rescaling of polynomial variables. -/
theorem pderiv_aeval_diagonal
    {R : Type*} [CommRing R] {n : ℕ} (d : Fin n → R)
    (p : MvPolynomial (Fin n) R) (i : Fin n) :
    MvPolynomial.pderiv i
        (MvPolynomial.aeval (fun j => MvPolynomial.C (d j) * MvPolynomial.X j) p) =
      MvPolynomial.C (d i) *
        MvPolynomial.aeval (fun j => MvPolynomial.C (d j) * MvPolynomial.X j)
          (MvPolynomial.pderiv i p) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq =>
      simp only [map_add, hp, hq]
      ring
  | mul_X p j hp =>
      simp only [map_mul, MvPolynomial.aeval_X, MvPolynomial.pderiv_mul,
        hp, MvPolynomial.pderiv_X]
      by_cases hij : i = j <;> simp [hij] <;> ring

/-- Scaling each polynomial variable by a unit is an algebra equivalence. -/
noncomputable def diagonalScaleEquiv
    {R : Type*} [CommRing R] {n : ℕ} (d : Fin n → Rˣ) :
    MvPolynomial (Fin n) R ≃ₐ[R] MvPolynomial (Fin n) R := by
  let φ : MvPolynomial (Fin n) R →ₐ[R] MvPolynomial (Fin n) R :=
    MvPolynomial.aeval (fun i => MvPolynomial.C (d i : R) * MvPolynomial.X i)
  let ψ : MvPolynomial (Fin n) R →ₐ[R] MvPolynomial (Fin n) R :=
    MvPolynomial.aeval (fun i => MvPolynomial.C (((d i)⁻¹ : Rˣ) : R) * MvPolynomial.X i)
  have hφψ : φ.comp ψ = AlgHom.id R _ := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [φ, ψ, AlgHom.comp_apply, MvPolynomial.aeval_X, map_mul,
      MvPolynomial.aeval_C, MvPolynomial.aeval_X]
    rw [← mul_assoc, MvPolynomial.algebraMap_eq, ← map_mul]
    simp
  have hψφ : ψ.comp φ = AlgHom.id R _ := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [φ, ψ, AlgHom.comp_apply, MvPolynomial.aeval_X, map_mul,
      MvPolynomial.aeval_C, MvPolynomial.aeval_X]
    rw [← mul_assoc, MvPolynomial.algebraMap_eq, ← map_mul]
    simp
  exact AlgEquiv.ofAlgHom φ ψ hφψ hψφ

theorem diagonalScaleEquiv_symm_X
    {R : Type*} [CommRing R] {n : ℕ} (d : Fin n → Rˣ) (i : Fin n) :
    (diagonalScaleEquiv d).symm (MvPolynomial.X i) =
      MvPolynomial.C (((d i)⁻¹ : Rˣ) : R) * MvPolynomial.X i := by
  simp [diagonalScaleEquiv]

/-- A polynomial relation remains generated by the correspondingly rescaled
relations after an invertible diagonal change of variables. -/
theorem diagonalScale_mem_span
    {R : Type*} [CommRing R] {n k : ℕ} (d : Fin n → Rˣ)
    (f : Fin k → MvPolynomial (Fin n) R) (p : MvPolynomial (Fin n) R)
    (hp : p ∈ Ideal.span (Set.range f)) :
    (diagonalScaleEquiv d).symm p ∈
      Ideal.span (Set.range (fun i => (diagonalScaleEquiv d).symm (f i))) := by
  have hm : (diagonalScaleEquiv d).symm p ∈
      Ideal.map (diagonalScaleEquiv d).symm.toRingHom (Ideal.span (Set.range f)) :=
    (Ideal.mem_map_iff_of_surjective _ (diagonalScaleEquiv d).symm.surjective).2
      ⟨p, hp, rfl⟩
  rw [Ideal.map_span] at hm
  have hrange : (diagonalScaleEquiv d).symm.toRingHom '' Set.range f =
      Set.range (fun i => (diagonalScaleEquiv d).symm (f i)) := by
    ext x
    constructor
    · rintro ⟨y, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨f i, ⟨i, rfl⟩, rfl⟩
  rw [hrange] at hm
  exact hm

/-- Evaluating a diagonally rescaled polynomial at the correspondingly scaled
variables recovers its original value. -/
theorem aeval_diagonalScale_symm
    {R T : Type*} [CommRing R] [CommRing T] [Algebra R T] {n : ℕ}
    (d : Fin n → Rˣ) (x : Fin n → T) (p : MvPolynomial (Fin n) R) :
    MvPolynomial.aeval (fun i => algebraMap R T (d i : R) * x i)
      ((diagonalScaleEquiv d).symm p) = MvPolynomial.aeval x p := by
  let e := diagonalScaleEquiv d
  have heq : (MvPolynomial.aeval (fun i => algebraMap R T (d i : R) * x i)).comp
      (e.symm.toAlgHom) = MvPolynomial.aeval x := by
    apply MvPolynomial.algHom_ext
    intro i
    rw [AlgHom.comp_apply]
    have hX : e.symm (MvPolynomial.X i) =
        MvPolynomial.C (((d i)⁻¹ : Rˣ) : R) * MvPolynomial.X i := by
      simpa [e] using diagonalScaleEquiv_symm_X d i
    change (MvPolynomial.aeval (fun j => algebraMap R T (d j : R) * x j))
      (e.symm (MvPolynomial.X i)) = MvPolynomial.aeval x (MvPolynomial.X i)
    rw [hX, map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_X]
    rw [← mul_assoc, ← map_mul]
    simp
  exact DFunLike.congr_fun heq p

/-- The pre-submersive Jacobian agrees with the determinant convention used by
the Stacks presentation API when the relation variables are the initial ones. -/
theorem preSub_jacobian_eq_aeval_jacobianDet
    {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    {n c : ℕ} (hcn : c ≤ n)
    (P : Algebra.PreSubmersivePresentation R A (Fin n) (Fin c))
    (hmap : P.map = Fin.castLE hcn) :
    P.jacobian = MvPolynomial.aeval P.toGenerators.val
      (jacobianDet hcn P.relation) := by
  classical
  rw [P.jacobian_eq_jacobiMatrix_det]
  have hmat : P.jacobiMatrix =
      (fun i j : Fin c => MvPolynomial.pderiv (Fin.castLE hcn i) (P.relation j)) := by
    ext i j
    rw [Algebra.PreSubmersivePresentation.jacobiMatrix_apply, hmap]
  rw [hmat, jacobianDet, P.toGenerators.algebraMap_apply]

/-- Clear the coefficients of a polynomial over a localization by a single
element of the original multiplicative set. -/
theorem exists_localization_multiple_polynomial_lift
    {R Rₛ : Type*} [CommRing R] [CommRing Rₛ] (S : Submonoid R)
    [Algebra R Rₛ] [IsLocalization S Rₛ]
    {n : ℕ} (p : MvPolynomial (Fin n) Rₛ) :
    ∃ s : S, ∃ q : MvPolynomial (Fin n) R,
      MvPolynomial.map (algebraMap R Rₛ) q =
        MvPolynomial.C (algebraMap R Rₛ (s : R)) * p := by
  classical
  let P := MvPolynomial (Fin n) R
  let Pₛ := MvPolynomial (Fin n) Rₛ
  let T : Submonoid P := S.map (MvPolynomial.C : R →+* P)
  let : Algebra P Pₛ := MvPolynomial.algebraMvPolynomial (σ := Fin n)
  let : IsLocalization T Pₛ :=
    MvPolynomial.isLocalization S Rₛ
  obtain ⟨t, ht⟩ := IsLocalization.exists_integer_multiple
    T (S := Pₛ) p
  change ∃ q : P, algebraMap P Pₛ q = (t : P) • p at ht
  obtain ⟨q, hq⟩ := ht
  obtain ⟨s, hs, hst⟩ := Submonoid.mem_map.mp t.2
  refine ⟨⟨s, hs⟩, q, ?_⟩
  calc
    MvPolynomial.map (algebraMap R Rₛ) q = algebraMap P Pₛ q := by
      rw [MvPolynomial.algebraMap_def]
    _ = algebraMap P Pₛ (t : P) * p := by
      simpa [Algebra.smul_def] using hq
    _ = MvPolynomial.C (algebraMap R Rₛ s) * p := by
      rw [← hst]
      rw [MvPolynomial.algebraMap_def, MvPolynomial.map_C]

/-- The kernel of evaluation at a finite family of constants is generated by the
differences between the variables and those constants. -/
theorem kernel_aeval_constants
    {A : Type*} [CommRing A] {n : ℕ} (v : Fin n → A) :
    RingHom.ker (MvPolynomial.aeval (R := A) (S₁ := A) v).toRingHom =
      Ideal.span (Set.range (fun i : Fin n =>
        (MvPolynomial.X i - MvPolynomial.C (v i) : MvPolynomial (Fin n) A))) := by
  classical
  apply le_antisymm
  · intro p hp
    have hcongr : p - MvPolynomial.aeval (fun i =>
        (MvPolynomial.C (v i) : MvPolynomial (Fin n) A)) p ∈
        Ideal.span (Set.range (fun i : Fin n =>
          (MvPolynomial.X i - MvPolynomial.C (v i) : MvPolynomial (Fin n) A))) :=
      sub_aeval_mem_span_X_sub (fun i =>
        (MvPolynomial.C (v i) : MvPolynomial (Fin n) A)) p
    let cAlg : A →ₐ[A] MvPolynomial (Fin n) A := {
      toRingHom := MvPolynomial.C
      commutes' := fun a => rfl }
    have hevalMap : MvPolynomial.aeval (R := A) (S₁ := MvPolynomial (Fin n) A)
        (fun i => MvPolynomial.C (v i)) =
        cAlg.comp (MvPolynomial.aeval (R := A) (S₁ := A) v) := by
      apply MvPolynomial.algHom_ext
      intro i
      simp only [MvPolynomial.aeval_X, AlgHom.comp_apply]
      rfl
    have heval : MvPolynomial.aeval (R := A) (S₁ := MvPolynomial (Fin n) A)
        (fun i => MvPolynomial.C (v i)) p =
        MvPolynomial.C ((MvPolynomial.aeval (R := A) (S₁ := A) v) p) :=
      calc
        _ = cAlg ((MvPolynomial.aeval (R := A) (S₁ := A) v) p) :=
          congrArg (fun f => f p) hevalMap
        _ = MvPolynomial.C ((MvPolynomial.aeval (R := A) (S₁ := A) v) p) := rfl
    have hp0 : (MvPolynomial.aeval (R := A) (S₁ := A) v) p = 0 :=
      RingHom.mem_ker.mp hp
    change p - MvPolynomial.aeval (fun i =>
      (MvPolynomial.C (v i) : MvPolynomial (Fin n) A)) p ∈ _ at hcongr
    rw [heval, hp0] at hcongr
    simpa using hcongr
  · apply Ideal.span_le.mpr
    rintro p ⟨i, rfl⟩
    change (MvPolynomial.aeval (R := A) (S₁ := A) v)
      (MvPolynomial.X i - MvPolynomial.C (v i)) = 0
    simp

end Stacks.Smoothing
