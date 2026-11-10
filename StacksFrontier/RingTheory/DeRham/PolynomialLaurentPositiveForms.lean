module

public import StacksFrontier.RingTheory.DeRham.WeightComparison
public import StacksFrontier.RingTheory.DeRham.LaurentResidueTransport
public import StacksFrontier.AlgebraicGeometry.DeRham.DeRhamCohomology.FormsDirectSum

/-!
# The forms of a polynomial algebra vanishing at the origin

Let `R` be a ring and `E` an `R`-algebra. On the total space `Spec E[X]` of a trivial line bundle
over `Spec E`, with zero section `X = 0` and complement `Spec E[T;T⁻¹]`, the relative forms over
`R` which vanish on the zero section are exactly the forms of positive weight, and restriction to
the complement of the zero section identifies them with the forms of positive weight on
`E[T;T⁻¹]`. The same holds for algebras `C ≅ E[X]` and `D ≅ E[T;T⁻¹]` over `R`.

## Main results

* `PolynomialDeRham.isInternal_weightGrading`, `LaurentDeRham.isInternal_weightGrading`: the
  weight gradings of `E[X]` and of `E[T;T⁻¹]` are internal direct sum decompositions, hence so are
  the induced gradings of the forms ([Stacks, Tag 0FU9]).
* `PolynomialDeRham.formsₛₗ_evalZero_eq_zero_of_pos`: a form of positive weight vanishes on the
  zero section.
* `PolynomialDeRham.Chart.injective_formsₛₗ_restrict`, `PolynomialDeRham.Chart.mem_posForms` and
  `PolynomialDeRham.Chart.exists_of_mem_posForms`: for `C ≅ E[X]` and `D ≅ E[T;T⁻¹]`, restriction
  of forms along `C → D` is injective, and it carries the forms vanishing along the zero section
  `C → E` onto the forms of positive weight on `D`.

## References

* [Stacks Project, Tag 0FUH](https://stacks.math.columbia.edu/tag/0FUH)
* [Stacks Project, Tag 0FU9](https://stacks.math.columbia.edu/tag/0FU9)
-/

@[expose] public noncomputable section

open KaehlerDifferential Polynomial LaurentPolynomial
open scoped LaurentPolynomial

universe u

namespace KaehlerDifferential

variable {R B C : Type u} [CommRing R] [CommRing B] [CommRing C] [Algebra R B] [Algebra R C]
  [Algebra B C] [IsScalarTower R B C]

/-- **The transport of forms along a structure map is the map of Kähler forms of the algebra.** -/
theorem formsₛₗ_toAlgHom (p : ℕ) (x : ⋀[B]^p (Ω[B⁄R])) :
    formsₛₗ (IsScalarTower.toAlgHom R B C) p x = mapExteriorPower R B C p x := by
  have hmap : ∀ y : Ω[B⁄R], mapₛₗ (IsScalarTower.toAlgHom R B C) y = map R R B C y := by
    intro y
    have hy : y ∈ Submodule.span B (Set.range (D R B)) := by
      rw [span_range_derivation]; trivial
    induction hy using Submodule.span_induction with
    | mem z hz =>
        obtain ⟨b, rfl⟩ := hz
        rw [mapₛₗ_D, map_D]
        rfl
    | zero => rw [map_zero, map_zero]
    | add z w _ _ hz hw => rw [map_add, map_add, hz, hw]
    | smul b z _ hz =>
        rw [map_smulₛₗ, hz, LinearMap.map_smul_of_tower, ← algebraMap_smul C b]
        rfl
  have hx : x ∈ Submodule.span B (Set.range (exteriorPower.ιMulti B p)) := by
    rw [exteriorPower.ιMulti_span]; trivial
  induction hx using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨v, rfl⟩ := hz
      rw [formsₛₗ_ιMulti, mapExteriorPower_ιMulti]
      exact congrArg _ (funext fun i => hmap (v i))
  | zero => rw [map_zero, map_zero]
  | add z w _ _ hz hw => rw [map_add, map_add, hz, hw]
  | smul b z _ hz =>
      rw [map_smulₛₗ, hz, LinearMap.map_smul, ← algebraMap_smul C b]
      rfl

end KaehlerDifferential

/-! ### Internal decompositions -/

namespace PolynomialDeRham

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]

/-- The weight grading of `A[X]` is multiplicative. -/
instance gradedMonoid_weightGrading : SetLike.GradedMonoid (weightGrading R A) where
  one_mem := ⟨1, by simp⟩
  mul_mem := by
    rintro i j _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨a * b, by simp [monomial_mul_monomial]⟩

/-- **The weight grading of `A[X]` is an internal direct sum decomposition**: a polynomial is the
sum of its monomials, uniquely. -/
theorem isInternal_weightGrading : DirectSum.IsInternal (weightGrading R A) := by
  classical
  refine ⟨?_, fun q => ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro x hx
    refine DFinsupp.ext fun n => ?_
    obtain ⟨c, hc⟩ := (x n).2
    have hcoeff : ∀ k, coeff ((x k : A[X])) n = if k = n then c else 0 := by
      intro k
      obtain ⟨c', hc'⟩ := (x k).2
      by_cases hk : k = n
      · subst hk
        rw [ite_eq_left rfl, ← hc, coeff_monomial, ite_eq_left rfl]
      · rw [ite_eq_right hk, ← hc', coeff_monomial, ite_eq_right hk]
    have h := congrArg (fun q : A[X] => coeff q n) hx
    simp only [DirectSum.coeAddMonoidHom_eq_dfinsuppSum, coeff_zero] at h
    rw [DFinsupp.sum, finsetSum_coeff] at h
    simp only [hcoeff, Finset.sum_ite_eq'] at h
    have hc0 : c = 0 := by
      by_cases hn : n ∈ DFinsupp.support x
      · rwa [ite_eq_left hn] at h
      · rw [DFinsupp.notMem_support_iff] at hn
        have := congrArg (fun z : weightGrading R A n => coeff (z : A[X]) n) hn
        simp only [← hc, coeff_monomial, ZeroMemClass.coe_zero, coeff_zero] at this
        exact this
    exact Subtype.ext (by rw [← hc, hc0, map_zero]; rfl)
  · refine ⟨∑ n ∈ q.support, DirectSum.of (fun n => weightGrading R A n) n
      ⟨monomial n (q.coeff n), monomial_mem_weightGrading R A n _⟩, ?_⟩
    rw [map_sum]
    simp only [DirectSum.coeAddMonoidHom_of]
    exact q.as_sum_support.symm

/-- **The forms of `A[X]` are the internal direct sum of their weight components.** -/
theorem isInternal_weightComponent (p : ℕ) :
    DirectSum.IsInternal fun n => weightComponent R A n p :=
  isInternal_gradedDifferentialFormComponent (weightGrading R A) (isInternal_weightGrading R A) p

end PolynomialDeRham

namespace LaurentDeRham

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]

/-- The weight grading of `A[T;T⁻¹]` is multiplicative. -/
instance gradedMonoid_weightGrading : SetLike.GradedMonoid (weightGrading R A) where
  one_mem := SetLike.one_mem_graded (AddMonoidAlgebra.grade A : ℤ → Submodule A A[T;T⁻¹])
  mul_mem _ _ _ _ ha hb :=
    SetLike.mul_mem_graded (A := (AddMonoidAlgebra.grade A : ℤ → Submodule A A[T;T⁻¹])) ha hb

/-- **The weight grading of `A[T;T⁻¹]` is an internal direct sum decomposition.** -/
theorem isInternal_weightGrading : DirectSum.IsInternal (weightGrading R A) :=
  AddMonoidAlgebra.grade.isInternal (R := A) (ι := ℤ)

/-- **The forms of `A[T;T⁻¹]` are the internal direct sum of their weight components.** -/
theorem isInternal_weightComponent (p : ℕ) :
    DirectSum.IsInternal fun g => weightComponent R A g p :=
  isInternal_gradedDifferentialFormComponent (weightGrading R A) (isInternal_weightGrading R A) p

end LaurentDeRham

/-! ### Positive weight and the zero section -/

namespace PolynomialDeRham

variable {R E : Type u} [CommRing R] [CommRing E] [Algebra R E]

variable (R E) in
/-- The inclusion `E → E[X]` of the functions on the base. -/
abbrev inclAlg : E →ₐ[R] E[X] := IsScalarTower.toAlgHom R E E[X]

variable (R E) in
/-- The restriction `E[X] → E` to the zero section `X = 0`. -/
abbrev evalZeroAlg : E[X] →ₐ[R] E := (aeval (0 : E)).restrictScalars R

variable (R E) in
/-- The restriction `E[X] → E[T;T⁻¹]` to the complement of the zero section. -/
abbrev toLaurentR : E[X] →ₐ[R] E[T;T⁻¹] := IsScalarTower.toAlgHom R E[X] E[T;T⁻¹]

/-- Restricting a function on the base to `E[X]` and then to the zero section returns it. -/
theorem evalZeroAlg_comp_inclAlg : (evalZeroAlg R E).comp (inclAlg R E) = AlgHom.id R E := by
  ext a
  simp

/-- The composite `E → E[X] → E[T;T⁻¹]` is the inclusion `E → E[T;T⁻¹]`. -/
theorem toLaurentR_comp_inclAlg :
    (toLaurentR R E).comp (inclAlg R E) = IsScalarTower.toAlgHom R E E[T;T⁻¹] := by
  refine AlgHom.ext fun a => ?_
  change toLaurent (Polynomial.C a) = LaurentPolynomial.C a
  exact toLaurent_C a

/-- **A form of positive weight on `E[X]` vanishes on the zero section.** -/
theorem formsₛₗ_evalZero_eq_zero_of_pos {n p : ℕ} (hn : 0 < n) {x : ⋀[E[X]]^p (Ω[E[X]⁄R])}
    (hx : x ∈ weightComponent R E n p) : formsₛₗ (evalZeroAlg R E) p x = 0 := by
  have hle : weightComponent R E n p ≤ LinearMap.ker (formsₗ (evalZeroAlg R E) p) := by
    rw [weightComponent, gradedDifferentialFormComponent_le_iff]
    intro degree a hsum
    rw [LinearMap.mem_ker, formsₗ_apply, formsₛₗ_smul_ιMulti_D]
    obtain ⟨i, hi⟩ : ∃ i, 0 < degree i := by
      by_contra h
      push Not at h
      have : ∑ i, degree i = 0 := Finset.sum_eq_zero fun i _ => Nat.le_zero.1 (h i)
      omega
    have hev : evalZeroAlg R E (a i : E[X]) = 0 := by
      obtain ⟨c, hc⟩ := (a i).2
      change (aeval (0 : E)) (a i : E[X]) = 0
      rw [← hc]
      simp [zero_pow hi.ne']
    induction i using Fin.cases with
    | zero => rw [hev, zero_smul]
    | succ k =>
        rw [(exteriorPower.ιMulti E p).map_coord_zero k (by rw [hev, map_zero]), smul_zero]
  exact hle hx

/-- The weight-zero forms of `E[X]` are pulled back from `E`. -/
theorem exists_formsₛₗ_inclAlg_eq {p : ℕ} {x : ⋀[E[X]]^p (Ω[E[X]⁄R])}
    (hx : x ∈ weightComponent R E 0 p) : ∃ z, formsₛₗ (inclAlg R E) p z = x := by
  rw [weightComponent_zero_eq_range] at hx
  obtain ⟨z, rfl⟩ := hx
  exact ⟨z, formsₛₗ_toAlgHom p z⟩

/-- Every form on `E[X]` is a finite sum of forms of the weights `n ∈ s`. -/
theorem exists_sum_weightComponent (p : ℕ) (x : ⋀[E[X]]^p (Ω[E[X]⁄R])) :
    ∃ (s : Finset ℕ) (y : ℕ → ⋀[E[X]]^p (Ω[E[X]⁄R])),
      (∀ n, y n ∈ weightComponent R E n p) ∧ x = ∑ n ∈ s, y n := by
  classical
  obtain ⟨ξ, hξ⟩ := (isInternal_weightComponent R E p).2 x
  refine ⟨DFinsupp.support ξ, fun n => (ξ n : ⋀[E[X]]^p (Ω[E[X]⁄R])), fun n => (ξ n).2, ?_⟩
  rw [← hξ, DirectSum.coeAddMonoidHom_eq_dfinsuppSum]
  rfl

/-- Restricting a form of weight `n` on `E[X]` to `E[T;T⁻¹]` gives a form of weight `n`. -/
private theorem formsₛₗ_toLaurentR_mem_weightComponent (n p : ℕ) {x : ⋀[E[X]]^p (Ω[E[X]⁄R])}
    (hx : x ∈ weightComponent R E n p) :
    formsₛₗ (toLaurentR R E) p x ∈ LaurentDeRham.weightComponent R E (n : ℤ) p := by
  rcases n with _ | k
  · obtain ⟨z, rfl⟩ := exists_formsₛₗ_inclAlg_eq hx
    rw [formsₛₗ_comp, toLaurentR_comp_inclAlg, formsₛₗ_toAlgHom]
    exact LaurentDeRham.mapExteriorPower_mem_weightComponent R E p z
  · rw [← map_weightComponent_eq_laurentWeightComponent R E (k + 1) p (Nat.succ_pos k)]
    exact ⟨x, hx, (formsₛₗ_toAlgHom p _).symm⟩

/-! ### The local computation, transported -/

namespace Chart

variable {C D : Type u} [CommRing C] [CommRing D] [Algebra R C] [Algebra R D]
  (eP : E[X] ≃ₐ[R] C) (eL : E[T;T⁻¹] ≃ₐ[R] D) (ρ : C →ₐ[R] D) (ε : C →ₐ[R] E)

/-- **The forms of positive weight on `D ≅ E[T;T⁻¹]`**: the sum of the images of the weight-`n`
components, `n ≥ 1`, of the forms on `E[T;T⁻¹]`. -/
def posForms (p : ℕ) : Submodule R (⋀[D]^p (Ω[D⁄R])) :=
  ⨆ n : ℕ, (LaurentDeRham.weightComponent R E ((n + 1 : ℕ) : ℤ) p).map
    (formsₗ (eL : E[T;T⁻¹] →ₐ[R] D) p)

variable {eP eL ρ ε}

/-- If `ρ` corresponds to `E[X] → E[T;T⁻¹]` under `eP` and `eL`, then the pullback of a form along
`ρ` is the transport along `eL` of the restriction to `E[T;T⁻¹]` of its transport along `eP⁻¹`. -/
theorem formsₛₗ_restrict_eq (hρ : ρ.comp (eP : E[X] →ₐ[R] C) =
      (eL : E[T;T⁻¹] →ₐ[R] D).comp (toLaurentR R E)) (p : ℕ) (ω : ⋀[C]^p (Ω[C⁄R])) :
    formsₛₗ ρ p ω = formsₛₗ (eL : E[T;T⁻¹] →ₐ[R] D) p
      (formsₛₗ (toLaurentR R E) p (formsₛₗ (eP.symm : C →ₐ[R] E[X]) p ω)) := by
  rw [formsₛₗ_comp, ← hρ, ← formsₛₗ_comp, formsₛₗ_apply_symm]

/-- If `ε` corresponds to the zero section under `eP`, then the pullback of a form along `ε` is
the restriction to the zero section of its transport to `E[X]` along `eP⁻¹`. -/
theorem formsₛₗ_zero_eq (hε : ε.comp (eP : E[X] →ₐ[R] C) = evalZeroAlg R E) (p : ℕ)
    (ω : ⋀[C]^p (Ω[C⁄R])) :
    formsₛₗ ε p ω = formsₛₗ (evalZeroAlg R E) p (formsₛₗ (eP.symm : C →ₐ[R] E[X]) p ω) := by
  rw [← hε, ← formsₛₗ_comp, formsₛₗ_apply_symm]

/-- **A form on `C` vanishing on the zero section restricts to a form of positive weight on
`D`.** -/
theorem mem_posForms (hρ : ρ.comp (eP : E[X] →ₐ[R] C) =
      (eL : E[T;T⁻¹] →ₐ[R] D).comp (toLaurentR R E))
    (hε : ε.comp (eP : E[X] →ₐ[R] C) = evalZeroAlg R E) {p : ℕ} {ω : ⋀[C]^p (Ω[C⁄R])}
    (h : formsₛₗ ε p ω = 0) : formsₛₗ ρ p ω ∈ posForms eL p := by
  classical
  rw [formsₛₗ_restrict_eq hρ]
  rw [formsₛₗ_zero_eq hε] at h
  obtain ⟨s, y, hy, hx⟩ := exists_sum_weightComponent p (formsₛₗ (eP.symm : C →ₐ[R] E[X]) p ω)
  rw [hx] at h ⊢
  have hy0 (h0 : 0 ∈ s) : y 0 = 0 := by
    obtain ⟨z, hz⟩ := exists_formsₛₗ_inclAlg_eq (hy 0)
    rw [map_sum, Finset.sum_eq_single_of_mem 0 h0 fun n _ hn =>
      formsₛₗ_evalZero_eq_zero_of_pos (Nat.pos_of_ne_zero hn) (hy n), ← hz, formsₛₗ_comp,
      evalZeroAlg_comp_inclAlg, formsₛₗ_id] at h
    rw [← hz, h, map_zero]
  rw [map_sum, map_sum]
  refine Submodule.sum_mem _ fun n hn => ?_
  rcases n with _ | k
  · rw [hy0 hn, map_zero, map_zero]
    exact zero_mem _
  · exact Submodule.mem_iSup_of_mem k
      ⟨formsₛₗ (toLaurentR R E) p (y (k + 1)),
        formsₛₗ_toLaurentR_mem_weightComponent (k + 1) p (hy (k + 1)), rfl⟩

/-- **Every form of positive weight on `D` is the restriction of a form on `C` vanishing on the
zero section.** -/
theorem exists_of_mem_posForms (hρ : ρ.comp (eP : E[X] →ₐ[R] C) =
      (eL : E[T;T⁻¹] →ₐ[R] D).comp (toLaurentR R E))
    (hε : ε.comp (eP : E[X] →ₐ[R] C) = evalZeroAlg R E) {p : ℕ} {η : ⋀[D]^p (Ω[D⁄R])}
    (hη : η ∈ posForms eL p) : ∃ ω, formsₛₗ ε p ω = 0 ∧ formsₛₗ ρ p ω = η := by
  induction hη using Submodule.iSup_induction' with
  | mem k η hη =>
      obtain ⟨ζ, hζ, rfl⟩ := hη
      rw [← map_weightComponent_eq_laurentWeightComponent R E (k + 1) p (Nat.succ_pos k)] at hζ
      obtain ⟨ξ, hξ, rfl⟩ := hζ
      refine ⟨formsₛₗ (eP : E[X] →ₐ[R] C) p ξ, ?_, ?_⟩
      · rw [formsₛₗ_comp, hε]
        exact formsₛₗ_evalZero_eq_zero_of_pos (Nat.succ_pos k) hξ
      · rw [formsₛₗ_comp, hρ, ← formsₛₗ_comp, formsₗ_apply]
        exact congrArg _ (formsₛₗ_toAlgHom p ξ)
  | zero => exact ⟨0, map_zero _, map_zero _⟩
  | add η η' _ _ h h' =>
      obtain ⟨ω, hω, rfl⟩ := h
      obtain ⟨ω', hω', rfl⟩ := h'
      exact ⟨ω + ω', by rw [map_add, hω, hω', add_zero], map_add _ _ _⟩

/-- **Restriction of forms along `C → D` is injective.** -/
theorem injective_formsₛₗ_restrict (hρ : ρ.comp (eP : E[X] →ₐ[R] C) =
      (eL : E[T;T⁻¹] →ₐ[R] D).comp (toLaurentR R E)) (p : ℕ) :
    Function.Injective (formsₛₗ ρ p) := by
  classical
  rw [injective_iff_map_eq_zero]
  intro ω hω
  rw [formsₛₗ_restrict_eq hρ, ← map_zero (formsₛₗ (eL : E[T;T⁻¹] →ₐ[R] D) p)] at hω
  replace hω := formsₛₗ_injective eL p hω
  obtain ⟨s, y, hy, hx⟩ := exists_sum_weightComponent p (formsₛₗ (eP.symm : C →ₐ[R] E[X]) p ω)
  rw [hx, map_sum] at hω
  have hind := (iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero _).1
    (LaurentDeRham.isInternal_weightComponent R E p).submodule_iSupIndep
    (s.map Nat.castEmbedding) (fun g => formsₛₗ (toLaurentR R E) p (y g.toNat))
    (fun g hg => by
      obtain ⟨n, -, rfl⟩ := Finset.mem_map.1 hg
      simpa using formsₛₗ_toLaurentR_mem_weightComponent n p (hy n))
    (by simpa using hω)
  have hzero : ∀ n ∈ s, y n = 0 := by
    intro n hn
    have h := hind (n : ℤ) (Finset.mem_map.2 ⟨n, hn, rfl⟩)
    simp only [Int.toNat_natCast] at h
    rcases n with _ | k
    · obtain ⟨z, hz⟩ := exists_formsₛₗ_inclAlg_eq (hy 0)
      rw [← hz, formsₛₗ_comp, toLaurentR_comp_inclAlg, formsₛₗ_toAlgHom,
        ← LaurentDeRham.weightPullback_zero_apply] at h
      rw [← hz, LaurentDeRham.eq_zero_of_weightPullback_eq_zero R E 0 p h, map_zero]
    · refine eq_zero_of_mem_weightComponent_of_mapExteriorPower_eq_zero R E (k + 1) p (hy _) ?_
      rwa [← formsₛₗ_toAlgHom]
  rw [← formsₛₗ_apply_symm eP p ω, hx, Finset.sum_eq_zero hzero, map_zero]

end Chart

end PolynomialDeRham

end
