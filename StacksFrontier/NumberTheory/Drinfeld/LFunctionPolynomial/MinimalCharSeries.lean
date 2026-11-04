module

public import StacksFrontier.CategoryTheory.FilteredDerived.Perfectness.CharSeries
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CharpolyTracePowers

/-!
# The characteristic series of an invertible endomorphism of a minimal complex

Let `A` be a local ring with maximal ideal `𝔪` and `F` a bounded complex of finite projective (so
free) `A`-modules which is *minimal*: every differential has image in `𝔪 F`. Let `φ` be an
endomorphism of `F` with a homotopy inverse `ψ`, for instance a representative of an automorphism
of `F` in the derived category. Write `rᵢ` for the rank of `Fⁱ`. Then

  `det(1 - φ T | F)⁻¹ = ∏_{i odd} det(1 - φᵢ T | Fⁱ) / ∏_{i even} det(1 - φᵢ T | Fⁱ)`

is a quotient `P / Q` of polynomials of degrees at most `a = ∑_{i odd} rᵢ` and `b = ∑_{i even} rᵢ`
whose coefficients in degrees `a` and `b` are units. Each `det(1 - φᵢ T)` is the reversed
characteristic polynomial of `φᵢ`, of degree `≤ rᵢ` with coefficient `(-1)^{rᵢ} det φᵢ` in degree
`rᵢ`. And `det φᵢ` is a unit: the homotopy `ψ φ - 1 = d h + h d` has image in `𝔪 F`, because `F`
is minimal, so `det(ψᵢ φᵢ) ≡ 1` modulo `𝔪`.

This is the input that `Stacks.Drinfeld.HasRationalApprox` needs from the cohomological
interpretation of an L-function at a finite level: there `F` is a minimal model of
`RΓ_c(X_k̄, ℱ)` over `Λ/𝔪ⁿ` and `φ` represents the geometric Frobenius, and `a - b` is
`-χ(X_k̄, ℱ ⊗ Λ/𝔪)`.

## Main results

* `Stacks.Drinfeld.exists_polynomial_eq_charSeries`: `det(1 - g T)` on a free module of rank `r`
  is a polynomial of degree `≤ r` with coefficient `(-1)^r det g` in degree `r`.
* `Stacks.Drinfeld.isUnit_det_of_sub_mem_smul_top`: an endomorphism congruent to the identity
  modulo `𝔪` has unit determinant.
* `Stacks.Drinfeld.isUnit_det_of_homotopy`: on a minimal complex, an endomorphism with a homotopy
  inverse has unit determinant in every degree.
* `Stacks.Drinfeld.exists_polynomial_mul_inv_alternatingCharSeries`: the quotient `P / Q`
  above.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Polynomial PowerSeries Finset
open Stacks.EtaleCohomology

universe v

namespace Stacks.Drinfeld

section Module

variable {Λ : Type*} [CommRing Λ] {M : Type*} [AddCommGroup M] [Module Λ M]

/-- **`det(1 - g T)` on a free module of rank `r` is a polynomial of degree `≤ r` with
coefficient `(-1)^r det g` in degree `r`**: the reversed characteristic polynomial of the matrix
of `g`. -/
theorem exists_polynomial_eq_charSeries [Nontrivial Λ] [Module.Finite Λ M] [Module.Projective Λ M]
    {r : ℕ}
    (b : Module.Basis (Fin r) Λ M) (g : M →ₗ[Λ] M) :
    ∃ P : Λ[X], (P : Λ⟦X⟧) = ProjectiveDeterminant.charSeries g 1 ∧ P.natDegree ≤ r ∧
      P.coeff r = (-1) ^ r * LinearMap.det g := by
  classical
  set A := LinearMap.toMatrix b b g
  refine ⟨A.charpolyRev, ?_, ?_, ?_⟩
  · rw [ProjectiveDeterminant.charSeries_eq_det_matrix b, ← localCharPolynomial_one_eq_charpolyRev,
      coe_localCharPolynomial]
    rfl
  · rw [← localCharPolynomial_one_eq_charpolyRev]
    simpa using natDegree_localCharPolynomial_le A 1
  · rw [← Matrix.reverse_charpoly, Polynomial.coeff_reverse, Matrix.charpoly_natDegree_eq_dim,
      Fintype.card_fin, Polynomial.revAt_le le_rfl, Nat.sub_self, ← LinearMap.det_toMatrix b,
      Matrix.det_eq_sign_charpoly_coeff, Fintype.card_fin, ← mul_assoc,
      ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul]

/-- The coordinates of an element of `I • M` in a basis lie in `I`. -/
theorem repr_mem_of_mem_smul_top {I : Ideal Λ} {ι : Type*} (b : Module.Basis ι Λ M) {y : M}
    (hy : y ∈ I • (⊤ : Submodule Λ M)) (i : ι) : b.repr y i ∈ I := by
  refine Submodule.smul_induction_on hy (fun r hr m _ => ?_) (fun x y hx hy => ?_)
  · rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
    exact I.mul_mem_right _ hr
  · rw [map_add, Finsupp.add_apply]
    exact I.add_mem hx hy

/-- A linear map sends `I • M` into `I • N`. -/
theorem map_mem_smul_top {N : Type*} [AddCommGroup N] [Module Λ N] {I : Ideal Λ}
    (f : M →ₗ[Λ] N) {y : M} (hy : y ∈ I • (⊤ : Submodule Λ M)) :
    f y ∈ I • (⊤ : Submodule Λ N) := by
  refine Submodule.smul_induction_on hy (fun r hr m _ => ?_) (fun x y hx hy => ?_)
  · rw [map_smul]
    exact Submodule.smul_mem_smul hr trivial
  · rw [map_add]
    exact Submodule.add_mem _ hx hy

/-- **An endomorphism congruent to the identity modulo the maximal ideal has unit
determinant.** Its matrix reduces to the identity matrix over the residue field. -/
theorem isUnit_det_of_sub_mem_smul_top [IsLocalRing Λ] {r : ℕ} (b : Module.Basis (Fin r) Λ M)
    (g : M →ₗ[Λ] M)
    (hg : ∀ x, g x - x ∈ (IsLocalRing.maximalIdeal Λ) • (⊤ : Submodule Λ M)) :
    IsUnit (LinearMap.det g) := by
  classical
  rw [← LinearMap.det_toMatrix b, ← IsLocalRing.notMem_maximalIdeal]
  intro hmem
  let π := Ideal.Quotient.mk (IsLocalRing.maximalIdeal Λ)
  have hmat : π.mapMatrix (LinearMap.toMatrix b b g) = 1 := by
    ext i j
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, LinearMap.toMatrix_apply]
    have hsub := repr_mem_of_mem_smul_top b (hg (b j)) i
    rw [map_sub, Finsupp.sub_apply, Module.Basis.repr_self, ← Ideal.Quotient.eq] at hsub
    rw [hsub, Finsupp.single_apply, Matrix.one_apply]
    obtain rfl | h := eq_or_ne i j
    · simp
    · simp [h, Ne.symm h]
  have h1 : π (LinearMap.toMatrix b b g).det = 1 := by
    rw [RingHom.map_det, hmat, Matrix.det_one]
  rw [Ideal.Quotient.eq_zero_iff_mem.2 hmem] at h1
  exact zero_ne_one h1

end Module

section Complex

variable {A : Type*} [CommRing A] [IsLocalRing A]

/-- A finite projective module over a local ring has a finite basis. -/
theorem nonempty_basis_of_projective (M : Type*) [AddCommGroup M] [Module A M] [Module.Finite A M]
    [Module.Projective A M] : Nonempty (Module.Basis (Fin (Module.finrank A M)) A M) := by
  have : Module.Free A M := Module.free_of_flat_of_isLocalRing
  exact ⟨Module.finBasis A M⟩

/-- **On a minimal complex, an endomorphism with a homotopy inverse has unit determinant in every
degree.** If `ψ φ - 1 = d h + h d` and every differential of `F` has image in `𝔪 F`, then
`ψᵢ φᵢ ≡ 1` modulo `𝔪`, so `det(ψᵢ) det(φᵢ)` is a unit. -/
theorem isUnit_det_of_homotopy (F : CochainComplex (ModuleCat.{v} A) ℤ)
    (hmin : ∀ i j, LinearMap.range (F.d i j).hom ≤
      (IsLocalRing.maximalIdeal A) • (⊤ : Submodule A (F.X j)))
    {φ ψ : F ⟶ F} (H : Homotopy (φ ≫ ψ) (𝟙 F)) (i : ℤ) [Module.Finite A (F.X i)]
    [Module.Projective A (F.X i)] : IsUnit (LinearMap.det (φ.f i).hom) := by
  obtain ⟨b⟩ := nonempty_basis_of_projective (A := A) (F.X i)
  have hg : ∀ x, (ψ.f i).hom ((φ.f i).hom x) - x ∈
      (IsLocalRing.maximalIdeal A) • (⊤ : Submodule A (F.X i)) := by
    intro x
    have hc := H.comm i
    rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel i (i + 1) from rfl),
      prevD_eq _ (show (ComplexShape.up ℤ).Rel (i - 1) i by simp)] at hc
    have hx := congrArg (fun t => t.hom x) hc
    simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f, ModuleCat.hom_comp,
      ModuleCat.hom_add, LinearMap.add_apply, LinearMap.comp_apply, ModuleCat.hom_id,
      LinearMap.id_apply] at hx
    rw [hx, add_sub_cancel_right]
    exact Submodule.add_mem _ (map_mem_smul_top _ (hmin i (i + 1) (LinearMap.mem_range_self _ x)))
      (hmin (i - 1) i (LinearMap.mem_range_self _ _))
  have hu := isUnit_det_of_sub_mem_smul_top b ((ψ.f i).hom ∘ₗ (φ.f i).hom) hg
  rw [LinearMap.det_comp] at hu
  exact isUnit_of_mul_isUnit_right hu

/-- The coefficient of a product in degree `∑ nᵢ`, when every factor has degree `≤ nᵢ`, is the
product of the coefficients in degrees `nᵢ`. -/
theorem coeff_prod_sum_of_natDegree_le {R : Type*} [CommRing R] {ι : Type*} (s : Finset ι)
    (f : ι → R[X]) (n : ι → ℕ) (h : ∀ i ∈ s, (f i).natDegree ≤ n i) :
    (∏ i ∈ s, f i).coeff (∑ i ∈ s, n i) = ∏ i ∈ s, (f i).coeff (n i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [prod_insert ha, sum_insert ha, prod_insert ha,
      coeff_mul_add_eq_of_natDegree_le (h a (mem_insert_self a s))
        (le_trans (Polynomial.natDegree_prod_le _ _)
          (sum_le_sum fun i hi => h i (mem_insert_of_mem hi))),
      ih fun i hi => h i (mem_insert_of_mem hi)]

/-- **The characteristic series of an invertible endomorphism of a minimal complex.** Let `F` be
a bounded minimal complex of finite projective modules over a local ring, vanishing outside the
finite set of degrees `S`, and `φ` an endomorphism of `F` with a homotopy inverse `ψ`. Then
`Q · det(1 - φ T | F)⁻¹ = P` for polynomials `P = ∏_{i odd} det(1 - φᵢ T)` and
`Q = ∏_{i even} det(1 - φᵢ T)` of degrees at most `∑_{i odd} rank Fⁱ` and `∑_{i even} rank Fⁱ`,
whose coefficients in those degrees are units. -/
theorem exists_polynomial_mul_inv_alternatingCharSeries
    (F : CochainComplex (ModuleCat.{v} A) ℤ) (hF : FilteredDerived.finiteProjectiveComplex A F)
    (hmin : ∀ i j, LinearMap.range (F.d i j).hom ≤
      (IsLocalRing.maximalIdeal A) • (⊤ : Submodule A (F.X j)))
    {φ ψ : F ⟶ F} (H : Homotopy (φ ≫ ψ) (𝟙 F)) (S : Finset ℤ)
    (hS : ∀ i ∉ S, IsZero (F.X i)) :
    ∃ P Q : A[X], P.natDegree ≤ ∑ i ∈ S with ¬ Even i, Module.finrank A (F.X i) ∧
      Q.natDegree ≤ ∑ i ∈ S with Even i, Module.finrank A (F.X i) ∧
      IsUnit (P.coeff (∑ i ∈ S with ¬ Even i, Module.finrank A (F.X i))) ∧
      IsUnit (Q.coeff (∑ i ∈ S with Even i, Module.finrank A (F.X i))) ∧
      (Q : A⟦X⟧) * (((FilteredDerived.alternatingCharSeries A F hF φ)⁻¹ : (A⟦X⟧)ˣ) : A⟦X⟧) =
        P := by
  classical
  have hpoly : ∀ i, ∃ p : A[X], (p : A⟦X⟧) =
      (FilteredDerived.charUnitAt A F hF i (φ.f i) : A⟦X⟧) ∧
      p.natDegree ≤ Module.finrank A (F.X i) ∧
      IsUnit (p.coeff (Module.finrank A (F.X i))) := by
    intro i
    let : Module.Projective A (F.X i) := (hF.2 i).1
    let : Module.Finite A (F.X i) := (hF.2 i).2
    obtain ⟨b⟩ := nonempty_basis_of_projective (A := A) (F.X i)
    obtain ⟨p, hp, hdeg, hcoeff⟩ := exists_polynomial_eq_charSeries b (φ.f i).hom
    refine ⟨p, ?_, hdeg, ?_⟩
    · rwa [FilteredDerived.coe_charUnitAt]
    · rw [hcoeff]
      exact ((isUnit_neg_one (α := A)).pow _).mul (isUnit_det_of_homotopy F hmin H i)
  choose p hp hdeg hunit using hpoly
  -- the alternating product over `S`
  have halt : FilteredDerived.alternatingCharSeries A F hF φ =
      ∏ i ∈ S, (if Even i then FilteredDerived.charUnitAt A F hF i (φ.f i)
        else (FilteredDerived.charUnitAt A F hF i (φ.f i))⁻¹) := by
    rw [FilteredDerived.alternatingCharSeries]
    refine finprod_eq_prod_of_mulSupport_subset _ fun i hi => ?_
    rw [Function.mem_mulSupport] at hi
    by_contra hiS
    apply hi
    simp only [FilteredDerived.charUnitAt_eq_one_of_isZero A F hF i _ (hS i hiS), inv_one,
      ite_self]
  have hsplit : (FilteredDerived.alternatingCharSeries A F hF φ)⁻¹ *
      ∏ i ∈ S with Even i, FilteredDerived.charUnitAt A F hF i (φ.f i) =
      ∏ i ∈ S with ¬ Even i, FilteredDerived.charUnitAt A F hF i (φ.f i) := by
    rw [halt, ← prod_filter_mul_prod_filter_not S Even, mul_inv,
      prod_congr rfl (fun i hi => ite_eq_left (mem_filter.1 hi).2),
      prod_congr rfl (fun i hi => ite_eq_right (mem_filter.1 hi).2), prod_inv_distrib, inv_inv,
      mul_right_comm, inv_mul_cancel, one_mul]
  refine ⟨∏ i ∈ S with ¬ Even i, p i, ∏ i ∈ S with Even i, p i,
    le_trans (Polynomial.natDegree_prod_le _ _) (sum_le_sum fun i _ => hdeg i),
    le_trans (Polynomial.natDegree_prod_le _ _) (sum_le_sum fun i _ => hdeg i), ?_, ?_, ?_⟩
  · rw [coeff_prod_sum_of_natDegree_le _ _ _ fun i _ => hdeg i]
    exact IsUnit.prod_iff.2 fun i _ => hunit i
  · rw [coeff_prod_sum_of_natDegree_le _ _ _ fun i _ => hdeg i]
    exact IsUnit.prod_iff.2 fun i _ => hunit i
  · have h := congrArg (fun u : (A⟦X⟧)ˣ => (u : A⟦X⟧)) hsplit
    simp only [Units.val_mul, Units.coe_prod] at h
    have hcoe : ∀ s : Finset ℤ, ((∏ i ∈ s, p i : A[X]) : A⟦X⟧) = ∏ i ∈ s, (p i : A⟦X⟧) :=
      fun s => map_prod (Polynomial.coeToPowerSeries.ringHom (R := A)) p s
    rwa [hcoe, hcoe, mul_comm, prod_congr rfl fun i _ => hp i, prod_congr rfl fun i _ => hp i]

end Complex

end Stacks.Drinfeld

end
