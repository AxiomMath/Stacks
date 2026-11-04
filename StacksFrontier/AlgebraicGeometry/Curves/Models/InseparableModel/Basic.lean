module

public import StacksFrontier.AlgebraicGeometry.Curves.Models.InseparableModel.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# A regular model with an inseparable component: the structure morphism and the charts

For the model `X = Proj (R[z] ⧸ J)` of `Stacks.Models.InseparableModel` this file defines the
structure morphism `X ⟶ Spec R` and proves it proper, and names the three affine charts
`D₊(z₀₀)`, `D₊(z₀₁)`, `D₊(z₁₁)` together with the explicit rings `R[s][T] ⧸ (x T - y)` that
present them:

* on `D₊(z₀₀)`: `x = π`, `y = s² - t` (`s = z₁₀/z₀₀`, `T = z₀₁/z₀₀`);
* on `D₊(z₀₁)`: `x = s² - t`, `y = π` (`s = z₁₁/z₀₁`, `T = z₀₀/z₀₁`);
* on `D₊(z₁₁)`: `x = 1 - t s²`, `y = π s²` (`s = z₀₁/z₁₁`, `T = z₁₀/z₁₁`).

## Main definitions

* `Stacks.Models.InseparableModel.X_to_R` — the structure morphism `X ⟶ Spec R`.
* `Stacks.Models.InseparableModel.zA` — the class in `A` of a variable.
* `Stacks.Models.InseparableModel.chartVar`, `chartX`, `chartY`, `chartRing` — the charts and
  their explicit rings.
* `Stacks.Models.InseparableModel.chartι` — the chart `Spec (A_{(z)})₀ ⟶ X`.

## Main results

* `Stacks.Models.InseparableModel.isProper_X_to_R` — `X ⟶ Spec R` is proper.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace Stacks.Models.InseparableModel

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The class in `A = R[z] ⧸ J` of the variable `zᵢ`. -/
def zA (i : Fin 4) : A := Ideal.Quotient.mk J.toIdeal (MvPolynomial.X i)

/-- Each variable `zᵢ` has degree one in `A`. -/
theorem zA_mem (i : Fin 4) : zA i ∈ grading 1 :=
  Stacks.RingTheory.HomogeneousQuotient.quotientGrading_mk_mem polyGrading J
    ((MvPolynomial.mem_homogeneousSubmodule _ _).2 (MvPolynomial.isHomogeneous_X R i))

/-- `R → A₀ → A` is a scalar tower, `A₀` the degree-zero part of `A`. -/
instance isScalarTower_grading_zero : IsScalarTower R (grading 0) A :=
  IsScalarTower.of_algebraMap_eq (S := grading 0) fun r =>
    (SetLike.GradeZero.coe_algebraMap grading r).symm

/-- The image of `r ∈ R` in `A` is the class of the constant polynomial `r`. -/
theorem A_algebraMap_eq_mk (r : R) :
    algebraMap R A r = Ideal.Quotient.mk J.toIdeal (MvPolynomial.C r) := by
  rw [IsScalarTower.algebraMap_apply R P A, Ideal.Quotient.algebraMap_eq,
    MvPolynomial.algebraMap_eq]

/-- The generators of `J` vanish in `A`. -/
theorem mk_gen_eq_zero {q : P} (hq : q ∈ gens) : Ideal.Quotient.mk J.toIdeal q = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span hq)

/-- The relation `q₀ = 0` in `A`: `z₀₀ z₁₁ = z₀₁ z₁₀`. -/
theorem zA_rel₀ : zA 0 * zA 3 = zA 1 * zA 2 := by
  rw [← sub_eq_zero]
  simpa [q₀, zA] using mk_gen_eq_zero (q := q₀) (by simp [gens])

/-- The relation `q₁ = 0` in `A`: `π z₀₀ z₀₁ + t z₀₀² = z₁₀²`. -/
theorem zA_rel₁ : algebraMap R A π * zA 0 * zA 1 + algebraMap R A tR * zA 0 ^ 2 = zA 2 ^ 2 := by
  rw [← sub_eq_zero]
  simpa [q₁, zA, A_algebraMap_eq_mk] using mk_gen_eq_zero (q := q₁) (by simp [gens])

/-- The relation `q₂ = 0` in `A`: `π z₀₁² + t z₀₀ z₀₁ = z₁₀ z₁₁`. -/
theorem zA_rel₂ : algebraMap R A π * zA 1 ^ 2 + algebraMap R A tR * zA 0 * zA 1 = zA 2 * zA 3 := by
  rw [← sub_eq_zero]
  simpa [q₂, zA, A_algebraMap_eq_mk] using mk_gen_eq_zero (q := q₂) (by simp [gens])

/-- `A` is of finite type over its degree-zero part. -/
instance finiteType_grading : Algebra.FiniteType (grading 0) A := by
  have h1 : Algebra.FiniteType R A :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ R J.toIdeal) Ideal.Quotient.mk_surjective
  exact Algebra.FiniteType.of_restrictScalars_finiteType R (grading 0) A

/-- The map from `R` to the degree-zero part of `A` is bijective: `A₀` is the image of the
constants, and `J` contains no nonzero constant, its generators having no constant term. -/
theorem bijective_algebraMap_grading_zero :
    Function.Bijective (algebraMap R ↥(grading 0)) := by
  constructor
  · intro r r' h
    have h' := congrArg (fun a : ↥(grading 0) => (a : A)) h
    simp only [SetLike.GradeZero.coe_algebraMap grading] at h'
    rw [← sub_eq_zero, ← map_sub] at h'
    have hmem : MvPolynomial.C (r - r') ∈ J.toIdeal := by
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      simpa [IsScalarTower.algebraMap_apply R P A] using h'
    have hJ : J.toIdeal ≤ RingHom.ker (MvPolynomial.constantCoeff (R := R) (σ := Fin 4)) := by
      show Ideal.span gens ≤ _
      rw [Ideal.span_le]
      rintro q (rfl | rfl | rfl) <;> simp [q₀, q₁, q₂]
    simpa [sub_eq_zero] using hJ hmem
  · rintro ⟨a, ha⟩
    obtain ⟨p, hp, rfl⟩ := (Stacks.RingTheory.HomogeneousQuotient.mem_quotientGrading_iff
      polyGrading J).1 ha
    obtain ⟨r, rfl⟩ : ∃ r, p = MvPolynomial.C r :=
      ⟨_, MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp
        (Nat.le_zero.mp ((MvPolynomial.mem_homogeneousSubmodule _ _).1 hp).totalDegree_le)⟩
    refine ⟨r, Subtype.ext ?_⟩
    simp [IsScalarTower.algebraMap_apply R P A]

/-- **The structure morphism `X ⟶ Spec R`.** -/
def X_to_R : XR ⟶ Spec (.of R) :=
  Proj.toSpecZero grading ≫ Spec.map (CommRingCat.ofHom (algebraMap R ↥(grading 0)))

/-- `Spec A₀ ⟶ Spec R` is an isomorphism, the map `R → A₀` being bijective. -/
instance isIso_SpecMap_grading_zero :
    IsIso (Spec.map (CommRingCat.ofHom (algebraMap R ↥(grading 0)))) := by
  have : IsIso (CommRingCat.ofHom (algebraMap R ↥(grading 0))) :=
    (ConcreteCategory.isIso_iff_bijective (CommRingCat.ofHom (algebraMap R ↥(grading 0)))).mpr
      bijective_algebraMap_grading_zero
  infer_instance

/-- **The model is proper over `R`.** -/
instance isProper_X_to_R : IsProper X_to_R := by
  unfold X_to_R
  infer_instance

/-! ### The charts -/

/-- The variable inverted on each of the three charts: `z₀₀`, `z₀₁`, `z₁₁`. -/
def chartVar : Fin 3 → Fin 4 := ![0, 1, 3]

/-- The coefficient `x` of the chart equation `x T - y`. -/
def chartX : Fin 3 → Polynomial R :=
  ![Polynomial.C π, Polynomial.X ^ 2 - Polynomial.C tR, 1 - Polynomial.C tR * Polynomial.X ^ 2]

/-- The coefficient `y` of the chart equation `x T - y`. -/
def chartY : Fin 3 → Polynomial R :=
  ![Polynomial.X ^ 2 - Polynomial.C tR, Polynomial.C π, Polynomial.C π * Polynomial.X ^ 2]

/-- The equation `x T - y ∈ R[s][T]` of a chart. -/
def chartEq (c : Fin 3) : Polynomial (Polynomial R) :=
  Polynomial.C (chartX c) * Polynomial.X - Polynomial.C (chartY c)

/-- **The explicit ring of a chart**, `R[s][T] ⧸ (x T - y)`. -/
abbrev chartRing (c : Fin 3) : Type :=
    Polynomial (Polynomial R) ⧸ Ideal.span ({chartEq c} : Set (Polynomial (Polynomial R)))

/-- The ring `(A_{(z)})₀` of the chart `D₊(z)`. -/
abbrev Away (c : Fin 3) : Type := HomogeneousLocalization.Away grading (zA (chartVar c))

/-- The structure map `R ⟶ (A_{(z)})₀`. -/
def awayBase (c : Fin 3) : R →+* Away c :=
  (HomogeneousLocalization.fromZeroRingHom grading (Submonoid.powers (zA (chartVar c)))).comp
    (algebraMap R ↥(grading 0))

/-- **The chart** `Spec (A_{(z)})₀ ⟶ X` onto `D₊(z)`. -/
def chartι (c : Fin 3) : Spec (.of (Away c)) ⟶ XR :=
  Proj.awayι grading (zA (chartVar c)) (zA_mem _) Nat.one_pos

/-- Each chart `Spec (A_{(z)})₀ ⟶ X` is an open immersion. -/
instance isOpenImmersion_chartι (c : Fin 3) : IsOpenImmersion (chartι c) := by
  unfold chartι
  infer_instance

/-- The chart followed by the structure morphism is `Spec` of the structure map
`R ⟶ (A_{(z)})₀`. -/
theorem chartι_comp_X_to_R (c : Fin 3) :
    chartι c ≫ X_to_R = Spec.map (CommRingCat.ofHom (awayBase c)) := by
  rw [chartι, X_to_R, Proj.awayι_toSpecZero_assoc, ← Spec.map_comp]
  show Spec.map (CommRingCat.ofHom (algebraMap R ↥(grading 0)) ≫
      CommRingCat.ofHom (HomogeneousLocalization.fromZeroRingHom grading
        (Submonoid.powers (zA (chartVar c))))) = Spec.map (CommRingCat.ofHom (awayBase c))
  rfl

/-- The image of the chart attached to `z` is the basic open `D₊(z)`. -/
theorem opensRange_chartι (c : Fin 3) :
    (chartι c).opensRange = Proj.basicOpen grading (zA (chartVar c)) :=
  Proj.opensRange_awayι _ _ _ _

end Stacks.Models.InseparableModel
