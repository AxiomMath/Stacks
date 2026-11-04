module

public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public import StacksFrontier.AlgebraicGeometry.ProjCoherentCohomologyFinite.Basic
public import StacksFrontier.AlgebraicGeometry.ProjIdealSheaf.Basic
public import StacksFrontier.AlgebraicGeometry.ProjSaturation.VPlus
public import StacksFrontier.AlgebraicGeometry.ProjectiveChart.HypersurfaceFinitePresentation

/-!
# Plane curves over a ring, cut out by one homogeneous equation

Let `R` be a commutative ring and let `F ∈ R[T₀, T₁, T₂]` be homogeneous. The closed subscheme

`V(F) = Proj (R[T₀, T₁, T₂]/(F)) ⊆ ℙ²_R`

is the scheme the examples of models of genus zero curves are written in: `T₁T₂ - πT₀²` for
[Stacks, Tag 0CA0] and `T₁² + T₂² - πT₀²` for [Stacks, Tag 0CDL]. This file builds it once, for an
arbitrary homogeneous `F`, with its closed immersion into `ℙ²_R` and its structure morphism to
`Spec R`, and reads off its homogeneous ideal and its standard affine charts.

## Main definitions

* `Stacks.Models.PlaneCurveModel.scheme`: the scheme `Proj (R[T₀, T₁, T₂]/(F))`.
* `Stacks.Models.PlaneCurveModel.embedding`: its closed immersion into `ℙ²_R`.
* `Stacks.Models.PlaneCurveModel.toSpec`: its structure morphism to `Spec R`.
* `Stacks.Models.PlaneCurveModel.chart`: the chart `V(F) ∩ D₊(Tⱼ)`.

## Main results

* `Stacks.Models.PlaneCurveModel.idealOfClosedSubscheme_embedding`: over a Noetherian unique
  factorization domain, if some coordinate `Tⱼ` does not divide `F`, then the homogeneous ideal
  of `V(F)` is `(F)`.
* `Stacks.Models.PlaneCurveModel.chartEquiv`: under the same hypotheses, the ring of the chart
  `V(F) ∩ D₊(Tₖ)` is `R[Y₀, Y₁]/(F(Tₖ = 1))`.
* `Stacks.Models.PlaneCurveModel.iSup_chart_eq_top`: the three charts cover `V(F)`.
* The structure morphism is proper and locally of finite presentation.

## Implementation notes

The grading of the quotient is `Stacks.HomogeneousIdeal.quotientGrading`, the grading for which
the saturation formula of [Stacks, Tag 0BXK] is available
(`AlgebraicGeometry.ProjectiveSpectrum.Proj.idealOfClosedSubscheme_projMap_quotientMk_eq`). The
ideal `(F)` is saturated as soon as one coordinate `Tⱼ` does not divide `F`: if
`Tⱼᴺ · x ∈ (F)` then `F` divides `x`, since `Tⱼ` is prime and `R[T₀, T₁, T₂]` is a unique
factorization domain. The homogeneous ideal being `(F)`, the chart presentations of
`Stacks.ProjectiveChart.chartQuotientEquiv` apply.

## References

* [Stacks Project, Tag 0BXK](https://stacks.math.columbia.edu/tag/0BXK)
* [Stacks Project, Tag 0CA0](https://stacks.math.columbia.edu/tag/0CA0)
* [Stacks Project, Tag 0CDL](https://stacks.math.columbia.edu/tag/0CDL)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry MvPolynomial
open AlgebraicGeometry.ProjectiveSpectrum.Proj (idealOfClosedSubscheme)

universe u

namespace Stacks.Models.PlaneCurveModel

attribute [local instance] MvPolynomial.gradedAlgebra

variable {R : Type u} [CommRing R] (F : MvPolynomial (Fin 3) R) {d : ℕ} (hF : F.IsHomogeneous d)

/-- The homogeneous ideal `(F)` of `R[T₀, T₁, T₂]`. -/
def equationIdeal : HomogeneousIdeal (homogeneousSubmodule (Fin 3) R) where
  toSubmodule := Ideal.span {F}
  is_homogeneous' := Ideal.homogeneous_span _ _ <| by
    rintro x hx
    rw [Set.mem_singleton_iff] at hx
    exact ⟨d, hx ▸ (mem_homogeneousSubmodule d F).2 hF⟩

/-- The underlying ideal of `equationIdeal F hF` is `Ideal.span {F}`. -/
theorem toIdeal_equationIdeal : (equationIdeal F hF).toIdeal = Ideal.span {F} := rfl

/-- The grading by total degree of the homogeneous coordinate ring `R[T₀, T₁, T₂]/(F)`. -/
abbrev grading : ℕ → AddSubgroup (MvPolynomial (Fin 3) R ⧸ (equationIdeal F hF).toIdeal) :=
  Stacks.HomogeneousIdeal.quotientGrading (equationIdeal F hF)

/-- **The plane curve `V(F) = Proj (R[T₀, T₁, T₂]/(F))`.** -/
abbrev scheme : Scheme.{u} := Proj (grading F hF)

/-- The closed immersion `V(F) ⟶ ℙ²_R` induced by the quotient map. -/
def embedding : scheme F hF ⟶ Proj (homogeneousSubmodule (Fin 3) R) :=
  Proj.map (Stacks.HomogeneousIdeal.quotientMk (equationIdeal F hF))
    (Proj.irrelevant_le_map_of_surjective _
      (Stacks.HomogeneousIdeal.surjective_quotientMk _))

/-- The embedding `V(F) ⟶ ℙ²_R` is a closed immersion. -/
instance isClosedImmersion_embedding : IsClosedImmersion (embedding F hF) :=
  Proj.isClosedImmersion_map_quotientMk _

/-- The structure morphism `V(F) ⟶ Spec R`: the embedding into `ℙ²_R` followed by the structure
morphism of `ℙ²_R`. -/
def toSpec : scheme F hF ⟶ Spec (CommRingCat.of R) :=
  embedding F hF ≫ Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff R 2

/-- The plane curve `V(F)` is proper over `R`. -/
instance isProper_toSpec : IsProper (toSpec F hF) := by
  have := Stacks.ProjCoherentCohomologyFinite.isProper_projToSpecCoeff R 2
  unfold toSpec
  infer_instance

/-- A coordinate `Tⱼ` does not divide `F` as soon as `F` does not vanish at a point whose `j`-th
coordinate is zero. -/
theorem not_X_dvd_of_eval_ne_zero {j : Fin 3} {v : Fin 3 → R} (hv : v j = 0)
    (hFv : eval v F ≠ 0) : ¬ (X j : MvPolynomial (Fin 3) R) ∣ F := by
  rintro ⟨q, rfl⟩
  simp [hv] at hFv

variable [IsDomain R] [UniqueFactorizationMonoid R] [IsNoetherianRing R]

/-- **The homogeneous ideal of `V(F)` is `(F)`** as soon as some coordinate `Tⱼ` does not divide
`F`. -/
theorem idealOfClosedSubscheme_embedding (j : Fin 3) (hj : ¬ (X j : MvPolynomial (Fin 3) R) ∣ F) :
    idealOfClosedSubscheme (homogeneousSubmodule (Fin 3) R) (embedding F hF) =
      Ideal.span {F} := by
  refine AlgebraicGeometry.ProjectiveSpectrum.Proj.idealOfClosedSubscheme_projMap_quotientMk_eq
    _ (equationIdeal F hF) _ (adjoin_homogeneousSubmodule_one_eq_top (Fin 3) R) ?_
  rintro x ⟨N, hN⟩
  have hXN : (X j : MvPolynomial (Fin 3) R) ^ N ∈ homogeneousSubmodule (Fin 3) R N := by
    rw [mem_homogeneousSubmodule]
    simpa using (isHomogeneous_X R j).pow N
  have h := hN _ hXN
  rw [toIdeal_equationIdeal, Ideal.mem_span_singleton] at h ⊢
  let _ := UniqueFactorizationMonoid.toGCDMonoid (MvPolynomial (Fin 3) R)
  exact ((MvPolynomial.X_prime (R := R) (i := j)).irreducible.isRelPrime_iff_not_dvd.mpr
    hj).pow_left.symm.dvd_of_dvd_mul_left h

/-- The chart `V(F) ∩ D₊(Tₖ)` of the plane curve. -/
abbrev chart (k : Fin 3) : (scheme F hF).Opens :=
  Stacks.ProjectiveChart.subschemeChart (embedding F hF) k

omit [IsDomain R] [UniqueFactorizationMonoid R] [IsNoetherianRing R] in
/-- The chart `V(F) ∩ D₊(Tₖ)` is an affine open of `V(F)`. -/
theorem isAffineOpen_chart (k : Fin 3) : IsAffineOpen (chart F hF k) :=
  Stacks.ProjectiveChart.isAffineOpen_subschemeChart (embedding F hF) k

omit [IsDomain R] [UniqueFactorizationMonoid R] [IsNoetherianRing R] in
/-- The three charts `V(F) ∩ D₊(Tₖ)` cover `V(F)`. -/
theorem iSup_chart_eq_top : ⨆ k : Fin 3, chart F hF k = ⊤ :=
  Stacks.ProjectiveChart.iSup_subschemeChart_eq_top (embedding F hF)

omit [IsDomain R] [UniqueFactorizationMonoid R] [IsNoetherianRing R] in
include hF in
/-- The equation `F` is homogeneous of degree `d • 1`. -/
theorem mem_homogeneousSubmodule_smul_one :
    F ∈ homogeneousSubmodule (Fin 3) R (d • 1) := by
  rwa [smul_eq_mul, mul_one, mem_homogeneousSubmodule]

/-- **The ring of the chart `V(F) ∩ D₊(Tₖ)` is `R[Y₀, Y₁]/(F(Tₖ = 1))`**, where the
dehomogenization `F(Tₖ = 1)` is `Stacks.ProjectiveChart.dehomCoeff R k F`. -/
def chartEquiv (j : Fin 3) (hj : ¬ (X j : MvPolynomial (Fin 3) R) ∣ F) (k : Fin 3) :
    (MvPolynomial (Fin 2) R ⧸ Ideal.span {Stacks.ProjectiveChart.dehomCoeff R k F}) ≃+*
      Γ(scheme F hF, chart F hF k) :=
  Stacks.ProjectiveChart.chartQuotientEquiv (embedding F hF) k F
    (mem_homogeneousSubmodule_smul_one F hF) (idealOfClosedSubscheme_embedding F hF j hj)

/-- The isomorphism `chartEquiv` carries the class of a constant `C r` to the pullback of `r` along
the structure morphism. -/
theorem chartEquiv_mk_C (j : Fin 3) (hj : ¬ (X j : MvPolynomial (Fin 3) R) ∣ F) (k : Fin 3)
    (r : R) :
    chartEquiv F hF j hj k (Ideal.Quotient.mk _ (C r)) =
      ((toSpec F hF).appLE ⊤ (chart F hF k) le_top).hom
        ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) := by
  rw [chartEquiv, Stacks.ProjectiveChart.chartQuotientEquiv_mk]
  exact Stacks.ProjectiveChart.chartPresentation_C (embedding F hF) k r

/-- The structure morphism of `V(F)` is locally of finite presentation. -/
theorem locallyOfFinitePresentation_toSpec (j : Fin 3)
    (hj : ¬ (X j : MvPolynomial (Fin 3) R) ∣ F) :
    LocallyOfFinitePresentation (toSpec F hF) :=
  Stacks.ProjectiveChart.locallyOfFinitePresentation_toSpec (embedding F hF) F
    (mem_homogeneousSubmodule_smul_one F hF) (idealOfClosedSubscheme_embedding F hF j hj)

/-- **A property of the structure morphism checked on the three charts.** If `P` is a property
of morphisms given affine-locally by the ring-map property `Q`, and `Q` holds for each of the
`R`-algebras `R[Y₀, Y₁]/(F(Tₖ = 1))`, then `P` holds for `V(F) ⟶ Spec R`. -/
theorem hasRingHomProperty_toSpec {P : MorphismProperty Scheme.{u}}
    {Q : ∀ {A B : Type u} [CommRing A] [CommRing B], (A →+* B) → Prop} [HasRingHomProperty P Q]
    (j : Fin 3) (hj : ¬ (X j : MvPolynomial (Fin 3) R) ∣ F)
    (hQ : ∀ k : Fin 3, Q (algebraMap R
      (MvPolynomial (Fin 2) R ⧸ Ideal.span {Stacks.ProjectiveChart.dehomCoeff R k F}))) :
    P (toSpec F hF) := by
  have hiso := (HasRingHomProperty.isLocal_ringHomProperty P).respectsIso
  refine HasRingHomProperty.of_iSup_eq_top (P := P) (Q := Q)
    (fun l : Fin 3 => ⟨chart F hF l, isAffineOpen_chart F hF l⟩)
    (iSup_chart_eq_top F hF) fun l => ?_
  set ψ := ((toSpec F hF).appLE ⊤ (chart F hF l) le_top).hom
  set e : R ≃+* Γ(Spec (CommRingCat.of R), ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv
  have hcomp : ψ.comp e.toRingHom = (chartEquiv F hF j hj l).toRingHom.comp
      (algebraMap R (MvPolynomial (Fin 2) R ⧸
        Ideal.span {Stacks.ProjectiveChart.dehomCoeff R l F})) := by
    ext r
    exact (chartEquiv_mk_C F hF j hj l r).symm
  have h1 : Q (ψ.comp e.toRingHom) := by
    rw [hcomp]
    exact hiso.1 _ _ (hQ l)
  have h2 := hiso.2 (ψ.comp e.toRingHom) e.symm h1
  rwa [RingHom.comp_assoc, show e.toRingHom.comp e.symm.toRingHom = RingHom.id _ from
    RingHom.ext fun x => e.apply_symm_apply x, RingHom.comp_id] at h2

end Stacks.Models.PlaneCurveModel

end
