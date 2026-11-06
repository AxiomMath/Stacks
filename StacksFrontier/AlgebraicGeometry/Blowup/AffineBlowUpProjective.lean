module

public import StacksFrontier.AlgebraicGeometry.Blowup.AffineBlowUpComparison
public import StacksFrontier.AlgebraicGeometry.Blowup.ProjectiveSpaceEmbedding
public import StacksFrontier.AlgebraicGeometry.ProjBaseChange.IsIso
public import StacksFrontier.AlgebraicGeometry.QuasiProjective.HProjective

/-!
# The blowup of an affine scheme in a finitely generated ideal is H-projective

Let `R` be a commutative ring and `K ⊆ R` a finitely generated ideal. A generating family
`x₀, …, xₙ` of `K` presents the Rees algebra as a graded quotient of `R[T₀, …, Tₙ]`, so the blowup
of `Spec R` in `K` is a closed subscheme of `Proj R[T₀, …, Tₙ] ≅ ℙⁿ_R` over `Spec R`
(`Stacks.Blowup.isClosedImmersion_blowUpSpecToProjSpace` and
`Stacks.AlgebraicGeometry.ProjBaseChange.polynomialComparison`). Hence the blowup morphism is
H-projective in the sense of `AlgebraicGeometry.IsProjectiveMorphism`, both for the affine blowup
`Stacks.Blowup.toSpec K` and for the blowup of the ideal sheaf `K` defines on `Spec R`.

## Main results

* `Stacks.Blowup.isProjectiveMorphism_toSpec` — the affine blowup is H-projective.
* `Stacks.Blowup.isProjectiveMorphism_blowUpToBase_ofIdealTop` — the blowup of the ideal sheaf
  attached to `K` is H-projective.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Blowup

attribute [local instance] MvPolynomial.gradedAlgebra

variable {R : Type u} [CommRing R]

/-- The structure morphism `Proj R[T₀, …, Tₙ] ⟶ Spec R` of `Stacks.Blowup.projSpaceToSpec`
corresponds, along the comparison `ℙⁿ_R ≅ Proj R[T₀, …, Tₙ]`, to the structure morphism of
`ℙⁿ_R`. -/
theorem polynomialComparison_inv_over (n : ℕ) :
    (Stacks.AlgebraicGeometry.ProjBaseChange.polynomialComparison R n).iso.inv ≫
        (projectiveSpaceOver n (Spec (CommRingCat.of R)) ↘ Spec (CommRingCat.of R)) =
      projSpaceToSpec R (n + 1) := by
  have h := (Stacks.AlgebraicGeometry.ProjBaseChange.polynomialComparison R n).toBase
  rw [← Iso.eq_inv_comp] at h
  show _ ≫ Limits.pullback.fst _ _ = _
  rw [← h, projSpaceToSpec]
  congr 2
  ext r m
  have hC : (MvPolynomial.C r : MvPolynomial (Fin (n + 1)) R) ∈
      Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading R n 0 :=
    MvPolynomial.isHomogeneous_C _ r
  refine congrArg (fun p : MvPolynomial (Fin (n + 1)) R => p.coeff m) ?_
  show ((GradedRing.projZeroRingHom (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading R n)
      (MvPolynomial.C r) : MvPolynomial (Fin (n + 1)) R)) =
    ((algebraMap R (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R 0) r :
      MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R 0) : MvPolynomial (Fin (n + 1)) R)
  rw [GradedRing.projZeroRingHom_apply, DirectSum.decompose_of_mem_same _ hC,
    SetLike.GradeZero.coe_algebraMap, MvPolynomial.algebraMap_eq]

/-- **The affine blowup of `Spec R` in a finitely generated ideal is a closed subscheme of a
projective space of positive dimension over `R`**, over `Spec R`. A generating family can be
padded by zeros, so the dimension can be taken positive. -/
theorem exists_isClosedImmersion_projectiveSpaceOver_succ (K : Ideal R) (hK : K.FG) :
    ∃ (m : ℕ) (i : blowUpSpec K ⟶ projectiveSpaceOver (m + 1) (Spec (CommRingCat.of R))),
      IsClosedImmersion i ∧
        i ≫ (projectiveSpaceOver (m + 1) (Spec (CommRingCat.of R)) ↘ Spec (CommRingCat.of R)) =
          toSpec K := by
  obtain ⟨k, y, hy⟩ := Submodule.fg_iff_exists_fin_generating_family.1 hK
  let x : Fin (k + 2) → R := Fin.cons 0 (Fin.cons 0 y)
  have hspan : K = Ideal.span (Set.range x) := by
    rw [← hy, Fin.range_cons, Fin.range_cons, Ideal.span_insert_zero, Ideal.span_insert_zero]
  have hx : ∀ i, x i ∈ K := fun i => hspan ▸ Ideal.subset_span ⟨i, rfl⟩
  refine ⟨k, blowUpSpecToProjSpace K x hx hspan ≫
    (Stacks.AlgebraicGeometry.ProjBaseChange.polynomialComparison R (k + 1)).iso.inv,
    inferInstance, ?_⟩
  rw [Category.assoc, polynomialComparison_inv_over,
    blowUpSpecToProjSpace_comp_projSpaceToSpec]

/-- **The affine blowup of `Spec R` in a finitely generated ideal is H-projective.** -/
theorem isProjectiveMorphism_toSpec (K : Ideal R) (hK : K.FG) :
    IsProjectiveMorphism (toSpec K) := by
  obtain ⟨m, i, hi, hw⟩ := exists_isClosedImmersion_projectiveSpaceOver_succ K hK
  exact ⟨m + 1, i, hi, hw⟩

/-- **The blowup of `Spec R` in the ideal sheaf of a finitely generated ideal is a closed
subscheme of a projective space of positive dimension over `R`**, over `Spec R`. -/
theorem exists_isClosedImmersion_projectiveSpaceOver_succ_blowUpToBase (K : Ideal R)
    (hK : K.FG) :
    ∃ (m : ℕ) (i : AlgebraicGeometry.blowUp (Scheme.IdealSheafData.ofIdealTop
        (Ideal.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom K)) ⟶
        projectiveSpaceOver (m + 1) (Spec (CommRingCat.of R))),
      IsClosedImmersion i ∧
        i ≫ (projectiveSpaceOver (m + 1) (Spec (CommRingCat.of R)) ↘ Spec (CommRingCat.of R)) =
          AlgebraicGeometry.blowUpToBase (Scheme.IdealSheafData.ofIdealTop
            (Ideal.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom K)) := by
  obtain ⟨e⟩ := nonempty_over_iso_blowUpToBase R K
  obtain ⟨m, i, _, hw⟩ := exists_isClosedImmersion_projectiveSpaceOver_succ K hK
  have : IsIso e.inv.left := (Over.forget _).map_isIso e.inv
  refine ⟨m, e.inv.left ≫ i, inferInstance, ?_⟩
  rw [Category.assoc, hw]
  simpa using Over.w e.inv

/-- **The blowup of `Spec R` in the ideal sheaf of a finitely generated ideal is H-projective.**
The two blowups agree over `Spec R` (`Stacks.Blowup.nonempty_over_iso_blowUpToBase`). -/
theorem isProjectiveMorphism_blowUpToBase_ofIdealTop (K : Ideal R) (hK : K.FG) :
    IsProjectiveMorphism (AlgebraicGeometry.blowUpToBase (Scheme.IdealSheafData.ofIdealTop
      (Ideal.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom K))) := by
  obtain ⟨e⟩ := nonempty_over_iso_blowUpToBase R K
  exact IsProjectiveMorphism.of_iso ((Over.forget _).mapIso e) (Iso.refl _)
    (by simpa using Over.w e.hom) (isProjectiveMorphism_toSpec K hK)

end Stacks.Blowup

end
