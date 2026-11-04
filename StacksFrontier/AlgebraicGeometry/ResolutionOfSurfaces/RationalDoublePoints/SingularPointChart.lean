module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalDoublePoints.ChartSingularPoint
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalDoublePoints.ClosedPointChart

/-!
# A singular closed point of the blowup, read on a chart

Let `(A, 𝔪)` be a Noetherian local ring with `𝔪 = (x₁, x₂, x₃)` and a quadratic relation
`Σ aₚᵩ xₚxᵩ ∈ 𝔪³`, and let `q` be a closed point of the blowup of `Spec A` in `𝔪` at which the
local ring is of dimension two and not regular. After reordering the generators, `q` is a
maximal ideal `𝔪'` of the chart `A[𝔪/x₁]` containing `𝔪A[𝔪/x₁]`, the local ring at `q` is the
localization there, and the dehomogenized quadratic form `q(1, y₂, y₃)` lies in the square of the
maximal ideal of `κ[y₂, y₃]` that `𝔪'` defines.

## Main results

* `AlgebraicGeometry.exists_chart_of_not_isRegularLocalRing_stalk_blowUp`: a singular closed
  point of the blowup of dimension two lies on a chart, at a point where the dehomogenized
  quadratic form is singular.

## References

* [Stacks Project, Tag 0BGE](https://stacks.math.columbia.edu/tag/0BGE)
-/

@[expose] public noncomputable section

open CategoryTheory IsLocalRing

universe u

namespace AlgebraicGeometry

variable (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]

/-- **A singular closed point of the blowup lies on a chart, at a point where the dehomogenized
quadratic form is singular.** -/
theorem exists_chart_of_not_isRegularLocalRing_stalk_blowUp (x : Fin 3 → A)
    (hspan : Ideal.span (Set.range x) = maximalIdeal A) (a : Fin 3 → Fin 3 → A)
    (hrel : ∑ p, ∑ r, a p r * (x p * x r) ∈ maximalIdeal A ^ 3)
    (q : blowUp (maximalIdealSheaf A)) (hq : IsClosed ({q} : Set (blowUp (maximalIdealSheaf A))))
    (hdim : ringKrullDim ((blowUp (maximalIdealSheaf A)).presheaf.stalk q) = 2)
    (hsing : ¬ IsRegularLocalRing ((blowUp (maximalIdealSheaf A)).presheaf.stalk q)) :
    ∃ (x' : Fin 3 → A) (hx' : ∀ i, x' i ∈ maximalIdeal A) (a' : Fin 3 → Fin 3 → A),
      (∃ σ : Equiv.Perm (Fin 3), x' = x ∘ σ ∧ a' = fun p r => a (σ p) (σ r)) ∧
      Ideal.span (Set.range x') = maximalIdeal A ∧
      ∑ p, ∑ r, a' p r * (x' p * x' r) ∈ maximalIdeal A ^ 3 ∧
      ∃ M : Ideal (affineBlowupAlgebra (maximalIdeal A) (x' 0) (Localization.Away (x' 0))),
        M.IsMaximal ∧
        Ideal.map (algebraMap A (affineBlowupAlgebra (maximalIdeal A) (x' 0)
          (Localization.Away (x' 0)))) (maximalIdeal A) ≤ M ∧
        (∃ _ : M.IsPrime, Nonempty ((blowUp (maximalIdealSheaf A)).presheaf.stalk q ≃+*
          Localization.AtPrime M)) ∧
        dehomogenizeFirst (ResidueField A) 2 (quadraticFormPoly fun p r => residue A (a' p r)) ∈
          ((M.map (Ideal.Quotient.mk (Ideal.span {algebraMap A
            (affineBlowupAlgebra (maximalIdeal A) (x' 0) (Localization.Away (x' 0)))
              (x' 0)}))).comap
              (chartPresentation (Localization.Away (x' 0)) hx')) ^ 2 := by
  obtain ⟨x', ⟨σ, rfl⟩, M, hM, hle, hprime, ⟨e⟩⟩ :=
    exists_isMaximal_ringEquiv_stalk_blowUp_maximalIdealSheaf A x hspan q hq
  have hspanσ : Ideal.span (Set.range (x ∘ σ)) = maximalIdeal A := by
    rw [Set.range_comp, Equiv.range_eq_univ, Set.image_univ, hspan]
  have hxσ : ∀ i, (x ∘ σ) i ∈ maximalIdeal A := fun i => hspanσ ▸ Ideal.subset_span ⟨i, rfl⟩
  have hrelσ : ∑ p, ∑ r, a (σ p) (σ r) * ((x ∘ σ) p * (x ∘ σ) r) ∈ maximalIdeal A ^ 3 := by
    have h : ∑ p, ∑ r, a (σ p) (σ r) * ((x ∘ σ) p * (x ∘ σ) r) =
        ∑ p, ∑ r, a p r * (x p * x r) := by
      rw [← Equiv.sum_comp σ (fun p => ∑ r, a p r * (x p * x r))]
      refine Finset.sum_congr rfl fun p _ => ?_
      exact Equiv.sum_comp σ (fun r => a (σ p) r * (x (σ p) * x r))
    rwa [h]
  have : IsLocallyNoetherian (blowUp (maximalIdealSheaf A)) :=
    LocallyOfFiniteType.isLocallyNoetherian (blowUpToBase (maximalIdealSheaf A))
  have : IsNoetherianRing (Localization.AtPrime M) := isNoetherianRing_of_ringEquiv _ e
  refine ⟨x ∘ σ, hxσ, fun p r => a (σ p) (σ r), ⟨σ, rfl, rfl⟩, hspanσ, hrelσ, M, hM, hle,
    ⟨hprime, ⟨e⟩⟩, ?_⟩
  refine dehomogenizeFirst_quadraticFormPoly_mem_sq_of_not_isRegularLocalRing
    (Localization.Away ((x ∘ σ) 0)) hxσ hspanσ _ hrelσ M hle ?_ ?_
  · rwa [← ringKrullDim_eq_of_ringEquiv e]
  · intro hreg
    exact hsing (IsRegularLocalRing.of_ringEquiv e.symm)

end AlgebraicGeometry

end
