module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.CurveDualityStalkComparisonOfBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.EtaleDerivedHomInverseImagePerfect

/-!
# Relative Poincaré duality for a smooth projective curve, from the local constancy of `Rf_* Λ`

Let `f : X ⟶ S` be a smooth projective curve as in
`Stacks.EtaleCohomology.ProperCurveRelativeDualityInput`, `ℓ` a prime and `Λ = ℤ/ℓ`. The
comparison `x̄⁻¹ RHom(K, M) ⟶ RHom(x̄⁻¹K, x̄⁻¹M)` of [Stacks, Tag 08JF] is invertible out of a
perfect complex `K`
(`Stacks.EtaleCohomology.isIso_etaleDerivedInverseImageHomComparison_of_isPerfect`), so relative
duality for `f` follows from the perfectness of `K = Rf_*(f⁻¹Λ_S)` on the constant ringed site
`(S_étale, Λ̲)`, which holds when `K` is bounded with locally constant cohomology sheaves of finite
type (`Stacks.EtaleCohomology.CurveDualityComplexLocallyConstant`):
`Stacks.EtaleCohomology.properCurveRelativeDualityInput_of_curveDualityComplexLocallyConstant`.

The derived categories are those of the standard model `HasDerivedCategory.standard`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

open Stacks.EtaleCohomology.ExtensionTorsor

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- **`Rf_* Λ` is bounded with locally constant cohomology of finite type**: in the setting of
`Stacks.EtaleCohomology.ProperCurveRelativeDualityInput`, the complex `K = Rf_*(f⁻¹Λ_S)` has
bounded cohomology, and its cohomology sheaves are locally constant of finite type. -/
def CurveDualityComplexLocallyConstant : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k], IsUnit (ℓ : k) →
    ∀ (S X : Scheme.{u}) (q : S ⟶ Spec (.of k)) (e : ℕ) [SmoothOfRelativeDimension e q]
      [IsAffine S] (f : X ⟶ S) [SmoothOfRelativeDimension 1 f] [GeometricallyIrreducible f],
      IsProjectiveMorphism f →
        ∃ a b : ℤ, (curveDualityComplex ℓ f).IsGE a ∧ (curveDualityComplex ℓ f).IsLE b ∧
          ∀ n : ℤ, Stacks.ConstantSheaf.IsFiniteTypeLocallyConstantModuleSheaf.{u, u + 1, 0}
            S.smallEtaleTopology (ZMod ℓ)
            ((DerivedCategory.homologyFunctor _ n).obj (curveDualityComplex ℓ f))

/-- The comparison of Tag 08JF is invertible at the geometric points once `Rf_* Λ` is bounded
with locally constant cohomology of finite type: it is then perfect. -/
theorem curveDualityHomComparisonIso_of_curveDualityComplexLocallyConstant
    (hP : CurveDualityComplexLocallyConstant.{u} ℓ) : CurveDualityHomComparisonIso.{u} ℓ := by
  intro k _ _ hℓ S X q e _ _ f _ _ hf x
  obtain ⟨a, b, ha, hb, hK⟩ := hP k hℓ S X q e f hf
  exact isIso_etaleDerivedInverseImageHomComparison_of_isFiniteTypeLocallyConstant (ZMod ℓ) x.hom
    _ _ a b hK

/-- **Relative Poincaré duality for a smooth projective curve**
(`Stacks.EtaleCohomology.ProperCurveRelativeDualityInput`), granted that `Rf_* Λ` is bounded with
locally constant cohomology of finite type. -/
theorem properCurveRelativeDualityInput_of_curveDualityComplexLocallyConstant
    (hP : CurveDualityComplexLocallyConstant.{u} ℓ) (k : Type u) [Field k] [IsAlgClosed k] :
    ProperCurveRelativeDualityInput ℓ k :=
  properCurveRelativeDualityInput_of_curveDualityHomComparisonIso ℓ
    (curveDualityHomComparisonIso_of_curveDualityComplexLocallyConstant ℓ hP) k

end Stacks.EtaleCohomology

end
