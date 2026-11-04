module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.CurveDualityStalkComparisonOfBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.CurveDualityComplexPerfect
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Relative Poincaré duality for a smooth projective curve

Let `k` be an algebraically closed field, `ℓ` a prime invertible in `k`, `S` affine and smooth over
`k`, and `f̄ : X̄ ⟶ S` smooth projective of relative dimension one with geometrically irreducible
fibres. For every top-degree trace `t : Rf̄_* Λ ⟶ Λ[-2]` the map
`Hom_X̄(Λ, Λ[m]) → Hom_S(Rf̄_* Λ, Λ[m - 2])`, `y ↦ t[m] ∘ Rf̄_*(y)`, is bijective for every `m`
(`Stacks.EtaleCohomology.properCurveRelativeDualityInput`, the statement
`Stacks.EtaleCohomology.ProperCurveRelativeDualityInput` of the proof of
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)), with no further hypothesis.

The proof: the duality map `D_t : Rf̄_* Λ ⟶ RHom(Rf̄_* Λ, Λ[-2])` built from the canonical
multiplication of `f̄⁻¹Λ` detects relative duality (`isBijectiveAt_of_isIso_curveDualityMap`, and
`isBijectiveAt_plus_of_forall_isBijectiveAt` on `D⁺`); it is invertible because its derived stalks
are, and at a geometric point `x̄` the inverse image of `D_t` is the duality map of the fibre
(`isIso_etaleModuleDerivedInverseImage_map_curveDualityMap`), up to the comparison of [Stacks,
Tag 08JF], which is invertible because `Rf̄_* Λ` is perfect
(`isIso_etaleDerivedInverseImageHomComparison_curveDualityComplex_of_smoothOfRelativeDimension`);
and the duality map of a smooth proper curve over an algebraically closed field is invertible
(`isIso_curveDualityMap_fibre`).

The derived categories are those of the standard model `HasDerivedCategory.standard`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

/-- The comparison of Tag 08JF is invertible at the geometric points, in the setting of
`Stacks.EtaleCohomology.ProperCurveRelativeDualityInput`. -/
theorem curveDualityHomComparisonIso_of_smoothOfRelativeDimension (ℓ : ℕ) [Fact ℓ.Prime] :
    CurveDualityHomComparisonIso.{u} ℓ :=
  fun k _ _ hℓ _ _ q e _ _ f _ _ hf x =>
    isIso_etaleDerivedInverseImageHomComparison_curveDualityComplex_of_smoothOfRelativeDimension
      ℓ f k hℓ q e hf x.hom _

/-- **Relative Poincaré duality for a smooth projective curve**, over every algebraically closed
field: `Stacks.EtaleCohomology.ProperCurveRelativeDualityInput ℓ k` holds. -/
@[sga "4½ Dualite 2.2" "special case", sga "4½ Th_finitude 2.1" "special case"]
theorem properCurveRelativeDualityInput (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    [IsAlgClosed k] : ProperCurveRelativeDualityInput ℓ k :=
  properCurveRelativeDualityInput_of_curveDualityHomComparisonIso ℓ
    (curveDualityHomComparisonIso_of_smoothOfRelativeDimension ℓ) k

end Stacks.EtaleCohomology

end
