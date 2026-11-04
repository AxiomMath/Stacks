module

public import StacksFrontier.AlgebraicGeometry.RelativeProjInvertibleMorphism.ThetaChartDatum

/-!
# Clause (3) of Stacks Tag 01O9, for the morphism, and the uniqueness it gives

Let `P = (ℒ, ψ)` be the datum of [Stacks, Tag 01O8] for `f : X ⟶ S` and `r = r_{ℒ,ψ}` the glued
morphism `U(ψ) ⟶ Proj_S(𝒜)`. Over an affine open `V` of the base write `ψ'` for the induced
datum `𝒜(V) ⟶ Γ_*(f^{-1}V, ℒ)` of [Stacks, Tag 01NK]. Clause (3) says that `U(ψ') = U(ψ) ∩ f^{-1}V`
and that, read through this identification and the chart `i_V : Proj 𝒜(V) ⟶ Proj_S(𝒜)` of
[Stacks, Tag 01NQ], `r` restricts to the morphism `r_{ℒ|_{f^{-1}V}, ψ'}` of Tag 01NK.

The identification of opens is `…GradedPowerMap.image_coveringOpen_affineDatum` together with
`…GradedPowerMap.coveringOpen_inf_preimage_eq`. The restriction is stated for every morphism
`j : U(ψ') ⟶ U(ψ)` over `X`; there is exactly one, and its existence is the identification.

## Main results

* `…GradedPowerMap.image_coveringOpen_affineDatum_eq`: `U(ψ') = U(ψ) ∩ f^{-1}V` inside `X`.
* `…GradedPowerMap.comp_globalMorphism_eq`: the restriction of `r` along `U(ψ') ⟶ U(ψ)` is
  `i_V ∘ r_{ℒ|_{f^{-1}V}, ψ'}`.
* `…GradedPowerMap.eq_globalMorphism_of_clauseThree`: a morphism `U(ψ) ⟶ Proj_S(𝒜)` with that
  restriction property over every affine open of the base is `r`.

## References

* [Stacks Project, Tag 01NK](https://stacks.math.columbia.edu/tag/01NK)
* [Stacks Project, Tag 01NQ](https://stacks.math.columbia.edu/tag/01NQ)
* [Stacks Project, Tag 01O9](https://stacks.math.columbia.edu/tag/01O9)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjFromSections

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism

namespace GradedPowerMap

variable {S : Scheme.{u}} {A : SheafGradedAlgebra.{u} S} {T : Scheme.{u}} {f : T ⟶ S}
  (P : GradedPowerMap A f) (rp : RelativeProjData A)

/-- **`U(ψ') = U(ψ) ∩ f^{-1}V`** for an affine open `V` of the base, as opens of `X`. -/
theorem image_coveringOpen_affineDatum_eq {V : S.Opens} (hV : IsAffineOpen V) :
    (f ⁻¹ᵁ V).ι ''ᵁ (P.affineDatum V).coveringOpen = P.coveringOpen ⊓ f ⁻¹ᵁ V :=
  (P.image_coveringOpen_affineDatum V).trans (P.coveringOpen_inf_preimage_eq hV).symm

/-- The inclusion `U(ψ') ⟶ U(ψ)` over `X`. -/
def affineDatumInclusion (V : S.affineOpens) :
    ((P.affineDatum V.1).coveringOpen).toScheme ⟶ P.coveringOpen.toScheme :=
  (P.pieceIso V.1 V.2).inv ≫ (P.toBase ⁻¹ᵁ V.1).ι

/-- The inclusion `U(ψ') ⟶ U(ψ)` composed with `U(ψ) ⟶ X` is the inclusion
`U(ψ') ⟶ f^{-1}V ⟶ X`. -/
theorem affineDatumInclusion_ι (V : S.affineOpens) :
    P.affineDatumInclusion V ≫ P.coveringOpen.ι
      = ((P.affineDatum V.1).coveringOpen).ι ≫ (f ⁻¹ᵁ V.1).ι := by
  rw [affineDatumInclusion, Category.assoc, ← P.pieceIso_comp_ι V.1 V.2, Iso.inv_hom_id_assoc]

/-- A morphism `U(ψ') ⟶ U(ψ)` over `X` is the inclusion. -/
theorem eq_affineDatumInclusion (V : S.affineOpens)
    {j : ((P.affineDatum V.1).coveringOpen).toScheme ⟶ P.coveringOpen.toScheme}
    (hj : j ≫ P.coveringOpen.ι = ((P.affineDatum V.1).coveringOpen).ι ≫ (f ⁻¹ᵁ V.1).ι) :
    j = P.affineDatumInclusion V :=
  (cancel_mono P.coveringOpen.ι).mp (hj.trans (P.affineDatumInclusion_ι V).symm)

/-- **Clause (3) of [Stacks, Tag 01O9], for the morphism**: over an affine open `V` of the base,
the restriction of `r_{ℒ,ψ}` along `U(ψ') ⟶ U(ψ)` is the morphism of [Stacks, Tag 01NK] for the
induced datum followed by the chart `i_V`. -/
theorem affineDatumInclusion_globalMorphism (V : S.affineOpens) :
    P.affineDatumInclusion V ≫ P.globalMorphism rp
      = (P.affineDatum V.1).glued ≫ rp.chart V.1 V.2 := by
  rw [affineDatumInclusion, Category.assoc, ← P.pieceLeg_comp_chart rp V]
  show (P.pieceIso V.1 V.2).inv ≫ ((P.pieceIso V.1 V.2).hom ≫ (P.affineDatum V.1).glued)
        ≫ rp.chart V.1 V.2 = _
  rw [Category.assoc, Iso.inv_hom_id_assoc]

/-- Clause (3) for the morphism, for any morphism `U(ψ') ⟶ U(ψ)` over `X`. -/
theorem comp_globalMorphism_eq (V : S.affineOpens)
    (j : ((P.affineDatum V.1).coveringOpen).toScheme ⟶ P.coveringOpen.toScheme)
    (hj : j ≫ P.coveringOpen.ι = ((P.affineDatum V.1).coveringOpen).ι ≫ (f ⁻¹ᵁ V.1).ι) :
    j ≫ P.globalMorphism rp = (P.affineDatum V.1).glued ≫ rp.chart V.1 V.2 := by
  rw [P.eq_affineDatumInclusion V hj, P.affineDatumInclusion_globalMorphism rp V]

/-- **Uniqueness**: a morphism `U(ψ) ⟶ Proj_S(𝒜)` whose restriction along `U(ψ') ⟶ U(ψ)` is
`i_V ∘ r_{ℒ|_{f^{-1}V}, ψ'}` for every affine open `V` of the base is `r_{ℒ,ψ}`. -/
theorem eq_globalMorphism_of_clauseThree {R : P.coveringOpen.toScheme ⟶ rp.scheme}
    (hR : ∀ V : S.affineOpens, P.affineDatumInclusion V ≫ R
      = (P.affineDatum V.1).glued ≫ rp.chart V.1 V.2) :
    R = P.globalMorphism rp := by
  refine P.eq_globalMorphism rp fun V => ?_
  have h := congrArg ((P.pieceIso V.1 V.2).hom ≫ ·) (hR V)
  simp only [affineDatumInclusion, Category.assoc, Iso.hom_inv_id_assoc] at h
  exact h.trans ((Category.assoc _ _ _).symm.trans (P.pieceLeg_comp_chart rp V)
    |>.trans (P.ι_globalMorphism rp V))

end GradedPowerMap

end Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism

end
