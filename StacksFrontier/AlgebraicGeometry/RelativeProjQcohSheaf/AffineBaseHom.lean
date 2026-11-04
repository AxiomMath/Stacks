module

public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.AffineQuadrupleRoundTrip

/-!
# The classifying morphism of [Stacks, Tag 01NU] lies over the quadruple's own base morphism

Let `S` be an affine scheme, `𝒜` a graded `𝒪_S`-algebra with quasi-coherent homogeneous pieces
(Situation 01NN), `d ≥ 1` and `A = Γ(S, 𝒜)`. A quadruple `(d, f : T ⟶ S, L, ψ)` of Section 01NS
classifies a morphism `T ⟶ U_d` into the open of Equation 27.12.0.1 inside `Proj A`
(`...RelativeProjQcohSheaf.Quadruple.classifyingHom`). This file proves that **composing it with
the structure morphism `U_d ⟶ Proj A ⟶ Spec A_0 ⟶ S` returns `f`**.

This is the compatibility demanded by the dependent sum `Σ (f : T ⟶ S)` of
`...RelativeProjQcohSheaf.Fd`. It is the composite of
`...ProjTripleDegreeZeroScalar.toProj_comp_toSpecZero_structureMorphism`, which says the
morphism classified by a triple, followed by `Proj A ⟶ Spec A_0 ⟶ S`, is the morphism determined
by the triple's degree-zero ring map, and
`...RelativeProjQcohSheaf.AffineTripleSections.structureHom_veroneseSections`, which says that for
the triple induced by a quadruple that morphism is the quadruple's own `f`.

## Main results

* `...RelativeProjQcohSheaf.Quadruple.toProj_classifyingHom_comp_toSpecZero` and
  `...RelativeProjQcohSheaf.Quadruple.toProj_classifyingHomOfClass_comp_toSpecZero`: **the
  classifying morphism of a quadruple, resp. of a strict equivalence class, lies over the
  recorded morphism to the base.**

## References

* [Stacks Project, Tag 01NU](https://stacks.math.columbia.edu/tag/01NU)
* [Stacks Project, Tag 01N8](https://stacks.math.columbia.edu/tag/01N8)
* [Stacks Project, Tag 01I1](https://stacks.math.columbia.edu/tag/01I1)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry
open Stacks.AlgebraicGeometry.MorphismsIntoProj (toProj)
open Stacks.AlgebraicGeometry.RelativeProjBridge

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

variable {S T : Scheme.{u}} {B : SheafGradedAlgebra S} {k : ℕ} {f : T ⟶ S}

/-- **The classifying morphism of a quadruple lies over the quadruple's own base morphism.**
Over an affine base, the morphism `T ⟶ U_d` that [Stacks, Tag 01NU] attaches to a quadruple
`(d, f, L, ψ)`, followed by the structure morphism `U_d ⟶ Proj Γ(S, 𝒜) ⟶ Spec A_0 ⟶ S`, is
`f`. -/
theorem Quadruple.toProj_classifyingHom_comp_toSpecZero [IsAffine S] (hk : 0 < k)
    (hqc : ∀ n : ℤ, ((situationAlgebra B).piece n).IsQuasicoherent)
    (Q : Quadruple f (situationAlgebra B) (k : ℤ)) :
    toProj (B.grading (⊤ : S.Opens)) (Quadruple.classifyingHom hk hqc Q)
        ≫ AlgebraicGeometry.Proj.toSpecZero (B.grading (⊤ : S.Opens))
        ≫ Spec.map (AffineTripleSections.structureRingHom B) ≫ S.isoSpec.inv
      = f := by
  have h := Quadruple.iSup_nonvanishingOpen_psiSection_eq_top hqc Q
  exact (ProjTripleDegreeZeroScalar.toProj_comp_toSpecZero_structureMorphism
      (𝒜 := B.grading (⊤ : S.Opens)) (ψ := veroneseSections Q.twisting)
      (AffineTripleSections.toFun_zero_eq_unitGlobal B (veroneseSections Q.twisting) h)
      (AffineTripleSections.structureRingHom B) hk h
      (ProjTripleClassifying.isCompatible_classifyingPair (B.grading (⊤ : S.Opens)) hk
        (veroneseSections Q.twisting) h)).trans
    (AffineTripleSections.structureHom_veroneseSections (B := B) Q.twisting h)

/-- **The classifying morphism of a strict equivalence class lies over the class's own base
morphism**, which is `Quadruple.toProj_classifyingHom_comp_toSpecZero` on the quotient. -/
theorem Quadruple.toProj_classifyingHomOfClass_comp_toSpecZero [IsAffine S] (hk : 0 < k)
    (hqc : ∀ n : ℤ, ((situationAlgebra B).piece n).IsQuasicoherent)
    (ξ : Fd (situationAlgebra B) (k : ℤ) T) :
    toProj (B.grading (⊤ : S.Opens)) (Quadruple.classifyingHomOfClass hk hqc ξ.2)
        ≫ AlgebraicGeometry.Proj.toSpecZero (B.grading (⊤ : S.Opens))
        ≫ Spec.map (AffineTripleSections.structureRingHom B) ≫ S.isoSpec.inv
      = ξ.1 := by
  obtain ⟨g, cls⟩ := ξ
  induction cls using Quotient.ind with
  | _ Q => exact Quadruple.toProj_classifyingHom_comp_toSpecZero hk hqc Q

end Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

end
