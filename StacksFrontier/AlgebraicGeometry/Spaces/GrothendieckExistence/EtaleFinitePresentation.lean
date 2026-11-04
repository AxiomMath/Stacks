module

public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.DerivedLimitBounded
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparationMorphismProperties

/-!
# An étale quasi-compact quasi-separated space over `X` is of finite presentation over `A`

In Situation [Stacks, Tag 0CX4] the algebraic space `X` is of finite presentation over `A`. If
`j : U ⟶ X` is étale and `U` is quasi-compact and quasi-separated, then `U` is of finite
presentation over `A`: `j` is locally of finite presentation, being étale, the composite
`U ⟶ X ⟶ Spec A` is locally of finite presentation and quasi-compact as a composite of such
morphisms, and it is quasi-separated because `U` is. This is the hypothesis under which
[Stacks, Tag 0CRW] applies to `j`, in the proof of [Stacks, Tag 0CX8].

## Main results

* `AlgebraicGeometry.Space.FlatSheafExistenceSituation.isFinitePresentation_comp_hom_of_isEtale`
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

namespace FlatSheafExistenceSituation

variable (D : FlatSheafExistenceSituation.{u})

/-- **An étale quasi-compact quasi-separated `U` over `X` is of finite presentation over `A`.** -/
theorem isFinitePresentation_comp_hom_of_isEtale {U : AlgebraicSpaces D.B D.S D.containsLimitBase}
    (j : U ⟶ D.X.left) (hj : IsEtale D.B D.S D.containsLimitBase j.hom)
    (hUqc : IsQuasiCompactSpace D.B D.S D.containsLimitBase U.1)
    (hUqs : IsAbsolutelyQuasiSeparated D.B D.S D.containsLimitBase D.B.contains_terminal U.1) :
    IsFinitePresentation D.B D.S D.containsLimitBase (j ≫ D.X.hom).hom :=
  ⟨isLocallyOfFinitePresentation_comp D.B D.S D.containsLimitBase U.2 D.X.left.2
      (schemeSpace (limitBaseObject D.system D.B D.containsLimitBase)).2 j.hom D.X.hom.hom
      (isLocallyOfFinitePresentation_of_isEtale D.B D.S D.containsLimitBase hj)
      D.finitePresentation.1,
    isQuasiCompact_comp D.B D.S D.containsLimitBase D.X.left.2
      (schemeSpace (limitBaseObject D.system D.B D.containsLimitBase)).2 j.hom D.X.hom.hom
      (isQuasiCompact_of_isQuasiCompactSpace D.B D.S D.containsLimitBase D.B.contains_terminal
        D.X.left.2 D.isAbsolutelyQuasiSeparated hUqc j.hom)
      D.finitePresentation.2.1,
    isQuasiSeparated_of_isAbsolutelyQuasiSeparated_source D.B D.S D.containsLimitBase
      D.B.contains_terminal U.2 hUqs _⟩

end FlatSheafExistenceSituation

end AlgebraicGeometry.Space

end
