module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.RelativePseudoCoherenceOfPerfect
public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.StageTransitionCounitCompatibility
public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.StageTensorSectionsTransitionCompatibility

/-!
# [Stacks, Tag 0CX7]: `K = R lim_{D_QCoh} Fₙ` is pseudo-coherent relative to `A`

In Situation [Stacks, Tag 0CX4] let `K = DQ_X(L)` be the object of [Stacks, Tag 0CX5], for a
coherator `DQ_X` and a derived limit `L = R lim_{D(𝒪_X)} Fₙ`. Then `K` is pseudo-coherent relative
to `A`.

## Main results

* `AlgebraicGeometry.Space.FlatSheafExistenceSituation.isRelativelyPseudoCoherent_coheratorObj`.

## References

* [Stacks Project, Tag 0CX7](https://stacks.math.columbia.edu/tag/0CX7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

universe u

namespace AlgebraicGeometry.Space

namespace FlatSheafExistenceSituation

variable (D : FlatSheafExistenceSituation.{u})

/-- **[Stacks, Tag 0CX7].** In Situation [Stacks, Tag 0CX4] let `K = DQ_X(L)` be as in
[Stacks, Tag 0CX5]: `DQ_X` is a coherator (`adj : ι ⊣ DQ_X`, the right adjoint of the inclusion
`D_QCoh(𝒪_X) ⟶ D(𝒪_X)`) and `L` is a derived limit `R lim_{D(𝒪_X)} Fₙ` of the system `(iₙ,* Fₙ)`.
Then `K` is pseudo-coherent relative to `A`. -/
@[stacks 0CX7 "the full statement: for every coherator DQ_X and every derived limit L of (F_n) in \
D(O_X), the K = DQ_X(L) of 0CX5 is pseudo-coherent relative to A; nothing is granted or assumed"]
theorem isRelativelyPseudoCoherent_coheratorObj
    {DQ : spaceDerivedCategory D.B D.S D.containsLimitBase D.X.left ⥤
      (spaceQuasicoherentProp D.B D.S D.containsLimitBase D.X.left).FullSubcategory}
    (adj : (spaceQuasicoherentProp D.B D.S D.containsLimitBase D.X.left).ι ⊣ DQ)
    (L : spaceDerivedCategory D.B D.S D.containsLimitBase D.X.left)
    (hL : IsDerivedLimit D.derivedSystem L) :
    IsRelativelyPseudoCoherent D.B D.S D.containsLimitBase D.X.left.1 D.X.left.2 D.X.hom.hom
      D.isLocallyOfFiniteType_structureMorphism (D.coheratorObj DQ L) :=
  D.isRelativelyPseudoCoherent_coheratorObj_of_transitionCompatible adj L hL
    (fun n => D.stageTransitionCounitCompatible n)
    (fun E n => D.stageTensorSectionsTransitionCompatible n E)

end FlatSheafExistenceSituation

end AlgebraicGeometry.Space

end
