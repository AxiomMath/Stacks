module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.CoequalizerGlueingTowerAdicBound
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.ProperKernelPairSheafDescent

/-!
# Glueing a proper modification back along a closed subspace, unconditionally

In the situation of Stacks 0AGH (`AlgebraicGeometry.Space.CoequalizerGlueSituation`): `X` is a
locally Noetherian algebraic space over a scheme `S`, `Z ⟶ X` a closed immersion with
complementary open subspace `U`, and `f : X' ⟶ X` a proper morphism which is an isomorphism
over `U`. The library proves Stacks 0AGI, 0AGK and the reading 0AGL of 0AGK from the conclusion
`AlgebraicGeometry.Space.ProperKernelPairCoequalizers` of Stacks 0AGG. Stacks 0AGG is the theorem
`AlgebraicGeometry.Space.properKernelPairCoequalizers_holds`, so all three hold with nothing
assumed beyond the source's hypotheses.

## Main results

* `AlgebraicGeometry.Space.CoequalizerGlueSituation.exists_glueCoequalizer`: **Stacks 0AGI**.
* `AlgebraicGeometry.Space.CoequalizerGlueSituation.exists_factorsThroughSection`:
  **Stacks 0AGK**.
* `AlgebraicGeometry.Space.CoequalizerGlueSituation.exists_isEssentiallyConstantWith`:
  **Stacks 0AGL**.

## References

* [Stacks Project, Tag 0AGH](https://stacks.math.columbia.edu/tag/0AGH)
* [Stacks Project, Tag 0AGI](https://stacks.math.columbia.edu/tag/0AGI)
* [Stacks Project, Tag 0AGJ](https://stacks.math.columbia.edu/tag/0AGJ)
* [Stacks Project, Tag 0AGK](https://stacks.math.columbia.edu/tag/0AGK)
* [Stacks Project, Tag 0AGL](https://stacks.math.columbia.edu/tag/0AGL)
* [Stacks Project, Tag 05PU](https://stacks.math.columbia.edu/tag/05PU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

namespace CoequalizerGlueSituation

variable (T : CoequalizerGlueSituation.{u})

/-- **Stacks 0AGI.** In Situation 0AGH (`X` locally Noetherian over `S`, `Z ⟶ X` a closed
immersion with complementary open `U`, `f : X' ⟶ X` proper and an isomorphism over `U`), let
`Y = X' ⨿ Z` and `R = Y ×_X Y` with projections `s, t : R ⟶ Y`. There exists a coequalizer `X₁`
of `s, t` in the category of algebraic spaces over `S`; the morphism `X₁ ⟶ X` is finite and a
universal homeomorphism, it is an isomorphism over `U` (its base change along `U ⟶ X` is an
isomorphism), and `Z ⟶ X` lifts to `X₁`. Everything is proved: Stacks 0AGG is
`AlgebraicGeometry.Space.properKernelPairCoequalizers_holds`. -/
@[stacks 0AGI]
theorem exists_glueCoequalizer :
    ∃ D : KernelPairCoequalizer T.B T.S T.hS T.glueMap,
      IsFinite T.B T.S T.hS D.toTarget.hom ∧
      UniversalHomeomorphism T.B T.S T.hS D.toTarget.hom ∧
      IsIso (pullback.snd D.toTarget.hom T.U.ι) ∧
      ∃ l : T.closedSpace ⟶ D.space, l ≫ D.toTarget = ObjectProperty.homMk T.i :=
  T.exists_glueCoequalizer_of_properKernelPairCoequalizers
    (properKernelPairCoequalizers_holds T.B T.S T.hS)

/-- **Stacks 0AGK.** In Situation 0AGH assume `X` quasi-compact. Let `Z_n` be the infinitesimal
neighbourhoods of `Z` in `X` and `X_n` the coequalizers of the kernel pairs of
`X' ⨿ Z_n ⟶ X`, forming the tower `X_1 ⟶ X_2 ⟶ X_3 ⟶ … ⟶ X` of Stacks 0AGJ (for any choice
`D` of these coequalizers, which exist by Stacks 0AGI). Then for all `n` large enough there is
an `m` such that `X_n ⟶ X_{n+m}` factors through a closed immersion `X ⟶ X_{n+m}`; the closed
immersion is moreover a section of `X_{n+m} ⟶ X`. Everything is proved: Stacks 0AGG is
`AlgebraicGeometry.Space.properKernelPairCoequalizers_holds`. -/
@[stacks 0AGK]
theorem exists_factorsThroughSection (hqc : IsQuasiCompactSpace T.B T.S T.hS T.X)
    (D : ∀ n, KernelPairCoequalizer T.B T.S T.hS (T.neighbourhoodSystem.glueMapAt n)) :
    ∃ n₀, ∀ n, n₀ ≤ n → ∃ m, T.neighbourhoodSystem.FactorsThroughSection D n m :=
  T.exists_factorsThroughSection_of_properKernelPairCoequalizers
    (properKernelPairCoequalizers_holds T.B T.S T.hS) hqc D

/-- **Stacks 0AGL.** In Situation 0AGH with `X` quasi-compact, the system
`X_1 ⟶ X_2 ⟶ X_3 ⟶ …` of Stacks 0AGJ (for any choice `D` of the coequalizers) is essentially
constant with value `X` in the sense of Stacks 05PU, with respect to the cocone of the morphisms
`X_n ⟶ X`. Everything is proved: Stacks 0AGG is
`AlgebraicGeometry.Space.properKernelPairCoequalizers_holds`. -/
@[stacks 0AGL]
theorem exists_isEssentiallyConstantWith (hqc : IsQuasiCompactSpace T.B T.S T.hS T.X)
    (D : ∀ n, KernelPairCoequalizer T.B T.S T.hS (T.neighbourhoodSystem.glueMapAt n)) :
    ∃ (i : ℕ) (r : T.targetSpace ⟶ (D i).space),
      CategoryTheory.EssentiallyConstantInd.IsEssentiallyConstantWith
        (T.neighbourhoodSystem.towerDiagram D)
        (T.neighbourhoodSystem.towerCocone D) i r :=
  T.exists_isEssentiallyConstantWith_of_properKernelPairCoequalizers
    (properKernelPairCoequalizers_holds T.B T.S T.hS) hqc D

end CoequalizerGlueSituation

end AlgebraicGeometry.Space

end
