module

public import StacksFrontier.AlgebraicGeometry.Blowup.ExceptionalDivisorCentreBundleTwist
public import StacksFrontier.AlgebraicGeometry.DeRham.BlowupExceptionalBoundaryLift
public import StacksFrontier.AlgebraicGeometry.DeRham.FirstChernClass.PicardFirstChernClass
public import StacksFrontier.AlgebraicGeometry.DeRham.LerayHirsch.ProjectiveBundleFibreBasis
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ChernClasses.SourceChernSetup

/-!
# The first Chern class of `𝒪_{X'}(-E)|_E` is the pullback of that of `𝒪_{𝐏(𝒞)}(1)`

Let `φ : E ≅ 𝐏(𝒞)` be the identification of the exceptional divisor of the blowing up of `X` along
a centre `Z` smooth over `S` with the projective bundle of the conormal sheaf of the centre, over
`Z` (`Stacks.AlgebraicGeometry.exceptionalDivisorIsoCentreBundle`). Since `φ^*𝒪_{𝐏(𝒞)}(1)` is
`𝒪_{X'}(-E)|_E` (`Stacks.AlgebraicGeometry.exceptionalDivisorIsoCentreBundle_twistIso`), the de
Rham pullback along `φ` carries `c₁^{dR}(𝒪_{𝐏(𝒞)}(1))` to `c₁^{dR}(𝒪_{X'}(-E)|_E)`, both read
relative to `S`.

## Main results

* `Stacks.DeRham.BlowupTriangle.deRhamPullbackSquare_centreBundleChernClass`.

## References

* [Stacks Project, Tag 0FUW](https://stacks.math.columbia.edu/tag/0FUW)
* [Stacks Project, Tag 0FUT](https://stacks.math.columbia.edu/tag/0FUT)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Stacks.AlgebraicGeometry
open Stacks.RelativeProj (projectiveBundleToBase tautologicalDatumTwist)

universe u

namespace Stacks.DeRham.BlowupTriangle

variable {S X Z : Scheme.{u}} (f : X ⟶ S) (i : Z ⟶ X) [IsClosedImmersion i] [Smooth f]
  [Smooth (i ≫ f)]

/-- The identification `φ : E ≅ 𝐏(𝒞)` lies over `S`. -/
theorem exceptionalDivisorIsoCentreBundle_hom_comp_structure :
    (exceptionalDivisorIsoCentreBundle f i).hom ≫
        (projectiveBundleToBase Z (centreConormal i) ≫ i ≫ f) =
      exceptionalStructure f i ≫ 𝟙 S := by
  rw [Category.comp_id, ← Category.assoc, exceptionalDivisorIsoCentreBundle_hom_toBase]

/-- **The de Rham pullback along `φ : E ≅ 𝐏(𝒞)` carries `c₁^{dR}(𝒪_{𝐏(𝒞)}(1))` to
`c₁^{dR}(𝒪_{X'}(-E)|_E)`**, relative to `S`. -/
theorem deRhamPullbackSquare_centreBundleChernClass :
    Stacks.DeRhamBaseChange.deRhamPullbackSquare (exceptionalDivisorIsoCentreBundle f i).hom
        (exceptionalStructure f i) (projectiveBundleToBase Z (centreConormal i) ≫ i ≫ f) (𝟙 S)
        (exceptionalDivisorIsoCentreBundle_hom_comp_structure f i) 2
        (DeRhamLerayHirsch.projectiveBundleChernClass (i ≫ f) (centreConormal i)) =
      SheafOfModules.deRhamCohomologyFirstChernClass
        (X := (Stacks.Blowup.exceptionalDivisor i.ker).toRingedSpace)
        (Scheme.Hom.deRhamAlgebras (exceptionalStructure f i))
        (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras (exceptionalStructure f i)))
        (exceptionalSituation f i).L
        (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ (exceptionalSituation f i).L
          (exceptionalSituation f i).invertible) := by
  rw [Stacks.ProjectiveBundleDeRham.projectiveBundleChernClass_eq_deRhamFirstChernClassPicard,
    Stacks.DeRhamBaseChange.deRhamPullbackSquare_deRhamFirstChernClassPicard,
    ← Stacks.ProjectiveBundleDeRham.deRhamCohomologyFirstChernClass_eq_deRhamFirstChernClassPicard
      (exceptionalStructure f i) (exceptionalSituation f i).L (exceptionalSituation f i).invertible]
  exact congrArg (Stacks.DeRhamBaseChange.deRhamFirstChernClassPicard (exceptionalStructure f i))
    (Stacks.WeilCohomology.picardClassOf_eq_of_iso _ _ _ _ _
      (exceptionalDivisorIsoCentreBundle_twistIso f i))

end Stacks.DeRham.BlowupTriangle

end
