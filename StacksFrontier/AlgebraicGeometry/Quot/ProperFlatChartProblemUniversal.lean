module

public import StacksFrontier.AlgebraicGeometry.Quot.ProperFlatChartProblem
public import StacksFrontier.Deformation.ToposThickening.PrescribedMapUniversal

/-!
# The prescribed map of `problemOnChart` is universal

Let `x = (X → Spec A)` be an object of `Spaces'_{fp, flat, proper}` over an affine chart and `D`
a square-zero thickening `Spec A ⊂ Spec A'` of Situation 07YX. The prescribed map
`c : f⁻¹𝒥 ⟶ 𝒪_X ⊗_A I` of the extension problem `problemOnChart x hx D` (posed over `Spec A`, on
the model of the small étale site of `X`) is universal: every `f⁻¹𝒪_{Spec A}`-linear map
`f⁻¹𝒥 ⟶ M` to an `𝒪_X`-module factors uniquely as `c` followed by an `𝒪_X`-linear map
`𝒪_X ⊗_A I ⟶ M`. On the small étale site, `c` is the unit of extension of scalars along `f♯`
(Stacks 03CZ).

## Main results

* `AlgebraicGeometry.Space.FlatThickeningDeformation.problem_prescribedMapUniversal`: the
  prescribed map of the problem of a flat deformation is universal.
* `AlgebraicGeometry.Space.ProperFlatLift.problemOnChart_prescribedMapUniversal`: the prescribed
  map of `problemOnChart x hx D` is universal.

## References

* [Stacks Project, Tag 03CZ](https://stacks.math.columbia.edu/tag/03CZ)
* [Stacks Project, Tag 08V3](https://stacks.math.columbia.edu/tag/08V3)
* [Stacks Project, Remark 0D1P](https://stacks.math.columbia.edu/tag/0D1P)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPushforward (inverseImageCommRingFunctor)

universe u

/- The global instance `Abelian (SheafOfModules.{max u v r w} O)` leaves a stuck universe
constraint against the `𝒪_X`-modules at the universe of the schemes. -/
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace AlgebraicGeometry.Space.FlatThickeningDeformation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {Y' : AlgebraicSpaces B S hS} {Z : ClosedSubspaces B S hS Y'.1}
  (hZ : IsFirstOrderThickening B S hS Y' Z.1)

/-- The prescribed map of the problem of a flat deformation is universal: it is the unit of
extension of scalars along `g♯` (Stacks 03CZ). -/
theorem problem_prescribedMapUniversal {X₁ : AlgebraicSpaces B S hS}
    (g : X₁ ⟶ (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS)) :
    (problem g hZ).PrescribedMapUniversal :=
  bijective_problem_c hZ g

end AlgebraicGeometry.Space.FlatThickeningDeformation

namespace AlgebraicGeometry.Space.ProperFlatLift

open Deformation.Artin Deformation.ToposThickening

attribute [local instance] restrictedFirstOrderExtension_isContinuous

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {A : Type u} [CommRing A] {toS : Spec (.of A) ⟶ S} {hA : B.Contains (Spec (.of A))}
  (x : CartesianProperFlatSpaces B S hS)
  (hx : (cartesianProperFlatProjection B S hS).obj x = algebraOver A B S hS toS hA)
  {A' : Type u} [CommRing A'] (D : SquareZeroThickening A B S hS toS hA A')

/-- The extension problem of `x` along `D` on the small étale site of `X`, for the morphism
`X → Spec A ≅ Z`. -/
abbrev chartEtaleProblem :=
  FlatThickeningDeformation.problem (chartStructureMap x hx ≫ (chartRangeIso D).hom)
    (isFirstOrderThickening_squareZeroSubspace B S hS D.arrow (isSquareZeroClosedImmersion_arrow D))

/-- **The prescribed map of `problemOnChart` is universal**: every `f⁻¹𝒪_{Spec A}`-linear map from
the ideal to an `𝒪_X`-module factors uniquely through `c : f⁻¹𝒥 ⟶ 𝒪_X ⊗_A I`. -/
theorem problemOnChart_prescribedMapUniversal :
    (problemOnChart x hx D).PrescribedMapUniversal := by
  have h₁ : (chartModelProblem x hx D).PrescribedMapUniversal :=
    RingedToposExtensionProblem.prescribedMapUniversal_siteTransport
      (X := smallEtaleRingedTopos B S hS x.obj.obj.left)
      (smallEtaleModelTopology B S hS x.obj.obj.left.1) (smallEtaleModelEquiv B S hS x.obj.obj.left)
      (chartEtaleProblem x hx D) (FlatThickeningDeformation.problem_prescribedMapUniversal
        (isFirstOrderThickening_squareZeroSubspace B S hS D.arrow
          (isSquareZeroClosedImmersion_arrow D)) _)
  unfold problemOnChart
  exact RingedToposExtensionProblem.prescribedMapUniversal_rebase (X := modelTopos x.obj.obj.left)
    (B₁ := smallEtaleRingedTopos B S hS
      (⟨(baseSubspace D.arrow (isSquareZeroClosedImmersion_arrow D)).1.toFunctor,
        (baseSubspace D.arrow (isSquareZeroClosedImmersion_arrow D)).2.1⟩ : AlgebraicSpaces B S hS))
    (B₂ := smallEtaleRingedTopos B S hS (schemeSpace (algebraOver A B S hS toS hA)))
    (chartModelProblem x hx D) _ _ _ _ _ _ _ _ _ h₁

end AlgebraicGeometry.Space.ProperFlatLift

end
