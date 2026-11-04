module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjConeTwistPresentation
public import StacksFrontier.AlgebraicGeometry.SectionRingProjIso.TwistComparison
public import StacksFrontier.AlgebraicGeometry.TwistTensor.RelativeLaurentComparison

/-!
# Situation 01QH as an isomorphism of graded algebras, modulo one hypothesis

Let `𝓛` be an ample invertible `𝒪_X`-module, `A = Γ_*(X, 𝓛)` its section ring and
`r : X ⟶ Proj A` the canonical morphism of [Stacks, Tag 01PZ]. Assuming that the twist
multiplications `𝒪(i) ⊗ 𝒪(j) ⟶ 𝒪(i + j)` of `Proj A` become isomorphisms after pullback along
`r`, this file constructs the comparison `r^*(⨁_{n ∈ ℤ} 𝒪_{Proj A}(n)) ≅ ⨁_{n ∈ ℤ} 𝓛^{⊗ n}` of
Situation [Stacks, Tag 01QH] as an isomorphism of sheaves of `ℤ`-graded `𝒪_X`-algebras.

## Main definitions

* `Stacks.SectionRingProjIso.pbTwistGradedAlgebra`: `r^*(⨁_{n ∈ ℤ} 𝒪_{Proj A}(n))`, the pullback
  along the canonical morphism of the graded algebra of all integral twists, whose degree-`n`
  piece is `Stacks.SectionRingVeroneseChart.pbTwist`.
* `Stacks.SectionRingProjIso.gradedTwistComparison`: the isomorphism of sheaves of `ℤ`-graded
  `𝒪_X`-algebras `r^*(⨁_{n ∈ ℤ} 𝒪_{Proj A}(n)) ≅ ⨁_{n ∈ ℤ} 𝓛^{⊗ n}`, under the hypothesis on the
  twist multiplications above.

## Main results

* `Stacks.SectionRingProjIso.gradedTwistComparison_hom_app`: the degreewise components of
  `gradedTwistComparison` are `Stacks.AlgebraicGeometry.GradedLaurentRecognition.pieceIso`.

## References

* [Stacks Project, Tag 01QH](https://stacks.math.columbia.edu/tag/01QH)
* [Stacks Project, Tag 01QI](https://stacks.math.columbia.edu/tag/01QI)
* [Stacks Project, Tag 01O1](https://stacks.math.columbia.edu/tag/01O1)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 0EKG](https://stacks.math.columbia.edu/tag/0EKG)
* [Stacks Project, Tag 0EKI](https://stacks.math.columbia.edu/tag/0EKI)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open Stacks.RingedSpace
open Stacks.Ample (IsInvertibleModule)
open Stacks.AmpleFiniteAvoidance (grading)
open Stacks.AlgebraicGeometry.ProjConeTwist (integerTwistAlgebra)
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf (laurent isSheafStruct)
open Stacks.SectionRingProjMorphism (projHomOfIsAmple)
open Stacks.SectionRingVeroneseChart (pbTwist degreeOneIso isInvertibleModule_pbTwist)

universe u

namespace Stacks.SectionRingProjIso

section Monoidal

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.SectionRingGeometric.schemePreadditive
  Stacks.SectionRingGeometric.schemeTensorRightAdditive

variable {X : Scheme.{u}} (L : X.Modules) [IsInvertibleModule X L]

/-- The pullback `r^*(⨁_{n ∈ ℤ} 𝒪_{Proj A}(n))`, along the canonical morphism `r` of Stacks Tag
01PZ, of the graded algebra of all integral twists of `Proj A`, for `A = Γ_*(X, 𝓛)` the section
ring of an ample invertible module `𝓛`. -/
def pbTwistGradedAlgebra (hL : Stacks.Ample.IsAmple X L) :
    SheafOfModules.GradedAlgebra.{u, u} X.ringCatSheaf :=
  pullbackGradedAlgebra (projHomOfIsAmple L hL).toLRSHom.toShHom (integerTwistAlgebra (grading L))

/-- The degree-`n` piece of `r^*(⨁_{n ∈ ℤ} 𝒪_{Proj A}(n))` is the `n`-th pulled-back twist, on
the nose. -/
@[simp] theorem pbTwistGradedAlgebra_piece (hL : Stacks.Ample.IsAmple X L) (n : ℤ) :
    (pbTwistGradedAlgebra L hL).piece n = pbTwist L hL n := rfl

/-- The isomorphism of sheaves of `ℤ`-graded `𝒪_X`-algebras

`r^*(⨁_{n ∈ ℤ} 𝒪_{Proj A}(n)) ≅ ⨁_{n ∈ ℤ} 𝓛^{⊗ n}`,

for `𝓛` an ample invertible `𝒪_X`-module, `A = Γ_*(X, 𝓛)` and `r` the canonical morphism of
Stacks Tag 01PZ, under the hypothesis `hmul` that the twist multiplications of `Proj A` become
isomorphisms after pullback along `r`. -/
def gradedTwistComparison (hL : Stacks.Ample.IsAmple X L)
    (hmul : ∀ i j : ℤ, IsIso ((pullbackFunctor (projHomOfIsAmple L hL).toLRSHom.toShHom).map
      (SheafOfModules.GradedAlgebra.mulSheaf (integerTwistAlgebra (grading L)) i j))) :
    letI : Stacks.SheafOfModules.IsInvertible X.toRingedSpace.presheaf (isSheafStruct X) L :=
      Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ inferInstance
    pbTwistGradedAlgebra L hL ≅ laurent L :=
  letI : Stacks.SheafOfModules.IsInvertible X.toRingedSpace.presheaf (isSheafStruct X) L :=
    Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ inferInstance
  Stacks.AlgebraicGeometry.GradedLaurentRecognition.gradedIso (pbTwistGradedAlgebra L hL) L
    (degreeOneIso L hL)
    (fun i j => isIso_mulSheaf_pullbackGradedAlgebra_of_isIso_map _ _ i j (hmul i j))
    (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _
      (isInvertibleModule_pbTwist L hL 0))

/-- The degreewise components of the graded comparison are the recognition theorem's
`Stacks.AlgebraicGeometry.GradedLaurentRecognition.pieceIso`. -/
theorem gradedTwistComparison_hom_app (hL : Stacks.Ample.IsAmple X L)
    (hmul : ∀ i j : ℤ, IsIso ((pullbackFunctor (projHomOfIsAmple L hL).toLRSHom.toShHom).map
      (SheafOfModules.GradedAlgebra.mulSheaf (integerTwistAlgebra (grading L)) i j)))
    (n : ℤ) :
    letI : Stacks.SheafOfModules.IsInvertible X.toRingedSpace.presheaf (isSheafStruct X) L :=
      Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ inferInstance
    (gradedTwistComparison L hL hmul).hom.app n =
      (Stacks.AlgebraicGeometry.GradedLaurentRecognition.pieceIso (pbTwistGradedAlgebra L hL) L
        (degreeOneIso L hL)
        (fun i j => isIso_mulSheaf_pullbackGradedAlgebra_of_isIso_map _ _ i j (hmul i j))
        (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _
          (isInvertibleModule_pbTwist L hL 0)) n).hom :=
  rfl

end Monoidal

end Stacks.SectionRingProjIso

end
