module

public import StacksFrontier.AlgebraicGeometry.Modules.ExteriorPowerDeterminant
public import StacksFrontier.AlgebraicGeometry.ProjEulerSequence.Exactness
public import StacksFrontier.AlgebraicGeometry.ProjTwistRank.Basic
public import StacksFrontier.AlgebraicGeometry.ProjChartKernel.Basic
public import StacksFrontier.AlgebraicGeometry.ProjTwistDegreeOneCover.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.SmoothOfRelativeDimension
public import StacksFrontier.AlgebraicGeometry.Different.TheDifferent.SmoothFormula
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.MonoidalInduced

/-!
# The canonical sheaf of projective space

Let `R` be a commutative ring and `X = ℙⁿ_R = Proj R[T₀, …, Tₙ]`. Then

`⋀ⁿ Ω_{X/R} ≅ 𝒪_X(-n-1)`.

The proof takes determinants in the Euler sequence `0 ⟶ Ω_{X/R} ⟶ 𝒪(-1)^{⊕ (n+1)} ⟶ 𝒪_X ⟶ 0`
of [Stacks, Tag 0FMH]: by [Stacks, Tag 0B38] `⋀ⁿ Ω ⊗ ⋀¹ 𝒪 ≅ ⋀ⁿ⁺¹(𝒪(-1)^{⊕ (n+1)})`, and the
top exterior power of `𝒪(-1)^{⊕ (m+1)}` is `𝒪(-m-1)`, by induction on `m` along the split
sequences `0 ⟶ 𝒪(-1) ⟶ 𝒪(-1)^{⊕ (m+2)} ⟶ 𝒪(-1)^{⊕ (m+1)} ⟶ 0` and the multiplication
`𝒪(-1) ⊗ 𝒪(-m-1) ≅ 𝒪(-m-2)` of [Stacks, Tag 01MT].

## Main definitions

* `Stacks.AlgebraicGeometry.ProjEulerSequence.exteriorPowerBiproductTwistIso`:
  `⋀^{m+1}(𝒪(-1)^{⊕ (m+1)}) ≅ 𝒪(-m-1)`.
* `Stacks.AlgebraicGeometry.ProjEulerSequence.exteriorPowerRelativeDifferentialsIso`:
  **`⋀ⁿ Ω_{ℙⁿ_R/R} ≅ 𝒪(-n-1)`**.

## References

* [Stacks Project, Tag 0FMH](https://stacks.math.columbia.edu/tag/0FMH)
* [Stacks Project, Tag 0B38](https://stacks.math.columbia.edu/tag/0B38)
* [Stacks Project, Tag 01MT](https://stacks.math.columbia.edu/tag/01MT)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry.ProjectiveSpectrum.Proj (twistingSheaf)
open Stacks.AlgebraicGeometry.ProjPolyChart (polyGrading projToSpecCoeff)

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The tensor product sheaf of [Stacks, Tag 01CA] as a monoidal structure on the `𝒪_X`-modules
of a scheme, used here only for its unitors. -/
@[instance_reducible]
local instance Stacks.AlgebraicGeometry.ProjEulerSequence.canonicalSheafModulesMonoidal
    (X : AlgebraicGeometry.Scheme.{u}) : MonoidalCategory X.Modules :=
  Stacks.SheafOfModules.sheafTensorMonoidal X.sheaf.obj X.ringCatSheaf.property

namespace Stacks.AlgebraicGeometry.ProjEulerSequence

variable (R : Type u) [CommRing R] (n : ℕ)

/-- **`⋀^{m+1}(𝒪(-1)^{⊕ (m+1)}) ≅ 𝒪(-m-1)`** on `ℙⁿ_R`: induction on `m`, along the split
sequences `0 ⟶ 𝒪(-1) ⟶ 𝒪(-1)^{⊕ (m+2)} ⟶ 𝒪(-1)^{⊕ (m+1)} ⟶ 0` and the multiplication
`𝒪(-1) ⊗ 𝒪(-m-1) ≅ 𝒪(-m-2)`. -/
def exteriorPowerBiproductTwistIso : (m : ℕ) →
    Scheme.Modules.exteriorPower (X := _root_.AlgebraicGeometry.Proj (polyGrading R n))
        (⨁ fun _ : Fin (m + 1) =>
          AlgebraicGeometry.ProjectiveSpectrum.Proj.twistingSheafModule (polyGrading R n) (-1))
        ((m + 1 : ℕ) : ℤ) ≅
      twistingSheaf (polyGrading R n) (-((m + 1 : ℕ) : ℤ))
  | 0 =>
    Scheme.Modules.exteriorPowerOneIsoSelf _ ≪≫ Scheme.Modules.biproductFinOneIso _
  | m + 1 =>
    (Scheme.Modules.exteriorPowerBiproductSuccIso
        (X := _root_.AlgebraicGeometry.Proj (polyGrading R n))
        (AlgebraicGeometry.ProjectiveSpectrum.Proj.twistingSheafModule (polyGrading R n) (-1)) m
        (hL := ProjTwistRank.isFiniteLocallyFreeOfRank_twistingSheaf R n (-1))).symm ≪≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor _).obj _).mapIso
        (exteriorPowerBiproductTwistIso m) ≪≫
      ProjTwistDegreeOneCover.twistMultiplicationIso (polyGrading R n)
        (ProjTwistRank.degreeOneCover_polyGrading R n) (-1) (-((m + 1 : ℕ) : ℤ)) ≪≫
      eqToIso (congrArg (twistingSheaf (polyGrading R n)) (by push_cast; ring))

/-- **The canonical sheaf of projective space: `⋀ⁿ Ω_{ℙⁿ_R/R} ≅ 𝒪(-n-1)`.** The determinant
of the Euler sequence `0 ⟶ Ω ⟶ 𝒪(-1)^{⊕ (n+1)} ⟶ 𝒪 ⟶ 0` ([Stacks, Tags 0FMH and 0B38]) gives
`⋀ⁿ Ω ⊗ ⋀¹ 𝒪 ≅ ⋀ⁿ⁺¹(𝒪(-1)^{⊕ (n+1)})`, and the right side is `𝒪(-n-1)`
(`exteriorPowerBiproductTwistIso`). -/
def exteriorPowerRelativeDifferentialsIso :
    Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials (projToSpecCoeff R n))
        (n : ℤ) ≅
      twistingSheaf (polyGrading R n) (-((n : ℤ) + 1)) :=
  have := ProjPolyChart.smoothOfRelativeDimension_projToSpecCoeff R n
  (ρ_ _).symm ≪≫
    (whiskerLeftIso _ (Scheme.Modules.exteriorPowerOneIsoSelf _)).symm ≪≫
    (Scheme.Modules.exteriorPowerTensorExteriorPowerIso (eulerFirstArrow R n)
      (eulerSurjection R n) (eulerFirstArrow_comp_eulerSurjection R n)
      (shortExact_eulerSequence R n) n 0
      (hE' := Stacks.Discriminant.isFiniteLocallyFreeOfRank_relativeDifferentials
        (projToSpecCoeff R n) n)
      (hE'' := ProjTwistRank.isFiniteLocallyFreeOfRank_unit R n) :) ≪≫
    exteriorPowerBiproductTwistIso R n n ≪≫
    eqToIso (congrArg (twistingSheaf (polyGrading R n)) (by push_cast; ring))

/-- **`⋀ⁿ Ω_{ℙⁿ_R/R} ≅ 𝒪(-n-1)`**, at the spelling `twistingSheafModule` of the twist. -/
theorem nonempty_exteriorPower_relativeDifferentials_iso_twistingSheafModule :
    Nonempty (Scheme.Modules.exteriorPower
        (Scheme.Hom.relativeDifferentials (projToSpecCoeff R n)) (n : ℤ) ≅
      AlgebraicGeometry.ProjectiveSpectrum.Proj.twistingSheafModule (polyGrading R n)
        (-((n : ℤ) + 1))) :=
  ⟨exteriorPowerRelativeDifferentialsIso R n⟩

end Stacks.AlgebraicGeometry.ProjEulerSequence

end
