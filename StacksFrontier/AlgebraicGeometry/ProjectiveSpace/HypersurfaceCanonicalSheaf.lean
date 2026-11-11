module

public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.CanonicalSheaf
public import StacksFrontier.AlgebraicGeometry.Conormal.AdjunctionFormula
public import StacksFrontier.AlgebraicGeometry.ExternalTensorPullback.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.HypersurfaceCohomology

/-!
# Smooth hypersurfaces of degree `n + 1` in `ℙⁿ` have trivial canonical sheaf

Let `R` be a commutative ring, `P = ℙ^{m+2}_R` and `i : Z ⟶ P` an immersion with `Z` smooth of
relative dimension `m + 1` over `R`, whose conormal sheaf is `i^*𝒪(-m-3)` — for instance a
smooth hypersurface of degree `m + 3`. Then

`⋀^{m+1} Ω_{Z/R} ≅ 𝒪_Z`.

Indeed `⋀^{m+2} Ω_{P/R} ≅ 𝒪(-m-3)`
(`Stacks.AlgebraicGeometry.ProjEulerSequence.exteriorPowerRelativeDifferentialsIso`)
and the adjunction formula (`Stacks.Conormal.pullbackExteriorPowerIsoConormalTensor`) give
`i^*𝒪(-m-3) ≅ i^*𝒪(-m-3) ⊗ ⋀^{m+1} Ω_{Z/R}`, and `i^*𝒪(-m-3)` is invertible with inverse
`i^*𝒪(m+3)`.

## Main definitions

* `Stacks.ProjectiveSpace.pullbackTwistTensorPullbackTwistIsoUnit`:
  `i^*𝒪(a) ⊗ i^*𝒪(-a) ≅ 𝒪_Z`.
* `Stacks.ProjectiveSpace.exteriorPowerRelativeDifferentialsIsoUnitOfConormalIso`:
  **`⋀^{m+1} Ω_{Z/R} ≅ 𝒪_Z`** given `𝒞_{Z/P} ≅ i^*𝒪(-m-3)`.

## References

* [Stacks Project, Tag 0FMH](https://stacks.math.columbia.edu/tag/0FMH)
* [Stacks Project, Tag 0B38](https://stacks.math.columbia.edu/tag/0B38)
* [Stacks Project, Tag 06AA](https://stacks.math.columbia.edu/tag/06AA)
* [Stacks Project, Tag 01MT](https://stacks.math.columbia.edu/tag/01MT)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry.ProjectiveSpectrum.Proj (twistingSheaf)
open Stacks.AlgebraicGeometry.ProjPolyChart (polyGrading projToSpecCoeff)

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The tensor product sheaf of [Stacks, Tag 01CA] as a monoidal structure on the `𝒪_X`-modules
of a scheme, used here for its unitors and associator. -/
@[instance_reducible]
local instance Stacks.ProjectiveSpace.hypersurfaceCanonicalModulesMonoidal
    (X : AlgebraicGeometry.Scheme.{u}) : MonoidalCategory X.Modules :=
  Stacks.SheafOfModules.sheafTensorMonoidal X.sheaf.obj X.ringCatSheaf.property

namespace Stacks.ProjectiveSpace

variable {R : Type u} [CommRing R] {n : ℕ} {Z : Scheme.{u}}

/-- **`i^*𝒪(a) ⊗ i^*𝒪(-a) ≅ 𝒪_Z`** for a morphism `i : Z ⟶ ℙⁿ_R`: the pullback commutes with
the tensor product ([Stacks, Tag 01CD]), `𝒪(a) ⊗ 𝒪(-a) ≅ 𝒪(0) = 𝒪` ([Stacks, Tag 01MT]) and the
pullback of the structure sheaf is the structure sheaf. -/
def pullbackTwistTensorPullbackTwistIsoUnit
    (i : Z ⟶ _root_.AlgebraicGeometry.Proj (polyGrading R n)) (a : ℤ) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨Z.toRingedSpace.presheaf, Z.toRingedSpace.IsSheaf⟩).obj
          ((Scheme.Modules.pullback i).obj (twistingSheaf (polyGrading R n) a))).obj
            ((Scheme.Modules.pullback i).obj (twistingSheaf (polyGrading R n) (-a)))) ≅
      SheafOfModules.unit Z.ringCatSheaf :=
  (Stacks.Tag01VSPullbackTensor.schemePullbackTensorIso i _ _).symm ≪≫
    (Scheme.Modules.pullback i).mapIso
      (Stacks.AlgebraicGeometry.ProjTwistDegreeOneCover.twistMultiplicationIso (polyGrading R n)
          (Stacks.AlgebraicGeometry.ProjTwistRank.degreeOneCover_polyGrading R n) a (-a) ≪≫
        eqToIso (congrArg (twistingSheaf (polyGrading R n)) (add_neg_cancel a)) ≪≫
        Stacks.AlgebraicGeometry.ProjEulerSequence.twistingSheafZeroIsoUnit (polyGrading R n)) ≪≫
    pullbackObjUnitIsoUnit i

/-- **A smooth hypersurface of degree `m + 3` in `ℙ^{m+2}_R` has trivial canonical sheaf.** For
an immersion `i : Z ⟶ ℙ^{m+2}_R` with `Z` smooth of relative dimension `m + 1` over `R` and
conormal sheaf `𝒞_{Z/P} ≅ i^*𝒪(-m-3)`, `⋀^{m+1} Ω_{Z/R} ≅ 𝒪_Z`. -/
def exteriorPowerRelativeDifferentialsIsoUnitOfConormalIso {m : ℕ}
    (i : Z ⟶ _root_.AlgebraicGeometry.Proj (polyGrading R (m + 2))) [IsImmersion i]
    [SmoothOfRelativeDimension (m + 1) (i ≫ projToSpecCoeff R (m + 2))]
    (e : (Stacks.ConormalSequenceRight.conormalShortComplex i (projToSpecCoeff R (m + 2))).X₁ ≅
      (Scheme.Modules.pullback i).obj (twistingSheaf (polyGrading R (m + 2)) (-((m : ℤ) + 3)))) :
    Scheme.Modules.exteriorPower
        (Scheme.Hom.relativeDifferentials (i ≫ projToSpecCoeff R (m + 2))) ((m + 1 : ℕ) : ℤ) ≅
      SheafOfModules.unit Z.ringCatSheaf :=
  have := Stacks.AlgebraicGeometry.ProjPolyChart.smoothOfRelativeDimension_projToSpecCoeff R
    (m + 2)
  let A := (Scheme.Modules.pullback i).obj (twistingSheaf (polyGrading R (m + 2)) (-((m : ℤ) + 3)))
  let A' := (Scheme.Modules.pullback i).obj (twistingSheaf (polyGrading R (m + 2)) ((m : ℤ) + 3))
  let B := Scheme.Modules.exteriorPower
    (Scheme.Hom.relativeDifferentials (i ≫ projToSpecCoeff R (m + 2))) ((m + 1 : ℕ) : ℤ)
  let h : A ≅ A ⊗ B :=
    (Scheme.Modules.pullback i).mapIso
        (eqToIso (congrArg (twistingSheaf (polyGrading R (m + 2))) (by push_cast; ring)) ≪≫
          (Stacks.AlgebraicGeometry.ProjEulerSequence.exteriorPowerRelativeDifferentialsIso R
            (m + 2)).symm) ≪≫
      Stacks.Conormal.pullbackExteriorPowerIsoConormalTensor i (projToSpecCoeff R (m + 2)) m ≪≫
      whiskerRightIso e B
  let T : A' ⊗ A ≅ 𝟙_ Z.Modules :=
    pullbackTwistTensorPullbackTwistIsoUnit i ((m : ℤ) + 3)
  (λ_ B).symm ≪≫ whiskerRightIso T.symm B ≪≫ α_ A' A B ≪≫ whiskerLeftIso A' h.symm ≪≫ T

end Stacks.ProjectiveSpace

end
