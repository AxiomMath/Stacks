module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjTwistGradedPieces
public import StacksFrontier.AlgebraicGeometry.ProjStalkGlobalSections.GlobalSections
public import StacksFrontier.AlgebraicGeometry.ProjectiveCohomology.TwistSections
public import StacksFrontier.AlgebraicGeometry.RelativeProjTwists.DegreeSection

/-!
# The sections of a twist over a standard open are a graded piece of one localization

Let `A = ⨁_{n ≥ 0} 𝒜 n` be a graded ring and `f ∈ 𝒜 k` homogeneous of positive degree. This
file identifies the sections of `𝒪_{Proj 𝒜}(n)` over the standard open `D₊(f)` with the degree-`n`
piece `Stacks.GradedLocalization.gradedPiece` of the graded localization `A_f`,

  `Γ(D₊(f), 𝒪_X(n)) ≅ (A_f)_n`,

and computes this isomorphism on the global sections of [Stacks, Tag 01MP].

## Main definitions

* `Stacks.AlgebraicGeometry.ProjTwistAwayPiece.awayGradingEquivGradedPiece`: the subgroup
  `Stacks.ProjectiveCohomology.awayGrading` of single fractions `a / f ^ m` of degree `n` and the
  degree-`n` piece of `A_f`, identified by the identity of `A_f`.
* `Stacks.AlgebraicGeometry.ProjTwistAwayPiece.sectionsTwistEquivGradedPiece`: the sections of
  `𝒪_X(n)` over `D₊(f)` are the degree-`n` piece of `A_f`.

## Main results

* `Stacks.AlgebraicGeometry.ProjTwistAwayPiece.coe_sectionsTwistEquivGradedPiece_degreeSection`:
  the degree-`n` section of a homogeneous `a ∈ 𝒜 n` is the fraction `a / 1` on every standard
  open of positive degree.

## References

* [Stacks Project, Tag 01M6](https://stacks.math.columbia.edu/tag/01M6)
* [Stacks Project, Tag 01MN](https://stacks.math.columbia.edu/tag/01MN)
* [Stacks Project, Tag 01MP](https://stacks.math.columbia.edu/tag/01MP)
* [Stacks Project, Tag 01M7](https://stacks.math.columbia.edu/tag/01M7)
* [Stacks Project, Tag 01NK](https://stacks.math.columbia.edu/tag/01NK)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj (integerGrading twistGrading twistingSheaf
  degreeZeroFraction degreeZeroLocalization_twistGrading_eq)
open Stacks.AlgebraicGeometry.ProjStalkGlobalSections (degreeZeroToGlobalSections_basicOpen)
open Stacks.AlgebraicGeometry.ProjTwistSections (mem_twistGrading_zero)
open AlgebraicGeometry.ProjectiveSpectrum.Proj (degreeSection)
open Stacks.GradedLocalization (gradedPiece)
open Stacks.ProjectiveCohomology (awayGrading sectionsTwistEquivAwayGrading
  coe_sectionsTwistEquivAwayGrading mem_degreeZeroLocalization_twistGrading_iff)
open scoped Stacks.GradedLocalization

universe u w

namespace Stacks.AlgebraicGeometry.ProjTwistAwayPiece

variable {σ : Type w} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜] {f : A} {k : ℕ}

/-- The subgroup `Stacks.ProjectiveCohomology.awayGrading` of single fractions of degree `n` and
the degree-`n` graded piece of `A_f` are isomorphic through the identity of `A_f`. -/
def awayGradingEquivGradedPiece (hf : f ∈ 𝒜 k) (n : ℤ) :
    awayGrading 𝒜 hf n ≃+ gradedPiece 𝒜 (integerGrading (S := A) 𝒜) f n where
  toFun z := ⟨z.1, (degreeZeroLocalization_twistGrading_eq 𝒜 hf n z.1).1
    ((mem_degreeZeroLocalization_twistGrading_iff 𝒜 hf n z.1).2 z.2)⟩
  invFun y := ⟨y.1, (mem_degreeZeroLocalization_twistGrading_iff 𝒜 hf n y.1).1
    ((degreeZeroLocalization_twistGrading_eq 𝒜 hf n y.1).2 y.2)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- The sections of `𝒪_X(n)` over the standard open `D₊(f)` are isomorphic to the degree-`n`
graded piece of the localization `A_f`. -/
def sectionsTwistEquivGradedPiece (hf : f ∈ 𝒜 k) (hk : 0 < k) (n : ℤ) :
    ((twistingSheaf 𝒜 n).val.obj (op (ProjectiveSpectrum.basicOpen 𝒜 f)))
      ≃+ gradedPiece 𝒜 (integerGrading (S := A) 𝒜) f n :=
  (sectionsTwistEquivAwayGrading 𝒜 hf hk n).trans (awayGradingEquivGradedPiece 𝒜 hf n)

/-- The fraction in `A_f` that `sectionsTwistEquivGradedPiece` attaches to a section is the one
`Stacks.ProjectiveCohomology.sectionsTwistEquivAwayGrading` attaches to it. -/
theorem coe_sectionsTwistEquivGradedPiece (hf : f ∈ 𝒜 k) (hk : 0 < k) (n : ℤ)
    (s : (twistingSheaf 𝒜 n).val.obj (op (ProjectiveSpectrum.basicOpen 𝒜 f))) :
    ((sectionsTwistEquivGradedPiece 𝒜 hf hk n s : LocalizedModule.Away f A))
      = (sectionsTwistEquivAwayGrading 𝒜 hf hk n s : LocalizedModule.Away f A) :=
  rfl

/-- The degree-`n` section of a homogeneous element `a ∈ 𝒜 n`, restricted to the standard open
`D₊(f)` of a homogeneous `f` of positive degree, is the fraction `a / 1`. -/
theorem coe_sectionsTwistEquivGradedPiece_degreeSection (hf : f ∈ 𝒜 k) (hk : 0 < k) (n : ℕ)
    (a : 𝒜 n) :
    ((sectionsTwistEquivGradedPiece 𝒜 hf hk (n : ℤ)
        ((twistingSheaf 𝒜 (n : ℤ)).val.map
          (homOfLE (le_top : ProjectiveSpectrum.basicOpen 𝒜 f ≤ ⊤)).op
          (degreeSection 𝒜 n a)) : LocalizedModule.Away f A))
      = LocalizedModule.mk (a : A) (1 : Submonoid.powers f) := by
  have h := degreeZeroToGlobalSections_basicOpen 𝒜 (twistGrading (S := A) 𝒜 (n : ℤ)) hf hk
    ⟨(a : A), mem_twistGrading_zero 𝒜 a⟩
  refine (congrArg (fun z : GradedModuleDegreeZeroLocalization 𝒜
    (twistGrading (S := A) 𝒜 (n : ℤ)) f => (z : LocalizedModule.Away f A)) h).trans ?_
  simp only [degreeZeroFraction]
  exact congrArg (LocalizedModule.mk (a : A)) (Subtype.ext (pow_zero f))

end Stacks.AlgebraicGeometry.ProjTwistAwayPiece

end
