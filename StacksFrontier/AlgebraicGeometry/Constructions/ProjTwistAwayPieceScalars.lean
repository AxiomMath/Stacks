module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjConeTwistStandardOpenMul
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjStandardOpenScalars
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjTwistAwayPiece

/-!
# The identification `Γ(D₊(f), 𝒪_X(n)) ≅ (A_f)_n` respects scalars and products

Let `A = ⨁_{n ≥ 0} 𝒜 n` be a graded ring and `f ∈ 𝒜 k` homogeneous of positive degree.
`Stacks.AlgebraicGeometry.ProjTwistAwayPiece.sectionsTwistEquivGradedPiece` identifies the sections
of `𝒪_{Proj 𝒜}(n)` over the standard open `D₊(f)` with the degree-`n` piece of the graded
localization `A_f`. This identification is semilinear for the action of `Γ(D₊(f), 𝒪_X)` and
multiplicative.

## Main results

* `Stacks.AlgebraicGeometry.ProjTwistAwayPiece.coe_sectionsTwistEquivGradedPiece_smul`: the
  identification is semilinear for the action of `Γ(D₊(f), 𝒪_X)` read through
  `AlgebraicGeometry.ProjectiveSpectrum.Proj.awayToSection`.
* `Stacks.AlgebraicGeometry.ProjTwistAwayPiece.coe_sectionsTwistEquivGradedPiece_mul`: the
  product of a section of `𝒪_X(i)` and one of `𝒪_X(j)` has for underlying element the product of
  theirs.

## References

* [Stacks Project, Tag 01MN](https://stacks.math.columbia.edu/tag/01MN)
* [Stacks Project, Tag 0EKG](https://stacks.math.columbia.edu/tag/0EKG)
* [Stacks Project, Tag 01NK](https://stacks.math.columbia.edu/tag/01NK)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj (integerGrading twistingSheaf)
open Stacks.GradedLocalization (gradedPiece)
open scoped Stacks.GradedLocalization

universe u w

attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
attribute [local instance_reducible] ProjectiveSpectrum.top

namespace Stacks.AlgebraicGeometry.ProjTwistAwayPiece

variable {σ : Type w} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜] {f : A} {k : ℕ}

/-- The identification `Γ(D₊(f), 𝒪_X(n)) ≅ (A_f)_n` is semilinear for the action of
`Γ(D₊(f), 𝒪_X)` read through `AlgebraicGeometry.ProjectiveSpectrum.Proj.awayToSection`: a section
scaled by the fraction `r` has for underlying element the product of `r.val` with the underlying
element of the section. -/
@[stacks 01MN "part (1), the scalar action in the description of the sections of a twist over a \
standard open as a homogeneous piece of the graded localization, written out on the underlying \
elements of the localization"]
theorem coe_sectionsTwistEquivGradedPiece_smul (hf : f ∈ 𝒜 k) (hk : 0 < k) (n : ℤ)
    (r : HomogeneousLocalization.Away 𝒜 f)
    (s : (twistingSheaf 𝒜 n).val.obj (op (ProjectiveSpectrum.basicOpen 𝒜 f))) :
    ((sectionsTwistEquivGradedPiece 𝒜 hf hk n
        ((ProjectiveSpectrum.Proj.awayToSection 𝒜 f).hom r • s) :
      LocalizedModule.Away f A)) =
      HomogeneousLocalization.val r •
        ((sectionsTwistEquivGradedPiece 𝒜 hf hk n s : LocalizedModule.Away f A)) :=
  Stacks.ProjectiveCohomology.coe_sectionsTwistEquivAwayGrading_smul 𝒜 hf hk n r s

section Mul

variable {A : Type u} {σ : Type w} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜] {f : A} {k : ℕ}

/-- The identification `Γ(D₊(f), 𝒪_X(n)) ≅ (A_f)_n` is multiplicative: the product of a section
of `𝒪_X(i)` and a section of `𝒪_X(j)` over `D₊(f)`, read in `(A_f)_{i + j}`, is the product in
`A_f` of the two underlying elements. -/
@[stacks 0EKG "the description of the sections of a twisting sheaf over a standard open as a \
homogeneous piece of the graded localization is multiplicative"]
theorem coe_sectionsTwistEquivGradedPiece_mul (hf : f ∈ 𝒜 k) (hk : 0 < k) (i j : ℤ)
    (x : (twistingSheaf 𝒜 i).val.obj (op (ProjectiveSpectrum.basicOpen 𝒜 f)))
    (y : (twistingSheaf 𝒜 j).val.obj (op (ProjectiveSpectrum.basicOpen 𝒜 f))) :
    ((sectionsTwistEquivGradedPiece 𝒜 hf hk (i + j)
          (Stacks.AlgebraicGeometry.ProjConeTwist.twistMulSection 𝒜 i j
            (op (ProjectiveSpectrum.basicOpen 𝒜 f)) x y) :
        LocalizedModule.Away f A))
      = (sectionsTwistEquivGradedPiece 𝒜 hf hk i x : LocalizedModule.Away f A) *
        (sectionsTwistEquivGradedPiece 𝒜 hf hk j y : LocalizedModule.Away f A) :=
  Stacks.AlgebraicGeometry.ProjConeTwist.coe_sectionsTwistEquivAwayGrading_mul 𝒜 hf hk i j x y

end Mul

end Stacks.AlgebraicGeometry.ProjTwistAwayPiece

end
