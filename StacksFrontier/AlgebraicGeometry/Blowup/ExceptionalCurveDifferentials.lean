module

public import StacksFrontier.AlgebraicGeometry.Blowup.AdmissibleDominating
public import StacksFrontier.AlgebraicGeometry.Blowup.AffineBlowUpComparison
public import StacksFrontier.AlgebraicGeometry.Blowup.ExceptionalDifferentials
public import StacksFrontier.AlgebraicGeometry.Blowup.ProjectiveLineExceptional
public import StacksFrontier.AlgebraicGeometry.Blowup.ProjectivePushforwardTruncation
public import StacksFrontier.AlgebraicGeometry.Curves.GenusZeroPositiveDegree.ProjectiveLineProperties
public import StacksFrontier.AlgebraicGeometry.Curves.RiemannHurwitzDegree
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.ExceptionalCurve
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The differentials of the exceptional divisor of a blown-up regular surface are invertible

Let `(A, 𝔪, κ)` be a regular local ring of dimension two, let `b : X ⟶ S = Spec A` be the
blowing up of `S` in `𝔪` and let `E ⊆ X` be its exceptional divisor, with structure morphism
`E ⟶ Spec κ` over the centre. Then

`Ω_{E/κ}` is finite locally free of rank one.

The exceptional divisor is the projective line over the residue field, and the relative
differentials of a smooth curve over a field are invertible.

## Main results

* `Stacks.Blowup.exists_iso_projectiveLine_exceptionalToCentre`: `E` is isomorphic to `𝐏¹_κ`
  *over* `Spec κ` — the isomorphism carries the structure morphism of `𝐏¹_κ` to the structure
  morphism of `E` over the centre.
* `Stacks.Blowup.isCurve_exceptionalToCentre` and `Stacks.Blowup.smooth_exceptionalToCentre`:
  `E` is a smooth curve over `κ`.
* `Stacks.Blowup.isFiniteLocallyFreeOfRank_one_relativeDifferentials_exceptionalToCentre`:
  **`Ω_{E/κ}` is invertible.**

## The argument

Both `E` and `𝐏¹_κ` are the fibre of the blowup over the closed point of `Spec A`:

* `Stacks.Blowup.isPullback_exceptionalToCentre` exhibits `E` as `X ×_S Spec κ`, the projection
  to `Spec κ` being `Stacks.Blowup.exceptionalToCentre`;
* part (1) of [Stacks, Tag 0AGQ] exhibits `𝐏¹_κ = Proj κ[T₀, T₁]` as the same fibre, the
  projection to `Spec κ` being the structure morphism `Proj κ[T₀, T₁] ⟶ Spec κ`.

A fibre product is unique up to a unique isomorphism compatible with both projections, so the
resulting isomorphism `E ≅ 𝐏¹_κ` is one over `Spec κ`. That is the input missing from the bare
statement that `E ≅ 𝐏¹_κ`: an isomorphism of schemes alone says nothing about the differentials
*relative to `κ`*, whereas an isomorphism over `Spec κ` carries `Ω_{𝐏¹_κ/κ}` to `Ω_{E/κ}`.

With the isomorphism over `Spec κ` in hand, `E` is proper, integral and one-dimensional over `κ`
(`AlgebraicGeometry.isCurve_of_iso_projectiveLine`) and smooth over `κ`
(`AlgebraicGeometry.smooth_of_iso_projectiveLine`), so [Stacks, Tag 02G1] in the form
`AlgebraicGeometry.isFiniteLocallyFreeOfRank_one_relativeDifferentials` gives that `Ω_{E/κ}` is
finite locally free of rank one.

## Implementation notes

The two statements being joined are about different presentations of the blowup of `Spec A` in
`𝔪`: part (1) of [Stacks, Tag 0AGQ] is proved for `Stacks.Blowup.blowUpSpec 𝔪 = Proj (⨁ₙ 𝔪ⁿ)`,
the `Proj` of the Rees algebra of an ideal of a ring, while
`Stacks.Blowup.exceptionalToCentre` — and with it [Stacks, Tag 0B4L] and the twist dichotomy of
[Stacks, Tag 0B3T] — is phrased for `Stacks.Blowup.blowUp ℐ`, the `Proj` of the Rees algebra of a
quasi-coherent ideal sheaf. The two are isomorphic over `Spec A` by
`Stacks.Blowup.nonempty_over_iso_blowUpToBase` composed with `Stacks.Blowup.blowUpOverIso`, and
`Stacks.Blowup.nonempty_over_iso_blowUpToBase_residuePoint` records that comparison with the
centre written as the closed point `Spec κ ⟶ Spec A`. Composing the projection of the cartesian
square with that isomorphism moves the square from one presentation to the other; everything
after that happens on `Stacks.Blowup.blowUp`.

The two structure morphisms `Proj κ[T₀, …, Tₙ] ⟶ Spec κ` in the library,
`Stacks.Blowup.projSpaceToSpec` and `Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff`, are
the same morphism (`Stacks.Blowup.projSpaceToSpec_eq_projToSpecCoeff`); the first is the spelling
of [Stacks, Tag 0AGQ] and the second the spelling of the curve results.

## References

* [Stacks Project, Tag 0AGQ](https://stacks.math.columbia.edu/tag/0AGQ)
* [Stacks Project, Tag 02G1](https://stacks.math.columbia.edu/tag/02G1)
* [Stacks Project, Tag 0B4L](https://stacks.math.columbia.edu/tag/0B4L)
* [Stacks Project, Tag 01OG](https://stacks.math.columbia.edu/tag/01OG)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open Stacks.AlgebraicGeometry.ProjPolyChart (polyGrading projToSpecCoeff)

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace Stacks.Blowup

variable (A : Type u) [CommRing A] [IsRegularLocalRing A]

/-- **The two presentations of the blowup of a regular local ring in its maximal ideal agree over
`Spec A`**, with the centre written as the closed point `Spec κ ⟶ Spec A`.

`Stacks.Blowup.nonempty_over_iso_blowUpToBase` compares the `Proj` of the Rees algebra of the
ideal `𝔪` with the blowup of the quasi-coherent ideal sheaf `𝔪` generates, in the presentation
`AlgebraicGeometry.blowUp`; `Stacks.Blowup.blowUpOverIso` passes from that presentation to
`Stacks.Blowup.blowUp`, and
`AlgebraicGeometry.ker_residuePoint_eq_ofIdealTop_map` identifies the ideal sheaf with the kernel
of the closed point. -/
theorem nonempty_over_iso_blowUpToBase_residuePoint :
    Nonempty (Over.mk (toSpec (IsLocalRing.maximalIdeal A)) ≅
      Over.mk (Stacks.Blowup.blowUpToBase (residuePoint A).ker)) := by
  obtain ⟨e⟩ := nonempty_over_iso_blowUpToBase A (IsLocalRing.maximalIdeal A)
  rw [← AlgebraicGeometry.ker_residuePoint_eq_ofIdealTop_map] at e
  exact ⟨e ≪≫ (blowUpOverIso (residuePoint A).ker).symm⟩

variable (hdim : ringKrullDim A = 2)

include hdim in
/-- **The exceptional divisor of the blowup of a regular local surface is the projective line
over the residue field, over `Spec κ`.** There is an isomorphism
`E ≅ 𝐏¹_κ = Proj κ[T₀, T₁]` carrying the structure morphism of `𝐏¹_κ` over `Spec κ` to the
structure morphism `Stacks.Blowup.exceptionalToCentre` of `E` over the centre of the blowup.

Both schemes are the fibre of the blowup over the closed point: `E` by
`Stacks.Blowup.isPullback_exceptionalToCentre` and `𝐏¹_κ` by part (1) of [Stacks, Tag 0AGQ],
after the cartesian square of the latter has been moved to the presentation
`Stacks.Blowup.blowUp` of the blowup. A fibre product is unique up to a unique isomorphism
compatible with the projections, and the projections to `Spec κ` are the two structure
morphisms. -/
@[ega "IV 14.4.10" "special case",
  sga "6 VII 3.1" "special case",
  sga "7 X 2.2" "The curvetta of s"]
theorem exists_iso_projectiveLine_exceptionalToCentre :
    ∃ e : exceptionalDivisor (residuePoint A).ker ≅
        AlgebraicGeometry.Proj (polyGrading (IsLocalRing.ResidueField A) 1),
      e.hom ≫ projToSpecCoeff (IsLocalRing.ResidueField A) 1 =
        exceptionalToCentre (residuePoint A) := by
  obtain ⟨r, -, -, s, hsq, -⟩ :=
    exists_isClosedImmersion_isPullback_projectiveLine_blowUpSpec_maximalIdeal A hdim
  obtain ⟨β⟩ := nonempty_over_iso_blowUpToBase_residuePoint A
  have hβ : β.hom.left ≫ Stacks.Blowup.blowUpToBase (residuePoint A).ker =
      toSpec (IsLocalRing.maximalIdeal A) := Over.w β.hom
  have hsq' : IsPullback (s ≫ β.hom.left)
      (projSpaceToSpec (IsLocalRing.ResidueField A) 2)
      (Stacks.Blowup.blowUpToBase (residuePoint A).ker) (residuePoint A) :=
    hsq.of_iso (Iso.refl _) ((Over.forget _).mapIso β) (Iso.refl _) (Iso.refl _)
      (by simp) (by simp) (by simpa using hβ.symm) (by simp [residuePoint])
  refine ⟨(isPullback_exceptionalToCentre (residuePoint A)).isoIsPullback _ _ hsq', ?_⟩
  rw [← projSpaceToSpec_eq_projToSpecCoeff (IsLocalRing.ResidueField A) 1]
  exact (isPullback_exceptionalToCentre (residuePoint A)).isoIsPullback_hom_snd _ _ hsq'

include hdim in
/-- **The exceptional divisor of the blowup of a regular local surface is integral**: it is the
projective line over the residue field. -/
theorem isIntegral_exceptionalDivisor_residuePoint :
    IsIntegral (exceptionalDivisor (residuePoint A).ker) := by
  obtain ⟨e, -⟩ := exists_iso_projectiveLine_exceptionalToCentre A hdim
  have := Stacks.AlgebraicGeometry.ProjPolyChart.isIntegral_proj
    (IsLocalRing.ResidueField A) 1
  have : Nonempty (exceptionalDivisor (residuePoint A).ker) :=
    ⟨e.inv (Nonempty.some inferInstance)⟩
  exact isIntegral_of_isOpenImmersion e.hom

include hdim in
/-- **The exceptional divisor of the blowup of a regular local surface is a curve over the
residue field**: it is the projective line over `κ`, over `Spec κ`. -/
theorem isCurve_exceptionalToCentre :
    IsCurve (IsLocalRing.ResidueField A) (exceptionalToCentre (residuePoint A)) := by
  obtain ⟨e, he⟩ := exists_iso_projectiveLine_exceptionalToCentre A hdim
  exact AlgebraicGeometry.isCurve_of_iso_projectiveLine _ e he

include hdim in
/-- **The exceptional divisor of the blowup of a regular local surface is smooth over the
residue field**: it is the projective line over `κ`, over `Spec κ`. -/
theorem smooth_exceptionalToCentre :
    Smooth (exceptionalToCentre (residuePoint A)) := by
  obtain ⟨e, he⟩ := exists_iso_projectiveLine_exceptionalToCentre A hdim
  exact AlgebraicGeometry.smooth_of_iso_projectiveLine _ e he

include hdim in
/-- **`Ω_{E/κ}` is invertible.** Let `(A, 𝔪, κ)` be a regular local ring of dimension two, let
`b : X ⟶ Spec A` be the blowing up of `Spec A` in `𝔪` and let `E` be its exceptional divisor,
with structure morphism `E ⟶ Spec κ` over the centre. Then the relative differentials `Ω_{E/κ}`
are finite locally free of rank one.

`E` is the projective line over `κ`, over `Spec κ`, hence a smooth curve over `κ`, and the sheaf
of differentials of a smooth curve over a field is invertible ([Stacks, Tag 02G1]).

This is the hypothesis `s = 1` of the twist dichotomy for a point blowup: the case in which the
exceptional divisor is a curve, so that the bound of [Stacks, Tag 0B3T] reads `k ≤ 1`. -/
theorem isFiniteLocallyFreeOfRank_one_relativeDifferentials_exceptionalToCentre :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (Scheme.Hom.relativeDifferentials (exceptionalToCentre (residuePoint A))) 1 := by
  have := isCurve_exceptionalToCentre A hdim
  have := smooth_exceptionalToCentre A hdim
  exact AlgebraicGeometry.isFiniteLocallyFreeOfRank_one_relativeDifferentials
    (exceptionalToCentre (residuePoint A))

end Stacks.Blowup

end
