module

public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyPicardAmpleLocusOpen

/-!
# Every family of curves is smooth locally polarized (the smoothness half of Stacks 0DQ0)

This file states the smoothness half of Stacks 0DQ0 in the one shape its consumers ask for:
`∀ X : CurveFamily B hZ, X.IsSmoothLocallyPolarized`. That is the `hpol` input of
`CurveFamily.exists_etale_isPullback_isProjectiveMorphism_of_isSmoothLocallyPolarized` (Stacks
0E6F), of
`AlgebraicGeometry.CurveFamily.exists_isOpen_isStructureContraction_of_isSmoothLocallyPolarized`
(Stacks 0E88) and of the Noetherian-diagonal results of
`StacksFrontier.AlgebraicGeometry.Quot.CurvesDiagonalNoetherianPolarizedOf` and
`StacksFrontier.AlgebraicGeometry.Quot.CurvesDiagonalPolarizedReduction`. Each of those consumers
quantifies over *all* families of curves, so the quantified form is what they can be applied to,
and it is not available from the single-family lemma
`AlgebraicGeometry.CurveFamily.isSmoothLocallyPolarized_of_picardCharts` without also quantifying
its chart input; that is what this file does.

Everything in the source's argument other than that one input is proved. Reading the base change
`PolarizedCurves ×_{𝒞urves} T` as the ample locus of `Picardstack_{X/T}` is
`AlgebraicGeometry.Space.PicardObject.IsInAmpleLocus`; that the ample locus meets the fibre over
every point of `T` — the surjectivity step, Stacks 0ADD followed by Stacks 09NZ and Stacks 01VK,
and the passage of the resulting module from the representing scheme to the algebraic space — is
`AlgebraicGeometry.CurveFamily.exists_picardObject_isInAmpleLocus_of_point`, with no hypothesis;
the passage from an ample module on the space-level base change to the scheme-level cartesian
square that `AlgebraicGeometry.CurveFamily.IsSmoothLocallyPolarized` asks for is
`AlgebraicGeometry.CurveFamily.isSmoothLocallyPolarized_of`.

The openness step of the source's proof, Stacks 0D3D, is a theorem of the library, so it is
discharged here: `AlgebraicGeometry.CurveFamily.exists_isOpenImmersion_isInAmpleLocus_of_point`
supplies the `hopen` input of
`AlgebraicGeometry.CurveFamily.isSmoothLocallyPolarized_of_picardCharts`.

One input remains:

* `hchart` stands for Stacks 0D04 (with Stacks 09DS) and Stacks 0DPJ: `Picardstack_{X/T}` is an
  algebraic stack and is smooth over `T`, so through every field-valued object of it there is a
  chart `π : T' ⟶ T` which is smooth, carrying an object `A` over `T'` whose pullback along a
  field-valued point `y` of `T'` over the given one is again in the ample locus.

Its shape is a **guess**, since none of those tags is stated in the library yet; it is
the shape of the `hchart` input of
`AlgebraicGeometry.CurveFamily.isSmoothLocallyPolarized_of_picardCharts`, quantified over the
family. Note that `Picardstack_{X/T}` becomes an object of
`AlgebraicGeometry.Stack.AlgebraicStacks` only once Stacks 0D04 is a theorem, since membership in
that 2-category *is* `AlgebraicGeometry.Stack.IsAlgebraicStack`. So Stacks 0DPJ cannot be phrased
here as smoothness, in the sense of Stacks 075U, of the 1-morphism `Picardstack_{X/T} ⟶ T`: that
statement does not typecheck before Stacks 0D04. The input is therefore phrased on objects of the
Picard stack (`AlgebraicGeometry.Space.PicardObject`) only, which is all the argument uses.
The coherence datum `AlgebraicGeometry.Space.modulePushforwardCoherence` that
`AlgebraicGeometry.Space.picardCFG` takes is itself a theorem of the library, so it is not what
blocks the 1-morphism phrasing.

No tag is registered in this file: Stacks 0DQ0 is a statement about the 1-morphism
`PolarizedCurves ⟶ 𝒞urves`, whose surjectivity half is
`AlgebraicGeometry.isSurjective_polarizedCurvesToCurvesAlgebraic_of` and whose smoothness half, in
the sense of Stacks 075U, needs a smooth diagram for that 1-morphism; the statement below is what
the source's smoothness half says about a single family.

## Main results

* `AlgebraicGeometry.CurveFamily.isSmoothLocallyPolarized`.

## References

* [Stacks Project, Tag 0DQ0](https://stacks.math.columbia.edu/tag/0DQ0)
* [Stacks Project, Tag 0D04](https://stacks.math.columbia.edu/tag/0D04)
* [Stacks Project, Tag 09DS](https://stacks.math.columbia.edu/tag/09DS)
* [Stacks Project, Tag 0DPJ](https://stacks.math.columbia.edu/tag/0DPJ)
* [Stacks Project, Tag 0D3D](https://stacks.math.columbia.edu/tag/0D3D)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.CurveFamily

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

/-- **Every family of curves is smooth locally polarized** — the smoothness half of Stacks 0DQ0,
in the quantified shape that Stacks 0E6F, Stacks 0E88 and the Noetherian-diagonal results consume
as their `hpol` input.

One input remains, the one tag of the source's proof that the library lacks, quantified over the
family of curves:

* `hchart` (Stacks 0D04 with Stacks 09DS, and Stacks 0DPJ): for every object `A₀` of the ample
  locus of `Picardstack_{X/T}` over a field-valued point `x` of the base there are a smooth
  `π : T' ⟶ T`, an object `A` over `T'`, a field-valued point `y` of `T'` lying over `x` through a
  field extension `e`, and the fact that the pullback of `A` along `y` is in the ample locus.

Its shape is a guess, pending statements of those tags. Openness of the ample locus, Stacks
0D3D, is proved, and enters as
`AlgebraicGeometry.CurveFamily.exists_isOpenImmersion_isInAmpleLocus_of_point`; everything else
the source's argument needs is proved too: see the module documentation. -/
theorem isSmoothLocallyPolarized
    (hchart : ∀ (X : CurveFamily B hZ) (K : Type u) (_ : Field K)
      (hK : B.Contains (Spec (.of K)))
      (x : (schemeOverIntegers B).obj (B.obj hK) ⟶ X.base)
      (A₀ : Space.PicardObject X.picardSituation), A₀.T = X.picardTestScheme x →
        A₀.IsInAmpleLocus →
        ∃ (T' : BigFppfOver B integerBase hZ) (π : T' ⟶ X.base),
          Smooth ((BigFppfOver.toScheme B integerBase hZ).map π) ∧
          ∃ (A : Space.PicardObject X.picardSituation) (hA : A.T = X.picardTestScheme π)
            (K' : Type u) (_ : Field K') (hK' : B.Contains (Spec (.of K')))
            (y : (schemeOverIntegers B).obj (B.obj hK') ⟶ T')
            (e : (schemeOverIntegers B).obj (B.obj hK') ⟶ (schemeOverIntegers B).obj (B.obj hK)),
            y ≫ π = e ≫ x ∧
            (Space.PicardSituation.pullbackObject A
              (X.picardTestSchemeMap y π ≫ eqToHom hA.symm)).IsInAmpleLocus) :
    ∀ X : CurveFamily B hZ, X.IsSmoothLocallyPolarized :=
  fun X => isSmoothLocallyPolarized_of_picardCharts X (hchart X)
    fun T' π A hA K' hK'f hK' y hy =>
      exists_isOpenImmersion_isInAmpleLocus_of_point X T' π A hA K' hK'f hK' y hy

end AlgebraicGeometry.CurveFamily

end
