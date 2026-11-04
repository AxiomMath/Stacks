module

public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilySmoothLocallyPolarizedOf
public import StacksFrontier.AlgebraicGeometry.Quot.PicardStack

/-!
# The ample locus of the Picard stack of a family of curves (the smoothness half of Stacks 0DQ0)

The smoothness half of the proof of Stacks 0DQ0 reads the base change of
`PolarizedCurves ⟶ 𝒞urves` along a family of curves `X ⟶ T` as a substack of the Picard stack
`Picardstack_{X/T}` of Stacks 0372:
`PolarizedCurves ×_{𝒞urves} T ⊂ Picardstack_{X/T}`.
The substack is the one of objects `(T', b, ℒ)` whose module `ℒ` is ample on `X_{T'}/T'`.

This file states that substack over the library's own Picard stack. The Picard situation of a
family of curves is `AlgebraicGeometry.CurveFamily.picardSituation`. A smooth test scheme
`π : T' ⟶ T` is read as a test scheme of that situation by
`AlgebraicGeometry.CurveFamily.picardTestScheme`. An object of the Picard stack is in the ample
locus when it satisfies `AlgebraicGeometry.Space.PicardObject.IsInAmpleLocus`: its module is
ample relative to the projection `X_{T'} ⟶ T'` in the sense of Stacks 0D31.

`AlgebraicGeometry.CurveFamily.isSmoothLocallyPolarized_of_picard` reduces the predicate
`AlgebraicGeometry.CurveFamily.IsSmoothLocallyPolarized`, which Stacks 0E6F and Stacks 0E88
consume, to one statement about the Picard stack: through every point of the base, the ample locus
has an object over a smooth test scheme. In the source this statement holds for three reasons:
* `Picardstack_{X/T}` is algebraic (Stacks 0D04, from Stacks 09DS) and smooth over `T`
  (Stacks 0DPJ), so it has smooth charts that are smooth over `T`;
* the ample locus is open (Stacks 0D3D);
* the ample locus meets every fibre, which is the surjectivity half
  (`AlgebraicGeometry.isSurjectiveOnObjects_polarizedCurvesSquare_snd`).
The input `hpic` is that statement. Its shape is a **guess**, since none of 0D04, 09DS and 0DPJ
is stated in the library yet; 0D3D is a theorem of the library
(`AlgebraicGeometry.Space.exists_isOpenSubspace_factors_iff_isRelativelyAmple_of_isProper`). The
proof here supplies the base change: the base change square of the Picard situation is the
cartesian square that the predicate asks for.

The Picard stack's identities and composition take a `ModulePushforwardCoherence` input. Only
objects of the Picard stack are used here, never its morphisms, so that input does not appear.

No tag is registered in this file.

## Main definitions

* `AlgebraicGeometry.CurveFamily.picardSituation`: the Picard situation of a family of curves.
* `AlgebraicGeometry.CurveFamily.picardTestScheme`: a morphism of the site into the base, as a
  test scheme of that situation.
* `AlgebraicGeometry.Space.PicardObject.IsInAmpleLocus`: the ample locus of the Picard stack.

## Main results

* `AlgebraicGeometry.CurveFamily.isSmoothLocallyPolarized_of_picard`.

## References

* [Stacks Project, Tag 0DQ0](https://stacks.math.columbia.edu/tag/0DQ0)
* [Stacks Project, Tag 0372](https://stacks.math.columbia.edu/tag/0372)
* [Stacks Project, Tag 0D31](https://stacks.math.columbia.edu/tag/0D31)
* [Stacks Project, Tag 0D3D](https://stacks.math.columbia.edu/tag/0D3D)
* [Stacks Project, Tag 0D04](https://stacks.math.columbia.edu/tag/0D04)
* [Stacks Project, Tag 0DPJ](https://stacks.math.columbia.edu/tag/0DPJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

namespace Space.PicardObject

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {s : PicardSituation B S hS}

/-- **The ample locus of the Picard stack.** An object `(T', b, ℒ)` of `Picardstack_{X/B}` is in
the ample locus when `ℒ` is ample on `X_{T'}` relative to the projection `X_{T'} ⟶ T'`, in the
sense of Stacks 0D31. -/
def IsInAmpleLocus (A : PicardObject s) : Prop :=
  Space.IsRelativelyAmple B S hS (baseChangeInclusion s.f A.T) A.lineBundle

end Space.PicardObject

namespace CurveFamily

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

/-- **The Picard situation of a family of curves** `X ⟶ T`: the morphism of algebraic spaces from
the total space to the base, whose Picard stack is `Picardstack_{X/T}`. -/
def picardSituation (X : CurveFamily B hZ) : Space.PicardSituation B integerBase hZ where
  X := X.total
  base := schemeSpace X.base
  f := X.toBase

/-- A morphism `π : T' ⟶ T` of the site into the base of a family of curves, read as a test
scheme of its Picard situation. -/
def picardTestScheme (X : CurveFamily B hZ) {T' : BigFppfOver B integerBase hZ}
    (π : T' ⟶ X.base) : X.picardSituation.SchemesOver :=
  CostructuredArrow.mk (Y := T') (schemeSpaceMap π)

/-- **A family of curves is smooth locally polarized**, given that through every point of its
base the ample locus of its Picard stack has an object over a smooth test scheme. That is the
input `hpic`: for every point `t` there are a smooth `π : T' ⟶ T` of the site through `t` and an
object `A` of `Picardstack_{X/T}` over `T'` in the ample locus.

The input combines Stacks 0D04, 09DS and 0DPJ (smooth charts of `Picardstack_{X/T}` that are
smooth over `T`), Stacks 0D3D (openness of the ample locus, a theorem of the library) and the
surjectivity half of Stacks 0DQ0. Its shape is a guess, pending statements of the first
three tags.

Over the test scheme `π`, the base change `X_{T'}` of the Picard situation sits in the cartesian
square of algebraic spaces that defines it. With the module of `A` this is the input of
`AlgebraicGeometry.CurveFamily.isSmoothLocallyPolarized_of`. -/
theorem isSmoothLocallyPolarized_of_picard (X : CurveFamily B hZ)
    (hpic : ∀ t : (BigFppfOver.toScheme B integerBase hZ).obj X.base,
      ∃ (T' : BigFppfOver B integerBase hZ) (π : T' ⟶ X.base),
        Smooth ((BigFppfOver.toScheme B integerBase hZ).map π) ∧
        t ∈ Set.range ((BigFppfOver.toScheme B integerBase hZ).map π) ∧
        ∃ A : Space.PicardObject X.picardSituation,
          A.T = X.picardTestScheme π ∧ A.IsInAmpleLocus) :
    X.IsSmoothLocallyPolarized := by
  refine isSmoothLocallyPolarized_of X fun t => ?_
  obtain ⟨T', π, hsm, ht, ⟨T, L, hL⟩, hT, hamp⟩ := hpic t
  change T = X.picardTestScheme π at hT
  subst hT
  exact ⟨T', π, hsm, ht, _, Space.baseChangeProjection X.toBase (X.picardTestScheme π),
    Space.baseChangeInclusion X.toBase (X.picardTestScheme π),
    AlgebraicSpaces.isPullback_fiberProduct B integerBase hZ X.toBase (schemeSpaceMap π),
    L, hamp⟩

end CurveFamily

end AlgebraicGeometry

end
