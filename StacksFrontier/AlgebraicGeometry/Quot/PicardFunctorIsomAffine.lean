module

public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackLimitFlatProperSupport
public import StacksFrontier.AlgebraicGeometry.Quot.PicardFunctorQuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Quot.PicardFunctorSeparatedIntegralFibres
public import StacksFrontier.AlgebraicGeometry.Quot.PicardStackOpenInCoherentStack
public import StacksFrontier.AlgebraicGeometry.Quot.RelativeHomSpaceRepresentable
public import StacksFrontier.AlgebraicGeometry.Quot.RelativeIsomRepresentableFinitePresentation

/-!
# `Isom(L, N)` of invertible modules on `X_T` is affine over `T`

Let `f : X ⟶ B` be a flat, proper morphism of finite presentation, `T` a scheme over `B`, and
`L`, `N` invertible modules on the base change `X_T`.  An invertible module satisfies the
hypotheses of Proposition 08K6 over `T` (the first part of the proof of Stacks 0D03), so by
Stacks 08K9 the relative Isom functor `Isom(L, N)` of `X_T ⟶ T` is an algebraic space affine and
of finite presentation over `T`.  Consequently an algebraic space representing `Pic_{X/B}` is
quasi-separated over `B`.

## Main results

* `PicardSituation.isAffineFinitePresentationAlgebraicSpaceOver_isomHomSituation_isomFunctor`:
  `Isom(L, N)` of invertible modules on `X_T` is an algebraic space affine and of finite
  presentation over `T`.
* `PicardSituation.isQuasiSeparated_of_represents_picardFunctor`:
  the quasi-separatedness half of Stacks 0DNI for any algebraic space representing `Pic_{X/B}`.

## Implementation notes

Stacks 08K9 is
`HomSituation.isAffineFinitePresentationAlgebraicSpaceOver_isomFunctor_of_finitePresentation`,
applied with Stacks 08K6,
`HomSituation.isAffineFinitePresentationAlgebraicSpaceOverBase_of_finitePresentation`.
Proper support is recorded for the invertible modules as
`AlgebraicGeometry.Space.CoherentSituation.HasProperSupportOver`, whose second component is the
proper support those two results take.

## References

* [Stacks Project, Tag 08K9](https://stacks.math.columbia.edu/tag/08K9)
* [Stacks Project, Tag 08K6](https://stacks.math.columbia.edu/tag/08K6)
* [Stacks Project, Tag 0D03](https://stacks.math.columbia.edu/tag/0D03)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space.PicardSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    (s : PicardSituation B S hS)

/-- **An invertible module on `X_T` meets the hypotheses of Proposition 08K6 over `T`.**  It is
of finite presentation, flat over `T` because `X_T ⟶ T` is flat (Stacks 03MO), and its support
is proper over `T` because `X_T ⟶ T` is proper (Stacks 04WP).  This is the first part of the
proof of Stacks 0D03. -/
private theorem targetHypotheses_of_isInvertibleModule
    (hflat : IsFlat B S hS s.f.hom) (hfp : IsFinitePresentation B S hS s.f.hom)
    (hproper : IsProper B S hS s.f.hom) (T : s.SchemesOver)
    (M : Modules.{u, u} B S hS (s.baseChange T).1 (s.baseChange T).2)
    (hM : IsInvertibleModule (s.baseChange T) M) :
    M.IsFinitePresentationOnSite ∧
      IsFlatOver B S hS (s.baseChange T).2 (baseChangeInclusion s.f T).hom M ∧
      CoherentSituation.HasProperSupportOver (baseChangeInclusion s.f T) M := by
  have hp : IsLocallyOfFiniteType B S hS (baseChangeInclusion s.f T).hom :=
    isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS
      (s.isFinitePresentation_baseChangeInclusion hfp T).1
  exact ⟨isFinitePresentationOnSite_of_isInvertibleModule M hM,
    isFlatOver_of_isInvertibleModule (baseChangeInclusion s.f T) M
      (s.isFlat_baseChangeInclusion hflat T) hM,
    hp, isProperOver_supportOfSheaf_of_isInvertibleModule (baseChangeInclusion s.f T) hp M
      (s.isProper_baseChangeInclusion hproper T) hM⟩

/-- **`Isom(L, N)` of two invertible modules on `X_T` is an algebraic space affine and of finite
presentation over `T`.**  Let `f : X ⟶ B` be flat, proper and of finite presentation, `T` a
scheme over `B`, and `L`, `N` invertible modules on the base change `X_T`.  Then the relative Isom
functor `Isom(L, N)` of `X_T ⟶ T` is an algebraic space affine and of finite presentation over
`T`: Stacks 08K9 for `X_T ⟶ T`, with Stacks 08K6, whose hypotheses for `L` and `N` hold by the
first part of the proof of Stacks 0D03.
-/
theorem isAffineFinitePresentationAlgebraicSpaceOver_isomHomSituation_isomFunctor
    (hflat : IsFlat B S hS s.f.hom) (hfp : IsFinitePresentation B S hS s.f.hom)
    (hproper : IsProper B S hS s.f.hom) (T : s.SchemesOver)
    (L N : Modules.{u, u} B S hS (s.baseChange T).1 (s.baseChange T).2)
    (hL : IsInvertibleModule (s.baseChange T) L) (hN : IsInvertibleModule (s.baseChange T) N) :
    IsAffineFinitePresentationAlgebraicSpaceOver ((schemeSpaceFunctor B S hS).obj T.left)
      (s.isomHomSituation T L N hL hN).isomFunctor := by
  let t := s.isomHomSituation T L N hL hN
  have hf : IsFinitePresentation B S hS t.f.hom := s.isFinitePresentation_baseChangeInclusion hfp T
  have hLt := s.targetHypotheses_of_isInvertibleModule hflat hfp hproper T L hL
  have hNt := s.targetHypotheses_of_isInvertibleModule hflat hfp hproper T N hN
  exact t.isAffineFinitePresentationAlgebraicSpaceOver_isomFunctor_of_finitePresentation hf hLt.1
    hNt.1 hLt.2.1 hNt.2.1 hLt.2.2.2 hNt.2.2.2
    fun s' hfp' hF' hG' hGflat' hGsupp' =>
      s'.isAffineFinitePresentationAlgebraicSpaceOverBase_of_finitePresentation hfp' hF' hG'
        hGflat' hGsupp'

/-- **The quasi-separatedness half of Stacks 0DNI, for any algebraic space representing
`Pic_{X/B}`.**  Let `f : X ⟶ B` be flat, proper and of finite presentation, and let `p : H ⟶ B`
be an algebraic space over `B` whose functor of points over `B` is identified (`c`) with the
relative Picard functor `Pic_{X/B}`.  Then `p` is quasi-separated: the diagonal of `H` over `B`
is computed on test schemes by the functors `Isom(L, N)`, which are affine over the test scheme
by Stacks 08K9. -/
theorem isQuasiSeparated_of_represents_picardFunctor
    {s : PicardSituation B S hS} {H : AlgebraicSpaces B S hS} {p : H ⟶ s.base}
    (c : spacePointsOver p ⋙ uliftFunctor.{u + 1, u} ≅ s.picardFunctor)
    (hflat : IsFlat B S hS s.f.hom) (hfp : IsFinitePresentation B S hS s.f.hom)
    (hproper : IsProper B S hS s.f.hom) :
    IsQuasiSeparated B S hS p.hom :=
  isQuasiSeparated_of_represents_of_isAffineAlgebraicSpaceOver_isomFunctor c
    fun T _ L N hL hN =>
      (s.isAffineFinitePresentationAlgebraicSpaceOver_isomHomSituation_isomFunctor hflat hfp
        hproper T L N hL hN).isAffineAlgebraicSpaceOver

end AlgebraicGeometry.Space.PicardSituation

end
