module

public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.FittingNormalForm
public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.FittingPerfectPullback

/-!
# Part (4) of Stacks 0ESN, for every finitely presented module

Let `ℱ` be a finitely presented module on a scheme `X` which is finite locally free of constant
rank `r` on a scheme-theoretically dense open `U`, and let `b : X' ⟶ X` be the blowup of the
`r`-th Fitting ideal of `ℱ`, written as the base change of that blowup along the identity of `X`.
Part (4) of Stacks tag 0ESN says that `b^*ℱ` and the kernel `𝒦` of its canonical surjection onto
the strict transform are perfect `𝒪_{X'}`-modules of Tor dimension at most one. This file proves
both, assuming nothing of `ℱ` beyond the finite presentation that the Fitting ideals already
need.

`StacksFrontier/AlgebraicGeometry/Blowup/Transform/FittingNormalForm.lean` carries the same two
conclusions about `𝒦` under the stronger hypotheses of tag 0EST, namely that `ℱ` itself is
perfect of Tor dimension at most one; those are what the existential statement of tag 0EST
consumes.

## Main results

* `AlgebraicGeometry.isPerfect_modulePullback_pullbackFst_blowUpToBase_of_blowUp` and
  `AlgebraicGeometry.hasTorAmplitude_modulePullback_pullbackFst_blowUpToBase_of_blowUp`: the
  transport of perfectness and of Tor amplitude from the blowup of an ideal sheaf to the base
  change of that blowup along the identity, asking for the two properties on the blowup rather
  than on `X`.
* `AlgebraicGeometry.isPerfect_modulePullback_fittingBlowUpFst` and
  `AlgebraicGeometry.hasTorAmplitude_modulePullback_fittingBlowUpFst`: the half of tag 0ESN (4)
  about `b^*ℱ`.
* `AlgebraicGeometry.isPerfect_strictTransformKernel_of_isFinitePresentation` and
  `AlgebraicGeometry.hasTorAmplitude_strictTransformKernel_of_isFinitePresentation`: the half of
  tag 0ESN (4) about `𝒦`.

## Implementation notes

**Where the two spellings of the blowup meet.** Tag 0ESN is formalized in the base-change spelling,
with structure morphism `CategoryTheory.Limits.pullback.fst (𝟙 X) (blowUpToBase I)`, whereas
`AlgebraicGeometry.isPerfect_and_hasTorAmplitude_modulePullback_fittingBlowUp` is about
`AlgebraicGeometry.blowUpToBase I` itself. The two transports below move perfectness and Tor
amplitude between them. They differ from
`AlgebraicGeometry.isPerfect_modulePullback_pullbackFst_blowUpToBase` and
`AlgebraicGeometry.hasTorAmplitude_modulePullback_pullbackFst_blowUpToBase` only in asking for
their input on the blowup, which is where tag 0F7M supplies it, instead of on `X`, which is
where tag 0ESS consumes it.

**Perfectness and Tor dimension of `b^*ℱ`.** Neither needs a hypothesis on `ℱ` beyond finite
presentation. The affine-local projective resolution of length one of `b^*ℱ` that Stacks 0F7M
provides is globalized in
`StacksFrontier/AlgebraicGeometry/Blowup/Transform/FittingPerfectPullback.lean`, and the transports
bring the result into the base-change spelling.

**Perfectness and Tor dimension of `𝒦`.** The kernel sequence gives a distinguished triangle
`𝒦 ⟶ b^*ℱ ⟶ 𝒬 ⟶ 𝒦[1]` (`CategoryTheory.ShortComplex.ShortExact.singleTriangle`). For
perfectness, `𝒬` is perfect because it is finite locally free of rank `r` by tag 0ESN (2)
(`AlgebraicGeometry.isPerfect_singleFunctor_of_isFiniteLocallyFree`), so tag 08CR for the first
vertex applies. For Tor amplitude, `𝒬` is flat, so tag 08CJ (3) puts `𝒦` in `[-1, 1]`, and a
module in degree `0` has no Tor in positive degrees, which removes degree `1`
(`AlgebraicGeometry.hasTorAmplitude_X₁_of_shortExact_isFiniteLocallyFree`).

## References

* [Stacks Project, Tag 0ESN](https://stacks.math.columbia.edu/tag/0ESN)
* [Stacks Project, Tag 0EST](https://stacks.math.columbia.edu/tag/0EST)
* [Stacks Project, Tag 0F7M](https://stacks.math.columbia.edu/tag/0F7M)
* [Stacks Project, Tag 08CJ](https://stacks.math.columbia.edu/tag/08CJ)
* [Stacks Project, Tag 08CR](https://stacks.math.columbia.edu/tag/08CR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits StrictlyPerfect
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.PerfectComplexes Stacks.Cohomology.TorAmplitude

universe u

attribute [local instance 10000] HasDerivedCategory.standard

namespace AlgebraicGeometry

/-! ### Transporting the two properties from the blowup to its base change -/

section Blowup

variable {X : Scheme.{u}} (I : X.IdealSheafData)

/-- **Perfectness passes from the blowup to the base change of the blowup along the identity.**
If the pullback of `ℱ` to the blowup of `I` is perfect, so is its pullback to the base change of
that blowup along the identity of `X`: the two pullbacks differ by pullback along the second
projection, which is an isomorphism.

This asks for perfectness where it is concluded, on the blowup, and so applies to an `ℱ` whose
pullback is perfect for a reason other than the perfectness of `ℱ` itself, which is what tag
0F7M supplies. -/
theorem isPerfect_modulePullback_pullbackFst_blowUpToBase_of_blowUp
    (F : OXMod.{u, u} X.toRingedSpace)
    (hperfect : IsPerfect.{u, u, u + 1} ((DerivedCategory.singleFunctor
      (OXMod.{u, u} (blowUp I).toRingedSpace) 0).obj
      ((Scheme.Modules.pullback (blowUpToBase I)).obj F))) :
    IsPerfect.{u, u, u + 1} ((DerivedCategory.singleFunctor
      (OXMod.{u, u} (Stacks.StrictTransform.baseChange (𝟙 X) (blowUpToBase I)).toRingedSpace)
        0).obj
      ((Scheme.Modules.pullback (pullback.fst (𝟙 X) (blowUpToBase I))).obj F)) :=
  isPerfect_single_of_iso (modulePullbackFstIso I F).symm
    (isPerfect_modulePullback_of_preservesHomology _ _ hperfect)

/-- **Tor amplitude passes from the blowup to the base change of the blowup along the identity.**
If the pullback of `ℱ` to the blowup of `I` has Tor amplitude in `[-1, 0]`, so does its pullback
to the base change of that blowup along the identity of `X`.

This asks for the bound where it is concluded, on the blowup, and so applies to an `ℱ` whose
pullback is of Tor dimension at most one for a reason other than a bound on `ℱ` itself. -/
theorem hasTorAmplitude_modulePullback_pullbackFst_blowUpToBase_of_blowUp
    (F : OXMod.{u, u} X.toRingedSpace)
    (htor : HasTorAmplitude (blowUp I).toRingedSpace ((DerivedCategory.singleFunctor
      (OXMod.{u, u} (blowUp I).toRingedSpace) 0).obj
      ((Scheme.Modules.pullback (blowUpToBase I)).obj F)) (-1) 0) :
    HasTorAmplitude
      (Stacks.StrictTransform.baseChange (𝟙 X) (blowUpToBase I)).toRingedSpace
      ((DerivedCategory.singleFunctor
        (OXMod.{u, u} (Stacks.StrictTransform.baseChange (𝟙 X)
          (blowUpToBase I)).toRingedSpace) 0).obj
        ((Scheme.Modules.pullback (pullback.fst (𝟙 X) (blowUpToBase I))).obj F)) (-1) 0 :=
  hasTorAmplitude_single_of_iso (modulePullbackFstIso I F).symm (-1) 0
    (hasTorAmplitude_modulePullback_of_preservesHomology _ _ (-1) 0 htor)

end Blowup

/-! ### Stacks 0ESN (4) for `b^*ℱ` and for the kernel -/

variable {X : Scheme.{u}} (F : X.Modules) (r : ℕ)

/-- **Stacks Project, Tag 0ESN, part (4), for the pullback.** Let `ℱ` be a finitely presented
module on `X` which is finite locally free of constant rank `r` on a scheme-theoretically dense
open `U`. The pullback of `ℱ` along the blowup of the `r`-th Fitting ideal of `ℱ`, written as the
base change of that blowup along the identity of `X`, is a perfect `𝒪_{X'}`-module.

No hypothesis on `ℱ` beyond finite presentation is needed:
`AlgebraicGeometry.isPerfect_and_hasTorAmplitude_modulePullback_fittingBlowUp`, the globalization
of Stacks 0F7M, gives perfectness on the blowup itself, and the transport above moves it into the
base-change spelling. -/
@[stacks 0ESN "the pullback along the Fitting blowup is perfect"]
theorem isPerfect_modulePullback_fittingBlowUpFst [F.IsFinitePresentation] (U : X.Opens)
    (hU : Scheme.Opens.IsSchemeTheoreticallyDense U)
    (hrank : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback U.ι).obj F) r) :
    IsPerfect.{u, u, u + 1} ((DerivedCategory.singleFunctor
      (OXMod.{u, u} (Stacks.StrictTransform.baseChange (𝟙 X)
        (blowUpToBase (fittingIdeal F (r : ℤ)))).toRingedSpace) 0).obj
      ((Scheme.Modules.pullback
        (pullback.fst (𝟙 X) (blowUpToBase (fittingIdeal F (r : ℤ))))).obj F)) :=
  isPerfect_modulePullback_pullbackFst_blowUpToBase_of_blowUp (fittingIdeal F (r : ℤ)) F
    (isPerfect_and_hasTorAmplitude_modulePullback_fittingBlowUp F U r hU hrank).1

/-- **Stacks Project, Tag 0ESN, part (4), for the pullback.** Let `ℱ` be a finitely presented
module on `X` which is finite locally free of constant rank `r` on a scheme-theoretically dense
open `U`. The pullback of `ℱ` along the blowup of the `r`-th Fitting ideal of `ℱ`, placed in
degree `0`, has Tor amplitude in `[-1, 0]`.

As above, finite presentation is all that is used. -/
@[stacks 0ESN "the Tor dimension of the pullback along the Fitting blowup"]
theorem hasTorAmplitude_modulePullback_fittingBlowUpFst [F.IsFinitePresentation] (U : X.Opens)
    (hU : Scheme.Opens.IsSchemeTheoreticallyDense U)
    (hrank : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback U.ι).obj F) r) :
    HasTorAmplitude (Stacks.StrictTransform.baseChange (𝟙 X)
        (blowUpToBase (fittingIdeal F (r : ℤ)))).toRingedSpace
      ((DerivedCategory.singleFunctor
        (OXMod.{u, u} (Stacks.StrictTransform.baseChange (𝟙 X)
          (blowUpToBase (fittingIdeal F (r : ℤ)))).toRingedSpace) 0).obj
        ((Scheme.Modules.pullback
          (pullback.fst (𝟙 X) (blowUpToBase (fittingIdeal F (r : ℤ))))).obj F)) (-1) 0 :=
  hasTorAmplitude_modulePullback_pullbackFst_blowUpToBase_of_blowUp (fittingIdeal F (r : ℤ)) F
    (isPerfect_and_hasTorAmplitude_modulePullback_fittingBlowUp F U r hU hrank).2

/-- The strict transform of a finitely presented `ℱ` along the Fitting blowup is finite locally
free, being of rank `r` by tag 0ESN (2). -/
private theorem isFiniteLocallyFree_strictTransform_fitting [F.IsFinitePresentation]
    (U : X.Opens) (hU : Scheme.Opens.IsSchemeTheoreticallyDense U)
    (hrank : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback U.ι).obj F) r) :
    SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (Stacks.StrictTransform.sheaf (𝟙 X) (blowUpToBase (fittingIdeal F (r : ℤ)))
        (exceptionalIdeal (fittingIdeal F (r : ℤ))) F) := by
  have : F.IsFiniteType := SheafOfModules.instIsFiniteTypeOfIsFinitePresentation F
  have : F.IsQuasicoherent := SheafOfModules.instIsQuasicoherentOfIsFinitePresentation F
  have := isFiniteLocallyFreeOfRank_strictTransform_of_dense F U r hU hrank
  exact SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree
    (Stacks.StrictTransform.sheaf (𝟙 X) (blowUpToBase (fittingIdeal F (r : ℤ)))
      (exceptionalIdeal (fittingIdeal F (r : ℤ))) F) r

/-- **Stacks Project, Tag 0ESN, part (4), for the kernel.** For a finitely presented module `ℱ`
which is finite locally free of constant rank `r` on a scheme-theoretically dense open `U`, the
kernel of the canonical surjection from `b^*ℱ` onto the strict transform of `ℱ` is a perfect
`𝒪_{X'}`-module.

The kernel sequence gives a distinguished triangle `𝒦 ⟶ b^*ℱ ⟶ 𝒬 ⟶ 𝒦[1]`; `b^*ℱ` is perfect by
`AlgebraicGeometry.isPerfect_modulePullback_fittingBlowUpFst` and `𝒬` is perfect because it is
finite locally free of rank `r` by tag 0ESN (2), so the first vertex is perfect by tag 08CR.

This is `AlgebraicGeometry.isPerfect_strictTransformKernel` with no hypothesis on `ℱ` beyond
finite presentation, which is as far as tag 0ESN assumes: the perfectness of `b^*ℱ` that the
triangle consumes is itself a consequence of finite presentation. -/
@[stacks 0ESN "the kernel is perfect"]
theorem isPerfect_strictTransformKernel_of_isFinitePresentation [F.IsFinitePresentation]
    (U : X.Opens) (hU : Scheme.Opens.IsSchemeTheoreticallyDense U)
    (hrank : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback U.ι).obj F) r) :
    IsPerfect.{u, u, u + 1} ((DerivedCategory.singleFunctor
      (OXMod.{u, u} (Stacks.StrictTransform.baseChange (𝟙 X)
        (blowUpToBase (fittingIdeal F (r : ℤ)))).toRingedSpace) 0).obj
      (strictTransformKernel F r)) := by
  have hQ := isFiniteLocallyFree_strictTransform_fitting F r U hU hrank
  exact Stacks.Cohomology.PerfectComplexTriangles.isPerfect_obj₁_of_distinguished
    (shortExact_strictTransformKernel F r).singleTriangle
    (shortExact_strictTransformKernel F r).singleTriangle_distinguished
    (isPerfect_modulePullback_fittingBlowUpFst F r U hU hrank)
    (isPerfect_singleFunctor_of_isFiniteLocallyFree
      (Stacks.StrictTransform.baseChange (𝟙 X) (blowUpToBase (fittingIdeal F (r : ℤ))))
      (Stacks.StrictTransform.sheaf (𝟙 X) (blowUpToBase (fittingIdeal F (r : ℤ)))
        (exceptionalIdeal (fittingIdeal F (r : ℤ))) F)
      ⟨SheafOfModules.IsFiniteLocallyFree.exists_isFiniteLocallyFreeData⟩)

/-- **Stacks Project, Tag 0ESN, part (4), for the kernel.** For a finitely presented module `ℱ`
which is finite locally free of constant rank `r` on a scheme-theoretically dense open `U`, the
kernel of the canonical surjection from `b^*ℱ` onto the strict transform of `ℱ`, placed in degree
`0`, has Tor amplitude in `[-1, 0]`.

The kernel sequence gives a distinguished triangle `𝒦 ⟶ b^*ℱ ⟶ 𝒬 ⟶ 𝒦[1]`. Here `b^*ℱ` has Tor
amplitude in `[-1, 0]` by `AlgebraicGeometry.hasTorAmplitude_modulePullback_fittingBlowUpFst` and
`𝒬` in `[0, 0]`, being finite locally free hence flat, so tag 08CJ (3) puts `𝒦` in `[-1, 1]`. A
module in degree `0` has no Tor in positive degrees, which removes degree `1`.

This is `AlgebraicGeometry.hasTorAmplitude_strictTransformKernel` with no bound assumed on `ℱ`,
which is as far as tag 0ESN assumes: the bound on `b^*ℱ` that the triangle consumes already
follows from finite presentation. -/
@[stacks 0ESN "the Tor dimension of the kernel"]
theorem hasTorAmplitude_strictTransformKernel_of_isFinitePresentation [F.IsFinitePresentation]
    (U : X.Opens) (hU : Scheme.Opens.IsSchemeTheoreticallyDense U)
    (hrank : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback U.ι).obj F) r) :
    HasTorAmplitude (Stacks.StrictTransform.baseChange (𝟙 X)
        (blowUpToBase (fittingIdeal F (r : ℤ)))).toRingedSpace
      ((DerivedCategory.singleFunctor
        (OXMod.{u, u} (Stacks.StrictTransform.baseChange (𝟙 X)
          (blowUpToBase (fittingIdeal F (r : ℤ)))).toRingedSpace) 0).obj
        (strictTransformKernel F r)) (-1) 0 := by
  have hQ := isFiniteLocallyFree_strictTransform_fitting F r U hU hrank
  exact hasTorAmplitude_X₁_of_shortExact_isFiniteLocallyFree (strictTransformKernelSequence F r)
    (shortExact_strictTransformKernel F r)
    (hasTorAmplitude_modulePullback_fittingBlowUpFst F r U hU hrank)
    (isFiniteLocallyFree_of_isFiniteLocallyFreeClass _)

end AlgebraicGeometry

end
