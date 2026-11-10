module

public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.FourierMukai.Composition
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.FourierMukai.LeftTensorNotation
public import StacksFrontier.AlgebraicGeometry.Perfect.VectorBundleComparison
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormulaLocalStrictlyPerfect

/-!
# The projection-formula step of the display of Tag 0G0E

The proof of [Stacks, Tag 0G0E] runs steps 1, 2 and 3 on one computation, the *display*

`H^i(X × X, K ⊗^𝐋 (ℰ ⊠ 𝒢)) = H^i(X, Φ_K(ℰ) ⊗^𝐋 𝒢)`.

Its middle equality is the derived projection formula for the second projection against a finite
locally free module on the base, and that is what this file assembles:

`Φ_K(ℰ) ⊗^𝐋_{𝒪_Y} 𝒢 ≅ R pr_{2,*}((L pr_1^*ℰ ⊗^𝐋 K) ⊗^𝐋 L pr_2^*𝒢)`.

Nothing here is specific to Tag 0G0E: the statement holds for an arbitrary kernel `K` on
`X ×_S Y`, an arbitrary object in place of `L pr_1^*ℰ ⊗^𝐋 K`, and any finite locally free `𝒢` on
`Y`, over an arbitrary base `S`.

## Main results

* `AlgebraicGeometry.isIso_dprojectionRight_snd_single` — the projection-formula transformation of
  [Stacks, Tag 0B53] at the second projection is invertible at a finite locally free module in
  degree zero.
* `AlgebraicGeometry.pushforwardSndTensorSingleIso` — that invertibility packaged as an
  isomorphism `R pr_{2,*}E ⊗^𝐋 𝒢 ≅ R pr_{2,*}(E ⊗^𝐋 L pr_2^*𝒢)`.
* `AlgebraicGeometry.fourierMukaiTensorSingleIso` — **the projection-formula step of the
  display**, read at `E = L pr_1^*ℰ ⊗^𝐋 K` so that the left-hand side is `Φ_K(ℰ) ⊗^𝐋 𝒢`.

## Implementation notes

*Two spellings of finite local freeness.*  The hypothesis is stated at
`AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree`, which is the spelling [Stacks, Tag 0FZ0]
produces and the one the statements of
`StacksFrontier/AlgebraicGeometry/Duality/IdentityFourierMukaiKernel.lean` are written with, while
`AlgebraicGeometry.isPerfect_singleFunctor_of_isFiniteLocallyFree` wants
`Stacks.FiniteLocallyFree.IsFiniteLocallyFree`.  The two are equivalent by
`Stacks.FiniteLocallyFree.isFiniteLocallyFree_iff_algebraicGeometry`, and that is the only place
they meet below.

*Why this is unconditional.*  [Stacks, Tag 0B54] is available in this library as
`Stacks.Cohomology.DerivedProjectionFormula.isIso_projectionFormulaMap_of_isPerfect`, for an
arbitrary morphism of ringed spaces and an arbitrary complex on the source, asking only that the
complex on the *target* be perfect.  A finite locally free module in degree zero is perfect, by
`AlgebraicGeometry.isPerfect_singleFunctor_of_isFiniteLocallyFree`, so no hypothesis on the
projection is needed — in particular it does not have to be a closed embedding, which it is not.
In particular the derived projection formula is not restricted to a closed embedding or to a
*strictly* perfect complex.

*Where `Φ_K` enters, and why it is free.*  `AlgebraicGeometry.fourierMukai` is by definition
`L pr_1^* ⋙ (- ⊗^𝐋 K) ⋙ R pr_{2,*}`, so `Φ_K(ℰ)` *is* `R pr_{2,*}(L pr_1^*ℰ ⊗^𝐋 K)` on the nose
(`AlgebraicGeometry.fourierMukai_obj`, a `rfl`).  `fourierMukaiTensorSingleIso` is therefore
`pushforwardSndTensorSingleIso` at that object and nothing more; it is stated separately because
the display is where it is used and `Φ_K` is how the display is written.

*The model of the derived categories.*  `HasDerivedCategory.standard` is activated as a local
instance, as in `FourierMukai/Basic.lean` and `FourierMukai/Composition.lean`: `dpull`, `dpush`,
`dtenLeft`, `dtenR`, `dprojectionFormulaRight` and `fourierMukai` are all available at that model,
and so is [Stacks, Tag 0B54].  The other step of the display,
`K ⊗^𝐋 (ℰ ⊠ 𝒢) ≅ (L pr_1^*ℰ ⊗^𝐋 K) ⊗^𝐋 L pr_2^*𝒢`, is not assembled here only because it needs
the box comparison and hence a field as the base; it is
`AlgebraicGeometry.kernelTensorBoxSingleIso` of `FourierMukai/BoxDisplay.lean`, and the two
compose there into `AlgebraicGeometry.fourierMukaiDisplayIso`.  The box comparison
`AlgebraicGeometry.derivedExternalTensorSingleIso` takes its models as binders, so it is read at
this model with no transport; `HasDerivedCategory` carries the localized category as data, so a
free binder is the only crossing there is.

## References

* [Stacks Project, Tag 0G0E](https://stacks.math.columbia.edu/tag/0G0E)
* [Stacks Project, Tag 0B53](https://stacks.math.columbia.edu/tag/0B53)
* [Stacks Project, Tag 0B54](https://stacks.math.columbia.edu/tag/0B54)
* [Stacks Project, Tag 0FYQ](https://stacks.math.columbia.edu/tag/0FYQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.DerivedTensor.RingedSite

universe u

namespace AlgebraicGeometry

attribute [local instance 100000] HasDerivedCategory.standard

variable {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)

/-- **[Stacks, Tag 0B54] at the second projection against a finite locally free module.**  The
projection-formula transformation of [Stacks, Tag 0B53]

`R pr_{2,*}E ⊗^𝐋_{𝒪_Y} - ⟶ L pr_2^* ⋙ (E ⊗^𝐋 -) ⋙ R pr_{2,*}`

is invertible at `𝒢[0]` for every finite locally free `𝒢`, because such a module in degree zero
is a perfect object and [Stacks, Tag 0B54] needs nothing else. -/
theorem isIso_dprojectionRight_snd_single_of_isPerfect
    (E : DerivedCategory (Limits.pullback f g).Modules) (G : Y.Modules)
    (hG : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := Y.toRingedSpace)
      ((DerivedCategory.singleFunctor Y.Modules 0).obj G)) :
    IsIso ((dprojectionFormulaRight (Limits.pullback.snd f g) E).app
      ((DerivedCategory.singleFunctor Y.Modules 0).obj G)) :=
  Stacks.Cohomology.DerivedProjectionFormula.isIso_projectionFormulaMap_of_isPerfect
    (Limits.pullback.snd f g).toLRSHom.toShHom E _ hG

/-- **`R pr_{2,*}E ⊗^𝐋 𝒢 ≅ R pr_{2,*}(E ⊗^𝐋 L pr_2^*𝒢)`** for a `𝒢` perfect in degree zero. -/
def pushforwardSndTensorSingleIsoOfIsPerfect
    (E : DerivedCategory (Limits.pullback f g).Modules) (G : Y.Modules)
    (hG : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := Y.toRingedSpace)
      ((DerivedCategory.singleFunctor Y.Modules 0).obj G)) :
    (dtenLeft Y ((dpush (Limits.pullback.snd f g)).obj E)).obj
        ((DerivedCategory.singleFunctor Y.Modules 0).obj G) ≅
      (dpush (Limits.pullback.snd f g)).obj
        ((dtenLeft (Limits.pullback f g) E).obj
          ((dpull (Limits.pullback.snd f g)).obj
            ((DerivedCategory.singleFunctor Y.Modules 0).obj G))) :=
  haveI := isIso_dprojectionRight_snd_single_of_isPerfect f g E G hG
  asIso ((dprojectionFormulaRight (Limits.pullback.snd f g) E).app
    ((DerivedCategory.singleFunctor Y.Modules 0).obj G))

/-- **The projection-formula step of the display of [Stacks, Tag 0G0E], for a `𝒢` perfect in
degree zero.**  This is the generality the projection formula of [Stacks, Tag 0B54] actually
holds in; `AlgebraicGeometry.fourierMukaiTensorSingleIso` is its finite locally free case, and
step 2 of the source's proof is where the wider generality is needed, the modules of
zero-dimensional support it runs on being perfect on a regular scheme but not locally free. -/
def fourierMukaiTensorSingleIsoOfIsPerfect (K : DerivedCategory (Limits.pullback f g).Modules)
    (E : X.Modules) (G : Y.Modules)
    (hG : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := Y.toRingedSpace)
      ((DerivedCategory.singleFunctor Y.Modules 0).obj G)) :
    (dtenLeft Y ((fourierMukai f g K).obj
          ((DerivedCategory.singleFunctor X.Modules 0).obj E))).obj
        ((DerivedCategory.singleFunctor Y.Modules 0).obj G) ≅
      (dpush (Limits.pullback.snd f g)).obj
        ((dtenLeft (Limits.pullback f g)
            ((dtenR (Limits.pullback f g) K).obj
              ((dpull (Limits.pullback.fst f g)).obj
                ((DerivedCategory.singleFunctor X.Modules 0).obj E)))).obj
          ((dpull (Limits.pullback.snd f g)).obj
            ((DerivedCategory.singleFunctor Y.Modules 0).obj G))) :=
  pushforwardSndTensorSingleIsoOfIsPerfect f g
    ((dtenR (Limits.pullback f g) K).obj
      ((dpull (Limits.pullback.fst f g)).obj
        ((DerivedCategory.singleFunctor X.Modules 0).obj E))) G hG

/-- A finite locally free module in degree zero is perfect, which is all
`AlgebraicGeometry.isIso_dprojectionRight_snd_single_of_isPerfect` asks of it. -/
theorem isPerfect_single_of_isFiniteLocallyFree' (G : Y.Modules)
    (hG : SheafOfModules.IsFiniteLocallyFree.{u, u, u} (R := Y.ringCatSheaf) G) :
    Stacks.Cohomology.PerfectComplexes.IsPerfect (X := Y.toRingedSpace)
      ((DerivedCategory.singleFunctor Y.Modules 0).obj G) :=
  isPerfect_singleFunctor_of_isFiniteLocallyFree Y G
    ((Stacks.FiniteLocallyFree.isFiniteLocallyFree_iff_algebraicGeometry G).2 hG)

/-- The projection-formula map at the second projection `pr_2 : X ×_S Y ⟶ Y` is an isomorphism
at a finite locally free module `𝒢` on `Y` placed in degree zero, for every `E` on `X ×_S Y`. -/
theorem isIso_dprojectionRight_snd_single
    (E : DerivedCategory (Limits.pullback f g).Modules) (G : Y.Modules)
    (hG : SheafOfModules.IsFiniteLocallyFree.{u, u, u} (R := Y.ringCatSheaf) G) :
    IsIso ((dprojectionFormulaRight (Limits.pullback.snd f g) E).app
      ((DerivedCategory.singleFunctor Y.Modules 0).obj G)) :=
  isIso_dprojectionRight_snd_single_of_isPerfect f g E G
    (isPerfect_single_of_isFiniteLocallyFree' G hG)

/-- **`R pr_{2,*}E ⊗^𝐋 𝒢 ≅ R pr_{2,*}(E ⊗^𝐋 L pr_2^*𝒢)`** for finite locally free `𝒢`: the
projection formula at the second projection, inverted. -/
def pushforwardSndTensorSingleIso
    (E : DerivedCategory (Limits.pullback f g).Modules) (G : Y.Modules)
    (hG : SheafOfModules.IsFiniteLocallyFree.{u, u, u} (R := Y.ringCatSheaf) G) :
    (dtenLeft Y ((dpush (Limits.pullback.snd f g)).obj E)).obj
        ((DerivedCategory.singleFunctor Y.Modules 0).obj G) ≅
      (dpush (Limits.pullback.snd f g)).obj
        ((dtenLeft (Limits.pullback f g) E).obj
          ((dpull (Limits.pullback.snd f g)).obj
            ((DerivedCategory.singleFunctor Y.Modules 0).obj G))) :=
  pushforwardSndTensorSingleIsoOfIsPerfect f g E G
    (isPerfect_single_of_isFiniteLocallyFree' G hG)

/-- **The projection-formula step of the display of [Stacks, Tag 0G0E]**:

`Φ_K(ℰ) ⊗^𝐋_{𝒪_Y} 𝒢 ≅ R pr_{2,*}((L pr_1^*ℰ ⊗^𝐋 K) ⊗^𝐋 L pr_2^*𝒢)`

for a finite locally free `𝒢` on `Y`, an arbitrary `ℰ` on `X` and an arbitrary kernel `K` on
`X ×_S Y`.  It is `AlgebraicGeometry.pushforwardSndTensorSingleIso` at
`E = L pr_1^*ℰ ⊗^𝐋 K`, which is what `Φ_K(ℰ)` is the direct image of by definition. -/
def fourierMukaiTensorSingleIso (K : DerivedCategory (Limits.pullback f g).Modules)
    (E : X.Modules) (G : Y.Modules)
    (hG : SheafOfModules.IsFiniteLocallyFree.{u, u, u} (R := Y.ringCatSheaf) G) :
    (dtenLeft Y ((fourierMukai f g K).obj
          ((DerivedCategory.singleFunctor X.Modules 0).obj E))).obj
        ((DerivedCategory.singleFunctor Y.Modules 0).obj G) ≅
      (dpush (Limits.pullback.snd f g)).obj
        ((dtenLeft (Limits.pullback f g)
            ((dtenR (Limits.pullback f g) K).obj
              ((dpull (Limits.pullback.fst f g)).obj
                ((DerivedCategory.singleFunctor X.Modules 0).obj E)))).obj
          ((dpull (Limits.pullback.snd f g)).obj
            ((DerivedCategory.singleFunctor Y.Modules 0).obj G))) :=
  fourierMukaiTensorSingleIsoOfIsPerfect f g K E G
    (isPerfect_single_of_isFiniteLocallyFree' G hG)

end AlgebraicGeometry

end
