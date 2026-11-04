module

public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundleFlat
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundleProper
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundleTwist
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveCompletionModule
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSheafChartRestriction

/-!
# The projective completion of a vector bundle on an algebraic space

Let `X` be an algebraic space and `ℰ` a finite locally free `𝒪_X`-module of rank `r`. The proof of
Stacks 0ERW compactifies the vector bundle of `ℰ` inside the projective bundle

`π : P = 𝐏(ℰ ⊕ 𝒪_X) ⟶ X`

of the rank `r + 1` module `ℰ ⊕ 𝒪_X`, with its twist `𝒪_P(1)` and the global section
`s ∈ Γ(P, 𝒪_P(1))` corresponding to the global section `(0, 1)` of `ℰ ⊕ 𝒪_X`: the image of
`π^*(0, 1)` under the tautological surjection `π^*(ℰ ⊕ 𝒪_X) ⟶ 𝒪_P(1)`. This file names these.

## Main definitions

* `AlgebraicGeometry.Space.projectiveCompletion`: `P = 𝐏(ℰ ⊕ 𝒪_X)`.
* `AlgebraicGeometry.Space.projectiveCompletionProj`: `π : P ⟶ X`.
* `AlgebraicGeometry.Space.projectiveCompletionTwist`: `𝒪_P(1)`.
* `AlgebraicGeometry.Space.projectiveCompletionSectionHom`: the map `𝒪_P ⟶ 𝒪_P(1)` given by the
  section `s`, and `AlgebraicGeometry.Space.projectiveCompletionSection` the section itself.

## Main results

* `AlgebraicGeometry.Space.isFlat_projectiveCompletionProj`,
  `AlgebraicGeometry.Space.hasRelativeDimension_projectiveCompletionProj`,
  `AlgebraicGeometry.Space.isProper_projectiveCompletionProj`: `π` is flat of relative
  dimension `r` and proper.
* `AlgebraicGeometry.Space.isInvertibleModule_projectiveCompletionTwist`: `𝒪_P(1)` is invertible.

## References

* [Stacks Project, Tag 0ERW](https://stacks.math.columbia.edu/tag/0ERW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X : AlgebraicSpaces B S hS}
    (E : Modules.{u, u} B S hS X.1 X.2) {r : ℕ}
    (hr : RingedSite.IsFiniteLocallyFreeOfRank (smallEtaleRingedSite B S hS X.1 X.2) E r)

/-- **The projective completion `P = 𝐏(ℰ ⊕ 𝒪_X)` of the vector bundle of `ℰ`.** -/
abbrev projectiveCompletion : AlgebraicSpaces B S hS :=
  @projectiveBundle B S hS X (addUnit X.2 E) (isQuasicoherentOnSite_addUnit hr)
    (isFiniteLocallyFreeOnSite_addUnit hr)

/-- The projection `π : P = 𝐏(ℰ ⊕ 𝒪_X) ⟶ X`. -/
abbrev projectiveCompletionProj : projectiveCompletion E hr ⟶ X :=
  @projectiveBundleProj B S hS X (addUnit X.2 E) (isQuasicoherentOnSite_addUnit hr)
    (isFiniteLocallyFreeOnSite_addUnit hr)

/-- The twist `𝒪_P(1)` of the projective completion. -/
abbrev projectiveCompletionTwist :
    QuasicoherentSheaves.{u, u} B S hS (projectiveCompletion E hr).obj
      (projectiveCompletion E hr).property :=
  @projectiveBundleTwist B S hS X (addUnit X.2 E) (isQuasicoherentOnSite_addUnit hr)
    (isFiniteLocallyFreeOnSite_addUnit hr)

/-- The tautological surjection `π^*(ℰ ⊕ 𝒪_X) ⟶ 𝒪_P(1)`. -/
abbrev projectiveCompletionTautological :
    (modulePullback B S hS (projectiveCompletionProj E hr)).obj (addUnit X.2 E) ⟶
      (projectiveCompletionTwist E hr).obj :=
  (@projectiveBundleTautological B S hS X (addUnit X.2 E) (isQuasicoherentOnSite_addUnit hr)
    (isFiniteLocallyFreeOnSite_addUnit hr)).hom

/-- **The section `s` of `𝒪_P(1)` given by `(0, 1)`**, as a map `𝒪_P ⟶ 𝒪_P(1)`: the composite
`𝒪_P ≅ π^*𝒪_X ⟶ π^*(ℰ ⊕ 𝒪_X) ⟶ 𝒪_P(1)` of the inverse image of the inclusion of the summand
`𝒪_X` with the tautological surjection. -/
def projectiveCompletionSectionHom :
    SheafOfModules.unit (structureRingSheaf B S hS (projectiveCompletion E hr)) ⟶
      (projectiveCompletionTwist E hr).obj :=
  (modulePullbackUnitIso B S hS (projectiveCompletionProj E hr)).inv ≫
    (modulePullback B S hS (projectiveCompletionProj E hr)).map (addUnitInr X.2 E) ≫
    projectiveCompletionTautological E hr

/-- **The global section `s ∈ Γ(P, 𝒪_P(1))` given by `(0, 1)`.** -/
def projectiveCompletionSection : (projectiveCompletionTwist E hr).obj.sections :=
  (projectiveCompletionTwist E hr).obj.unitHomEquiv (projectiveCompletionSectionHom E hr)

/-- The section `s` corresponds to the map `𝒪_P ⟶ 𝒪_P(1)` it is defined by. -/
theorem unitHomEquiv_symm_projectiveCompletionSection :
    (projectiveCompletionTwist E hr).obj.unitHomEquiv.symm (projectiveCompletionSection E hr) =
      projectiveCompletionSectionHom E hr :=
  Equiv.symm_apply_apply _ _

/-- **The projection of the projective completion is flat of relative dimension `r`.** -/
theorem isFlat_projectiveCompletionProj :
    IsFlat B S hS (projectiveCompletionProj E hr).hom :=
  @isFlat_projectiveBundleProj B S hS X (addUnit X.2 E) (isQuasicoherentOnSite_addUnit hr) r
    (isFiniteLocallyFreeOfRank_addUnit hr) (isFiniteLocallyFreeOnSite_addUnit hr)

/-- **The projection of the projective completion has relative dimension `r`.** -/
theorem hasRelativeDimension_projectiveCompletionProj :
    HasRelativeDimension r B S hS (projectiveCompletionProj E hr).hom :=
  @hasRelativeDimension_projectiveBundleProj B S hS X (addUnit X.2 E)
    (isQuasicoherentOnSite_addUnit hr) r (isFiniteLocallyFreeOfRank_addUnit hr)
    (isFiniteLocallyFreeOnSite_addUnit hr)

/-- **The projection of the projective completion is proper.** -/
theorem isProper_projectiveCompletionProj :
    IsProper B S hS (projectiveCompletionProj E hr).hom :=
  @isProper_projectiveBundleProj B S hS X (addUnit X.2 E) (isQuasicoherentOnSite_addUnit hr)
    (isFiniteLocallyFreeOnSite_addUnit hr)

/-- **The twist `𝒪_P(1)` of the projective completion is invertible.** -/
theorem isInvertibleModule_projectiveCompletionTwist :
    IsInvertibleModule (projectiveCompletion E hr) (projectiveCompletionTwist E hr).obj :=
  @isInvertibleModule_projectiveBundleTwist B S hS X (addUnit X.2 E)
    (isQuasicoherentOnSite_addUnit hr) (isFiniteLocallyFreeOnSite_addUnit hr)

end AlgebraicGeometry.Space

end
