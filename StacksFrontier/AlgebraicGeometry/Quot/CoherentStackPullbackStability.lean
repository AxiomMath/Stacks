module

public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackFibered
public import StacksFrontier.AlgebraicGeometry.Spaces.Properness.ModuleSupportProperBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackQuasicoherence
public import StacksFrontier.AlgebraicGeometry.Topologies.FinitePresentationOnSiteUniverses

/-!
# The base-change stability of modules that the coherent-sheaf category needs

An object of `Coh_{X/Y}` carries an `𝒪_{X_T}`-module which is quasi-coherent, of finite
presentation, flat over the test scheme and of proper support, and pulling such an object back
along a morphism of test schemes asks each of those four conditions to be inherited by an inverse
image.  Three assertions about inverse images of modules on algebraic spaces are what that
amounts to: finite presentation is inherited (Stacks 03DO, clause 03DL(7)), flatness over the
target is inherited in a cartesian square (Stacks 05VW), and so is properness of the support over
the target (Stacks 0CZJ).  They are collected in
`AlgebraicGeometry.Space.ModulePullbackStability`.

Two of the three are theorems of this development.  Properness of the support under base change
is `AlgebraicGeometry.Space.isProperOver_supportOfSheaf_modulePullback`.  Finite presentation
under pullback is Stacks 03DO at the morphism of small étale ringed topoi of Stacks 03G8, read
through the comparison of the two renderings of Stacks 03DL(7) in
`StacksFrontier/AlgebraicGeometry/Topologies/FinitePresentationOnSiteUniverses.lean`: the modules
here satisfy `SheafOfModules.IsFinitePresentationOnSite`, whereas Stacks 03DO is proved for
Mathlib's `SheafOfModules.IsFinitePresentation`, and the two are the same condition.  Flatness
under base change is the one assertion left as a hypothesis, at the generality of its own source.

## Main results

* `AlgebraicGeometry.Space.isFinitePresentationOnSite_modulePullback`: **Stacks 03DO for the
  clause 03DL(7) at a morphism of algebraic spaces.**  The inverse image of Stacks 03LU of an
  `𝒪_Y`-module of finite presentation on the small étale site is again of finite presentation on
  the small étale site.
* `AlgebraicGeometry.Space.modulePullbackStability`: the three base-change assertions, assembled
  from the two that are available and the flatness assertion of Stacks 05VW taken as the single
  hypothesis.

## Implementation notes

`AlgebraicGeometry.Space.isFinitePresentationOnSite_modulePullback` is the exact companion of
`AlgebraicGeometry.Space.isFiniteTypeOnSite_modulePullback`, which is the same clause of
Stacks 03DO for finite type, and belongs beside it in
`StacksFrontier/AlgebraicGeometry/Spaces/ModulePullbackSupport.lean`; it is here because it is the
one place that consumes it.  Both are instances of a statement about a morphism of ringed topoi
at the morphism `AlgebraicGeometry.Space.smallEtaleRingedToposModulesHom` of Stacks 03G8, for
which `AlgebraicGeometry.Space.modulePullback` is on the nose the pullback of modules of
Stacks 03D6(2), so no comparison isomorphism intervenes.

The flatness hypothesis is written out as a `∀`-statement rather than named, so that no further
piece of data stands between a proof of Stacks 05VW and a value of
`AlgebraicGeometry.Space.ModulePullbackStability`: it is verbatim the `flat` field, and
supplying the tag's statement for `AlgebraicGeometry.Space.IsFlatOver` is all that is left.

The `properSupport` field quantifies over an arbitrary proof that the support is closed, while
Stacks 0CZJ is stated with the proof that finite type supplies; the two agree because the
closedness of a subset is a proposition.

## References

* [Stacks Project, Tag 03DO](https://stacks.math.columbia.edu/tag/03DO)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 05VW](https://stacks.math.columbia.edu/tag/05VW)
* [Stacks Project, Tag 0CZJ](https://stacks.math.columbia.edu/tag/0CZJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Finite presentation of an inverse image -/

variable {X' X : AlgebraicSpaces B S hS}

/-- **Stacks 03DO for the clause 03DL(7) at a morphism of algebraic spaces.**  The inverse image
of Stacks 03LU of an `𝒪_X`-module of finite presentation on the small étale site is again of
finite presentation on the small étale site.

This is `Stacks.Sheaves.FinitePresentation.pullbackModules_isFinitePresentationOnSite` at the
morphism of small étale ringed topoi of Stacks 03G8. -/
theorem isFinitePresentationOnSite_modulePullback (g : X' ⟶ X)
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : SheafOfModules.IsFinitePresentationOnSite F) :
    SheafOfModules.IsFinitePresentationOnSite ((modulePullback B S hS g).obj F) :=
  Stacks.Sheaves.FinitePresentation.pullbackModules_isFinitePresentationOnSite
    (smallEtaleRingedToposModulesHom B S hS g) F hF

/-! ### The three base-change assertions -/

/-- **The base-change stability of modules that the pullback of an object of `Coh_{X/Y}` needs**,
assembled from the two assertions that are theorems here and the flatness assertion of
Stacks 05VW.

Finite presentation of an inverse image is
`AlgebraicGeometry.Space.isFinitePresentationOnSite_modulePullback`, and properness of the support
of an inverse image is `AlgebraicGeometry.Space.isProperOver_supportOfSheaf_modulePullback`.  The
hypothesis is the remaining assertion: in a cartesian square of algebraic spaces, the inverse
image of a quasi-coherent module flat over the target is flat over the new target. -/
theorem modulePullbackStability
    (hflat : ∀ {X Y X' Y' : AlgebraicSpaces B S hS} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y}
      {g : Y' ⟶ Y}, IsPullback g' f' f g → ∀ F : Modules.{u, u} B S hS X.1 X.2,
        F.IsQuasicoherentOnSite → IsFlatOver B S hS X.2 f.hom F →
        IsFlatOver B S hS X'.2 f'.hom ((modulePullback B S hS g').obj F)) :
    ModulePullbackStability B S hS where
  finitePresentation := fun g F hF => isFinitePresentationOnSite_modulePullback B S hS g F hF
  flat := hflat
  properSupport := fun sq hf F hqc hft _hU hproper =>
    ⟨_, isProperOver_supportOfSheaf_modulePullback B S hS sq hf F hqc hft hproper⟩

end AlgebraicGeometry.Space

end

