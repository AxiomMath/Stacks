module

public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackPullbackStability
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleBaseChange

/-!
# Base-change stability of modules of finite presentation

An object of `Coh_{X/Y}` carries an `𝒪_{X_T}`-module which is quasi-coherent, of finite
presentation, flat over the test scheme and of proper support, and pulling such an object back
along a morphism of test schemes asks each of those four conditions to be inherited by an inverse
image.  Three assertions about inverse images of modules on algebraic spaces are what that
amounts to: finite presentation is inherited (Stacks 03DO, clause 03DL(7)), flatness over the
target is inherited in a cartesian square (Stacks 05VW), and so is properness of the support over
the target (Stacks 0CZJ).

`AlgebraicGeometry.Space.ModulePullbackStability` of
`StacksFrontier/AlgebraicGeometry/Quot/CoherentStackFibered.lean` collects the three with the
flatness assertion stated for a *quasi-coherent* module, and in that shape it cannot be proved
here: Stacks 05VW reads flatness at the geometric stalks, and assembling the pointwise condition
back into flatness over the target needs quasi-coherence of the inverse image as well as of the
module, which quasi-coherence of the module alone does not give — Stacks 03GA for an arbitrary
morphism of algebraic spaces is not available in this development.

The flatness assertion is stated here for a module of **finite presentation** instead.  That is
no loss: the inverse image of a module of finite presentation is again of finite presentation,
hence quasi-coherent, so both quasi-coherence hypotheses of Stacks 05VW are discharged and the
assertion becomes a theorem.  And it is the generality every consumer uses, an object of
`Coh_{X/Y}` carrying `SheafOfModules.IsFinitePresentationOnSite` by
`AlgebraicGeometry.Space.CoherentObject.finitePresentation`.

## Main results

* `AlgebraicGeometry.Space.isFlatOver_modulePullback_of_isFinitePresentationOnSite`:
  **Stacks 05VW for a module of finite presentation.**  In a cartesian square of algebraic
  spaces, the inverse image of a module of finite presentation flat over the target is flat over
  the new target.
* `AlgebraicGeometry.Space.modulePullbackStabilityOfFinitePresentation`: the three base-change
  assertions, at the generality of a module of finite presentation, **with no hypothesis**.

## Implementation notes

`AlgebraicGeometry.Space.ModulePullbackStabilityOfFinitePresentation` repeats the three fields of
`AlgebraicGeometry.Space.ModulePullbackStability` with one change: the `flat` field asks the
module to be of finite presentation rather than quasi-coherent.  The two other fields are
verbatim.  So the structure here is the weaker of the two — a value of the one in
`StacksFrontier/AlgebraicGeometry/Quot/CoherentStackFibered.lean` gives one of this, quasi-coherence
following from finite presentation by
`SheafOfModules.isQuasicoherentOnSite_of_isFinitePresentationOnSite` — and it is the weaker one
that is provable.  No conversion between the two is written: the one that would type-check takes
the unprovable structure as its hypothesis, and nothing would consume it.

The structure is repeated rather than the original amended because the original's module may not
be edited; `StacksFrontier/AlgebraicGeometry/Quot/CoherentStackFiberedUnconditional.lean` and
`StacksFrontier/AlgebraicGeometry/Quot/CoherentStackBaseChangeUnconditional.lean` rebuild on this
one the two consequences that the original hypothesis was blocking.

`AlgebraicGeometry.Space.isFlatOver_modulePullback` takes both quasi-coherence hypotheses as
instances.  Finite presentation of the module supplies the first through the instance above, and
`AlgebraicGeometry.Space.isFinitePresentationOnSite_modulePullback` supplies the second by giving
finite presentation of the inverse image first.  That route is shorter than the one through
Stacks 03GA for a module of finite presentation, which would reach quasi-coherence of the inverse
image without passing through its finite presentation.

## References

* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03DO](https://stacks.math.columbia.edu/tag/03DO)
* [Stacks Project, Tag 03GA](https://stacks.math.columbia.edu/tag/03GA)
* [Stacks Project, Tag 05VW](https://stacks.math.columbia.edu/tag/05VW)
* [Stacks Project, Tag 0CZJ](https://stacks.math.columbia.edu/tag/0CZJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-! ### Flatness over the target of the inverse image of a module of finite presentation -/

/-- **Stacks 05VW, the final assertion, for a module of finite presentation.**  In a cartesian
square of algebraic spaces

```
X' --g'--> X
|f'        |f
v          v
Y' --g---> Y
```

the inverse image of an `𝒪_X`-module of finite presentation flat over `Y` is flat over `Y'`.

This is `AlgebraicGeometry.Space.isFlatOver_modulePullback`, whose two quasi-coherence instances
finite presentation supplies: the module is quasi-coherent because it is of finite presentation,
and its inverse image is of finite presentation by
`AlgebraicGeometry.Space.isFinitePresentationOnSite_modulePullback`, hence quasi-coherent for the
same reason. -/
@[stacks 05VW "the final assertion for a module of finite presentation"]
theorem isFlatOver_modulePullback_of_isFinitePresentationOnSite
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y X' Y' : AlgebraicSpaces B S hS} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (hpb : IsPullback g' f' f g) (F : Modules.{u, u} B S hS X.1 X.2)
    (hF : SheafOfModules.IsFinitePresentationOnSite F)
    (hflat : IsFlatOver B S hS X.2 f.hom F) :
    IsFlatOver B S hS X'.2 f'.hom ((modulePullback B S hS g').obj F) :=
  have := hF
  have := isFinitePresentationOnSite_modulePullback B S hS g' F hF
  isFlatOver_modulePullback B S hS hpb F hflat

/-! ### The three base-change assertions at the generality their consumers use -/

/-- **The base-change stability of modules of finite presentation.**  The three assertions about
inverse images of modules on algebraic spaces that the pullback of an object of `Coh_{X/Y}`
needs, with the flatness assertion of Stacks 05VW stated for a module of finite presentation.

This is `AlgebraicGeometry.Space.ModulePullbackStability` with the `flat` field restated: there
the module is asked only to be quasi-coherent, which leaves the assertion out of reach, and here
it is asked to be of finite presentation, which every consumer has. -/
structure ModulePullbackStabilityOfFinitePresentation (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) where
  /-- **Stacks 03DO, clause (7).**  The inverse image of a module of finite presentation along a
  morphism of algebraic spaces is of finite presentation. -/
  finitePresentation : ∀ {X Y : AlgebraicSpaces B S hS} (g : X ⟶ Y)
    (F : Modules.{u, u} B S hS Y.1 Y.2), F.IsFinitePresentationOnSite →
      ((modulePullback B S hS g).obj F).IsFinitePresentationOnSite
  /-- **Stacks 05VW for a module of finite presentation.**  In a cartesian square of algebraic
  spaces, the inverse image of a module of finite presentation flat over the target is flat over
  the new target. -/
  flat : ∀ {X Y X' Y' : AlgebraicSpaces B S hS} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y}
    {g : Y' ⟶ Y}, IsPullback g' f' f g → ∀ F : Modules.{u, u} B S hS X.1 X.2,
      F.IsFinitePresentationOnSite → IsFlatOver B S hS X.2 f.hom F →
      IsFlatOver B S hS X'.2 f'.hom ((modulePullback B S hS g').obj F)
  /-- **Stacks 0CZJ.**  In a cartesian square of algebraic spaces whose right vertical morphism
  is locally of finite type, the support of the inverse image of a quasi-coherent module of
  finite type whose support is proper over the target is closed and proper over the new
  target. -/
  properSupport : ∀ {X Y X' Y' : AlgebraicSpaces B S hS} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : IsPullback g' f' f g)
    (hf : IsLocallyOfFiniteType B S hS f.hom) (F : Modules.{u, u} B S hS X.1 X.2),
      F.IsQuasicoherentOnSite → F.IsFiniteTypeOnSite →
      ∀ hU : IsClosed (supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj F)),
      IsProperOver B S hS X.2 Y.2 f.hom hf
          (supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj F)) hU →
      ∃ hU' : IsClosed (supportOfSheaf B S hS X'.1
          ((SheafOfModules.toSheaf _).obj ((modulePullback B S hS g').obj F))),
        IsProperOver B S hS X'.2 Y'.2 f'.hom
          ((isLocallyOfFiniteType_isStableUnderBaseChange B S hS).of_isPullback sq hf)
          (supportOfSheaf B S hS X'.1
            ((SheafOfModules.toSheaf _).obj ((modulePullback B S hS g').obj F))) hU'

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The base-change stability of modules of finite presentation holds.**  Finite presentation
of an inverse image is `AlgebraicGeometry.Space.isFinitePresentationOnSite_modulePullback`,
flatness over the new target is
`AlgebraicGeometry.Space.isFlatOver_modulePullback_of_isFinitePresentationOnSite`, and properness
of the support of an inverse image is
`AlgebraicGeometry.Space.isProperOver_supportOfSheaf_modulePullback`. -/
theorem modulePullbackStabilityOfFinitePresentation :
    ModulePullbackStabilityOfFinitePresentation B S hS where
  finitePresentation g F hF := isFinitePresentationOnSite_modulePullback B S hS g F hF
  flat sq F hF hflat :=
    isFlatOver_modulePullback_of_isFinitePresentationOnSite B S hS sq F hF hflat
  properSupport sq hf F hqc hft _hU hproper :=
    ⟨_, isProperOver_supportOfSheaf_modulePullback B S hS sq hf F hqc hft hproper⟩

end AlgebraicGeometry.Space

end
