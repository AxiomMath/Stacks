module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoherentFinitePresentation
public import StacksFrontier.AlgebraicGeometry.OneDimensionalLocal.Basic
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.ZeroDimensionalFibres

/-!
# Zero-dimensional fibres: the stalk of a higher direct image

Let `f : X ⟶ Y` be a proper morphism onto a locally Noetherian scheme and let `y ∈ Y` be a point
whose fibre has dimension `0`. This file proves that `(Rᵖ f_* ℱ)_y = 0` for every coherent `ℱ`
on `X` and every `p > 0`, and draws the global consequence that `Rᵖ f_* ℱ` is a zero object when
*every* fibre of `f` is zero-dimensional.

These two statements are the fibre-dimension-zero instances of [Stacks, Tag 02V7], which is
proved for an arbitrary fibre dimension in
`StacksFrontier/AlgebraicGeometry/HigherDirectImageFibreDimension/GeneralDimension.lean` and carries
its attribute there. What is done here is the same conclusion by a *different and far shorter
route*, which is why it is kept: at `d = 0` Zariski's main theorem applies, so neither the
theorem on formal functions ([Stacks, Tag 02OD], through [Stacks, Tag 02OC]) nor the coherence of
the higher direct images ([Stacks, Tag 02O5]) — both of which the general argument uses — is
needed. A proper morphism with zero-dimensional fibres is finite, so the preimage of an affine
open is affine and the cohomology of a quasi-coherent module on it vanishes in positive degrees
([Stacks, Tag 01XB]). That route is already carried out in
`StacksFrontier/AlgebraicGeometry/TopDegreeBaseChange/ZeroDimensionalFibres.lean` for
[Stacks, Tag 0E7D], the generalisation to a non-Noetherian base and a merely quasi-coherent
module; what is added here is the statement in the vocabulary of [Stacks, Tag 02V7] itself.

## Main results

* `Stacks.AlgebraicGeometry.FibreDimension.isZero_stalk_rightDerivedPlus_of_fiber_dimension_zero`:
  the stalk at `y` of `Rᵖ f_* ℱ` vanishes for `p > 0`, for a fibre of dimension `0`.
* `Stacks.AlgebraicGeometry.FibreDimension.isZero_rightDerivedPlus_of_forall_fiber_dimension_zero`:
  the same with `y` quantified away: `Rᵖ f_* ℱ = 0` for `p > 0` when every fibre of `f` is
  zero-dimensional.

## Implementation notes

No Stacks attribute for Tag 02V7 is carried here. The tag asserts the vanishing for an arbitrary
`d`, and that is the content of
`Stacks.AlgebraicGeometry.FibreDimension.isZero_stalk_rightDerivedPlus_of_fiber_dimension_le`,
which is where the attribute sits. The two statements below are its `d = 0` instances, obtained
independently of it.

Fibre dimension is `topologicalKrullDim (f.fiber y)` and is bounded above rather than fixed, as
everywhere else in this development; the source's `dim(X_y) = d` is read as `dim(X_y) ≤ d`, which
is the direction its conclusion uses.

Coherence of `ℱ` is the hypothesis [Stacks, Tag 02V7] makes; only quasi-coherence is used, by
`Stacks.SheafOfModules.isQuasicoherent_of_isCoherent` ([Stacks, Tag 01BW]). Local Noetherianness
of `Y` is likewise the tag's hypothesis and is not needed at `d = 0`; both are kept so that the
statements are specialisations of the tag's own and not strengthenings of it.

## References

* [Stacks Project, Tag 02V7](https://stacks.math.columbia.edu/tag/02V7)
* [Stacks Project, Tag 0E7D](https://stacks.math.columbia.edu/tag/0E7D)
* [Stacks Project, Tag 02OD](https://stacks.math.columbia.edu/tag/02OD)
* [Stacks Project, Tag 02O5](https://stacks.math.columbia.edu/tag/02O5)
* [Stacks Project, Tag 01BW](https://stacks.math.columbia.edu/tag/01BW)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.AlgebraicGeometry.FibreDimension

attribute [local instance] HasDerivedCategory.standard

noncomputable section

/-- **Vanishing at a zero-dimensional fibre.** Let `f : X ⟶ Y` be a proper morphism onto a
locally Noetherian scheme and let `y ∈ Y` be a point whose fibre has dimension `0`. Then the
stalk at `y` of `Rᵖ f_* ℱ` vanishes for every coherent `ℱ` and every `p > 0`.

A coherent module is quasi-coherent ([Stacks, Tag 01BW]), and for a quasi-coherent module the
vanishing is `Stacks.AlgebraicGeometry.TopDegreeBaseChange`'s
`isZero_stalk_rightDerivedPlus_of_fiber_dimension_le_zero`,
which is the `d = 0` case of [Stacks, Tag 0E7D] proved through Zariski's main theorem. Neither
the theorem on formal functions nor coherence of the higher direct images enters. -/
theorem isZero_stalk_rightDerivedPlus_of_fiber_dimension_zero
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] [IsLocallyNoetherian Y] (y : Y)
    (hdim : topologicalKrullDim (f.fiber y) ≤ ((0 : ℕ) : WithBot ℕ∞))
    (F : X.Modules) [F.IsCoherent] (p : ℤ) (hp : 0 < p) :
    IsZero ((((Scheme.Modules.pushforward f).rightDerivedPlus p).obj F).presheaf.stalk y) :=
  have : F.IsQuasicoherent := _root_.isQuasicoherent_of_isCoherent F
  TopDegreeBaseChange.isZero_stalk_rightDerivedPlus_of_fiber_dimension_le_zero f y hdim F p hp

/-- **Vanishing for a proper morphism all of whose fibres are zero-dimensional.** Here every
stalk of `Rᵖ f_* ℱ` vanishes for `p > 0`, so the higher direct image is a zero object.

A sheaf of modules on a scheme whose stalks all vanish is zero
(`AlgebraicGeometry.isZero_of_forall_isZero_stalk`). -/
theorem isZero_rightDerivedPlus_of_forall_fiber_dimension_zero
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] [IsLocallyNoetherian Y]
    (hdim : ∀ y : Y, topologicalKrullDim (f.fiber y) ≤ ((0 : ℕ) : WithBot ℕ∞))
    (F : X.Modules) [F.IsCoherent] (p : ℤ) (hp : 0 < p) :
    IsZero (((Scheme.Modules.pushforward f).rightDerivedPlus p).obj F) :=
  _root_.AlgebraicGeometry.isZero_of_forall_isZero_stalk _ fun y =>
    isZero_stalk_rightDerivedPlus_of_fiber_dimension_zero f y (hdim y) F p hp

end

end Stacks.AlgebraicGeometry.FibreDimension

end
