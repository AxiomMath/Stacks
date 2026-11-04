module

public import StacksFrontier.Algebra.Homology.DerivedCategory.CompositionOfRightDerivedFunctors
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.AbelianProperDirectImage

/-!
# The acyclicity input of the derived clause of Stacks 0DCU, in its cohomological form

`AbelianProperDirectImage.lean` reduces the derived clause of Stacks 0DCU to a single hypothesis:
for `f : X ⟶ Y` proper, the comparison inverse image `π_X^{-1}` carries a bounded-below complex of
injective abelian sheaves on the small Zariski site of `X` to an `f_{Zar,*}`-acyclic complex. That
hypothesis is stated at the level of the bounded-below homotopy category, as the invertibility of
the unit of `R f_{Zar,*}` at a complex, and in that shape it is neither a statement about objects
nor one that can be read as a vanishing.

This file turns it into one. **Leray's acyclicity lemma** ([Stacks, Tag 015E]) says that a
bounded-below complex whose terms are right acyclic for an additive functor computes the right
derived functor of that functor, so the complex-level hypothesis follows from the object-level one:
`π_X^{-1} J` is right acyclic for `f_{Zar,*}` for every *injective* abelian sheaf `J` on the small
Zariski site of `X`. Since `f_{Zar,*}` is a right adjoint, hence left exact, right acyclicity is in
turn the vanishing `R^i f_{Zar,*}(π_X^{-1} J) = 0` for `i > 0` ([Stacks, Tag 015C] part (2)).

## Main results

All in the namespace `Stacks.Topology.LocallyQuasiCompactZariskiSituation`.

* `isIso_properDerivedImageComparison_of_rightAcyclic`: the derived clause of Stacks 0DCU for a
  proper map, assuming only that `π_X^{-1} J` is right acyclic for `f_{Zar,*}` at every
  injective `J`.
* `isIso_properDerivedImageComparison_of_isZero_rightDerivedPlus`: the same with the hypothesis
  in its cohomological form, `R^i f_{Zar,*}(π_X^{-1} J) = 0` for `i > 0`.
* `preservesFiniteLimits_zariskiSlicePushforward`: `f_{Zar,*}` is left exact, being a right
  adjoint.

## What remains open

The vanishing `R^i f_{Zar,*}(π_X^{-1} J) = 0` is the whole of what the derived clause adds to the
underived one, and it is *not* the injectivity of `π_X^{-1} J`: that is false. Localisation at an
object `Z` of `LC_Zar/X` has an exact left adjoint, so an injective `π_X^{-1} J` would force
`H^i(Z, π_X^{-1} J) = 0` for `i > 0`, while `zariskiCohomologyComparisonIso` identifies that group
with `H^i(Z_top, g'^{-1} J)`, which for `X` a point, `J` the constant sheaf `ℚ` and `Z` a circle is
`ℚ ≠ 0`. The vanishing is nevertheless true, because `R^i f_{Zar,*}` is the *sheafification* of
`Z ↦ H^i(Z ×_Y X, -)` and the presheaf of higher cohomology always has vanishing sheafification.

Obtaining it is the argument Stacks gives for 0DCU (7b): the cohomology clause rewrites
`H^i_{Zar}(Z ×_Y X, π_X^{-1} K)` as `H^i(Z', g'^{-1} K)`, Leray for `f' : Z' ⟶ Z` rewrites that as
`H^i(Z, R f'_* g'^{-1} K)`, and *topological derived proper base change* identifies
`R f'_* g'^{-1}` with `g^{-1} R f_*`, after which the cohomology clause returns the answer to the
big site. The two inputs beyond this file are therefore Leray for a continuous map, which the
library has (`Stacks.Cohomology.Leray.exists_spectralSequence_sectionsFunctor_comp_pushforward`
and, for the form used here, [Stacks, Tag 015E] itself), and the invertibility of
`Stacks.Cohomology.BaseChange.abelianBaseChange` for a proper map, which it does not: the map is
constructed in
`StacksFrontier/Topology/Sheaves/Cohomology/HigherDirectImage/AbelianBaseChangeMap.lean` and is
nowhere proved to be an isomorphism. Stacks itself omits the verification that the canonical map
induces the isomorphism.

These declarations carry no tag. Stacks 0DCU has eight assertions and the
eighth, `proper_derived_image`, is not proved while that hypothesis is a hypothesis.

## References

* [Stacks Project, Tag 0DCU](https://stacks.math.columbia.edu/tag/0DCU)
* [Stacks Project, Tag 015E](https://stacks.math.columbia.edu/tag/015E), Leray's acyclicity lemma
* [Stacks Project, Tag 015C](https://stacks.math.columbia.edu/tag/015C), right acyclicity as a
  vanishing
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace Stacks.Topology.LocallyQuasiCompactZariskiSituation

universe u w v

attribute [local instance] HasDerivedCategory.standard

-- `HomotopyCategory.Plus.hasPointwiseRightDerivedFunctorAt_of_injective` applies to an arbitrary
-- functor out of `K⁺(𝒜)` at an arbitrary object, so instance search reaches for it before the
-- instance that gets the same conclusion from `EnoughInjectives 𝒜`, and then embarks on proving
-- termwise injectivity of an unknown complex. The statements below mention `Functor.rightAcyclic`,
-- which needs that conclusion at every object, so the cheap instance is given precedence here.
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable {S₀ : Set LocallyQuasiCompactHausdorff.{u}} {Bound : Cardinal.{u} → Cardinal.{u}}
  (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound) {X Y : S.category} (f : X ⟶ Y)

/-- **`f_{Zar,*}` is left exact.** It is a right adjoint, the left adjoint being the inverse image
of the localisation morphism, so it preserves all limits. -/
lemma preservesFiniteLimits_zariskiSlicePushforward
    [HasSheafify (S.zariskiTopology.over X) AddCommGrpCat.{max (u + 1) v}] :
    PreservesFiniteLimits ((Over.pullback f).sheafPushforwardContinuous
      AddCommGrpCat.{max (u + 1) v} (S.zariskiTopology.over Y) (S.zariskiTopology.over X)) :=
  have : PreservesLimitsOfSize.{0, 0} ((Over.pullback f).sheafPushforwardContinuous
    AddCommGrpCat.{max (u + 1) v} (S.zariskiTopology.over Y)
    (S.zariskiTopology.over X)) := inferInstance
  PreservesLimitsOfSize.preservesFiniteLimits _

section Derived

variable [HasSheafify (Opens.grothendieckTopology X.obj) AddCommGrpCat.{max (u + 1) v}]
  [HasSheafify (Opens.grothendieckTopology Y.obj) AddCommGrpCat.{max (u + 1) v}]
  [HasSheafify (S.zariskiTopology.over X) AddCommGrpCat.{max (u + 1) v}]
  [HasSheafify (S.zariskiTopology.over Y) AddCommGrpCat.{max (u + 1) v}]
  [EnoughInjectives (Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{max (u + 1) v})]
  [EnoughInjectives (Sheaf (Opens.grothendieckTopology Y.obj) AddCommGrpCat.{max (u + 1) v})]
  [EnoughInjectives (Sheaf (S.zariskiTopology.over X) AddCommGrpCat.{max (u + 1) v})]

/-- **Stacks 0DCU, the derived clause, with its remaining input stated on objects.** For a proper
map the derived Zariski base-change map is invertible as soon as `π_X^{-1} J` is right acyclic for
`f_{Zar,*}` for every injective abelian sheaf `J` on the small Zariski site of `X`.

This is Leray's acyclicity lemma: the terms of `π_X^{-1} I`, for `I` a bounded-below complex of
injectives, are the sheaves `π_X^{-1} J` with `J` injective, so the complex computes
`R f_{Zar,*}` as soon as each of its terms does, which is the hypothesis of
`isIso_properDerivedImageComparison_of_properMap`. -/
theorem isIso_properDerivedImageComparison_of_rightAcyclic
    (hf : StacksDraft.Topology.IsProperMap.{u, u, u}
      (((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).map f) : X.obj → Y.obj))
    (hac : ∀ J : Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{max (u + 1) v},
      Injective J →
        ((Over.pullback f).sheafPushforwardContinuous AddCommGrpCat.{max (u + 1) v}
            (S.zariskiTopology.over Y) (S.zariskiTopology.over X)).rightAcyclic
          ((S.abelianComparisonInverseImage.{u, w, max (u + 1) v} X).obj J)) :
    IsIso (properDerivedImageComparison.{u, w, v} S f) :=
  isIso_properDerivedImageComparison_of_properMap.{u, w, v} S f hf fun K =>
    Functor.isIso_rightDerivedFunctorPlusUnit_app_of_rightAcyclic _ _
      fun n => hac _ (K.obj.as.X n).property

/-- **Stacks 0DCU, the derived clause, with its remaining input in cohomological form.** For a
proper map the derived Zariski base-change map is invertible as soon as
`R^i f_{Zar,*}(π_X^{-1} J) = 0` for every `i > 0` and every injective abelian sheaf `J` on the
small Zariski site of `X`.

Right acyclicity for a left exact functor is exactly that vanishing ([Stacks, Tag 015C] part (2)),
and `f_{Zar,*}` is left exact by `preservesFiniteLimits_zariskiSlicePushforward`. -/
theorem isIso_properDerivedImageComparison_of_isZero_rightDerivedPlus
    (hf : StacksDraft.Topology.IsProperMap.{u, u, u}
      (((S.qcSite.inclusion ⋙ locallyQuasiCompactHausdorffToTop).map f) : X.obj → Y.obj))
    (hac : ∀ J : Sheaf (Opens.grothendieckTopology X.obj) AddCommGrpCat.{max (u + 1) v},
      Injective J → ∀ i > 0, IsZero ((((Over.pullback f).sheafPushforwardContinuous
          AddCommGrpCat.{max (u + 1) v} (S.zariskiTopology.over Y)
          (S.zariskiTopology.over X)).rightDerivedPlus i).obj
        ((S.abelianComparisonInverseImage.{u, w, max (u + 1) v} X).obj J))) :
    IsIso (properDerivedImageComparison.{u, w, v} S f) :=
  isIso_properDerivedImageComparison_of_rightAcyclic.{u, w, v} S f hf fun J hJ =>
    ((Functor.rightAcyclic_iff_isIso_and_isZero_rightDerivedPlus _ _).2
      (preservesFiniteLimits_zariskiSlicePushforward.{u, w, v} S f)).2 (hac J hJ)

end Derived

end Stacks.Topology.LocallyQuasiCompactZariskiSituation

end
