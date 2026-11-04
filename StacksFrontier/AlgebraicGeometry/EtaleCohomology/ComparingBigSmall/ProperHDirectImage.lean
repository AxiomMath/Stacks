module

public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.ComparingBigSmall.ChangeOfTopologyDirectImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ProperPushforwardBaseChangeUnconditional
public import StacksFrontier.AlgebraicGeometry.Topologies.ChangeOfSites.HToEtaleSquares
public import StacksFrontier.AlgebraicGeometry.Topologies.HTopologyEtaleComparisonProperBaseChange

/-!
# Extension from the small étale site to the big h site commutes with a proper direct image

Let `B` be a chosen big h site and `f : X ⟶ Y` a morphism of it. Write `a_X` for the morphism
of topoi from the big h topos over `X` to the small étale topos of `X`, the composite
`a_X = π_X ∘ ε_X` of the change of topology `ε_X` to the big étale topos and of the projection
`π_X` to the small étale topos (`AlgebraicGeometry.hToSmallEtaleMorphism`). The square of topoi
`a_Y ∘ f_{big,h} = f_{small} ∘ a_X` of Stacks 0EW9 has a canonical base change map

`a_Y⁻¹ ∘ f_{small,*} ⟶ f_{big,h,*} ∘ a_X⁻¹`,

`AlgebraicGeometry.bigHSmallEtaleBaseChange`, its mate. This file proves that it is an
isomorphism when `f` is proper, Stacks 0EWA.

## Main definitions

* `AlgebraicGeometry.bigHSmallEtaleDirectImageIso` — for `f` proper, the isomorphism
  `a_Y⁻¹ ∘ f_{small,*} ≅ f_{big,h,*} ∘ a_X⁻¹` given by the base change map.

## Main results

* `AlgebraicGeometry.isIso_bigHSmallEtaleBaseChange` — **Stacks 0EWA**: for `f` proper the base
  change map is an isomorphism.

## Implementation notes

The source deduces the result from Stacks 0DDJ (1) and Stacks 0EW8.
`AlgebraicGeometry.isIso_bigHSmallEtaleBaseChange_of_isIso_smallEtaleSetBaseChange` carries out
this deduction from two inputs, both supplied here:

* proper base change for sheaves of sets (Stacks 0A3U) for `f`, which is
  `Stacks.EtaleCohomology.isIso_smallEtaleSetBaseChange_of_isProper`;
* descent of `π_X⁻¹G` along proper surjective morphisms of finite presentation over `X`, the half
  of Stacks 0EW8 the source deduces from Stacks 0A3T, which is
  `AlgebraicGeometry.smallEtaleInverseImage_isProperFinitePresentationSheaf`.

## References

* [Stacks Project, Tag 0EWA](https://stacks.math.columbia.edu/tag/0EWA)
* [Stacks Project, Tag 0EW8](https://stacks.math.columbia.edu/tag/0EW8)
* [Stacks Project, Tag 0EW9](https://stacks.math.columbia.edu/tag/0EW9)
* [Stacks Project, Tag 0DDJ](https://stacks.math.columbia.edu/tag/0DDJ)
* [Stacks Project, Tag 0A3U](https://stacks.math.columbia.edu/tag/0A3U)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

universe u

namespace AlgebraicGeometry

variable (B : BigHSite.{u}) {X Y : B.Schemes} (f : X ⟶ Y)

/-- **Stacks 0EWA.** Let `f : X ⟶ Y` be a proper morphism of the big h site. Then the base change
map `a_Y⁻¹ ∘ f_{small,*} ⟶ f_{big,h,*} ∘ a_X⁻¹` of the square of topoi of Stacks 0EW9 is an
isomorphism. -/
@[stacks 0EWA]
public theorem isIso_bigHSmallEtaleBaseChange [IsProper (B.inclusion.map f)] :
    IsIso (bigHSmallEtaleBaseChange B f) :=
  isIso_bigHSmallEtaleBaseChange_of_isIso_smallEtaleSetBaseChange B f
    (fun G => smallEtaleInverseImage_isProperFinitePresentationSheaf B X.1 X.2 G)
    fun _ _ g g' f' sq =>
      have : IsProper ((hAssociatedBigEtaleSite B).inclusion.map f) :=
        ‹IsProper (B.inclusion.map f)›
      Stacks.EtaleCohomology.isIso_smallEtaleSetBaseChange_of_isProper _ g g' f' sq

/-- **Stacks 0EWA**, as an isomorphism of functors: for `f` proper,
`a_Y⁻¹ ∘ f_{small,*} ≅ f_{big,h,*} ∘ a_X⁻¹`, by the base change map. -/
public def bigHSmallEtaleDirectImageIso [IsProper (B.inclusion.map f)] :
    (hAssociatedBigEtaleSite B).smallPushforward f (Type (u + 1)) ⋙
        (hToSmallEtaleMorphism B Y).inverseImage ≅
      (hToSmallEtaleMorphism B X).inverseImage ⋙
        (Over.pullback f).sheafPushforwardContinuous (Type (u + 1))
          (B.topology.over Y) (B.topology.over X) :=
  haveI := isIso_bigHSmallEtaleBaseChange B f
  asIso (bigHSmallEtaleBaseChange B f)

end AlgebraicGeometry

end
