module

public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothMorphismProperty
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothRelationBaseChangeStepC

/-!
# Step C of Stacks 0DS9 at an arbitrary iterated cartesian square of presheaves

`AlgebraicGeometry.Space.AlgebraicSpaces.ringKrullDim_etaleLocalRing_stepC_of_isClosed` is the
Step C identity of **Stacks 0DS9** for the doubled base change
`R' = (U' ×_{h, U, t} R) ×_{s, U} U'` built as an iterated fibre product in the category
`AlgebraicGeometry.AlgebraicSpaces`. The chart comparison of Stacks 0DS9 does not meet the
doubled base change in that form: the refined self-intersection of a chart arrives as an
iterated *presheaf* pullback —
`AlgebraicGeometry.Stack.isPullback_representingMap_refinementTargetBaseChange`
and `AlgebraicGeometry.Stack.isPullback_representingMap_refinementSourceBaseChange` — of whatever
algebraic spaces happen to present the apexes of the two 2-fibre products.

This file states Step C for that form: two cartesian squares of presheaves

```
A --- q ---> R        X --- p ---> A
|            |        |            |
m            t        n          q ≫ s
↓            ↓        ↓            ↓
U' -- h ---> U        U' -- h ---> U
```

with no hypothesis that either apex is a chosen fibre product. The identity is the same one, and
so is its proof: the two legs `p` and `q` are base changes of `h`, hence smooth, and the
dimension formula along a smooth morphism is applied three times.

## Main results

* `AlgebraicGeometry.Space.isSmooth_fst_of_isPullback`: a leg of a cartesian square of
  presheaves whose opposite side is smooth is smooth — **Stacks 03ZE** read at a cartesian square
  of presheaves rather than at the chosen fibre product of algebraic spaces.
* `AlgebraicGeometry.Space.ringKrullDim_etaleLocalRing_stepC_isPullback_of_closedFibre_eq`: the
  Step C identity reduced to the two closed-fibre comparisons, one for each leg.
* `AlgebraicGeometry.Space.ringKrullDim_etaleLocalRing_stepC_isPullback_of_isClosed`: the same
  with the two comparisons discharged from
  `AlgebraicGeometry.Space.HasClosedChartFibreSquare`, which is where the closedness of the
  chart point in its chart fibres enters.

## Relation to the fibre-product form, and what is not duplicated

`AlgebraicGeometry.Space.AlgebraicSpaces.relationBaseChange` is one instance of the configuration
below — its two legs sit in cartesian squares of presheaves by
`AlgebraicGeometry.Space.AlgebraicSpaces.isPullback_relationBaseChangeFst` and
`AlgebraicGeometry.Space.AlgebraicSpaces.isPullback_relationBaseChangeSnd` — so the results here
*generalise* those of `SmoothRelationBaseChangeStepC.lean` rather than repeating them. Nothing
below re-proves a closed-fibre comparison: `hfst` and `hsnd` are discharged by the one public
route, `AlgebraicGeometry.Space.ringKrullDim_closedFibre_eq_of_hasClosedChartFibreSquare`, which
is already stated for an arbitrary cartesian square of presheaves. What this file adds is the
arrangement at that generality, and the base-change smoothness of the two legs in the same form.

**The closedness is not removable**, exactly as in the fibre-product form: the module
documentation of `StacksFrontier/AlgebraicGeometry/Spaces/BaseChangeClosedFibreDimension.lean`
records the counterexamples, and the docstring of
`AlgebraicGeometry.Space.AlgebraicSpaces.ringKrullDim_etaleLocalRing_stepC_of_closedFibre_eq`
records one which lies on the diagonal, so being on the diagonal does not supply it.

**The two `U'`-coordinates still have to be identified by the caller.** `hxfst` and `hxsnd` say
that the coordinate `n(r)` of the outer square and the coordinate `m(p(r))` of the inner one are
the same geometric point of `U'`; they are different in general, and the conclusion has room for
only one.

## Implementation notes

Smoothness of a leg is Stacks 03ZE, which the repository has as stability under base change of
`AlgebraicGeometry.Space.smoothMorphismProperty`, a property of morphisms of the category of
algebraic spaces. Transporting it to a cartesian square of presheaves is the only place where
that category is touched: the chosen fibre product of algebraic spaces is cartesian on the
underlying presheaves (`AlgebraicGeometry.AlgebraicSpaces.isPullback_hom`), so the given apex is
isomorphic to it, and an isomorphism of presheaves between algebraic spaces is étale, hence
smooth.

## References

* [Stacks Project, Tag 00ON](https://stacks.math.columbia.edu/tag/00ON)
* [Stacks Project, Tag 03ZE](https://stacks.math.columbia.edu/tag/03ZE)
* [Stacks Project, Tag 0DS9](https://stacks.math.columbia.edu/tag/0DS9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 03ZE at a cartesian square of presheaves.** If `IsPullback fst snd f g` is a
cartesian square of presheaves on the big fppf site all four of whose corners are algebraic
spaces, and `g` is smooth, then the leg `fst` opposite to it is smooth.

The repository has Stacks 03ZE as stability under base change of
`AlgebraicGeometry.Space.smoothMorphismProperty`, which is a property of morphisms of the
category `AlgebraicGeometry.AlgebraicSpaces` and so speaks about the chosen fibre product there.
This is that statement at an arbitrary cartesian square: the chosen fibre product is cartesian on
the underlying presheaves by `AlgebraicGeometry.AlgebraicSpaces.isPullback_hom`, so the given
apex is isomorphic to it over the two legs, and an isomorphism of presheaves between algebraic
spaces is étale (`AlgebraicGeometry.Space.isEtale_of_isIso`), hence smooth. -/
theorem isSmooth_fst_of_isPullback {E₁ E₂ Z T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hE₁ : IsAlgebraicSpace B S hS E₁) (hE₂ : IsAlgebraicSpace B S hS E₂)
    (hZ : IsAlgebraicSpace B S hS Z) (hT : IsAlgebraicSpace B S hS T)
    {f : E₁ ⟶ Z} {g : E₂ ⟶ Z} {fst : T ⟶ E₁} {snd : T ⟶ E₂}
    (sq : IsPullback fst snd f g) (hg : IsSmooth B S hS g) :
    IsSmooth B S hS fst := by
  let F : (⟨E₁, hE₁⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Z, hZ⟩ := ObjectProperty.homMk f
  let G : (⟨E₂, hE₂⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Z, hZ⟩ := ObjectProperty.homMk g
  have hcan : IsPullback (pullback.fst F G).hom (pullback.snd F G).hom f g :=
    AlgebraicSpaces.isPullback_hom B S hS (IsPullback.of_hasPullback F G)
  rw [← sq.isoIsPullback_hom_fst _ _ hcan]
  exact isSmooth_comp B S hS hT (pullback F G).property hE₁ _ _
    (isSmooth_of_isEtale B S hS (pullback F G).property
      (isEtale_of_isIso B S hS (sq.isoIsPullback _ _ hcan).hom))
    (MorphismProperty.pullback_fst (P := smoothMorphismProperty B S hS) F G hg)

section StepC

variable {U U' R A X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **The Step C identity of Stacks 0DS9 at an iterated cartesian square of presheaves, reduced
to the two closed-fibre comparisons.** In the subtraction-free form

`dim(𝒪_{U', ū'}) + dim(𝒪_{U', ū'}) + dim(𝒪_{R, q(p(r))})
    = dim(𝒪_{U, ū}) + dim(𝒪_{U, ū}) + dim(𝒪_{X, r})`,

which is `2 dim(𝒪_{U', ū'}) - dim(𝒪_{X, r}) = 2 dim(𝒪_{U, ū}) - dim(𝒪_{R, q(p(r))})` with the
two differences cleared, `ringKrullDim` being valued in `WithBot ℕ∞` where subtraction is not
available.

This is
`AlgebraicGeometry.Space.AlgebraicSpaces.ringKrullDim_etaleLocalRing_stepC_of_closedFibre_eq`
with the doubled base change replaced by two arbitrary cartesian squares of presheaves, and it is
proved the same way: the two legs are base changes of `h`, hence smooth
(`AlgebraicGeometry.Space.isSmooth_fst_of_isPullback`), so the dimension formula
`AlgebraicGeometry.Space.ringKrullDim_etaleLocalRing_eq_add_closedFibre_of_isSmooth` applies
along each of them and along `h`. No cancellation in `WithBot ℕ∞` is performed: the identity is
a substitution.

LIKE THAT THEOREM THIS IS A REDUCTION. The hypotheses `hfst` and `hsnd` say that each leg has, at
the given point, a closed fibre of the same dimension as the closed fibre of `h` itself, and they
are false at a point which is not closed in its fibre — see the module documentation. They are
discharged under closedness in
`AlgebraicGeometry.Space.ringKrullDim_etaleLocalRing_stepC_isPullback_of_isClosed`. -/
theorem ringKrullDim_etaleLocalRing_stepC_isPullback_of_closedFibre_eq
    (hU : IsAlgebraicSpace B S hS U) (hU' : IsAlgebraicSpace B S hS U')
    (hR : IsAlgebraicSpace B S hS R) (hA : IsAlgebraicSpace B S hS A)
    (hX : IsAlgebraicSpace B S hS X)
    (h : U' ⟶ U) (s t : R ⟶ U) (q : A ⟶ R) (m : A ⟶ U') (p : X ⟶ A) (n : X ⟶ U')
    (hAsq : IsPullback q m t h) (hXsq : IsPullback p n (q ≫ s) h)
    (hh : IsSmooth B S hS h)
    (hNU : HasEtaleLocalProperty B S hS U (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (hNR : HasEtaleLocalProperty B S hS R (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (r : GeometricPoint B S hS X) (x' : GeometricPoint B S hS U')
    (hfst : ringKrullDim (closedFibreEtaleLocalRing B S hS hX p r) =
      ringKrullDim (closedFibreEtaleLocalRing B S hS hU' h x'))
    (hsnd : ringKrullDim (closedFibreEtaleLocalRing B S hS hA q (geometricPointMap p r)) =
      ringKrullDim (closedFibreEtaleLocalRing B S hS hU' h x')) :
    ringKrullDim (etaleLocalRing B S hS U' x') + ringKrullDim (etaleLocalRing B S hS U' x') +
        ringKrullDim (etaleLocalRing B S hS R (geometricPointMap q (geometricPointMap p r))) =
      ringKrullDim (etaleLocalRing B S hS U (geometricPointMap h x')) +
          ringKrullDim (etaleLocalRing B S hS U (geometricPointMap h x')) +
        ringKrullDim (etaleLocalRing B S hS X r) := by
  have hq : IsSmooth B S hS q := isSmooth_fst_of_isPullback B S hS hR hU' hU hA hAsq hh
  have hp : IsSmooth B S hS p := isSmooth_fst_of_isPullback B S hS hA hU' hU hX hXsq hh
  have hNA : HasEtaleLocalProperty B S hS A (fun T : Scheme.{u} => IsLocallyNoetherian T) :=
    isLocallyNoetherian_of_isLocallyOfFiniteType B S hS hA hR q
      (isLocallyOfFiniteType_of_isSmooth B S hS hq) hNR
  rw [ringKrullDim_etaleLocalRing_eq_add_closedFibre_of_isSmooth B S hS hX hA p hp hNA r,
    ringKrullDim_etaleLocalRing_eq_add_closedFibre_of_isSmooth B S hS hA hR q hq hNR
      (geometricPointMap p r),
    hfst, hsnd,
    ringKrullDim_etaleLocalRing_eq_add_closedFibre_of_isSmooth B S hS hU' hU h hh hNU x']
  abel

/-- **The Step C identity of Stacks 0DS9 at an iterated cartesian square of presheaves.** The two
closed-fibre comparisons of
`AlgebraicGeometry.Space.ringKrullDim_etaleLocalRing_stepC_isPullback_of_closedFibre_eq` are
discharged here from `AlgebraicGeometry.Space.HasClosedChartFibreSquare`, one condition for each
leg, through
`AlgebraicGeometry.Space.ringKrullDim_closedFibre_eq_of_hasClosedChartFibreSquare`.

THE HYPOTHESES THAT REMAIN ARE OF EXACTLY TWO KINDS, and neither is removable.

`hxfst` and `hxsnd` identify the two `U'`-coordinates of `r`: the closed fibre of the outer leg
is compared with the closed fibre of `h` at `n(r)` and that of the inner leg with the closed
fibre of `h` at `m(p(r))`, and these are different points of `U'` in general, whereas the
conclusion has room for only one.

`hcl₁` and `hcl₂` are the CLOSEDNESS of the chart point in its chart fibres, one for each leg.
They are caller-supplied and NOT derivable; the module documentation of
`StacksFrontier/AlgebraicGeometry/Spaces/BaseChangeClosedFibreDimension.lean` records the
counterexamples, and
`AlgebraicGeometry.Space.exists_chart_square_hasClosedChartFibreSquare_of_isPullback` is the
route by which a caller supplies one: for a leg which sits in a cartesian square the chart square
always exists, and closedness of its chart point is the only thing left. -/
theorem ringKrullDim_etaleLocalRing_stepC_isPullback_of_isClosed
    (hU : IsAlgebraicSpace B S hS U) (hU' : IsAlgebraicSpace B S hS U')
    (hR : IsAlgebraicSpace B S hS R) (hA : IsAlgebraicSpace B S hS A)
    (hX : IsAlgebraicSpace B S hS X)
    (h : U' ⟶ U) (s t : R ⟶ U) (q : A ⟶ R) (m : A ⟶ U') (p : X ⟶ A) (n : X ⟶ U')
    (hAsq : IsPullback q m t h) (hXsq : IsPullback p n (q ≫ s) h)
    (hh : IsSmooth B S hS h)
    (hNU : HasEtaleLocalProperty B S hS U (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (hNR : HasEtaleLocalProperty B S hS R (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (r : GeometricPoint B S hS X) (x' : GeometricPoint B S hS U')
    (hxfst : geometricPointMap n r = x')
    (hxsnd : geometricPointMap m (geometricPointMap p r) = x')
    (hcl₁ : HasClosedChartFibreSquare B S hS h p n r)
    (hcl₂ : HasClosedChartFibreSquare B S hS h q m (geometricPointMap p r)) :
    ringKrullDim (etaleLocalRing B S hS U' x') + ringKrullDim (etaleLocalRing B S hS U' x') +
        ringKrullDim (etaleLocalRing B S hS R (geometricPointMap q (geometricPointMap p r))) =
      ringKrullDim (etaleLocalRing B S hS U (geometricPointMap h x')) +
          ringKrullDim (etaleLocalRing B S hS U (geometricPointMap h x')) +
        ringKrullDim (etaleLocalRing B S hS X r) := by
  have hlft : IsLocallyOfFiniteType B S hS h := isLocallyOfFiniteType_of_isSmooth B S hS hh
  refine ringKrullDim_etaleLocalRing_stepC_isPullback_of_closedFibre_eq B S hS hU hU' hR hA hX
    h s t q m p n hAsq hXsq hh hNU hNR r x' ?_ ?_
  · rw [← hxfst]
    exact ringKrullDim_closedFibre_eq_of_hasClosedChartFibreSquare B S hS hA hU hU' h p n hX
      hlft r hcl₁
  · rw [← hxsnd]
    exact ringKrullDim_closedFibre_eq_of_hasClosedChartFibreSquare B S hS hR hU hU' h q m hA
      hlft (geometricPointMap p r) hcl₂

end StepC

end AlgebraicGeometry.Space

end
