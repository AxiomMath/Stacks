module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.AffineSections
public import StacksFrontier.AlgebraicGeometry.Thickenings.Affine

/-!
# Regular functions on an affine étale scheme chart of a thickening

Let `G ⊂ X` be a thickening of algebraic spaces over a scheme `S`, of arbitrary order, and let
`U` be an object of the small étale site of `X` (Stacks 03ED), that is a scheme étale over `X`,
whose base change `G ×_X U` along the inclusion is affine. This file proves, with nothing
granted, that `U` is affine and that the restriction map
`Γ(U, 𝒪_U) → Γ(G ×_X U, 𝒪_{G ×_X U})`
along the cartesian projection is surjective: the case of a scheme chart of Stacks 05ZQ.

Both ends of the cartesian projection are then schemes, so the projection is a thickening of
schemes and `Stacks.Thickenings.isAffine_of_isThickening`, the unconditional Stacks 06AD,
supplies the affineness step that the source's proof defers to Stacks 07VS. For an arbitrary
object of the spaces-étale site, and with the source's own quantifier over an affine object of
the site of `G`, the statement is
`AlgebraicGeometry.Space.surjective_globalFunctionsMap_of_isThickening` in
`StacksFrontier/AlgebraicGeometry/Spaces/Thickenings/AffineSectionsSpacesEtale.lean`.

## Main results

* `AlgebraicGeometry.Space.isAffineSpace_of_isClosedImmersion_of_isSurjective_of_representable`:
  a thickening of algebraic spaces with affine closed subspace and *representable* ambient space
  has affine ambient space.
* `AlgebraicGeometry.Space.isAffineSpace_chart_of_isThickening_of_isAffineSpace_baseChange`: in
  a thickening `G ⊂ X`, an étale scheme chart of `X` whose base change to `G` is affine is
  itself affine.
* `AlgebraicGeometry.Space.surjective_globalFunctionsMap_chart_projection_of_isThickening`:
  **Stacks 05ZQ** at a thickening of arbitrary order with nothing granted, for an étale scheme
  chart of the ambient space.

## References

* [Stacks Project, Tag 05ZQ](https://stacks.math.columbia.edu/tag/05ZQ)
* [Stacks Project, Tag 03ED](https://stacks.math.columbia.edu/tag/03ED)
* [Stacks Project, Tag 06AD](https://stacks.math.columbia.edu/tag/06AD)
* [Stacks Project, Tag 07VS](https://stacks.math.columbia.edu/tag/07VS)
* [Stacks Project, Tag 07VT](https://stacks.math.columbia.edu/tag/07VT)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Thickenings

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {X : AlgebraicSpaces B S hS} {G : Subfunctor X.1}

/-! ### Affineness of a representable ambient space -/

/-- **A thickening of an affine algebraic space whose ambient space is representable is
affine.** Let `p : Z ⟶ W` be a closed immersion of algebraic spaces over `S` which is
surjective on points, with `Z` affine, and let `e` identify `W` with the algebraic space
represented by an object `T` of the site. Then `W` is affine.

Representability of the closed immersion `p` turns `e.inv` into a cartesian square whose
projection `P ⟶ T` has an underlying morphism of schemes that is a closed immersion and, by
`AlgebraicGeometry.Space.presheafSurjective_of_isSurjective`, surjective; that is a thickening
of schemes. Its source is affine, because the other leg of the square is an isomorphism, so `P`
represents the affine `Z`. Hence Stacks 06AD, `Stacks.Thickenings.isAffine_of_isThickening`,
makes the scheme underlying `T` affine.

This is the representable case of the thickening case of Stacks 07VT, which for an arbitrary
algebraic space `W` is
`AlgebraicGeometry.Space.isAffineSpace_of_isClosedImmersion_of_isSurjective`; it is the case
the source's proof of Stacks 05ZQ uses at an étale scheme chart. -/
theorem isAffineSpace_of_isClosedImmersion_of_isSurjective_of_representable
    {Z W : AlgebraicSpaces B S hS} (p : Z ⟶ W)
    (hp : IsClosedImmersion B S hS p.hom) (hsurj : IsSurjective B S hS p.hom)
    {T : BigFppfOver B S hS} (e : W.obj ≅ yoneda.obj T)
    (hZ : IsAffineSpace B S hS Z.obj) :
    IsAffineSpace B S hS W.obj := by
  have hsq : IsPullback (hp.rep.fst e.inv) (yoneda.map (hp.rep.snd e.inv)) p.hom e.inv :=
    hp.rep.isPullback e.inv
  have hci : _root_.AlgebraicGeometry.IsClosedImmersion
      ((BigFppfOver.toScheme B S hS).map (hp.rep.snd e.inv)) := hp.property_snd e.inv
  have hsj : _root_.AlgebraicGeometry.Surjective
      ((BigFppfOver.toScheme B S hS).map (hp.rep.snd e.inv)) :=
    (presheafSurjective_of_isSurjective B S hS p.hom hp.rep hsurj).property_snd e.inv
  have : IsIso (hp.rep.fst e.inv) := hsq.isIso_fst_of_isIso
  obtain ⟨T₀, hT₀, ⟨e₀⟩⟩ := hZ
  have eP : yoneda.obj (hp.rep.pullback e.inv) ≅ yoneda.obj T₀ :=
    (asIso (hp.rep.fst e.inv)).trans e₀
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj (hp.rep.pullback e.inv)) :=
    (IsAffine.iff_of_isIso
      ((BigFppfOver.toScheme B S hS).map (yoneda.preimageIso eP).hom)).mpr hT₀
  have hTaff : IsAffine ((BigFppfOver.toScheme B S hS).obj T) :=
    Stacks.Thickenings.isAffine_of_isThickening ⟨hci, hsj.surj⟩
  exact (isAffineSpace_yoneda B S hS T hTaff).of_iso e.symm

/-- **An étale scheme chart of the ambient space of a thickening whose base change is affine is
itself affine.** For a thickening `G ⊂ X` of algebraic spaces over `S` and an object `U` of the
small étale site of `X` — a scheme étale over `X`, Stacks 03ED — whose base change `G ×_X U`
along the inclusion is affine, the chart `U` is affine.

Nothing is granted. The image of `U` under the comparison functor of Stacks 03G1 is
represented by the chart on the nose, so
`AlgebraicGeometry.Space.isAffineSpace_of_isClosedImmersion_of_isSurjective_of_representable`
applies to the cartesian projection, which is a closed immersion by
`AlgebraicGeometry.Space.isClosedImmersion_spacesBaseChange_projection_of_isThickening` and
surjective on points by
`AlgebraicGeometry.Space.bijective_pointsMap_spacesBaseChange_projection_of_isThickening`. -/
theorem isAffineSpace_chart_of_isThickening_of_isAffineSpace_baseChange
    (hG : IsThickening B S hS X G) (U : SmallEtale B S hS X.1)
    (hU : IsAffineSpace B S hS
      ((SpacesEtale.toSpaces B S hS (IsThickening.space B S hS hG)).obj
        ((spacesBaseChange B S hS (IsThickening.inclusion B S hS hG)).functor.obj
          ((comparisonFunctor B S hS X).obj U))).obj) :
    IsAffineSpace B S hS
      ((SpacesEtale.toSpaces B S hS X).obj ((comparisonFunctor B S hS X).obj U)).obj :=
  isAffineSpace_of_isClosedImmersion_of_isSurjective_of_representable B S hS
    ((spacesBaseChange B S hS (IsThickening.inclusion B S hS hG)).projection.app
      ((comparisonFunctor B S hS X).obj U))
    (isClosedImmersion_spacesBaseChange_projection_of_isThickening B S hS hG _)
    (bijective_pointsMap_spacesBaseChange_projection_of_isThickening B S hS hG _).2
    (T := (SmallEtale.toOver B S hS X.1).obj U) (Iso.refl _) hU

/-- **Stacks 05ZQ for an étale scheme chart, at a thickening of arbitrary order.** Let
`G ⊂ X` be a thickening of algebraic spaces over `S` and let `U` be an object of the small
étale site of `X`, that is a scheme étale over `X`, whose base change `G ×_X U` along the
inclusion is affine. Then restriction of global regular functions along the cartesian
projection `G ×_X U ⟶ U`, that is `Γ(U, 𝒪_U) → Γ(G ×_X U, 𝒪_{G ×_X U})`, is surjective.

The chart `U` is affine by
`AlgebraicGeometry.Space.isAffineSpace_chart_of_isThickening_of_isAffineSpace_baseChange`,
which proves the step the source's proof defers to Stacks 07VS, and the projection is a closed
immersion, so
`AlgebraicGeometry.Space.surjective_globalFunctionsMap_of_isClosedImmersion` applies.

This is the case of a scheme chart of the statement registered as Stacks 05ZQ,
`AlgebraicGeometry.Space.surjective_globalFunctionsMap_of_isThickening`, and it carries no
registration of its own. -/
theorem surjective_globalFunctionsMap_chart_projection_of_isThickening
    (hG : IsThickening B S hS X G) (U : SmallEtale B S hS X.1)
    (hU : IsAffineSpace B S hS
      ((SpacesEtale.toSpaces B S hS (IsThickening.space B S hS hG)).obj
        ((spacesBaseChange B S hS (IsThickening.inclusion B S hS hG)).functor.obj
          ((comparisonFunctor B S hS X).obj U))).obj) :
    Function.Surjective (globalFunctionsMap B S hS
      ((spacesBaseChange B S hS (IsThickening.inclusion B S hS hG)).projection.app
        ((comparisonFunctor B S hS X).obj U))) :=
  surjective_globalFunctionsMap_of_isClosedImmersion B S hS _
    (isClosedImmersion_spacesBaseChange_projection_of_isThickening B S hS hG _)
    (isAffineSpace_chart_of_isThickening_of_isAffineSpace_baseChange B S hS hG U hU)

end AlgebraicGeometry.Space

end
