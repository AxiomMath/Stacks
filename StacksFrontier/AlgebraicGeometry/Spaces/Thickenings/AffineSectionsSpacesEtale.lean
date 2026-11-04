module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.AffineOfAffineClosedSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.AffineSections

/-!
# Regular functions on an affine object of the spaces-étale site of a thickening (Stacks 05ZQ)

Let `G ⊂ X` be a thickening of algebraic spaces over a scheme `S`, of arbitrary order, so `X` is
the ambient space and `G` the closed subspace. In the notation of the source, `G` is `X` and
`X` is `X'`. **Stacks 05ZQ** asserts that for an affine object `V` of `G_{spaces,étale}` the
map `Γ(V, 𝒪_{X'}) → Γ(V, 𝒪_V)` is surjective, `𝒪_{X'}` being read as a sheaf on
`G_{spaces,étale}` through the equivalence of Stacks 05ZM.

The source's proof is followed. Base change along the inclusion is essentially surjective on
spaces-étale sites at a thickening of arbitrary order,
`AlgebraicGeometry.Space.essSurj_spacesBaseChange_of_isThickening` (Stacks 05ZH), so `V` is
isomorphic to `G ×_X U` for an object `U` of `X_{spaces,étale}`; under Stacks 05ZM this `U` is
the object corresponding to `V` and `Γ(V, 𝒪_{X'})` is `Γ(U, 𝒪_U)`. The cartesian projection
`G ×_X U ⟶ U` is a closed immersion surjective on points, so `U` is affine by the thickening
case of Stacks 07VT,
`AlgebraicGeometry.Space.isAffineSpace_of_isClosedImmersion_of_isSurjective`, which is where
the source cites Stacks 07VS; and a closed immersion with affine target is surjective on global
regular functions, `AlgebraicGeometry.Space.surjective_globalFunctionsMap_of_isClosedImmersion`.

## Main results

* `AlgebraicGeometry.Space.isAffineSpace_of_isAffineSpace_spacesBaseChange_of_isThickening`: an
  object of the spaces-étale site of the ambient space of a thickening whose base change to the
  closed subspace is affine is itself affine.
* For such an object `U`, restriction of regular functions along `G ×_X U ⟶ U` is surjective,
  `surjective_globalFunctionsMap_spacesBaseChange_projection_of_isThickening`.
* `AlgebraicGeometry.Space.surjective_globalFunctionsMap_of_isThickening`: **Stacks 05ZQ**, with
  the source's quantifier over an arbitrary affine object of the spaces-étale site of the closed
  subspace.

## References

* [Stacks Project, Tag 05ZQ](https://stacks.math.columbia.edu/tag/05ZQ)
* [Stacks Project, Tag 05ZH](https://stacks.math.columbia.edu/tag/05ZH)
* [Stacks Project, Tag 05ZM](https://stacks.math.columbia.edu/tag/05ZM)
* [Stacks Project, Tag 07VS](https://stacks.math.columbia.edu/tag/07VS)
* [Stacks Project, Tag 07VT](https://stacks.math.columbia.edu/tag/07VT)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {X : AlgebraicSpaces B S hS} {G : Subfunctor X.1}

/-- **An object of the spaces-étale site of the ambient space of a thickening whose base change
is affine is itself affine.** For a thickening `G ⊂ X` and an object `U` of the spaces-étale
site of `X` with `G ×_X U` affine, the cartesian projection `G ×_X U ⟶ U` is a closed immersion
surjective on points, so `U` is affine by the thickening case of Stacks 07VT,
`AlgebraicGeometry.Space.isAffineSpace_of_isClosedImmersion_of_isSurjective`. -/
theorem isAffineSpace_of_isAffineSpace_spacesBaseChange_of_isThickening
    (hG : IsThickening B S hS X G) (U : SpacesEtale B S hS X)
    (hU : IsAffineSpace B S hS
      ((SpacesEtale.toSpaces B S hS (IsThickening.space B S hS hG)).obj
        ((spacesBaseChange B S hS (IsThickening.inclusion B S hS hG)).functor.obj U)).obj) :
    IsAffineSpace B S hS ((SpacesEtale.toSpaces B S hS X).obj U).obj :=
  isAffineSpace_of_isClosedImmersion_of_isSurjective B S hS
    ((spacesBaseChange B S hS (IsThickening.inclusion B S hS hG)).projection.app U).hom
    ((SpacesEtale.toSpaces B S hS (IsThickening.space B S hS hG)).obj
      ((spacesBaseChange B S hS (IsThickening.inclusion B S hS hG)).functor.obj U)).property
    ((SpacesEtale.toSpaces B S hS X).obj U).property
    (isClosedImmersion_spacesBaseChange_projection_of_isThickening B S hS hG U)
    (bijective_pointsMap_spacesBaseChange_projection_of_isThickening B S hS hG U).2
    hU

/-- **Restriction of regular functions along the cartesian projection of a thickening is
surjective.** Let `G ⊂ X` be a thickening of algebraic spaces over `S` and let `U` be an object
of the spaces-étale site of `X` whose base change `G ×_X U` along the inclusion is affine. Then
restriction of global regular functions along the cartesian projection `G ×_X U ⟶ U`, that is
`Γ(U, 𝒪_U) → Γ(G ×_X U, 𝒪_{G ×_X U})`, is surjective.

`U` is affine by
`AlgebraicGeometry.Space.isAffineSpace_of_isAffineSpace_spacesBaseChange_of_isThickening` and the
projection is a closed immersion, so
`AlgebraicGeometry.Space.surjective_globalFunctionsMap_of_isClosedImmersion` applies. -/
theorem surjective_globalFunctionsMap_spacesBaseChange_projection_of_isThickening
    (hG : IsThickening B S hS X G) (U : SpacesEtale B S hS X)
    (hU : IsAffineSpace B S hS
      ((SpacesEtale.toSpaces B S hS (IsThickening.space B S hS hG)).obj
        ((spacesBaseChange B S hS (IsThickening.inclusion B S hS hG)).functor.obj U)).obj) :
    Function.Surjective (globalFunctionsMap B S hS
      ((spacesBaseChange B S hS (IsThickening.inclusion B S hS hG)).projection.app U)) :=
  surjective_globalFunctionsMap_of_isClosedImmersion B S hS _
    (isClosedImmersion_spacesBaseChange_projection_of_isThickening B S hS hG U)
    (isAffineSpace_of_isAffineSpace_spacesBaseChange_of_isThickening B S hS hG U hU)

/-- **Stacks 05ZQ.** Let `S` be a scheme and let `G ⊂ X` be a thickening of algebraic spaces
over `S`, of arbitrary order. Let `V` be an object of the spaces-étale site of `G` whose
underlying algebraic space is affine. Then restriction of global regular functions
`Γ(U, 𝒪_U) → Γ(V, 𝒪_V)` is surjective, where `U` is the object of the spaces-étale site of `X`
whose base change along the inclusion is isomorphic to `V`, and the map is pullback along the
composite `V ≅ G ×_X U ⟶ U` of that isomorphism with the cartesian projection.

In the notation of the source, `G` is `X`, `X` is `X'`, and `V` is the source's `U`: the object
`U` here is the source's `U'` with `U = X ×_{X'} U'`, and `Γ(U, 𝒪_U)` is the source's
`Γ(U, 𝒪_{X'})`, the sections of `𝒪_{X'}` read on `X_{spaces,étale}` through Stacks 05ZM.

Base change along the inclusion is essentially surjective at a thickening of arbitrary order,
`AlgebraicGeometry.Space.essSurj_spacesBaseChange_of_isThickening`; the instance is discharged
in the statement, so no part of Stacks 05ZH is granted. The object `U` and the isomorphism are
the `CategoryTheory.Functor.objPreimage` and `CategoryTheory.Functor.objObjPreimageIso` of that
essential surjectivity. Affineness of `V` transported across the isomorphism makes
`AlgebraicGeometry.Space.surjective_globalFunctionsMap_spacesBaseChange_projection_of_isThickening`
apply at `U`, and pullback along an isomorphism is bijective on global regular functions. -/
@[stacks 05ZQ "for a thickening of arbitrary order and an arbitrary affine object `V` of the \
spaces-étale site of the closed subspace. The source's `Γ(U, 𝒪_{X'})`, the sections of \
`𝒪_{X'}` read on the site of the closed subspace through Stacks 05ZM, is stated as \
`Γ(U', 𝒪_{U'})` for the object `U'` of the ambient space's site with `V ≅ X ×_{X'} U'` given by \
essential surjectivity of base change, and the map is pullback along `V ≅ X ×_{X'} U' ⟶ U'`"]
theorem surjective_globalFunctionsMap_of_isThickening
    (hG : IsThickening B S hS X G)
    (V : SpacesEtale B S hS (IsThickening.space B S hS hG))
    (hV : IsAffineSpace B S hS
      ((SpacesEtale.toSpaces B S hS (IsThickening.space B S hS hG)).obj V).obj) :
    letI : (spacesBaseChange B S hS (IsThickening.inclusion B S hS hG)).functor.EssSurj :=
      essSurj_spacesBaseChange_of_isThickening B S hS hG
    Function.Surjective (globalFunctionsMap B S hS
      ((SpacesEtale.toSpaces B S hS (IsThickening.space B S hS hG)).map
          ((spacesBaseChange B S hS (IsThickening.inclusion B S hS hG)).functor.objObjPreimageIso
            V).inv ≫
        (spacesBaseChange B S hS (IsThickening.inclusion B S hS hG)).projection.app
          ((spacesBaseChange B S hS (IsThickening.inclusion B S hS hG)).functor.objPreimage
            V))) := by
  have key : ∀ (U : SpacesEtale B S hS X)
      (e : (spacesBaseChange B S hS (IsThickening.inclusion B S hS hG)).functor.obj U ≅ V),
      Function.Surjective (globalFunctionsMap B S hS
        ((SpacesEtale.toSpaces B S hS (IsThickening.space B S hS hG)).map e.inv ≫
          (spacesBaseChange B S hS (IsThickening.inclusion B S hS hG)).projection.app U)) := by
    intro U e
    have hproj := surjective_globalFunctionsMap_spacesBaseChange_projection_of_isThickening
      B S hS hG U (hV.of_iso ((ObjectProperty.ι _).mapIso
        ((SpacesEtale.toSpaces B S hS (IsThickening.space B S hS hG)).mapIso e.symm)))
    have hid : (globalFunctionsMap B S hS
          ((SpacesEtale.toSpaces B S hS (IsThickening.space B S hS hG)).map e.inv)).comp
        (globalFunctionsMap B S hS
          ((SpacesEtale.toSpaces B S hS (IsThickening.space B S hS hG)).map e.hom)) =
        RingHom.id _ := by
      rw [← globalFunctionsMap_comp, ← CategoryTheory.Functor.map_comp, Iso.inv_hom_id,
        CategoryTheory.Functor.map_id, globalFunctionsMap_id]
    have hiso : Function.Surjective (globalFunctionsMap B S hS
        ((SpacesEtale.toSpaces B S hS (IsThickening.space B S hS hG)).map e.inv)) :=
      fun s => ⟨globalFunctionsMap B S hS
        ((SpacesEtale.toSpaces B S hS (IsThickening.space B S hS hG)).map e.hom) s, by
          rw [← RingHom.comp_apply, hid, RingHom.id_apply]⟩
    rw [globalFunctionsMap_comp, RingHom.coe_comp]
    exact hiso.comp hproj
  exact key _ _

end AlgebraicGeometry.Space

end
