module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleToposMorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtalePostcomp
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Restriction to the small étale site of an étale morphism is its inverse image

Let `f : X ⟶ Y` be an étale morphism of algebraic spaces over a scheme `S` contained in a big
fppf site `B`.  Stacks 03LP attaches to it the postcomposition functor
`j : X_étale ⥤ Y_étale`, `(φ : U ⟶ X) ↦ (φ ≫ f : U ⟶ Y)`, which is continuous, so that
restriction along `j` carries sheaves on `Y_étale` to sheaves on `X_étale`.  Stacks 03LQ is the
identification of that restriction with the inverse image of the morphism of small étale topoi
of Stacks 03G2, part (3):

`G|_{X_étale} = f_{small}^{-1} G`.

This file proves it, and with it the assertion of Stacks 03LP that the morphism of topoi
attached to `j` by Sites 00XO *is* `f_{small}`.

## Main definitions

* `CategoryTheory.Over.beckChevalleyIso` is the Beck–Chevalley isomorphism of a cartesian
  square, as an isomorphism of functors between slice categories.
* `AlgebraicGeometry.Space.spacesEtalePostcompBaseChangeAdjunction`: on spaces-étale sites,
  postcomposition along an étale morphism is left adjoint to base change along it.
* `AlgebraicGeometry.Space.spacesEtalePostcompSheafAdjunction` is the same adjunction between
  the two restriction functors on sheaves, for arbitrary coefficients.

## Main results

* `AlgebraicGeometry.Space.spacesToposMorphism_inverseImageIso`: on the spaces-étale topoi the
  inverse image of an étale morphism is restriction along postcomposition.
* `AlgebraicGeometry.Space.smallToposMorphism_inverseImageIso`: **Stacks 03LQ**, the same on the
  small étale topoi, which is the remaining assertion of Stacks 03LP.
* `AlgebraicGeometry.Space.smallToposMorphism_inverseImage_obj_obj`: the displayed formula
  `f_{small}^{-1}G(U) = G(jU)`.

## Implementation notes

The proof is not the one in Stacks, which identifies the spaces-étale postcomposition functor
with a localization functor and appeals to Sites 03CE and 03L5.  It is instead the observation
that postcomposition and base change are *adjoint as functors of sites*: on full slice
categories this is `CategoryTheory.Over.mapPullbackAdj`, and both functors restrict to the
objects étale over the base — postcomposition by Stacks 03FT and base change by Stacks 03FU —
so `CategoryTheory.Adjunction.restrictFullyFaithful` transports the adjunction to the étale
subcategories, both restrictions being `CategoryTheory.ObjectProperty.lift`s whose composites
with the inclusion are the original functors by `CategoryTheory.ObjectProperty.liftCompιIso`.
Mathlib's `CategoryTheory.Adjunction.sheafPushforwardContinuous` then carries that adjunction to
the two restriction functors on sheaves, using only that both functors of sites are continuous,
which is `AlgebraicGeometry.Space.isContinuous_spacesEtalePostcomp` and
`AlgebraicGeometry.Space.isContinuous_spacesBaseChange`.  Since the direct image of the
spaces-étale morphism of topoi *is* restriction along base change, uniqueness of left adjoints
identifies its inverse image with restriction along postcomposition.

This corrects the implementation note of
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtalePostcompCocontinuous.lean`, which records this
adjunction as the missing input of Stacks 03LQ and 03LR and suggests that the obstruction is
structural, namely that `AlgebraicGeometry.Space.smallBaseChange` of Stacks 03G2, part (4)
needs a representable morphism.  No representability is needed: the adjunction is on the
spaces-étale sites throughout, where base change exists for an arbitrary morphism.

Passing from the spaces-étale topoi to the small étale ones costs nothing beyond the comparison
equivalence of Stacks 03G1, because `AlgebraicGeometry.Space.smallToposMorphism` is defined by
transport along it and because
`AlgebraicGeometry.Space.comparisonFunctor_comp_spacesEtalePostcomp` holds by `rfl`: the two
composites of restriction functors in
`AlgebraicGeometry.Space.smallEtaleToposEquiv_comp_postcomp_restriction` are therefore equal on
the nose and that comparison is `CategoryTheory.Iso.refl`.

Every intermediate isomorphism in `smallToposMorphism_inverseImageIso` is named with its type
written out and the reassociation is explicit.  Leaving a metavariable in a functor-composition
position here hands the unifier `?F ⋙ ?G =?= (P ⋙ A) ⋙ B`, whose fallback unfolds the small
étale direct image through `CategoryTheory.Functor.objPreimage` into `Classical.choose` and
diverges.

The two declarations in the namespace `CategoryTheory.Over` are general facts about slice
categories and belong with that notion; they are here only to keep the files they would belong
to untouched.

## References

* [Stacks Project, Tag 03LQ](https://stacks.math.columbia.edu/tag/03LQ)
* [Stacks Project, Tag 03LP](https://stacks.math.columbia.edu/tag/03LP)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 03G1](https://stacks.math.columbia.edu/tag/03G1)
* [Stacks Project, Tag 00XO](https://stacks.math.columbia.edu/tag/00XO)
* [Stacks Project, Tag 00XR](https://stacks.math.columbia.edu/tag/00XR)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v₀ u₀ u

/-! ### Beck–Chevalley for slice categories -/

namespace CategoryTheory.Over

variable {C : Type u₀} [Category.{v₀} C] {X X' Y Y' : C} {i : X' ⟶ X} {f' : X' ⟶ Y'}
  {f : X ⟶ Y} {g : Y' ⟶ Y}

/-- For a cartesian square with `i` and `g` horizontal, an object `W` over `Y'` has the same
base change to `X` computed in two ways: pull back along `f'` and push forward along `i`, or
push forward along `g` and pull back along `f`.

The isomorphism of underlying objects is the one supplied by the pasting of the chosen fibre
product of `W` and `X'` over `Y'` with the given cartesian square. -/
noncomputable def beckChevalleyObjIso (sq : IsPullback i f' f g) [HasPullbacksAlong f]
    [HasPullbacksAlong f'] (W : Over Y') :
    (Over.pullback f' ⋙ Over.map i).obj W ≅ (Over.map g ⋙ Over.pullback f).obj W :=
  Over.isoMk (((IsPullback.of_hasPullback W.hom f').flip.paste_horiz sq).flip.isoPullback)
    (by simp)

/-- **The Beck–Chevalley isomorphism for slice categories.** For a cartesian square, base
change along `f'` followed by postcomposition with `i` is isomorphic to postcomposition with
`g` followed by base change along `f`.

Naturality is checked on the two projections of the target fibre product, where both sides
reduce to the universal property of the source one. -/
noncomputable def beckChevalleyIso (sq : IsPullback i f' f g) [HasPullbacksAlong f]
    [HasPullbacksAlong f'] :
    Over.pullback f' ⋙ Over.map i ≅ Over.map g ⋙ Over.pullback f :=
  NatIso.ofComponents (beckChevalleyObjIso sq) (by
    intro W W' a
    ext
    apply pullback.hom_ext <;>
      simp [beckChevalleyObjIso])

end CategoryTheory.Over

/-! ### Postcomposition is left adjoint to base change -/

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {U V : AlgebraicSpaces B S hS}

/-- **Stacks 03LP and 03G2, part (1), as an adjoint pair of functors of sites.**
Postcomposition with an étale morphism `h : U ⟶ V` is left adjoint to base change along `h`,
as functors between the spaces-étale sites.

On full slice categories this is `CategoryTheory.Over.mapPullbackAdj`; both functors restrict
to the objects étale over the base, so the adjunction restricts along the two fully faithful
inclusions. -/
@[sga "3 I 1.6" "special case"]
noncomputable def spacesEtalePostcompBaseChangeAdjunction (h : U ⟶ V)
    (hh : IsEtale B S hS h.hom) :
    spacesEtalePostcomp B S hS h hh ⊣ (spacesBaseChange B S hS h).functor :=
  Adjunction.restrictFullyFaithful (Over.mapPullbackAdj h)
    (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _)
    (ObjectProperty.liftCompιIso _ _ _).symm (ObjectProperty.liftCompιIso _ _ _).symm

/-- Restriction along postcomposition with an étale morphism is left adjoint to restriction
along base change along it, for sheaves with arbitrary coefficients.

Both functors of sites are continuous, so Mathlib's
`CategoryTheory.Adjunction.sheafPushforwardContinuous` carries
`AlgebraicGeometry.Space.spacesEtalePostcompBaseChangeAdjunction` to sheaves. -/
noncomputable def spacesEtalePostcompSheafAdjunction (A : Type*) [Category A] (h : U ⟶ V)
    (hh : IsEtale B S hS h.hom) :
    (spacesEtalePostcomp B S hS h hh).sheafPushforwardContinuous A
        (SpacesEtale.topology B S hS U) (SpacesEtale.topology B S hS V) ⊣
      (spacesBaseChange B S hS h).functor.sheafPushforwardContinuous A
        (SpacesEtale.topology B S hS V) (SpacesEtale.topology B S hS U) :=
  (spacesEtalePostcompBaseChangeAdjunction B S hS h hh).sheafPushforwardContinuous (E := A)
    (SpacesEtale.topology B S hS U) (SpacesEtale.topology B S hS V)

/-- **Stacks 03LQ on the spaces-étale topoi.** The inverse image of the morphism of
spaces-étale topoi attached to an étale morphism `h : U ⟶ V` is restriction along
postcomposition with `h`.

Its direct image is restriction along base change along `h`, and
`AlgebraicGeometry.Space.spacesEtalePostcompSheafAdjunction` exhibits restriction along
postcomposition as another left adjoint of that functor, so the two agree by uniqueness of
left adjoints. -/
@[stacks 03LQ "on the spaces-étale topoi"]
noncomputable def spacesToposMorphism_inverseImageIso (h : U ⟶ V)
    (hh : IsEtale B S hS h.hom) :
    ((spacesBaseChange_isMorphismOfSites B S hS h).morphismOfTopoi).inverseImage ≅
      (spacesEtalePostcomp B S hS h hh).sheafPushforwardContinuous (Type (u + 1))
        (SpacesEtale.topology B S hS U) (SpacesEtale.topology B S hS V) :=
  Adjunction.leftAdjointUniq
    ((spacesBaseChange_isMorphismOfSites B S hS h).morphismOfTopoi).adj
    (spacesEtalePostcompSheafAdjunction B S hS (Type (u + 1)) h hh)

/-- Restriction along spaces-étale postcomposition and restriction along small étale
postcomposition correspond under the comparison equivalences of Stacks 03G1.

Both sides are restriction along a composite of two functors of sites, and the two composites
are equal by `AlgebraicGeometry.Space.comparisonFunctor_comp_spacesEtalePostcomp`, so the
comparison is the identity. -/
noncomputable def smallEtaleToposEquiv_comp_postcomp_restriction (h : U ⟶ V)
    (hh : IsEtale B S hS h.hom) :
    (spacesEtalePostcomp B S hS h hh).sheafPushforwardContinuous (Type (u + 1))
        (SpacesEtale.topology B S hS U) (SpacesEtale.topology B S hS V) ⋙
      (smallEtaleToposEquiv B S hS U).functor ≅
    (smallEtaleToposEquiv B S hS V).functor ⋙
      (smallEtalePostcomp B S hS h hh).sheafPushforwardContinuous (Type (u + 1))
        (SmallEtale.topology B S hS U.1) (SmallEtale.topology B S hS V.1) :=
  Iso.refl _

/-- **Stacks 03LQ**, and the remaining assertion of **Stacks 03LP**: for an étale morphism
`h : U ⟶ V` of algebraic spaces, the inverse image of the morphism of *small* étale topoi
`h_{small}` of Stacks 03G2, part (3) is restriction along the postcomposition functor `j` of
Stacks 03LP, i.e. `G|_{U_étale} = h_{small}^{-1}G`.

The small étale morphism of topoi is the transport of the spaces-étale one along the comparison
equivalences of Stacks 03G1, so this is
`AlgebraicGeometry.Space.spacesToposMorphism_inverseImageIso` conjugated by those
equivalences, the comparison with small étale postcomposition being the identity. -/
@[stacks 03LQ, stacks 03LP "the morphism of topoi attached to j is f_small"]
noncomputable def smallToposMorphism_inverseImageIso (h : U ⟶ V) (hh : IsEtale B S hS h.hom) :
    (smallToposMorphism B S hS h).inverseImage ≅
      (smallEtalePostcomp B S hS h hh).sheafPushforwardContinuous (Type (u + 1))
        (SmallEtale.topology B S hS U.1) (SmallEtale.topology B S hS V.1) :=
  let Iu : Sheaf (SpacesEtale.topology B S hS U) (Type (u + 1)) ≌
      Sheaf (SmallEtale.topology B S hS U.1) (Type (u + 1)) := smallEtaleToposEquiv B S hS U
  let Iv : Sheaf (SpacesEtale.topology B S hS V) (Type (u + 1)) ≌
      Sheaf (SmallEtale.topology B S hS V.1) (Type (u + 1)) := smallEtaleToposEquiv B S hS V
  let P : Sheaf (SpacesEtale.topology B S hS V) (Type (u + 1)) ⥤
      Sheaf (SpacesEtale.topology B S hS U) (Type (u + 1)) :=
    (spacesEtalePostcomp B S hS h hh).sheafPushforwardContinuous (Type (u + 1))
      (SpacesEtale.topology B S hS U) (SpacesEtale.topology B S hS V)
  let Q : Sheaf (SmallEtale.topology B S hS V.1) (Type (u + 1)) ⥤
      Sheaf (SmallEtale.topology B S hS U.1) (Type (u + 1)) :=
    (smallEtalePostcomp B S hS h hh).sheafPushforwardContinuous (Type (u + 1))
      (SmallEtale.topology B S hS U.1) (SmallEtale.topology B S hS V.1)
  let N : Sheaf (SpacesEtale.topology B S hS V) (Type (u + 1)) ⥤
      Sheaf (SpacesEtale.topology B S hS U) (Type (u + 1)) :=
    ((spacesBaseChange_isMorphismOfSites B S hS h).morphismOfTopoi).inverseImage
  let e₁ : Iv.inverse ⋙ N ⋙ Iu.functor ≅ Iv.inverse ⋙ P ⋙ Iu.functor :=
    Functor.isoWhiskerLeft Iv.inverse
      (Functor.isoWhiskerRight (spacesToposMorphism_inverseImageIso B S hS h hh) Iu.functor)
  let e₂ : Iv.inverse ⋙ P ⋙ Iu.functor ≅ Iv.inverse ⋙ Iv.functor ⋙ Q :=
    Functor.isoWhiskerLeft Iv.inverse
      (smallEtaleToposEquiv_comp_postcomp_restriction B S hS h hh)
  let e₃ : Iv.inverse ⋙ Iv.functor ⋙ Q ≅ (Iv.inverse ⋙ Iv.functor) ⋙ Q :=
    (Functor.associator Iv.inverse Iv.functor Q).symm
  let e₄ : (Iv.inverse ⋙ Iv.functor) ⋙ Q ≅ 𝟭 _ ⋙ Q := Functor.isoWhiskerRight Iv.counitIso Q
  let e₅ : 𝟭 _ ⋙ Q ≅ Q := Functor.leftUnitor Q
  e₁ ≪≫ e₂ ≪≫ e₃ ≪≫ e₄ ≪≫ e₅

/-- **Stacks 03LP, the displayed formula for the inverse image.** The sections of
`h_{small}^{-1}G` over an étale chart `W` of `U` are the sections of `G` over the composite
chart `jW`.

This is `AlgebraicGeometry.Space.smallToposMorphism_inverseImageIso` evaluated at `G` and at
`W`, the sections of a restricted sheaf being the asserted ones by definition. -/
@[stacks 03LP "the displayed formula for the inverse image"]
noncomputable def smallToposMorphism_inverseImage_obj_obj (h : U ⟶ V)
    (hh : IsEtale B S hS h.hom)
    (G : Sheaf (SmallEtale.topology B S hS V.1) (Type (u + 1)))
    (W : SmallEtale B S hS U.1) :
    (((smallToposMorphism B S hS h).inverseImage.obj G).obj.obj (.op W)) ≅
      G.obj.obj (.op ((smallEtalePostcomp B S hS h hh).obj W)) :=
  (sheafToPresheaf (SmallEtale.topology B S hS U.1) (Type (u + 1)) ⋙
      (evaluation (SmallEtale B S hS U.1)ᵒᵖ (Type (u + 1))).obj (.op W)).mapIso
    ((smallToposMorphism_inverseImageIso B S hS h hh).app G)

end AlgebraicGeometry.Space

end
