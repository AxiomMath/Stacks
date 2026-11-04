module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRestrictionInverseImage
public import StacksFrontier.AlgebraicGeometry.Spaces.EtalePermanence

/-!
# Étale base change for direct images of sheaves of sets

Let

```
X' --i--> X
|f'       |f
Y' --g--> Y
```

be a cartesian square of algebraic spaces over a scheme `S` contained in a big fppf site `B`,
with `g` étale.  Then direct image on the small étale sites commutes with restriction:
`f'_{small,*}(F|_{X'}) = (f_{small,*}F)|_{Y'}`.  That is part (1) of Stacks 03LR.

## Main definitions

* `AlgebraicGeometry.Space.spacesEtaleBaseChangeSquare` is the commutation of spaces-étale base
  change with postcomposition, as an isomorphism of functors of sites.
* `AlgebraicGeometry.Space.smallEtalePushforwardBaseChangeIso` is **Stacks 03LR, part (1)**.
* `AlgebraicGeometry.Space.smallEtaleInverseImageSquareIso` is the inverse-image identification
  around the square, built from the composition isomorphisms of Stacks 03G2, part (3).

## Main results

* `AlgebraicGeometry.Space.spacesPushforwardBaseChangeIso` is the same base-change
  isomorphism on the spaces-étale topoi, where both sides are restriction functors.

## Implementation notes

Both sides of the spaces-étale statement are restriction along a composite of two functors of
sites: the left-hand side along base change along `f'` followed by postcomposition with `i`,
the right-hand side along postcomposition with `g` followed by base change along `f`.  The
whole content is therefore the isomorphism of those two composites, which is the
Beck–Chevalley isomorphism `CategoryTheory.Over.beckChevalleyIso` of the cartesian square,
lifted to the étale objects.  The lift is `CategoryTheory.Functor.fullyFaithfulCancelRight` along
the inclusion into the slice, which applies because all four functors are
`CategoryTheory.ObjectProperty.lift`s whose composites with that inclusion are the
corresponding slice functors on the nose.  Mathlib's
`CategoryTheory.Functor.sheafPushforwardContinuousComp'` then turns the isomorphism of site
functors into the isomorphism of restriction functors.

Passing to the *small* étale topoi uses two inputs and no further geometry.  First, the direct
image of `AlgebraicGeometry.Space.smallToposMorphism` is by construction the conjugate, by the
comparison equivalences of Stacks 03G1, of restriction along spaces-étale base change.  Second,
the inverse image of the small étale morphism of topoi of an étale morphism is the conjugate of
restriction along spaces-étale postcomposition, which is
`AlgebraicGeometry.Space.spacesToposMorphism_inverseImageIso`, Stacks 03LQ.  So each of the four
functors in the statement is a conjugate, and
`CategoryTheory.Equivalence.conjugateCompIso` collapses the two composites of conjugates to the
conjugates of the two composites, where the spaces-étale statement applies.

Étaleness of `i` is not a hypothesis: it is Stacks 03FU applied to the square, exactly as in
the source.

What is **not** proved here is that this isomorphism is the adjunction mate of
`AlgebraicGeometry.Space.smallEtaleInverseImageSquareIso` composed with the counit of `f`.  The
source asserts an equality of restricted sheaves and says nothing about canonicity, and the
isomorphism built here is the one coming from the equality of site functors rather than one
chosen with the same endpoints; but the identification with the mate is a separate statement
and is left open.

Every intermediate isomorphism is named with its type written out and the reassociations are
explicit, since a metavariable in a functor-composition position here drives the unifier
through `CategoryTheory.Functor.objPreimage` and `Classical.choose`.

The declaration in the namespace `CategoryTheory.Equivalence` is a general fact about
conjugation by equivalences and belongs with that notion; it is here only to keep the file it
would belong to untouched.

## References

* [Stacks Project, Tag 03LR](https://stacks.math.columbia.edu/tag/03LR)
* [Stacks Project, Tag 03LQ](https://stacks.math.columbia.edu/tag/03LQ)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 03FU](https://stacks.math.columbia.edu/tag/03FU)
* [Stacks Project, Tag 03CF](https://stacks.math.columbia.edu/tag/03CF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v₁ u₁ v₂ u₂ v₃ u₃ v₄ u₄ v₅ u₅ v₆ u₆ u

/-! ### Conjugation by equivalences -/

namespace CategoryTheory.Equivalence

variable {A : Type u₁} [Category.{v₁} A] {A' : Type u₂} [Category.{v₂} A']
  {D : Type u₃} [Category.{v₃} D] {D' : Type u₄} [Category.{v₄} D']
  {E : Type u₅} [Category.{v₅} E] {E' : Type u₆} [Category.{v₆} E']

/-- Conjugating two functors by three equivalences and composing the results is the same as
conjugating their composite: the two copies of the middle equivalence cancel.

This is the functor-level form of the compatibility of `MorphismOfTopoi.transport` with
composition. -/
noncomputable def conjugateCompIso (eA : A ≌ A') (eD : D ≌ D') (eE : E ≌ E') (F : A ⥤ D)
    (G : D ⥤ E) :
    (eA.inverse ⋙ F ⋙ eD.functor) ⋙ (eD.inverse ⋙ G ⋙ eE.functor) ≅
      eA.inverse ⋙ (F ⋙ G) ⋙ eE.functor :=
  Functor.isoWhiskerLeft (eA.inverse ⋙ F)
    (Functor.isoWhiskerRight eD.unitIso.symm (G ⋙ eE.functor))

end CategoryTheory.Equivalence

/-! ### Base change on the spaces-étale sites -/

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X X' Y Y' : AlgebraicSpaces B S hS} (i : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)

/-- Spaces-étale base change along `f'` followed by postcomposition with `i` is isomorphic to
postcomposition with `g` followed by base change along `f`, for a cartesian square whose
bottom arrow `g` is étale.

On full slice categories this is `CategoryTheory.Over.beckChevalleyIso`; all four functors are
lifts of slice functors to the étale objects, and the inclusion into the slice is fully
faithful, so the isomorphism descends. -/
noncomputable def spacesEtaleBaseChangeSquare (sq : IsPullback i f' f g)
    (hg : IsEtale B S hS g.hom) :
    (spacesBaseChange B S hS f').functor ⋙
        spacesEtalePostcomp B S hS i
          (isEtale_of_isPullback B S hS f' i g f sq.flip hg) ≅
      spacesEtalePostcomp B S hS g hg ⋙ (spacesBaseChange B S hS f).functor :=
  let w : ((spacesBaseChange B S hS f').functor ⋙
        spacesEtalePostcomp B S hS i
          (isEtale_of_isPullback B S hS f' i g f sq.flip hg)) ⋙
        SpacesEtale.inclusion B S hS X ≅
      (spacesEtalePostcomp B S hS g hg ⋙ (spacesBaseChange B S hS f).functor) ⋙
        SpacesEtale.inclusion B S hS X :=
    Functor.isoWhiskerLeft (SpacesEtale.inclusion B S hS Y') (Over.beckChevalleyIso sq)
  Functor.fullyFaithfulCancelRight (SpacesEtale.inclusion B S hS X) w

/-- **Stacks 03LR, part (1), on the spaces-étale topoi.** Restriction along postcomposition
with `i` followed by spaces-étale direct image along `f'` is restriction along base change
along `f` followed by restriction along postcomposition with `g`.

Both sides are restriction along a composite of functors of sites, so this is
`AlgebraicGeometry.Space.spacesEtaleBaseChangeSquare` transported by
`CategoryTheory.Functor.sheafPushforwardContinuousComp'`. -/
noncomputable def spacesPushforwardBaseChangeIso (sq : IsPullback i f' f g)
    (hg : IsEtale B S hS g.hom) :
    (spacesEtalePostcomp B S hS i
          (isEtale_of_isPullback B S hS f' i g f sq.flip hg)).sheafPushforwardContinuous
          (Type (u + 1)) (SpacesEtale.topology B S hS X') (SpacesEtale.topology B S hS X) ⋙
        (spacesBaseChange B S hS f').functor.sheafPushforwardContinuous (Type (u + 1))
          (SpacesEtale.topology B S hS Y') (SpacesEtale.topology B S hS X') ≅
      (spacesBaseChange B S hS f).functor.sheafPushforwardContinuous (Type (u + 1))
          (SpacesEtale.topology B S hS Y) (SpacesEtale.topology B S hS X) ⋙
        (spacesEtalePostcomp B S hS g hg).sheafPushforwardContinuous (Type (u + 1))
          (SpacesEtale.topology B S hS Y') (SpacesEtale.topology B S hS Y) :=
  haveI := Functor.isContinuous_comp (spacesEtalePostcomp B S hS g hg)
    (spacesBaseChange B S hS f).functor (SpacesEtale.topology B S hS Y')
    (SpacesEtale.topology B S hS Y) (SpacesEtale.topology B S hS X)
  Functor.sheafPushforwardContinuousComp'
      (spacesEtaleBaseChangeSquare B S hS i f' f g sq hg) (Type (u + 1))
      (SpacesEtale.topology B S hS Y') (SpacesEtale.topology B S hS X')
      (SpacesEtale.topology B S hS X) ≪≫
    (Functor.sheafPushforwardContinuousComp (spacesEtalePostcomp B S hS g hg)
      (spacesBaseChange B S hS f).functor (Type (u + 1))
      (SpacesEtale.topology B S hS Y') (SpacesEtale.topology B S hS Y)
      (SpacesEtale.topology B S hS X)).symm

/-! ### Base change on the small étale topoi -/

variable {U V : AlgebraicSpaces B S hS}

/-- The inverse image of the small étale morphism of topoi of an étale morphism, written as
the conjugate by the comparison equivalences of Stacks 03G1 of restriction along spaces-étale
postcomposition.

This is `AlgebraicGeometry.Space.spacesToposMorphism_inverseImageIso` (Stacks 03LQ) conjugated
by those equivalences; it is the form in which Stacks 03LR consumes it. -/
noncomputable def smallToposMorphism_inverseImage_conjIso (h : U ⟶ V)
    (hh : IsEtale B S hS h.hom) :
    (smallToposMorphism B S hS h).inverseImage ≅
      (smallEtaleToposEquiv B S hS V).inverse ⋙
        (spacesEtalePostcomp B S hS h hh).sheafPushforwardContinuous (Type (u + 1))
          (SpacesEtale.topology B S hS U) (SpacesEtale.topology B S hS V) ⋙
        (smallEtaleToposEquiv B S hS U).functor :=
  Functor.isoWhiskerLeft (smallEtaleToposEquiv B S hS V).inverse
    (Functor.isoWhiskerRight (spacesToposMorphism_inverseImageIso B S hS h hh)
      (smallEtaleToposEquiv B S hS U).functor)

/-- **Stacks 03LR, part (1).** For a cartesian square of algebraic spaces whose bottom arrow
`g` is étale, direct image of sheaves of sets on the small étale sites commutes with
restriction: `f'_{small,*}(F|_{X'}) = (f_{small,*}F)|_{Y'}`, naturally in the sheaf `F`.

Restriction is the inverse image of the small étale morphism of topoi, by Stacks 03LQ.  Each of
the four functors is the conjugate by the comparison equivalences of Stacks 03G1 of a
restriction functor on the spaces-étale sites, where the statement is
`AlgebraicGeometry.Space.spacesPushforwardBaseChangeIso`. -/
@[stacks 03LR "part (1), sheaves of sets"]
noncomputable def smallEtalePushforwardBaseChangeIso (sq : IsPullback i f' f g)
    (hg : IsEtale B S hS g.hom) :
    (smallToposMorphism B S hS i).inverseImage ⋙
        (smallToposMorphism B S hS f').pushforward ≅
      (smallToposMorphism B S hS f).pushforward ⋙
        (smallToposMorphism B S hS g).inverseImage :=
  let Ix : Sheaf (SpacesEtale.topology B S hS X) (Type (u + 1)) ≌
      Sheaf (SmallEtale.topology B S hS X.1) (Type (u + 1)) := smallEtaleToposEquiv B S hS X
  let Ix' : Sheaf (SpacesEtale.topology B S hS X') (Type (u + 1)) ≌
      Sheaf (SmallEtale.topology B S hS X'.1) (Type (u + 1)) := smallEtaleToposEquiv B S hS X'
  let Iy : Sheaf (SpacesEtale.topology B S hS Y) (Type (u + 1)) ≌
      Sheaf (SmallEtale.topology B S hS Y.1) (Type (u + 1)) := smallEtaleToposEquiv B S hS Y
  let Iy' : Sheaf (SpacesEtale.topology B S hS Y') (Type (u + 1)) ≌
      Sheaf (SmallEtale.topology B S hS Y'.1) (Type (u + 1)) := smallEtaleToposEquiv B S hS Y'
  let Pi : Sheaf (SpacesEtale.topology B S hS X) (Type (u + 1)) ⥤
      Sheaf (SpacesEtale.topology B S hS X') (Type (u + 1)) :=
    (spacesEtalePostcomp B S hS i
        (isEtale_of_isPullback B S hS f' i g f sq.flip hg)).sheafPushforwardContinuous
      (Type (u + 1)) (SpacesEtale.topology B S hS X') (SpacesEtale.topology B S hS X)
  let Pg : Sheaf (SpacesEtale.topology B S hS Y) (Type (u + 1)) ⥤
      Sheaf (SpacesEtale.topology B S hS Y') (Type (u + 1)) :=
    (spacesEtalePostcomp B S hS g hg).sheafPushforwardContinuous (Type (u + 1))
      (SpacesEtale.topology B S hS Y') (SpacesEtale.topology B S hS Y)
  let Rf' : Sheaf (SpacesEtale.topology B S hS X') (Type (u + 1)) ⥤
      Sheaf (SpacesEtale.topology B S hS Y') (Type (u + 1)) :=
    (spacesBaseChange B S hS f').functor.sheafPushforwardContinuous (Type (u + 1))
      (SpacesEtale.topology B S hS Y') (SpacesEtale.topology B S hS X')
  let Rf : Sheaf (SpacesEtale.topology B S hS X) (Type (u + 1)) ⥤
      Sheaf (SpacesEtale.topology B S hS Y) (Type (u + 1)) :=
    (spacesBaseChange B S hS f).functor.sheafPushforwardContinuous (Type (u + 1))
      (SpacesEtale.topology B S hS Y) (SpacesEtale.topology B S hS X)
  let a₁ : (smallToposMorphism B S hS i).inverseImage ⋙
        (smallToposMorphism B S hS f').pushforward ≅
      (Ix.inverse ⋙ Pi ⋙ Ix'.functor) ⋙ (smallToposMorphism B S hS f').pushforward :=
    Functor.isoWhiskerRight
      (smallToposMorphism_inverseImage_conjIso B S hS i
        (isEtale_of_isPullback B S hS f' i g f sq.flip hg))
      (smallToposMorphism B S hS f').pushforward
  let a₂ : (Ix.inverse ⋙ Pi ⋙ Ix'.functor) ⋙ (Ix'.inverse ⋙ Rf' ⋙ Iy'.functor) ≅
      Ix.inverse ⋙ (Pi ⋙ Rf') ⋙ Iy'.functor :=
    Equivalence.conjugateCompIso Ix Ix' Iy' Pi Rf'
  let a₃ : Ix.inverse ⋙ (Pi ⋙ Rf') ⋙ Iy'.functor ≅
      Ix.inverse ⋙ (Rf ⋙ Pg) ⋙ Iy'.functor :=
    Functor.isoWhiskerLeft Ix.inverse
      (Functor.isoWhiskerRight (spacesPushforwardBaseChangeIso B S hS i f' f g sq hg)
        Iy'.functor)
  let a₄ : Ix.inverse ⋙ (Rf ⋙ Pg) ⋙ Iy'.functor ≅
      (Ix.inverse ⋙ Rf ⋙ Iy.functor) ⋙ (Iy.inverse ⋙ Pg ⋙ Iy'.functor) :=
    (Equivalence.conjugateCompIso Ix Iy Iy' Rf Pg).symm
  let a₅ : (smallToposMorphism B S hS f).pushforward ⋙ (Iy.inverse ⋙ Pg ⋙ Iy'.functor) ≅
      (smallToposMorphism B S hS f).pushforward ⋙ (smallToposMorphism B S hS g).inverseImage :=
    Functor.isoWhiskerLeft (smallToposMorphism B S hS f).pushforward
      (smallToposMorphism_inverseImage_conjIso B S hS g hg).symm
  a₁ ≪≫ a₂ ≪≫ a₃ ≪≫ a₄ ≪≫ a₅

/-- The inverse-image identification around a cartesian square, built from the inverse-image
composition isomorphism of Stacks 03G2, part (3) and the commutativity of the square.

It is the datum of which the inverse of `smallEtalePushforwardBaseChangeIso` is expected to be
the adjunction mate; that identification is not proved here.

This is the parenthetical assertion of Stacks 03LR — "Also `(f')^{-1}_{small}(G|_{Y'}) =
(f_{small}^{-1}G)|_{X'}` because of commutativity of the diagram and (03LQ)" — which is why the
hypothesis is only `sq` and not the étaleness of `g`: the identity is pure functoriality. -/
@[stacks 03LR "the inverse-image footnote"]
noncomputable def smallEtaleInverseImageSquareIso (sq : IsPullback i f' f g) :
    (smallToposMorphism B S hS g).inverseImage ⋙
        (smallToposMorphism B S hS f').inverseImage ≅
      (smallToposMorphism B S hS f).inverseImage ⋙
        (smallToposMorphism B S hS i).inverseImage :=
  (smallToposMorphism_comp_inverseImage B S hS f' g).symm ≪≫
    eqToIso ((congrArg
      (fun h : X' ⟶ Y => (smallToposMorphism B S hS h).inverseImage) sq.w).symm) ≪≫
    smallToposMorphism_comp_inverseImage B S hS i f

end AlgebraicGeometry.Space

end
