module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningPushout07RT
public import StacksFrontier.AlgebraicGeometry.Thickenings.Affine

/-!
# Pushouts along an arbitrary thickening and an affine morphism

Let `i : X ⟶ X'` be a thickening of schemes — a closed immersion which is surjective on points,
so a locally nilpotent one, of no bounded order — and let `f : X ⟶ Y` be an affine morphism.
[Stacks Project, Tag 07RT] makes four assertions about the pushout `Y' = Y ⨿_X X'`: that it
exists in the category of schemes, that `Y ⟶ Y'` is again a thickening, that the pushout square
is simultaneously cartesian, so that `X = Y ×_{Y'} X'`, and that `𝒪_{Y'}` is the fibre product
`𝒪_Y ×_{f_*𝒪_X} f'_*𝒪_{X'}`.  This file states all four for an arbitrary thickening, with no
hypothesis beyond the geometric data of the tag.

## Main results

* `Stacks.Pushout.exists_isPushout_isPullback_isThickening_of_isThickening` carries the first
  three assertions on an explicitly constructed apex: a scheme with maps from `X'` and `Y` whose
  square is cocartesian, cartesian, and has the map from `Y` a thickening.
* `Stacks.Pushout.hasPushout_of_isThickening_of_isAffineHom'` is the first assertion: the pushout
  exists in the category of schemes.
* `Stacks.Pushout.pushout_inr_isThickening'` is the second: `Y ⟶ Y'` is a thickening.
* `Stacks.Pushout.isPullback_pushout_of_isThickening_of_isAffineHom'` is the third: the pushout
  square is cartesian, `X = Y ×_{Y'} X'`.
* `Stacks.Pushout.pushout_structureSheaf_isPullback'` is the fourth: over every open of the
  pushout the ring of sections is the fibre product of the rings of sections on `Y` and on `X'`
  over the one on `X`.

## Implementation notes

`StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningPushoutGlobal` and
`StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningPushout07RT` prove the four assertions for
an arbitrary thickening granted a universally quantified hypothesis `H` asserting
[Stacks Project, Tag 06AD] — *a thickening of an affine scheme is affine*.  That hypothesis is
discharged here by `Stacks.Thickenings.forall_isAffine_of_isThickening`, which is Tag 06AD proved
outright: a thickening is a closed immersion, hence finite, and surjective, so its target is the
target of a finite surjective morphism with affine source, affine by
`Stacks.AffineFromFiniteSurjective.isAffine_of_finite_surjective` ([Stacks Project, Tag 01ZT]).

So nothing mathematical is added to those two files; this one only removes their hypothesis.  The
module docstrings of
`StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningPushoutFiniteOrder` and
`StacksFrontier.AlgebraicGeometry.Pushout.ThickeningPushout` describe the general case as waiting on
Tag 06AD by way of [Stacks Project, Tag 05YU]; the route actually taken to Tag 06AD is the
lighter one through finite surjective morphisms, and
`StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningPushoutFiniteOrder` remains of interest
only because it avoids that machinery for a thickening of finite order.

## References

* [Stacks Project, Tag 01ZT](https://stacks.math.columbia.edu/tag/01ZT)
* [Stacks Project, Tag 04EX](https://stacks.math.columbia.edu/tag/04EX)
* [Stacks Project, Tag 06AD](https://stacks.math.columbia.edu/tag/06AD)
* [Stacks Project, Tag 07RT](https://stacks.math.columbia.edu/tag/07RT)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.Pushout

open Stacks.Thickenings

variable {X X' Y : Scheme.{u}}

/-- **Stacks Project, Tag 07RT for an arbitrary thickening, on an explicitly constructed apex.**
For a thickening `i : X ⟶ X'` and an affine morphism `f : X ⟶ Y` there is a scheme `Q` with maps
`A : X' ⟶ Q` and `B : Y ⟶ Q` whose square is cocartesian, is simultaneously cartesian, and has
`B` a thickening. -/
@[stacks 07RT "the existence of the pushout, that Y ⊂ Y' is a thickening and that the square is \
cartesian, X = Y ×_{Y'} X'"]
theorem exists_isPushout_isPullback_isThickening_of_isThickening (i : X ⟶ X') (f : X ⟶ Y)
    (hi : IsThickening i) [IsAffineHom f] :
    ∃ (Q : Scheme.{u}) (A : X' ⟶ Q) (B : Y ⟶ Q),
      IsPushout i f A B ∧ IsPullback i f A B ∧ IsThickening B := by
  have := hi.1
  obtain ⟨Q, A, B, hcol, hch⟩ := exists_isPushout_forgetToLocallyRingedSpace_of_isThickening
    forall_isAffine_of_isThickening i f hi
  exact ⟨Q, A, B, IsPushout.of_map_of_faithful Scheme.forgetToLocallyRingedSpace hcol,
    isPullback_of_isPushout_forgetToLocallyRingedSpace i f A B hcol hch,
    isThickening_of_isPushout_forgetToLocallyRingedSpace hi f hcol hch⟩

/-- **Stacks Project, Tag 07RT, first assertion.**  A thickening and an affine morphism have a
pushout in the category of schemes. -/
@[stacks 07RT "the existence of the pushout"]
theorem hasPushout_of_isThickening_of_isAffineHom' (i : X ⟶ X') (f : X ⟶ Y)
    (hi : IsThickening i) [IsAffineHom f] : HasPushout i f :=
  hasPushout_of_isThickening_of_isAffineHom forall_isAffine_of_isThickening i f hi

/-- **Stacks Project, Tag 07RT, second assertion.**  The map from `Y` into the pushout of a
thickening `i : X ⟶ X'` and an affine morphism `f : X ⟶ Y` is again a thickening; stated for
Mathlib's canonical pushout. -/
@[stacks 07RT "that Y ⊂ Y' is a thickening"]
theorem pushout_inr_isThickening' (i : X ⟶ X') (f : X ⟶ Y) (hi : IsThickening i) [IsAffineHom f]
    [HasPushout i f] : IsThickening (pushout.inr i f) :=
  pushout_inr_isThickening forall_isAffine_of_isThickening i f hi

/-- **Stacks Project, Tag 07RT, third assertion.**  The pushout square of a thickening and an
affine morphism is also cartesian, that is, `X = Y ×_{Y'} X'`; stated for Mathlib's canonical
pushout. -/
@[stacks 07RT "that the square is cartesian, X = Y ×_{Y'} X'"]
theorem isPullback_pushout_of_isThickening_of_isAffineHom' (i : X ⟶ X') (f : X ⟶ Y)
    (hi : IsThickening i) [IsAffineHom f] [HasPushout i f] :
    IsPullback i f (pushout.inl i f) (pushout.inr i f) :=
  isPullback_pushout_of_isThickening_of_isAffineHom forall_isAffine_of_isThickening i f hi

/-- **Stacks Project, Tag 07RT, fourth assertion.**  On every open `U` of the pushout of a
thickening `i : X ⟶ X'` and an affine morphism `f : X ⟶ Y` the ring of sections is the fibre
product of the rings of sections over the two preimages of `U` in `Y` and `X'` above the ring of
sections over their common preimage in `X`; this is `𝒪_{Y'} = 𝒪_Y ×_{f_*𝒪_X} f'_*𝒪_{X'}`. -/
@[stacks 07RT "the description of 𝒪_{Y'} as 𝒪_Y ×_{f_*𝒪_X} f'_*𝒪_{X'}"]
theorem pushout_structureSheaf_isPullback' (i : X ⟶ X') (f : X ⟶ Y) (hi : IsThickening i)
    [IsAffineHom f] [HasPushout i f] (U : (pushout i f).Opens) :
    IsPullback ((pushout.inr i f).app U) ((pushout.inl i f).app U)
      (f.app (pushout.inr i f ⁻¹ᵁ U))
      (i.app (pushout.inl i f ⁻¹ᵁ U) ≫ eqToHom (congrArg (fun V : X.Opens ↦ Γ(X, V))
        (congrArg (fun g : X ⟶ pushout i f ↦ g ⁻¹ᵁ U)
          (pushout.condition (f := i) (g := f))))) :=
  pushout_structureSheaf_isPullback forall_isAffine_of_isThickening i f hi U

end Stacks.Pushout

end
