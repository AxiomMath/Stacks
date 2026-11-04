module

public import StacksFrontier.AlgebraicGeometry.InvertiblePullbackFlat.MeromorphicGermFraction
public import StacksFrontier.AlgebraicGeometry.InvertiblePullbackFlat.MeromorphicPullback

/-!
# The square of [Stacks, Tag 02OT] on the local rings

`Stacks.Meromorphic.pullbackMeromorphic_toTotalQuotientSheaf` says that pulling a regular
function back and then reading it as meromorphic is the same as reading it as meromorphic and
then pulling it back. That is a statement about sections over an open of the base, while the
uniqueness sentence of [Stacks, Tag 0BD7] is a statement about local rings: two multipliers are
compared at a point, where `AlgebraicGeometry.exists_mul_toTotalQuotientStalk_eq` presents a
germ of `𝒦_Y` as a fraction of germs of `𝒪_Y`.

This file is the stalk form of that square.

## Main definitions

* `AlgebraicGeometry.totalQuotientStalkMap`: the ring map `(𝒦_Y)_{φ(x)} ⟶ (𝒦_X)_x`.

## Main results

* `AlgebraicGeometry.totalQuotientStalkMap_germ`: it takes the germ of a meromorphic function to
  the germ of its pullback, which is what carries a relation between sections of `𝒦_X` over an
  open of `X` down to the local ring at a point of that open.
* `AlgebraicGeometry.totalQuotientStalkMap_toTotalQuotientStalk`: the square itself — on germs
  of *regular* functions the map is `AlgebraicGeometry.Scheme.Hom.stalkMap`. This is what turns
  a relation between germs of `𝒦_Y` into one between germs of `𝒪_Y` and their images under
  `φ^♯`, the form `AlgebraicGeometry.exists_isUnit_mul_eq_of_isUnit_stalkMap` consumes.

## References

* [Stacks Project, Tag 02OT](https://stacks.math.columbia.edu/tag/02OT)
* [Stacks Project, Tag 0BD7](https://stacks.math.columbia.edu/tag/0BD7)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] (x : X)

/-- The ring map `(𝒦_Y)_{φ(x)} ⟶ (𝒦_X)_x` induced on stalks by `𝒦_Y ⟶ φ_*𝒦_X`. -/
noncomputable def totalQuotientStalkMap :
    ↑(Y.totalQuotientSheaf.presheaf.stalk (f.base x)) →+*
      ↑(X.totalQuotientSheaf.presheaf.stalk x) :=
  ((TopCat.Presheaf.stalkFunctor CommRingCat (f.base x)).map
      (Stacks.Meromorphic.Scheme.totalQuotientSheafPullbackOfFlat f).hom ≫
    X.totalQuotientSheaf.presheaf.stalkPushforward CommRingCat f.base x).hom

/-- **The germ of a pullback is the pullback of the germ.** On a germ of `𝒦_Y` the stalk map is
computed by pulling back any meromorphic function representing it. -/
theorem totalQuotientStalkMap_germ (V : Y.Opens) (hx : f.base x ∈ V)
    (g : Y.totalQuotientSheaf.presheaf.obj (op V)) :
    totalQuotientStalkMap f x (Y.totalQuotientSheaf.presheaf.germ V (f.base x) hx g)
      = X.totalQuotientSheaf.presheaf.germ (f ⁻¹ᵁ V) x hx
          (Stacks.Meromorphic.pullbackMeromorphic f.toLRSHom
            (pullbacksMeromorphicSections_of_flat f) V g) :=
  (congrArg (X.totalQuotientSheaf.presheaf.stalkPushforward CommRingCat.{u} f.base x).hom
      (TopCat.Presheaf.stalkFunctor_map_germ_apply V (f.base x) hx
        (Stacks.Meromorphic.Scheme.totalQuotientSheafPullbackOfFlat f).hom g)).trans
    (TopCat.Presheaf.stalkPushforward_germ_apply CommRingCat.{u} f.base
      X.totalQuotientSheaf.presheaf V x hx _)

/-- **[Stacks, Tag 02OT] on the local rings.** On the image of `𝒪_{Y, φ(x)}` the stalk map of
`𝒦` is the stalk map of `φ`: a germ of a regular function, pulled back as a meromorphic
function, is the meromorphic function that its pullback as a regular function is. -/
theorem totalQuotientStalkMap_toTotalQuotientStalk (a : ↑(Y.presheaf.stalk (f.base x))) :
    totalQuotientStalkMap f x (toTotalQuotientStalk Y (f.base x) a)
      = toTotalQuotientStalk X x ((f.stalkMap x).hom a) := by
  obtain ⟨V, hx, b, rfl⟩ := Y.presheaf.exists_germ_eq a
  have hY : toTotalQuotientStalk Y (f.base x) (Y.presheaf.germ V (f.base x) hx b)
      = Y.totalQuotientSheaf.presheaf.germ V (f.base x) hx
          ((Y.toTotalQuotientSheaf.hom.app (op V)).hom b) :=
    TopCat.Presheaf.stalkFunctor_map_germ_apply V (f.base x) hx Y.toTotalQuotientSheaf.hom b
  have hst : (f.stalkMap x).hom (Y.presheaf.germ V (f.base x) hx b)
      = X.presheaf.germ (f ⁻¹ᵁ V) x hx ((f.app V).hom b) :=
    Scheme.Hom.germ_stalkMap_apply f V x hx b
  have hX : toTotalQuotientStalk X x
        (X.presheaf.germ (f ⁻¹ᵁ V) x hx ((f.app V).hom b))
      = X.totalQuotientSheaf.presheaf.germ (f ⁻¹ᵁ V) x hx
          ((X.toTotalQuotientSheaf.hom.app (op (f ⁻¹ᵁ V))).hom ((f.app V).hom b)) :=
    TopCat.Presheaf.stalkFunctor_map_germ_apply (f ⁻¹ᵁ V) x hx X.toTotalQuotientSheaf.hom _
  have hpb : Stacks.Meromorphic.pullbackMeromorphic f.toLRSHom
        (pullbacksMeromorphicSections_of_flat f) V
        ((Y.toTotalQuotientSheaf.hom.app (op V)).hom b)
      = (X.toTotalQuotientSheaf.hom.app (op (f ⁻¹ᵁ V))).hom ((f.app V).hom b) :=
    Stacks.Meromorphic.pullbackMeromorphic_toTotalQuotientSheaf f.toLRSHom
      (pullbacksMeromorphicSections_of_flat f) V b
  rw [hY, totalQuotientStalkMap_germ f x V hx _, hpb, hst, hX]

end AlgebraicGeometry

end
