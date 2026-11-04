module

public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteHilbert.Diagram
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.FiniteFreeAlgebra.UniversalCover

/-!
# The degree-`d` cover attached to a family of free algebra structures

A point `x : T ⟶ X_S` of the scheme of structure constants over an object `T` of the big fppf
site over `S` is a family of free `d`-dimensional algebra structures parametrised by `T`. Taking
the spectrum of that family gives a degree-`d` finite locally free cover of `T`, obtained from
the universal degree-`d` cover by base change along `x`. This is the map on objects of the
1-morphism `Spec : FA_d ⟶ ℋ_d` named in the proof of Stacks 05YQ.

Base change along a morphism `h : T' ⟶ T` of the site carries the cover of `x` to the cover of
`h ≫ x`: the two pullback squares paste, so the cover of `h ≫ x` is the fibre product of the
cover of `x` with `T'`, which is exactly the data of a morphism of `ℋ_d` lying over `h`.

## Main definitions

* `AlgebraicGeometry.Space.specFiniteCover`: the degree-`d` finite locally free cover attached to
  a point of the scheme of structure constants.
* `AlgebraicGeometry.Space.specFiniteCoverMap`: the morphism of `ℋ_d` over `h : T' ⟶ T` from the
  cover of `h ≫ x` to the cover of `x`.

## Main results

* `AlgebraicGeometry.Space.specFiniteCover_U`, `AlgebraicGeometry.Space.specFiniteCover_Z` and
  `AlgebraicGeometry.Space.specFiniteCover_q`: the three components of the cover.
* `AlgebraicGeometry.Space.specFiniteCoverMap_g_comp_fst` and
  `AlgebraicGeometry.Space.specFiniteCoverMap_hom_ext`: the cover component of
  `AlgebraicGeometry.Space.specFiniteCoverMap` is determined by the two projections of the
  cartesian square defining the cover of `x`.

## Implementation notes

The degree is read off the defining cartesian square by
`Stacks.Morphisms.IsFiniteLocallyFreeOfRank.of_isPullback`, after transporting the square to
schemes along `AlgebraicGeometry.BigFppfOver.toScheme`, exactly as in
`AlgebraicGeometry.Stack.FiniteCover.exists_lift`.

The cover component of `AlgebraicGeometry.Space.specFiniteCoverMap` is the morphism produced by
the universal property of the cartesian square defining the cover of `x`, and that the resulting
square is cartesian is `CategoryTheory.IsPullback.of_right'`: the rectangle over `h ≫ x` and the
square over `x` are both cartesian by construction.

## References

* [Stacks Project, Tag 05YQ](https://stacks.math.columbia.edu/tag/05YQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

open AlgebraicGeometry.FiniteFreeAlgebra

variable (𝒞 : BigFppfSite.{u}) (S : Scheme.{u}) (hS : 𝒞.Contains S) (d : ℕ) [NeZero d]

/-- The degree-`d` finite locally free cover attached to a point `x` of the scheme of structure
constants over an object `T` of the big fppf site: the base change of the universal degree-`d`
cover along `x`. -/
noncomputable def specFiniteCover {T : BigFppfOver 𝒞 S hS}
    (x : T ⟶ structureConstantsSiteObject 𝒞 S hS d) : Stack.FiniteCover 𝒞 S hS d where
  U := T
  Z := pullback (universalCoverSiteHom 𝒞 S hS d) x
  q := pullback.snd _ _
  finiteLocallyFree :=
    have := isFiniteLocallyFreeOfRank_universalCoverSiteHom 𝒞 S hS d
    Stacks.Morphisms.IsFiniteLocallyFreeOfRank.of_isPullback
      ((IsPullback.of_hasPullback (universalCoverSiteHom 𝒞 S hS d) x).map
        (BigFppfOver.toScheme 𝒞 S hS))

/-- The base of the cover attached to `x : T ⟶ X_S` is `T`. -/
@[simp] theorem specFiniteCover_U {T : BigFppfOver 𝒞 S hS}
    (x : T ⟶ structureConstantsSiteObject 𝒞 S hS d) :
    (specFiniteCover 𝒞 S hS d x).U = T := rfl

/-- The total space of the cover attached to `x` is the fibre product over `X_S` of the
universal degree-`d` cover and `x`. -/
@[simp] theorem specFiniteCover_Z {T : BigFppfOver 𝒞 S hS}
    (x : T ⟶ structureConstantsSiteObject 𝒞 S hS d) :
    (specFiniteCover 𝒞 S hS d x).Z = pullback (universalCoverSiteHom 𝒞 S hS d) x := rfl

/-- The structure morphism of the cover attached to `x` is the second projection of the fibre
product over `X_S` of the universal degree-`d` cover and `x`. -/
@[simp] theorem specFiniteCover_q {T : BigFppfOver 𝒞 S hS}
    (x : T ⟶ structureConstantsSiteObject 𝒞 S hS d) :
    (specFiniteCover 𝒞 S hS d x).q = pullback.snd (universalCoverSiteHom 𝒞 S hS d) x := rfl

/-- The cover attached to `x` is cartesian over the universal degree-`d` cover. -/
theorem specFiniteCover_isPullback {T : BigFppfOver 𝒞 S hS}
    (x : T ⟶ structureConstantsSiteObject 𝒞 S hS d) :
    IsPullback (pullback.fst (universalCoverSiteHom 𝒞 S hS d) x)
      (specFiniteCover 𝒞 S hS d x).q (universalCoverSiteHom 𝒞 S hS d) x :=
  IsPullback.of_hasPullback _ _

/-- Base change along `h : T' ⟶ T` carries the cover attached to `x` to the cover attached to
`h ≫ x`: a morphism of `ℋ_d` lying over `h`. -/
noncomputable def specFiniteCoverMap {T' T : BigFppfOver 𝒞 S hS} (h : T' ⟶ T)
    (x : T ⟶ structureConstantsSiteObject 𝒞 S hS d) :
    specFiniteCover 𝒞 S hS d (h ≫ x) ⟶ specFiniteCover 𝒞 S hS d x where
  f := h
  g := (IsPullback.of_hasPullback (universalCoverSiteHom 𝒞 S hS d) x).lift
    (pullback.fst (universalCoverSiteHom 𝒞 S hS d) (h ≫ x))
    (pullback.snd (universalCoverSiteHom 𝒞 S hS d) (h ≫ x) ≫ h)
    (pullback.condition.trans (Category.assoc _ _ _).symm)
  square := IsPullback.of_right' (IsPullback.of_hasPullback _ _) (IsPullback.of_hasPullback _ _)

/-- The morphism of `ℋ_d` attached to `h : T' ⟶ T` and `x` lies over `h`. -/
@[simp] theorem specFiniteCoverMap_f {T' T : BigFppfOver 𝒞 S hS} (h : T' ⟶ T)
    (x : T ⟶ structureConstantsSiteObject 𝒞 S hS d) :
    (specFiniteCoverMap 𝒞 S hS d h x).f = h := rfl

/-- The cover component of `AlgebraicGeometry.Space.specFiniteCoverMap` commutes with the
projections to the universal degree-`d` cover. -/
@[simp] theorem specFiniteCoverMap_g_comp_fst {T' T : BigFppfOver 𝒞 S hS} (h : T' ⟶ T)
    (x : T ⟶ structureConstantsSiteObject 𝒞 S hS d) :
    (specFiniteCoverMap 𝒞 S hS d h x).g ≫ pullback.fst (universalCoverSiteHom 𝒞 S hS d) x =
      pullback.fst (universalCoverSiteHom 𝒞 S hS d) (h ≫ x) :=
  IsPullback.lift_fst _ _ _ _

/-- Two morphisms into the cover attached to `x` agree as soon as they agree after both
projections of the cartesian square defining that cover. -/
theorem specFiniteCoverMap_hom_ext {T : BigFppfOver 𝒞 S hS}
    (x : T ⟶ structureConstantsSiteObject 𝒞 S hS d) {W : BigFppfOver 𝒞 S hS}
    {a b : W ⟶ (specFiniteCover 𝒞 S hS d x).Z}
    (hfst : a ≫ pullback.fst (universalCoverSiteHom 𝒞 S hS d) x =
      b ≫ pullback.fst (universalCoverSiteHom 𝒞 S hS d) x)
    (hsnd : a ≫ (specFiniteCover 𝒞 S hS d x).q = b ≫ (specFiniteCover 𝒞 S hS d x).q) : a = b :=
  (specFiniteCover_isPullback 𝒞 S hS d x).hom_ext hfst hsnd

end AlgebraicGeometry.Space

end
