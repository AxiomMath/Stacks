module

public import StacksFrontier.AlgebraicGeometry.Quot.QuotientFunctor
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SmallEtaleFirstOrderThickening
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.BaseChangeOrder
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversalThickeningUnramified
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.FormalGlueingAffineSituation

/-!
# A first order thickening of test schemes in the situation of the functor of quotients

In Situation 082M, let `T ⊂ T'` be a first order thickening of schemes over `B` (Stacks 04EX),
given by a morphism `h : T ⟶ T'` of schemes over `B`. Remark 0CZU opens with the observation that
`X_T ⊂ X_{T'}` is then a first order thickening of algebraic spaces. This file proves that, in the
form the deformation theory of ringed topoi consumes: the morphism `X_T ⟶ X_{T'}` identifies
`X_T` with the inverse image of `T` in `X_{T'}`, which is a first order thickening of `X_{T'}`
(Stacks 05ZK, 09ZX), so its morphism of small étale ringed topoi is a first order thickening of
ringed topoi (the content of Stacks 0D16), and likewise for `T ⊂ T'` itself.

## Main results

* `AlgebraicGeometry.Space.QuotientSituation.range_relativeMap`: the image of `X_T` in `X_{T'}` is
  the inverse image of the image of `T` in `T'`.
* `AlgebraicGeometry.Space.QuotientSituation.isFirstOrderThickening_range_relativeMap`: it is a
  first order thickening of `X_{T'}`.
* `AlgebraicGeometry.Space.QuotientSituation.relativeMapFirstOrderThickening` and
  `AlgebraicGeometry.Space.QuotientSituation.testSchemeFirstOrderThickening`: the first order
  thickenings of small étale ringed topoi `X_T ⊂ X_{T'}` and `T ⊂ T'`.

## References

* [Stacks Project, Tag 0CZU](https://stacks.math.columbia.edu/tag/0CZU)
* [Stacks Project, Tag 04EX](https://stacks.math.columbia.edu/tag/04EX)
* [Stacks Project, Tag 05ZK](https://stacks.math.columbia.edu/tag/05ZK)
* [Stacks Project, Tag 09ZX](https://stacks.math.columbia.edu/tag/09ZX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

/-- **In a cartesian square of presheaves of types, the image of the top map is the inverse image
of the image of the bottom map.** -/
theorem CategoryTheory.Subfunctor.range_eq_preimage_range_of_isPullback {C : Type*} [Category C]
    {P A B Z : Cᵒᵖ ⥤ Type u} {fst : P ⟶ A} {snd : P ⟶ B} {f : A ⟶ Z} {g : B ⟶ Z}
    (h : IsPullback fst snd f g) :
    Subfunctor.range fst = (Subfunctor.range g).preimage f := by
  ext U x
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨snd.app U p, (congrArg (fun φ => φ.app U p) h.w).symm⟩
  · rintro ⟨y, hy⟩
    obtain ⟨p, hp, -⟩ :=
      Types.exists_of_isPullback (h.map ((evaluation Cᵒᵖ (Type u)).obj U)) x y hy.symm
    exact ⟨p, hp⟩

namespace AlgebraicGeometry.Space.QuotientSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (D : QuotientSituation B S hS) {T T' : SchemesOver D.Y} (h : T ⟶ T')

/-- **The image of `X_T` in `X_{T'}` is the inverse image of the image of `T` in `T'`**: the
square of base changes is cartesian. -/
theorem range_relativeMap :
    Subfunctor.range (D.relativeMap h).hom =
      (Subfunctor.range ((schemeSpaceFunctor B S hS).map h.left).hom).preimage
        (D.projection T').hom :=
  Subfunctor.range_eq_preimage_range_of_isPullback
    (AlgebraicSpaces.isPullback_hom B S hS (isPullback_baseChangeMap D.f h))

variable (hh : Stacks.Thickenings.IsFirstOrderThickening ((BigFppfOver.toScheme B S hS).map h.left))

include hh in
/-- The morphism `X_T ⟶ X_{T'}` is a monomorphism, being a base change of the closed immersion
`T ⟶ T'`. -/
theorem mono_relativeMap : Mono (D.relativeMap h).hom := by
  have : Mono ((schemeSpaceFunctor B S hS).map h.left).hom :=
    mono_yoneda_map_of_isClosedImmersion h.left hh.1
  exact PullbackCone.mono_fst_of_is_pullback_of_mono
    (AlgebraicSpaces.isPullback_hom B S hS (isPullback_baseChangeMap D.f h)).isLimit

include hh in
/-- **Remark 0CZU, `X_T ⊂ X_{T'}` is a first order thickening**: the image of `X_T` in `X_{T'}`,
which is the inverse image of the first order thickening `T ⊂ T'`, is a first order thickening of
`X_{T'}` (Stacks 09ZX). -/
@[stacks 0CZU]
theorem isFirstOrderThickening_range_relativeMap :
    IsFirstOrderThickening B S hS (D.space T') (Subfunctor.range (D.relativeMap h).hom) := by
  rw [range_relativeMap]
  exact isFirstOrderThickening_preimage B S hS _ (D.projection T')
    (isFirstOrderThickening_range_yoneda_map B S hS h.left hh)

/-- **The first order thickening `X_T ⊂ X_{T'}` of small étale ringed topoi.** -/
def relativeMapFirstOrderThickening :
    Deformation.ToposThickening.FirstOrderThickening.{u, u + 1, u, u, u + 1, u}
      (smallEtaleRingedToposHom B S hS (D.relativeMap h)) :=
  haveI := D.mono_relativeMap h hh
  smallEtaleRingedToposHomFirstOrderThickening B S hS (D.relativeMap h) inferInstance
    (D.isFirstOrderThickening_range_relativeMap h hh)

/-- **The first order thickening `T ⊂ T'` of small étale ringed topoi.** -/
def testSchemeFirstOrderThickening :
    Deformation.ToposThickening.FirstOrderThickening.{u, u + 1, u, u, u + 1, u}
      (smallEtaleRingedToposHom B S hS ((schemeSpaceFunctor B S hS).map h.left)) :=
  haveI : Mono ((schemeSpaceFunctor B S hS).map h.left).hom :=
    mono_yoneda_map_of_isClosedImmersion h.left hh.1
  smallEtaleRingedToposHomFirstOrderThickening B S hS ((schemeSpaceFunctor B S hS).map h.left)
    inferInstance (isFirstOrderThickening_range_yoneda_map B S hS h.left hh)

end AlgebraicGeometry.Space.QuotientSituation

end
