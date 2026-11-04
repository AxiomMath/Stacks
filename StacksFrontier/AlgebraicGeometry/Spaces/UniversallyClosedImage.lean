module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Proper
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosed

/-!
# Universal closedness descends along a surjection of the source

Let `X ⟶ Y` be a surjective morphism of algebraic spaces over `S`, both of them over a base
algebraic space `Z`. If `X` is universally closed over `Z`, then so is `Y`. This is the first
assertion of Stacks 08AJ, and the second is the observation that `Y` is then proper over `Z`
as soon as it is separated and of finite type over `Z`.

The argument is purely topological. Fix a base change `T ⟶ Z`. A closed set `K` of
`|T ×_Z Y|` has closed preimage `K'` in `|T ×_Z X|`, and the image of `K'` in `|T|` is the
image of `K`, because `|T ×_Z X| → |T ×_Z Y|` is surjective — this is Stacks 03MH,
surjectivity on points being stable under base change. The projection of `T ×_Z X` is closed
by hypothesis, so the image of `K` is closed.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.Space.isClosedMap_pointsMap_of_surjective_comp`: if a composite has
  closed map on points and the first factor is surjective on points, then the second factor
  has closed map on points.
* `AlgebraicGeometry.Space.universallyClosed_of_isSurjective`: the first assertion of
  Stacks 08AJ.
* `AlgebraicGeometry.Space.isProper_of_isSurjective`: the second assertion of Stacks 08AJ.

## Implementation notes

The space-level statement is what a development of algebraic spaces needs. The corresponding
scheme-level statement is Stacks 03GN, and the proofs of Stacks 082H and Stacks 0A4X cite
03GN only after their object of interest has already been shown to be a *scheme*; the
argument never uses that, and 08AJ is the form in which it applies to an algebraic space.

The comparison of the two base changes is the pasting isomorphism
`(T ×_Z Y) ×_Y X ≅ T ×_Z X` of `CategoryTheory.Limits.pullbackLeftPullbackSndIso`, which
identifies the projection of `T ×_Z X` to `T` with the composite of the base change
`(T ×_Z Y) ×_Y X ⟶ T ×_Z Y` of `X ⟶ Y` and the projection of `T ×_Z Y` to `T`. Its
surjectivity on points is `AlgebraicGeometry.Space.surjective_pointsMap_of_isPullback`, the
content of Stacks 03MH.

`AlgebraicGeometry.Space.pointTopology` is installed as a local instance so that
`IsClosedMap` elaborates without explicit topology arguments.

## References

* [Stacks Project, Tag 03GN](https://stacks.math.columbia.edu/tag/03GN)
* [Stacks Project, Tag 03ME](https://stacks.math.columbia.edu/tag/03ME)
* [Stacks Project, Tag 03MH](https://stacks.math.columbia.edu/tag/03MH)
* [Stacks Project, Tag 08AJ](https://stacks.math.columbia.edu/tag/08AJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The topological step -/

/-- **A closed map on points descends along a surjection on points.** If the map on points of
a composite `f ≫ g` of morphisms of presheaves on the big fppf site of `S` is closed and the
map on points of `f` is surjective, then the map on points of `g` is closed.

The image under `g` of a closed set `K` is the image under `f ≫ g` of the preimage of `K`
under `f`, which is closed because the map on points of `f` is continuous. -/
theorem isClosedMap_pointsMap_of_surjective_comp
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : Function.Surjective (pointsMap B S hS X f))
    (hfg : IsClosedMap (pointsMap B S hS X (f ≫ g))) :
    IsClosedMap (pointsMap B S hS Y g) := by
  intro K hK
  have himg : pointsMap B S hS Y g '' K
      = pointsMap B S hS X (f ≫ g) '' (pointsMap B S hS X f ⁻¹' K) := by
    rw [pointsMap_comp, Set.image_comp, Set.image_preimage_eq K hf]
  rw [himg]
  exact hfg _ (hK.preimage (continuous_pointsMap B S hS f))

/-! ### Stacks 08AJ -/

/-- **Stacks 08AJ, first assertion.** Let `p : X ⟶ Z` and `q : Y ⟶ Z` be morphisms of
algebraic spaces over `S` and let `f : X ⟶ Y` be a morphism over `Z`. If `p` is universally
closed and `f` is surjective, then `q` is universally closed.

A base change `T ×_Z Y ⟶ T` of `q` is, after the pasting isomorphism
`(T ×_Z Y) ×_Y X ≅ T ×_Z X`, preceded by the base change of `f`, which is surjective on
points by Stacks 03MH; the composite is the base change `T ×_Z X ⟶ T` of `p`, closed by
hypothesis. -/
@[stacks 08AJ "first assertion: universal closedness"]
theorem universallyClosed_of_isSurjective {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (_hX : IsAlgebraicSpace B S hS X) (_hY : IsAlgebraicSpace B S hS Y)
    (_hZ : IsAlgebraicSpace B S hS Z) (f : X ⟶ Y) (p : X ⟶ Z) (q : Y ⟶ Z)
    (hcomm : f ≫ q = p) (hf : IsSurjective B S hS f)
    (hp : UniversallyClosed B S hS p) :
    UniversallyClosed B S hS q := by
  subst hcomm
  intro T hT t
  have hm : Function.Surjective
      (pointsMap B S hS (pullback (pullback.snd t q) f) (pullback.fst (pullback.snd t q) f)) :=
    surjective_pointsMap_of_isPullback B S hS (IsPullback.of_hasPullback _ _).flip hf
  refine isClosedMap_pointsMap_of_surjective_comp B S hS _ (pullback.fst t q) hm ?_
  exact isClosedMap_pointsMap_of_comp_isIso B S hS (pullbackLeftPullbackSndIso t q f).hom
    (pullbackLeftPullbackSndIso_hom_fst t q f) (hp T hT t)

/-- **Stacks 08AJ, second assertion.** In the situation of
`AlgebraicGeometry.Space.universallyClosed_of_isSurjective`, if moreover `q` is separated and
of finite type, then `q` is proper. -/
@[stacks 08AJ "second assertion: properness"]
theorem isProper_of_isSurjective {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hZ : IsAlgebraicSpace B S hS Z) (f : X ⟶ Y) (p : X ⟶ Z) (q : Y ⟶ Z)
    (hcomm : f ≫ q = p) (hf : IsSurjective B S hS f)
    (hp : UniversallyClosed B S hS p)
    (hsep : IsSeparated B S hS q) (hft : IsFiniteType B S hS q) :
    IsProper B S hS q :=
  IsProper.mk' B S hS hsep hft
    (universallyClosed_of_isSurjective B S hS hX hY hZ f p q hcomm hf hp)

end AlgebraicGeometry.Space

end
