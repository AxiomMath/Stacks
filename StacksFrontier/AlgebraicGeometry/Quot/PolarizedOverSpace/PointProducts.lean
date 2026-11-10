module

public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedOverSpace.BaseChangeFullBase
public import StacksFrontier.AlgebraicGeometry.Spaces.FibreDegreeStratification

/-!
# Products of points of an algebraic space, and the fibre products of base changes

For two points `a = (U, s)` and `b = (V, t)` of an algebraic space `T`, the fibre product
`U ×_T V` is represented by a scheme (the diagonal of `T` is representable), which is a point
`a ⊓ b` of `T` with morphisms of points to `a` and to `b`. For a polarized family `X ⟶ T`, the base
change of `X` along `a ⊓ b` is the fibre product over `X` of the base changes along `a` and `b`.
This is how the pairwise fibre products of the descent data of Stacks 04W8 are read on points of
`T`.

## Main definitions

* `AlgebraicGeometry.PolarizedOverSpace.pullPoint`: the restriction of a point along a morphism of
  schemes, with `pullPointHom` its morphism of points.
* `AlgebraicGeometry.PolarizedOverSpace.prodPoint`, `prodPointFst`, `prodPointSnd`: the product of
  two points.

## Main results

* `AlgebraicGeometry.PolarizedOverSpace.isPullback_fibreMap_prodPoint`: the base change along
  `a ⊓ b` is the fibre product of the base changes along `a` and `b`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.PolarizedOverSpace

attribute [local implicit_reducible] Stack.fibredCategory BasedCategory.ofFunctor schemeSpace
  Functor.toPseudofunctor' pseudofunctorOfIsLocallyDiscrete typeToGrpd Grpd.forgetToCat
  MorphismProperty

variable {B : BigFppfSite.{u}} {T : AlgebraicSpaces B integerBase (hZ B)}

section Pull

variable (a : (Points T).obj) {W : Site B} (g : W ⟶ a.base)

/-- The restriction of a point of `T` along a morphism of schemes into its base. -/
abbrev pullPoint : (Points T).obj :=
  SpacesOverSpace.pt W (yonedaEquiv (yoneda.map g ≫ (SpacesOverSpace.pointMap a).hom))

/-- The morphism classifying `pullPoint a g` is `yoneda.map g` followed by the morphism
classifying `a`. -/
theorem pointMap_pullPoint :
    (SpacesOverSpace.pointMap (pullPoint a g)).hom =
      yoneda.map g ≫ (SpacesOverSpace.pointMap a).hom :=
  SpacesOverSpace.pointMap_pt_yonedaEquiv _

/-- If `c` is the composite of `yoneda.map g` with the morphism classifying `a`, then the section
of `T` classified by `c` is the restriction of the section of `a` along `g`. -/
theorem yonedaEquiv_comp_pointMap {c : yoneda.obj W ⟶ T.obj}
    (hc : yoneda.map g ≫ (SpacesOverSpace.pointMap a).hom = c) :
    yonedaEquiv c = T.obj.map g.op a.fiber.as := by
  subst hc
  change yonedaEquiv (yoneda.map g ≫ yonedaEquiv.symm a.fiber.as) = _
  rw [yonedaEquiv_symm_naturality_left, Equiv.apply_symm_apply]

/-- The morphism of points from a restriction. -/
abbrev pullPointHom : pullPoint a g ⟶ a :=
  SpacesOverSpace.toPoint g (yonedaEquiv_comp_pointMap a g rfl)

end Pull

section Product

variable (a b : (Points T).obj)

/-- The morphism from the scheme of a point to `T` classifying it is relatively representable. -/
theorem relativelyRepresentable_pointMap :
    yoneda.relativelyRepresentable (SpacesOverSpace.pointMap a).hom :=
  Space.relativelyRepresentable_of_isAlgebraicSpace B integerBase (hZ B) T.property _

/-- The scheme representing `U ×_T V`. -/
def prodScheme : Site B :=
  (relativelyRepresentable_pointMap a).pullback (SpacesOverSpace.pointMap b).hom

/-- The projection `U ×_T V ⟶ V`. -/
def prodSnd : prodScheme a b ⟶ b.base :=
  (relativelyRepresentable_pointMap a).snd (SpacesOverSpace.pointMap b).hom

/-- The projection `U ×_T V ⟶ U`. -/
def prodFst : prodScheme a b ⟶ a.base :=
  (relativelyRepresentable_pointMap a).fst' (SpacesOverSpace.pointMap b).hom

/-- The square formed by the projections `prodFst a b`, `prodSnd a b` and the morphisms
classifying `a` and `b` is a pullback of presheaves. -/
theorem isPullback_prod :
    IsPullback (yoneda.map (prodFst a b)) (yoneda.map (prodSnd a b))
      (SpacesOverSpace.pointMap a).hom (SpacesOverSpace.pointMap b).hom :=
  (relativelyRepresentable_pointMap a).isPullback' _

/-- **The product of two points of `T`.** -/
abbrev prodPoint : (Points T).obj := pullPoint b (prodSnd a b)

/-- The second projection of the product of two points. -/
abbrev prodPointSnd : prodPoint a b ⟶ b := pullPointHom b (prodSnd a b)

/-- The first projection of the product of two points. -/
abbrev prodPointFst : prodPoint a b ⟶ a :=
  SpacesOverSpace.toPoint (prodFst a b)
    (yonedaEquiv_comp_pointMap a (prodFst a b) (isPullback_prod a b).w)

/-- The morphism of bases underlying `prodPointFst a b` is `prodFst a b`. -/
theorem prodPointFst_base : (prodPointFst a b).base = prodFst a b := rfl

/-- The morphism of bases underlying `prodPointSnd a b` is `prodSnd a b`. -/
theorem prodPointSnd_base : (prodPointSnd a b).base = prodSnd a b := rfl

end Product

section Fibre

variable (ξ : PolarizedSpacesOver B T)

/-- The base change along a morphism of points is cartesian over the morphism of bases, on
presheaves. -/
theorem isPullback_yoneda_fibreMap {a' a : (Points T).obj} (u : a' ⟶ a) :
    IsPullback (yoneda.map (fibreMap ξ u)) (yoneda.map (fibreProj ξ a'))
      (yoneda.map (fibreProj ξ a)) (yoneda.map u.base) := by
  have big : IsPullback (yoneda.map (fibreMap ξ u) ≫ fibreFst ξ a) (yoneda.map (fibreProj ξ a'))
      (familyMap ξ).hom (yoneda.map u.base ≫ (SpacesOverSpace.pointMap a).hom) := by
    rw [fibreMap_fst, SpacesOverSpace.yoneda_map_comp_pointMap_hom u]
    exact isPullback_fibre ξ a'
  exact IsPullback.of_right big (by rw [← Functor.map_comp, ← Functor.map_comp, fibreMap_proj])
    (isPullback_fibre ξ a)

/-- **The base change along the product of two points is the fibre product over `X` of the base
changes along the two points.** -/
theorem isPullback_fibreMap_prodPoint (a b : (Points T).obj) :
    IsPullback (yoneda.map (fibreMap ξ (prodPointFst a b)))
      (yoneda.map (fibreMap ξ (prodPointSnd a b))) (fibreFst ξ a) (fibreFst ξ b) := by
  have h₁ := isPullback_yoneda_fibreMap ξ (prodPointFst a b)
  have big := h₁.paste_vert (isPullback_prod a b)
  rw [← (isPullback_yoneda_fibreMap ξ (prodPointSnd a b)).w,
    (isPullback_fibre ξ a).w.symm] at big
  refine IsPullback.of_bot big ?_ (isPullback_fibre ξ b)
  rw [fibreMap_fst, fibreMap_fst]

end Fibre

end AlgebraicGeometry.PolarizedOverSpace

end
