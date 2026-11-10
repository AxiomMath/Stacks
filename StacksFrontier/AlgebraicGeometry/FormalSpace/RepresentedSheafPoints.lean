module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.SubcanonicalYoneda
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedPointsComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedQuasiCompactPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresented
public import StacksFrontier.CategoryTheory.Sites.SubcanonicalSheafifiedYoneda

/-!
# The point space of a sheafified representable is the representing scheme

Let `S` be a scheme contained in a big fppf site `B` and let `U` be an object of the big fppf
site of `S`. The fppf sheaf of `Type (u + 1)` represented by `U` is the sheafified representable
`h_U^#` of `CategoryTheory.Sheaf.sheafifiedYoneda`, and it has a point space
`AlgebraicGeometry.Space.pointsULift` carrying `AlgebraicGeometry.Space.pointTopologyULift`. This
file identifies that point space with the topological space of the representing scheme.

This is the dictionary between the two ways a point of a formal algebraic space presented by a
ring `A` can be read: as a point of the point space of the sheaf, where a closed subset such as
the one a completion is taken along lives, and as a point of a scheme over `Spec A`, where the
ideal it cuts out of `A` lives.

## Main definitions

* `AlgebraicGeometry.Space.sheafifiedYonedaPresheafIso`: the underlying presheaf of `h_U^#` is
  the universe lift of the presheaf `h_U` represented by `U` in `Type u`.
* `AlgebraicGeometry.Space.pointsULiftHomeomorphScheme`: **the point space of `h_U^#` is the
  representing scheme.**

## Main results

* `AlgebraicGeometry.Space.pointsULiftHomeomorphScheme_pointsMapULift`: the identification is
  natural in `U`, the map on points induced by a morphism of the site being the underlying map
  of schemes.

## Implementation notes

The homeomorphism is the composite of three identifications from the library, taken at the one
object `U`: the site is subcanonical, so `h_U^#` is the Yoneda embedding of `U` into sheaves of
`Type (u + 1)` by `CategoryTheory.Sheaf.sheafifiedYonedaIsoUliftYoneda'`, whose underlying
presheaf is the universe lift of `h_U`; the points of a universe lift are the points of the
presheaf, by `AlgebraicGeometry.Space.pointsHomeomorphPointsULift`; and the points of a
represented presheaf of `Type u` are the points of the representing scheme, by clause (1) of
Stacks 03BX, `AlgebraicGeometry.Space.schemePointsHomeomorph`. None of the three is
generalised: the first is a statement about an arbitrary subcanonical site and knows nothing of
schemes, the second is about an arbitrary presheaf of `Type u` and knows nothing of
representability, and the third is about presheaves of `Type u` only, which is the universe in
which `AlgebraicGeometry.Space.pointsToScheme` is available at all. What this file adds is exactly
their composite at a sheafified representable, which is the shape the formal algebraic spaces
use.

## References

* [Stacks Project, Tag 03BX](https://stacks.math.columbia.edu/tag/03BX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] pointTopology pointTopologyULift

/-- The underlying presheaf of the fppf sheaf `h_U^#` of `Type (u + 1)` represented by an object
`U` of the big fppf site of `S` is the universe lift of the presheaf `h_U` of `Type u`
represented by `U`. The site being subcanonical, `h_U^#` is the Yoneda embedding of `U` into
sheaves by `CategoryTheory.Sheaf.sheafifiedYonedaIsoUliftYoneda'`, whose underlying presheaf is
that universe lift. -/
def sheafifiedYonedaPresheafIso (U : BigFppfOver B S hS) :
    ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj U).obj ≅
      (yoneda.obj U ⋙ uliftFunctor.{u + 1}) :=
  (sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1))).mapIso
    ((Sheaf.sheafifiedYonedaIsoUliftYoneda'.{u, u + 1} (BigFppfOver.topology B S hS)).app U)

/-- **The point space of a sheafified representable is the representing scheme.** For an object
`U` of the big fppf site of `S`, the point space of the fppf sheaf `h_U^#` of `Type (u + 1)` it
represents is homeomorphic to the topological space of the scheme representing `U`.

This is the dictionary that reads a point of a formal algebraic space presented by a ring `A`,
tested on a sheafified representable, as a point of a scheme over `Spec A`. It is the composite
of `AlgebraicGeometry.Space.sheafifiedYonedaPresheafIso`,
`AlgebraicGeometry.Space.pointsHomeomorphPointsULift` and clause (1) of Stacks 03BX,
`AlgebraicGeometry.Space.schemePointsHomeomorph`. -/
def pointsULiftHomeomorphScheme (U : BigFppfOver B S hS) :
    pointsULift.{u + 1} B S hS
        ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj U).obj ≃ₜ
      (BigFppfOver.toScheme B S hS).obj U :=
  (pointsULiftHomeomorphOfIso.{u + 1} B S hS (sheafifiedYonedaPresheafIso B S hS U)).trans
    ((pointsHomeomorphPointsULift.{u + 1} B S hS (yoneda.obj U)).symm.trans
      (schemePointsHomeomorph B S hS U))

/-- **The dictionary is natural in the object of the site**: the map on points of the fppf sheaf
morphism represented by a morphism `b` of the big fppf site of `S` is the underlying map of
schemes of `b`.

All three constituents of `AlgebraicGeometry.Space.pointsULiftHomeomorphScheme` are natural:
the comparison of the sheafified Yoneda embedding with the Yoneda embedding into sheaves is a
natural isomorphism, the identification of the points of a presheaf with those of its universe
lift is `AlgebraicGeometry.Space.pointsMapULift_whiskerRight_pointsULiftEquiv`, and the
comparison of the points of a represented presheaf with the points of the representing scheme is
`AlgebraicGeometry.Space.pointsToScheme_pointsMap_yoneda`. -/
theorem pointsULiftHomeomorphScheme_pointsMapULift {U' U : BigFppfOver B S hS} (b : U' ⟶ U)
    (x : pointsULift.{u + 1} B S hS
      ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj U').obj) :
    pointsULiftHomeomorphScheme B S hS U
        (pointsMapULift.{u + 1} B S hS _
          ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map b).hom x) =
      (BigFppfOver.toScheme B S hS).map b (pointsULiftHomeomorphScheme B S hS U' x) := by
  have hsq : ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map b).hom ≫
      (sheafifiedYonedaPresheafIso B S hS U).hom =
    (sheafifiedYonedaPresheafIso B S hS U').hom ≫
      Functor.whiskerRight (yoneda.map b) uliftFunctor.{u + 1} :=
    congrArg (fun φ => φ.hom) ((Sheaf.sheafifiedYonedaIsoUliftYoneda'.{u, u + 1}
      (BigFppfOver.topology B S hS)).hom.naturality b)
  -- the comparison isomorphism moves past the transition map
  have hA : pointsMapULift.{u + 1} B S hS _ (sheafifiedYonedaPresheafIso B S hS U).hom
        (pointsMapULift.{u + 1} B S hS _
          ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map b).hom x) =
      pointsMapULift.{u + 1} B S hS _
        (Functor.whiskerRight (yoneda.map b) uliftFunctor.{u + 1})
        (pointsMapULift.{u + 1} B S hS _ (sheafifiedYonedaPresheafIso B S hS U').hom x) := by
    simpa only [pointsMapULift_comp, Function.comp_apply] using
      congrArg (fun φ => pointsMapULift.{u + 1} B S hS _ φ x) hsq
  -- the identification of the two point spaces is natural
  have hB : ∀ y : pointsULift.{u + 1} B S hS (yoneda.obj U' ⋙ uliftFunctor.{u + 1}),
      (pointsHomeomorphPointsULift.{u + 1} B S hS (yoneda.obj U)).symm
          (pointsMapULift.{u + 1} B S hS _
            (Functor.whiskerRight (yoneda.map b) uliftFunctor.{u + 1}) y) =
        pointsMap B S hS (yoneda.obj U') (yoneda.map b)
          ((pointsHomeomorphPointsULift.{u + 1} B S hS (yoneda.obj U')).symm y) := by
    intro y
    have h := congrFun (pointsMapULift_whiskerRight_pointsULiftEquiv.{u + 1} B S hS
      (yoneda.map b)) ((pointsHomeomorphPointsULift.{u + 1} B S hS (yoneda.obj U')).symm y)
    rw [Function.comp_apply, Function.comp_apply] at h
    rw [show pointsULiftEquiv.{u + 1} B S hS (yoneda.obj U')
          ((pointsHomeomorphPointsULift.{u + 1} B S hS (yoneda.obj U')).symm y) = y from
        (pointsHomeomorphPointsULift.{u + 1} B S hS (yoneda.obj U')).apply_symm_apply y] at h
    rw [h]
    exact (pointsHomeomorphPointsULift.{u + 1} B S hS (yoneda.obj U)).symm_apply_apply _
  change schemePointsHomeomorph B S hS U
      ((pointsHomeomorphPointsULift.{u + 1} B S hS (yoneda.obj U)).symm
        (pointsMapULift.{u + 1} B S hS _ (sheafifiedYonedaPresheafIso B S hS U).hom
          (pointsMapULift.{u + 1} B S hS _
            ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map b).hom x))) = _
  rw [hA, hB]
  exact pointsToScheme_pointsMap_yoneda B S hS b _

/-- **The dictionary is natural in the object of the site, read backwards**: the point of
`h_{U'}^#` named by a point `y` of the scheme underlying `U'` is carried by the morphism of
sheaves represented by `b : U' ⟶ U` to the point named by the image of `y` under the underlying
map of schemes. This is
`AlgebraicGeometry.Space.pointsULiftHomeomorphScheme_pointsMapULift` read through the inverse of
the homeomorphism at both ends. -/
theorem pointsMapULift_pointsULiftHomeomorphScheme_symm {U' U : BigFppfOver B S hS} (b : U' ⟶ U)
    (y : (BigFppfOver.toScheme B S hS).obj U') :
    pointsMapULift.{u + 1} B S hS _
        ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map b).hom
        ((pointsULiftHomeomorphScheme B S hS U').symm y) =
      (pointsULiftHomeomorphScheme B S hS U).symm
        ((BigFppfOver.toScheme B S hS).map b y) := by
  refine (pointsULiftHomeomorphScheme B S hS U).injective ?_
  rw [pointsULiftHomeomorphScheme_pointsMapULift B S hS b, Homeomorph.apply_symm_apply,
    Homeomorph.apply_symm_apply]

end AlgebraicGeometry.Space

end
