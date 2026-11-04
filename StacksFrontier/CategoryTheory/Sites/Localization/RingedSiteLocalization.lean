module

public import Mathlib.CategoryTheory.Sites.Over
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Relocalization
public import StacksFrontier.CategoryTheory.Sites.Topos.MorphismOfTopoi
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite

/-!
# Localizing a ringed site at an object

Let `(C, O)` be a ringed site and `U` an object of `C`. The localization of `(C, O)` at `U` has
as underlying site the slice `Over U` with the topology `J.over U` of Mathlib's
`CategoryTheory.Sites.Over`, and as structure sheaf the restriction `O.over U`, whose value at
`V ⟶ U` is `O(V)`. The forgetful functor `Over.forget U` is both continuous and cocontinuous for
these topologies, so it induces a morphism of topoi `Sh(C/U) ⟶ Sh(C)` whose inverse image is
restriction along the slice projection; and because the structure sheaf of the localization *is*
that restriction, the structure map of this morphism is the identity.

## Main definitions

* `AlgebraicGeometry.RingedSite.over X U`: the localization of the ringed site `X` at `U`.
* `AlgebraicGeometry.RingedSite.overFsharp X U`: the structure map of the localization, the
  identity of `O.over U`.
* `AlgebraicGeometry.RingedSite.overMorphismOfTopoi X U`: the localization morphism of topoi,
  with its inverse image restriction along `Over.forget U` and its direct image the right
  adjoint of that restriction.

## Main results

* `AlgebraicGeometry.RingedSite.over_O` and `AlgebraicGeometry.RingedSite.over_O_obj_obj`: the
  structure sheaf of the localization is the restriction of `O`, with value `O(V)` at an object
  `V ⟶ U` of the slice.
* `AlgebraicGeometry.RingedSite.overFsharp_eq`: the structure map is the identity.

## Implementation notes

The inverse image of the localization morphism of topoi is `sheafPushforwardContinuous` —
*restriction* along `Over.forget U` — and not `sheafPullback`: for the slice projection the two
adjoint pairs available on sheaves are `(restriction, right Kan extension)` from
cocontinuity and `(sheafification of left Kan extension, restriction)` from continuity, and the
geometric morphism of the source is the former, with restriction as its left exact inverse
image. Left exactness is
`CategoryTheory.Functor.preservesFiniteLimits_sheafPushforwardContinuous`.

The value universe of the topoi is `max u v w`, large enough to contain both the slice category
`Over U : Type (max u v)` and the sections of `O`, so that the right adjoint of restriction
exists.

The source also identifies the canonical inverse image `π⁻¹ O` *as a sheaf of commutative
rings* with `O.over U`, and transports the identity structure map across that identification.
That half needs the inverse-image functor on sheaves of rings along a morphism of topoi, so it
is supplied separately, in
`StacksFrontier/CategoryTheory/Sites/Localization/RingedSiteLocalizationInverseImage.lean`.

## References

* [Stacks Project, Tag 00Y0](https://stacks.math.columbia.edu/tag/00Y0)
* [Stacks Project, Tag 04IX](https://stacks.math.columbia.edu/tag/04IX)
-/

@[expose] public section

open CategoryTheory

universe u v w

namespace AlgebraicGeometry.RingedSite

/-- The localization of a ringed site at an object `U`: its underlying site is the slice
over `U`, and its structure sheaf is the restriction of the original structure sheaf. -/
@[implicit_reducible]
def over (X : RingedSite.{u, v, w}) (U : X.C) : RingedSite.{max u v, v, w} where
  C := Over U
  J := X.J.over U
  O := X.O.over U

/-- The structure sheaf on the localized site is the restriction of the original structure
sheaf along the slice projection. -/
@[simp]
theorem over_O (X : RingedSite.{u, v, w}) (U : X.C) : (X.over U).O = X.O.over U := rfl

/-- At an object `V ⟶ U` of the localized site, the localized structure sheaf has value
the original structure sheaf evaluated at `V`. -/
@[simp]
theorem over_O_obj_obj (X : RingedSite.{u, v, w}) (U : X.C) (V : (Over U)ᵒᵖ) :
    (X.over U).O.obj.obj V = X.O.obj.obj (Opposite.op V.unop.left) := rfl

/-- The structure map of the localization, in the presentation of the localized structure
sheaf as a restriction: it is the identity. -/
def overFsharp (X : RingedSite.{u, v, w}) (U : X.C) :
    X.O.over U ⟶ (X.over U).O := 𝟙 _

/-- The structure map of the localization is the identity map. -/
@[simp]
theorem overFsharp_eq (X : RingedSite.{u, v, w}) (U : X.C) :
    X.overFsharp U = 𝟙 _ := rfl

/-- The localization morphism of topoi. Its inverse image is restriction along the slice
projection and its direct image is the right Kan extension along it. -/
noncomputable def overMorphismOfTopoi (X : RingedSite.{u, v, w}) (U : X.C) :
    MorphismOfTopoi (Sheaf (X.J.over U) (Type (max u v w)))
      (Sheaf X.J (Type (max u v w))) where
  inverseImage := (Over.forget U).sheafPushforwardContinuous _ (X.J.over U) X.J
  pushforward := (Over.forget U).sheafPushforwardCocontinuous _ (X.J.over U) X.J
  adj := (Over.forget U).sheafAdjunctionCocontinuous _ (X.J.over U) X.J
  preservesFiniteLimits := inferInstance

end AlgebraicGeometry.RingedSite
