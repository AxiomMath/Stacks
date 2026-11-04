module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Topology.Sheaves.Functors
public import StacksFrontier.AlgebraicGeometry.AffineQcohPushforward.Basic

/-!
# Direct image of sheaves of modules along a continuous map

`AlgebraicGeometry.Scheme.Modules.pushforward` is the direct image of sheaves of modules along a
*morphism of schemes*: it needs the comparison `𝒪_V ⟶ f_*𝒪_U` to restrict scalars along. An
argument that has only a continuous map `φ : |U| ⟶ Y` of the underlying spaces cannot use it, and
does not need to: the direct image `φ_*𝒪_U` is itself a sheaf of rings on `Y`, and the modules over
it are the direct images of the modules over `𝒪_U`, with no comparison to supply.

This file provides that functor and the properties a cohomological argument asks of it — it is a
right adjoint, hence additive and left exact.

The construction is `SheafOfModules.pushforward` along `TopologicalSpace.Opens.map φ`, which is
continuous for the open-cover topologies with no hypothesis on `φ` (the instance is in
`Mathlib/Topology/Sheaves/SheafCondition/Sites.lean`), applied to the identity of the direct image
ring sheaf. The pattern is also what transport along a homeomorphism of underlying spaces needs,
that being the special case of an invertible `φ`.

## Main definitions

* `Stacks.ContinuousMapPushforward.modules`: the direct image of sheaves of modules along `φ`, over
  the direct image sheaf of rings `Stacks.AlgebraicGeometry.AffineQcohPushforward.pushforwardRing`.
* `Stacks.ContinuousMapPushforward.schemeModules`: the same with the source the structure sheaf of
  a scheme, so that its domain is `U.Modules`.

## Implementation notes

`Stacks.ContinuousMapPushforward.toPushforward` is the identity of the direct image ring sheaf at
the type `SheafOfModules.pushforward` asks for, so that `modules` is literally a
`SheafOfModules.pushforward` at the site spelling. Instance synthesis for
`Stacks.ContinuousMapPushforward.isRightAdjoint_modules` cannot reach the presheaf-level adjoint
underneath on its own: `PresheafOfModules.pushforward` wants its argument at the type
`S.obj ⟶ (Opens.map φ).op ⋙ R.obj`, while `Sheaf.Hom.hom` delivers it at
`S.obj ⟶ (((Opens.map φ).sheafPushforwardContinuous RingCat _ _).obj R).obj`, and the two agree
only once `Functor.sheafPushforwardContinuous` is unfolded. That one instance is therefore built
in the proof from `CategoryTheory.Functor.isRightAdjoint_of_leftAdjointObjIsDefined_eq_top` and
`PresheafOfModules.pullbackObjIsDefined_eq_top`, which is the construction Mathlib's own
anonymous instance uses.

## References

* [Stacks Project, Tag 0E3X](https://stacks.math.columbia.edu/tag/0E3X)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.ContinuousMapPushforward

section Topological

variable {X Y : TopCat.{u}} (φ : X ⟶ Y) (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})

/-- **The identity of the direct image sheaf of rings**, at the type
`SheafOfModules.pushforward` asks of its argument. -/
def toPushforward : AlgebraicGeometry.AffineQcohPushforward.pushforwardRing φ R ⟶
    ((Opens.map φ).sheafPushforwardContinuous RingCat.{u}
      (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)).obj R :=
  𝟙 _

/-- **The direct image of sheaves of modules along a continuous map.** A sheaf of `R`-modules on
`X` is carried to the sheaf `U ↦ M(φ⁻¹U)` of modules over `φ_*R`. -/
def modules : SheafOfModules.{u} R ⥤
    SheafOfModules.{u} (AlgebraicGeometry.AffineQcohPushforward.pushforwardRing φ R) :=
  SheafOfModules.pushforward (toPushforward φ R)

/-- **The direct image along a continuous map is a right adjoint**, its left adjoint being the
inverse image. Everything else in this file follows from this. -/
instance isRightAdjoint_modules : (modules φ R).IsRightAdjoint := by
  -- The presheaf-level adjoint, which synthesis cannot reach through `Sheaf.Hom.hom`: the type
  -- ascription names the shape `PresheafOfModules.pushforward` wants, and the construction is
  -- Mathlib's own for that instance.
  have : (PresheafOfModules.pushforward.{u}
      ((toPushforward φ R).hom :
        (AlgebraicGeometry.AffineQcohPushforward.pushforwardRing φ R).obj ⟶
          (Opens.map φ).op ⋙ R.obj)).IsRightAdjoint :=
    Functor.isRightAdjoint_of_leftAdjointObjIsDefined_eq_top
      (PresheafOfModules.pullbackObjIsDefined_eq_top _)
  unfold modules
  infer_instance

section Additive

attribute [local instance] preservesBinaryBiproducts_of_preservesBinaryProducts

/-- **The direct image along a continuous map is additive**, being a right adjoint. -/
instance additive_modules : (modules φ R).Additive :=
  Functor.additive_of_preservesBinaryBiproducts _

end Additive

end Topological

section Scheme

variable {U : Scheme.{u}} {Y : TopCat.{u}} (φ : (U : TopCat) ⟶ Y)

/-- **The direct image of `𝒪_U`-modules along a continuous map out of the space of a scheme.**
This is `Stacks.ContinuousMapPushforward.modules` for the structure sheaf of `U`, declared with
domain `AlgebraicGeometry.Scheme.Modules` so that short complexes of `U.Modules` can be mapped
along it. -/
def schemeModules :
    U.Modules ⥤ SheafOfModules.{u}
      (AlgebraicGeometry.AffineQcohPushforward.pushforwardRing φ U.ringCatSheaf) :=
  modules φ U.ringCatSheaf

/-- The direct image of `𝒪_U`-modules along a continuous map is a right adjoint.
Instance synthesis does not see `AlgebraicGeometry.Scheme.ringCatSheaf` as a sheaf on the
open-cover site without unfolding `TopCat.Sheaf`, so the instances of the previous section are
supplied by name rather than found. -/
instance isRightAdjoint_schemeModules : (schemeModules φ).IsRightAdjoint :=
  isRightAdjoint_modules φ U.ringCatSheaf

/-- The direct image of `𝒪_U`-modules along a continuous map is additive. -/
instance additive_schemeModules : (schemeModules φ).Additive :=
  additive_modules φ U.ringCatSheaf

end Scheme

end Stacks.ContinuousMapPushforward

end
