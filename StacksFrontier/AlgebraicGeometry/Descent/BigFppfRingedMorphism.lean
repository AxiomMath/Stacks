module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigFppfStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.FibreProducts
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.MorphismOfTopoi
public import StacksFrontier.CategoryTheory.Sites.MorphismOfSites.MorphismDefs
public import StacksCore.Tactic.StacksAttribute

/-!
# The morphism of ringed big fppf sites induced by a morphism of schemes

A morphism of schemes `f : X ⟶ Y`, both contained in a big fppf site `B`, induces a morphism of
big sites `f_big : (Sch/X)_fppf → (Sch/Y)_fppf`.  As in Stacks Definition 00X1 a morphism of
sites is *given by* a continuous functor in the opposite direction, and here that functor is
base change: it sends `T / Y` to `X ×_Y T / X`.  Together with the map of sheaves of rings
`f_big^♯ : 𝒪_Y → f_{big, *} 𝒪_X`, whose component at `T / Y` is the map on global functions
induced by the projection `X ×_Y T → T`, this makes `f_big` a morphism of ringed sites
`((Sch/X)_fppf, 𝒪_X) ⟶ ((Sch/Y)_fppf, 𝒪_Y)` in the sense of Stacks Definition 03AD.

## Main definitions

* `CategoryTheory.Over.pullbackForget`: for a morphism `h : U ⟶ V` of a category with fibre
  products, the projection `W ×_V U → W` out of the base change of an object `W / V`, natural
  in `W / V`.
* `AlgebraicGeometry.BigFppfOver.siteHom`: a morphism of schemes contained in a big fppf site,
  as a morphism of the site's chosen category of schemes.
* `AlgebraicGeometry.BigFppfOver.baseChange`: the base-change functor
  `(Sch/Y)_fppf ⥤ (Sch/X)_fppf`, the continuous functor giving `f_big`.
* `AlgebraicGeometry.BigFppfOver.baseChangeProjection`: the projection `X ×_Y T → T` of
  schemes, natural in `T / Y`.
* `AlgebraicGeometry.BigFppfOver.structureComparison`: the map of structure sheaves
  `f_big^♯ : 𝒪_Y → f_{big, *} 𝒪_X`.

## Main results

* `AlgebraicGeometry.BigFppfOver.isContinuous_baseChange`: base change is continuous for the two
  localized fppf topologies.
* `AlgebraicGeometry.BigFppfOver.isMorphismOfSites_baseChange`: base change defines a morphism
  of sites, its inverse image being the restriction along postcomposition, which is left exact.

## Implementation notes

The big fppf category over a scheme is a slice category and its topology is the localized
topology on the nose, so base change is Mathlib's `CategoryTheory.Over.pullback` and its
continuity is the general slice instance; no rewriting of topologies intervenes.  What makes the
slice construction applicable is that the site's chosen category of schemes is closed under
fibre products, which is Stacks 021U.

The direction of the underlying functor is opposite to the direction of the morphism of sites,
and it is base change rather than postcomposition that is wanted here: postcomposition
`CategoryTheory.Over.map` runs from `(Sch/X)` to `(Sch/Y)`, so as a continuous functor it gives
the morphism of sites in the other direction.  That the two describe the *same* morphism of
topoi is the content of Stacks 021W, formalized as
`AlgebraicGeometry.bigFppfMorphism`; the identification of the two pushforwards is what supplies
the left exact left adjoint here, since the inverse image of `f_big` is restriction along
postcomposition.

`CategoryTheory.Functor.IsMorphismOfSites` is not usable for these sites: it is stated for small
categories, with the objects of the two sites and the sections of their sheaves of sets in one
universe.  A big fppf category has its objects one universe above its morphisms, so the
universe-general class `IsMorphismOfSites` is used instead, at the universe of the sheaves of
sets on a big site.

The structure sheaf of a big fppf site over `S` is `T ↦ Γ(T, 𝒪_T)`.  The index scheme `S` enters
only through the category being indexed, so the two structure sheaves here are two instances of
one formula and the comparison needs no bridge between differently-presented presheaves of
rings: its component is literally the map on global functions along the projection.

This file supplies the pair `(f_big, f_big^♯)` of Stacks Definition 03AD, and no more.  The
pullback functor on sheaves of modules along it is available downstream, in
`StacksFrontier.AlgebraicGeometry.Descent.AssociatedModulePullbackBigFppf`: `SheafOfModules.pullback`
needs the pushforward of presheaves of modules to have a left adjoint, and neither Mathlib's
instance nor the generalization `Stacks.ModulePullback.isRightAdjoint_pushforward` provides it —
both require the *source* category to be small, which a big fppf category is not — but
`SheafOfModules.pushforward_isRightAdjoint_of_essentiallySmall` asks only for essential
smallness, which is `AlgebraicGeometry.BigFppfOver.essentiallySmall`.

## References

* [Stacks Project, Tag 070R](https://stacks.math.columbia.edu/tag/070R)
* [Stacks Project, Tag 03AD](https://stacks.math.columbia.edu/tag/03AD)
* [Stacks Project, Tag 00X1](https://stacks.math.columbia.edu/tag/00X1)
* [Stacks Project, Tag 021U](https://stacks.math.columbia.edu/tag/021U)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace CategoryTheory.Over

variable {C : Type*} [Category* C] [HasPullbacks C] {U V : C} (h : U ⟶ V)

/-- The projection `W ×_V U → W` out of the base change along `h : U ⟶ V` of an object `W / V`,
natural in `W / V`.  This is the counit of `CategoryTheory.Over.mapPullbackAdj` read in the base
category. -/
public noncomputable def pullbackForget :
    Over.pullback h ⋙ Over.forget U ⟶ Over.forget V where
  app W := pullback.fst W.hom h
  naturality _ _ _ := pullback.lift_fst _ _ _

/-- The component of `CategoryTheory.Over.pullbackForget h` at `W / V` is the first projection
`W ×_V U → W`. -/
@[simp]
public theorem pullbackForget_app (W : Over V) :
    (pullbackForget h).app W = pullback.fst W.hom h := rfl

end CategoryTheory.Over

namespace AlgebraicGeometry.BigFppfOver

variable (B : BigFppfSite.{u}) {X Y : Scheme.{u}} (hX : B.Contains X) (hY : B.Contains Y)
  (f : X ⟶ Y)

/-- A morphism of schemes, both contained in a big fppf site, as a morphism of the site's chosen
category of schemes. -/
@[implicit_reducible]
public def siteHom : B.obj hX ⟶ B.obj hY := ObjectProperty.homMk f

/-- The underlying morphism of schemes of `siteHom B hX hY f` is `f`. -/
@[simp]
public theorem siteHom_hom : (siteHom B hX hY f).hom = f := rfl

/-- The continuous functor giving the morphism of big fppf sites
`f_big : (Sch/X)_fppf → (Sch/Y)_fppf`: base change along `f`, sending `T / Y` to `X ×_Y T / X`.
-/
@[stacks 070R "part (1): the functor underlying the morphism of big fppf sites `f_big`"]
public noncomputable def baseChange : BigFppfOver B Y hY ⥤ BigFppfOver B X hX :=
  Over.pullback (siteHom B hX hY f)

/-- The underlying object of the base change of `T / Y` along `f` is the fibre product
`T ×_Y X`. -/
@[simp]
public theorem baseChange_obj_left (T : BigFppfOver B Y hY) :
    ((baseChange B hX hY f).obj T).left = pullback T.hom (siteHom B hX hY f) := rfl

/-- Base change along `f` is continuous for the two localized fppf topologies.  The big fppf
category over a scheme is a slice and its topology the localized one, and the site's chosen
category of schemes is closed under fibre products by Stacks 021U, so this is the general slice
instance. -/
public instance isContinuous_baseChange :
    (baseChange B hX hY f).IsContinuous (topology B Y hY) (topology B X hX) :=
  inferInstanceAs ((Over.pullback (siteHom B hX hY f)).IsContinuous
    (B.topology.over (B.obj hY)) (B.topology.over (B.obj hX)))

/-- Base change along `f` defines a morphism of big fppf sites
`f_big : (Sch/X)_fppf → (Sch/Y)_fppf` in the sense of Stacks 00X1: it is continuous, and the
pushforward it induces on sheaves of sets has a left exact left adjoint.

That left adjoint is the inverse image of `f_big`, which is restriction along postcomposition:
the pushforward along the cocontinuous functor `CategoryTheory.Over.map` agrees with the
pushforward along its continuous right adjoint `CategoryTheory.Over.pullback`, and restriction
along postcomposition is left exact. -/
@[stacks 070R "part (1): base change is a morphism of sites, so `f_big` is one"]
public instance isMorphismOfSites_baseChange :
    IsMorphismOfSites.{u + 1} (baseChange B hX hY f) (topology B Y hY) (topology B X hX) where
  hasExactLeftAdjoint :=
    ⟨(Over.map (siteHom B hX hY f)).sheafPullbackCocontinuous (Type (u + 1))
        (topology B X hX) (topology B Y hY),
      ⟨((Over.map (siteHom B hX hY f)).sheafAdjunctionPullbackCocontinuous (Type (u + 1))
          (topology B X hX) (topology B Y hY)).ofNatIsoRight
        ((Over.mapPullbackAdj (siteHom B hX hY f)).sheafPushforwardCocontinuousIso
          (Type (u + 1)))⟩,
      inferInstance⟩

/-- The projection `X ×_Y T → T` of schemes out of the base change of an object `T / Y` of the
big fppf category over `Y`, natural in `T / Y`. -/
public noncomputable def baseChangeProjection :
    baseChange B hX hY f ⋙ toScheme B X hX ⟶ toScheme B Y hY :=
  Functor.whiskerRight (Over.pullbackForget (siteHom B hX hY f)) B.inclusion

/-- The component of `baseChangeProjection B hX hY f` at `T / Y` is the first projection out of
the fibre product, viewed as a morphism of schemes. -/
@[simp]
public theorem baseChangeProjection_app (T : BigFppfOver B Y hY) :
    (baseChangeProjection B hX hY f).app T
      = B.inclusion.map (pullback.fst T.hom (siteHom B hX hY f)) := rfl

/-- The map of structure sheaves `f_big^♯ : 𝒪_Y → f_{big, *} 𝒪_X` which, together with the
morphism of sites `f_big`, makes `f_big` a morphism of ringed sites
`((Sch/X)_fppf, 𝒪_X) ⟶ ((Sch/Y)_fppf, 𝒪_Y)` as in Stacks Definition 03AD.

Its component at an object `T / Y` is the map on global functions induced by the projection
`X ×_Y T → T`, that is, the map `𝒪(T / Y) → 𝒪(X ×_Y T / X)` of the source. -/
@[stacks 070R "part (1): the structure-sheaf map `f_big^♯` of the morphism of ringed sites"]
public noncomputable def structureComparison :
    structureSheaf B Y hY ⟶
      ((baseChange B hX hY f).sheafPushforwardContinuous RingCat.{u}
        (topology B Y hY) (topology B X hX)).obj (structureSheaf B X hX) :=
  ⟨Functor.whiskerRight (NatTrans.op (baseChangeProjection B hX hY f))
    (Scheme.Γ ⋙ forget₂ CommRingCat RingCat.{u})⟩

/-- The component of `structureComparison B hX hY f` at `T / Y` is the map on global functions
induced by the first projection out of the fibre product. -/
@[simp]
public theorem structureComparison_hom_app (T : (BigFppfOver B Y hY)ᵒᵖ) :
    (structureComparison B hX hY f).hom.app T
      = (Scheme.Γ ⋙ forget₂ CommRingCat RingCat.{u}).map
          (B.inclusion.map (pullback.fst T.unop.hom (siteHom B hX hY f))).op := rfl

end AlgebraicGeometry.BigFppfOver

end
