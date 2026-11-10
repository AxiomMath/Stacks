module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.PullbackUnivLE
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedZariskiEpsilonSquare

/-!
# `ε^*` for a represented algebraic space, with module sections in `Type (u + 1)`

Let `U` be an object of the big fppf site over a scheme `S : Scheme.{u}`, let `X₀` be its
underlying scheme and `X = h_U` the algebraic space it represents, and let
`ε : (X_étale, 𝒪_X) ⟶ (X_{0,Zar}, 𝒪_{X₀})` be the morphism of ringed topoi of Equation 75.4.0.1
(Stacks 08H7), `AlgebraicGeometry.Space.representedToSchemeZariskiRingedToposHom`.

The library's pullback of sheaves of modules along `ε` is the one of an abstract morphism of
ringed topoi, and it carries modules whose sections live in the universe `u` of the structure
sheaves.  The naive cotangent complex `NL_{X/Y}` of Stacks 0D0V
(`AlgebraicGeometry.Space.naiveCotangentComplex`) has its module sections in `Type (u + 1)`,
because the site-level construction puts them at the maximum of the ring universe and the object
universe of the site, and the objects of the small étale site of `X` form a `Type (u + 1)`.  So
the identification `NL_{X/Y} = ε^*NL_{X₀/Y₀}` of Stacks 0D0X needs `ε^*` with module sections in
`Type (u + 1)`.  This file provides it.

`ε` is presented by the continuous functor `representedEpsilonFunctor` reading a Zariski open of
`X₀` as an étale chart of `X`, so `ε` is a morphism of ringed topoi in the site-presented sense
of Stacks 01D3 (2), and its pullback is Mathlib's `SheafOfModules.pullback` along the structure
map.  Mathlib's construction of that pullback is universe-polymorphic; what it asks for is

* the presheaf-level pushforward to be a right adjoint, which
  `PresheafOfModules.isRightAdjoint_pushforward_of_univLE` supplies at independent universes,
  the Zariski site of `X₀` being small and both sites being locally small at `u + 1`;
* sheafification of abelian presheaves with sections in `Type (u + 1)` on the small étale site,
  which exists since `u + 1` contains both universes of that site.

## Main definitions

* `AlgebraicGeometry.Space.representedToZariskiRingedToposSiteHom`: `ε` as a morphism of ringed
  topoi presented by the continuous functor `representedEpsilonFunctor`, with the structure map
  of `AlgebraicGeometry.Space.representedToSchemeZariskiRingedToposHom` read through the
  identification of the abstract direct image with restriction along that functor.
* `AlgebraicGeometry.Space.representedEpsilonModulePullback`: **`ε^*` on sheaves of modules
  with sections in `Type (u + 1)`**.
* `AlgebraicGeometry.Space.representedEpsilonModulePushforward`: `ε_*` at the same universe.
* `AlgebraicGeometry.Space.representedEpsilonModuleAdjunction`: `ε^* ⊣ ε_*` (Stacks 03D7).

## Implementation notes

The continuity of `representedEpsilonFunctor`, `isContinuous_representedEpsilonFunctor`, is
stated at the `AlgebraicGeometry.RingedTopos.J` spelling of the two topologies, but instance
search does not find it where the category structure on the Zariski site is the one carried by
`AlgebraicGeometry.Scheme.zariskiRingedTopos` rather than `Preorder.smallCategory`; the two are
equal only after unfolding a `def`.  So the instance is passed positionally wherever such a
category structure is involved.  For the same reason the sheafification instances at
`AddCommGrpCat.{u + 1}` are given explicitly: the general ones are stated at
`AddCommGrpCat.{max u v}` and unification of `u + 1 =?= max (u + 1) ?v` is stuck.

## References

* [Stacks Project, Tag 0D0X](https://stacks.math.columbia.edu/tag/0D0X)
* [Stacks Project, Tag 08H7](https://stacks.math.columbia.edu/tag/08H7)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPullback

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (U : BigFppfOver B S hS)

/-- **`ε : (X_étale, 𝒪_X) ⟶ (X_{0,Zar}, 𝒪_{X₀})` presented by a continuous functor of sites.**
The functor is `AlgebraicGeometry.Space.representedEpsilonFunctor`, reading a Zariski open of
the scheme `X₀` underlying `U` as an étale chart of `X = h_U`, and the structure map is that of
`AlgebraicGeometry.Space.representedToSchemeZariskiRingedToposHom` (Stacks 08H7) followed by the
identification, which is the identity on sections, of the abstract direct image of sheaves of
commutative rings with restriction along the functor. -/
def representedToZariskiRingedToposSiteHom :
    RingedToposSiteHom (smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U))
      ((BigFppfOver.toScheme B S hS).obj U).zariskiRingedTopos where
  u := representedEpsilonFunctor B S hS U
  isContinuous := isContinuous_representedEpsilonFunctor B S hS U
  fSharp := (representedToSchemeZariskiRingedToposHom B S hS U).fSharp ≫
    (@restrictionCommRingIso _ _ _ _ ((BigFppfOver.toScheme B S hS).obj U).zariskiRingedTopos.J
      (smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U)).J _
      (representedEpsilonFunctor B S hS U) (isContinuous_representedEpsilonFunctor B S hS U)
      (smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U)).O).hom

/-- Sheafification of abelian presheaves with sections in `Type (u + 1)` on the small étale site
of `X = h_U`. -/
instance hasSheafify_representedSmallEtale_addCommGrpCat :
    HasSheafify (smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U)).J
      AddCommGrpCat.{u + 1} :=
  GrothendieckTopology.hasSheafify_addCommGrpCat.{u + 1, u, u + 1} _

/-- Weak equivalences of abelian presheaves with sections in `Type (u + 1)` on the small étale
site of `X = h_U` are the locally bijective morphisms. -/
instance wEqualsLocallyBijective_representedSmallEtale_addCommGrpCat :
    (smallEtaleRingedTopos B S hS
      (representedAlgebraicSpace B S hS U)).J.WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_addCommGrpCat.{u + 1, u + 1, u} _

/-- **The presheaf-level pushforward along `ε^♯` is a right adjoint at module sections in
`Type (u + 1)`**: the Zariski site of `X₀` is small, and both sites and both structure sheaves are
small at `u + 1`. -/
instance isRightAdjoint_representedEpsilonPresheafPushforward :
    (PresheafOfModules.pushforward.{u + 1}
      (representedToZariskiRingedToposSiteHom B S hS U).fSharpRing.hom).IsRightAdjoint :=
  have : Small.{u + 1} ((BigFppfOver.toScheme B S hS).obj U).Opens :=
    small_lift.{u, u, u + 1} _
  have : LocallySmall.{u + 1} ((BigFppfOver.toScheme B S hS).obj U).Opens :=
    locallySmall_max.{u + 1, u, u}
  have : LocallySmall.{u + 1} (SmallEtale B S hS (yoneda.obj U)) :=
    locallySmall_max.{u + 1, u, u + 1}
  PresheafOfModules.isRightAdjoint_pushforward_of_univLE.{u + 1}
    (F := (representedToZariskiRingedToposSiteHom B S hS U).u)
    (R := (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U)).O).obj)
    (S := (Stacks.SheafOfModules.Tensor.ringSheaf
      ((BigFppfOver.toScheme B S hS).obj U).zariskiRingedTopos.O).obj)
    (representedToZariskiRingedToposSiteHom B S hS U).fSharpPresheaf

/-- **`ε^*` on sheaves of modules with sections in `Type (u + 1)`**, for `ε` the morphism of
ringed topoi of Stacks 08H7 attached to the algebraic space `X = h_U` represented by `U`: the
pullback of Stacks 03D6 (2), the left adjoint of `ε_*`, which by Mathlib's construction is the
sheafification of `𝒪_X ⊗_{ε⁻¹𝒪_{X₀}} ε⁻¹(-)`. -/
def representedEpsilonModulePullback :
    SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
        ((BigFppfOver.toScheme B S hS).obj U).zariskiRingedTopos.O) ⥤
      SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U)).O) :=
  @SheafOfModules.pullback.{u + 1} _ _ _ _ _ _ _ _ _
    (representedToZariskiRingedToposSiteHom B S hS U).isContinuous
    (representedToZariskiRingedToposSiteHom B S hS U).fSharpRing _

/-- `ε_*` on sheaves of modules with sections in `Type (u + 1)`: restriction to the Zariski opens
of `X₀`, read over `𝒪_{X₀}` by restriction of scalars along `ε^♯`. -/
def representedEpsilonModulePushforward :
    SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U)).O) ⥤
      SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
        ((BigFppfOver.toScheme B S hS).obj U).zariskiRingedTopos.O) :=
  @SheafOfModules.pushforward.{u + 1} _ _ _ _ _ _ _ _ _
    (representedToZariskiRingedToposSiteHom B S hS U).isContinuous
    (representedToZariskiRingedToposSiteHom B S hS U).fSharpRing

/-- **Stacks 03D7 for `ε`, at module sections in `Type (u + 1)`**: `ε^* ⊣ ε_*`. -/
def representedEpsilonModuleAdjunction :
    representedEpsilonModulePullback B S hS U ⊣ representedEpsilonModulePushforward B S hS U :=
  @SheafOfModules.pullbackPushforwardAdjunction.{u + 1} _ _ _ _ _ _ _ _ _
    (representedToZariskiRingedToposSiteHom B S hS U).isContinuous
    (representedToZariskiRingedToposSiteHom B S hS U).fSharpRing _

/-- `ε_*` on sheaves of modules with sections in `Type (u + 1)` is an additive functor. -/
instance representedEpsilonModulePushforward_additive :
    (representedEpsilonModulePushforward B S hS U).Additive where
  map_add := by intros; rfl

/-- `ε^*` on sheaves of modules with sections in `Type (u + 1)` is an additive functor. -/
instance representedEpsilonModulePullback_additive :
    (representedEpsilonModulePullback B S hS U).Additive :=
  Adjunction.left_adjoint_additive (representedEpsilonModuleAdjunction B S hS U)

end AlgebraicGeometry.Space

end
