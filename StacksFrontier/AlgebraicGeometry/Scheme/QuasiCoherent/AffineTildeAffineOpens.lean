module

public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.AffineTilde

/-!
# Pullback of the associated sheaf between two affine opens

For a morphism of schemes `g : Y ⟶ X` and affine opens `U ⊆ X`, `V ⊆ Y` with `V ⊆ g⁻¹U`,
passing from `Γ(X, U)`-modules to `𝒪_U`-modules and pulling back along `V ⟶ U` is extension of
scalars to `Γ(Y, V)` followed by passage to `𝒪_V`-modules (Stacks tag 01I9 read through
`U ≅ Spec Γ(X, U)` and `V ≅ Spec Γ(Y, V)`).

## Main definitions

* `AlgebraicGeometry.restrictIsoSpecPullbackIsoOfLE`: restriction along `U ≅ Spec Γ(X, U)` then
  pullback along `V ⟶ U` is pullback along `Spec Γ(Y, V) ⟶ Spec Γ(X, U)` then restriction along
  `V ≅ Spec Γ(Y, V)`.
* `AlgebraicGeometry.restrictPullbackTildeIsoOfLE`: `AlgebraicGeometry.pullbackTildeIso`
  conjugated by those two identifications.
-/

@[expose] public noncomputable section

namespace AlgebraicGeometry

open AlgebraicGeometry CategoryTheory
open RingedSpaceModuleAdjunction
open scoped ChangeOfRings

universe u

section AffineOpens

variable {X Y : Scheme.{u}} (g : Y ⟶ X) {U : X.Opens} (hU : IsAffineOpen U) {V : Y.Opens}
  (hV : IsAffineOpen V) (hVU : V ≤ g ⁻¹ᵁ U)

/-- **Restriction along `U ≅ Spec Γ(X, U)` and pullback along `V ⟶ U`** for affine opens
`V ⊆ g⁻¹U` is pullback along `Spec Γ(Y, V) ⟶ Spec Γ(X, U)` and restriction along
`V ≅ Spec Γ(Y, V)`. Both restrictions are pullbacks along isomorphisms, and the two composites
of the square agree by `AlgebraicGeometry.Scheme.Opens.toSpecΓ_SpecMap_appLE`. -/
public noncomputable def restrictIsoSpecPullbackIsoOfLE :
    Scheme.Modules.restrictFunctor hU.isoSpec.hom ⋙ Scheme.Modules.pullback (g.resLE U V hVU) ≅
      Scheme.Modules.pullback (Spec.map (g.appLE U V hVU)) ⋙
        Scheme.Modules.restrictFunctor hV.isoSpec.hom :=
  Functor.isoWhiskerRight (Scheme.Modules.restrictFunctorIsoPullback hU.isoSpec.hom)
      (Scheme.Modules.pullback (g.resLE U V hVU)) ≪≫
    Scheme.Modules.pullbackComp (g.resLE U V hVU) hU.isoSpec.hom ≪≫
    Scheme.Modules.pullbackCongr (Scheme.Opens.toSpecΓ_SpecMap_appLE g U V hVU).symm ≪≫
    (Scheme.Modules.pullbackComp hV.isoSpec.hom (Spec.map (g.appLE U V hVU))).symm ≪≫
    Functor.isoWhiskerLeft (Scheme.Modules.pullback (Spec.map (g.appLE U V hVU)))
      (Scheme.Modules.restrictFunctorIsoPullback hV.isoSpec.hom).symm

/-- **Stacks tag 01I9 on two affine opens `V ⊆ g⁻¹U`.**  Passing from `Γ(X, U)`-modules to
`𝒪_U`-modules and pulling back along `V ⟶ U` is extension of scalars to `Γ(Y, V)` followed by
passage to `𝒪_V`-modules: `AlgebraicGeometry.pullbackTildeIso` conjugated by `U ≅ Spec Γ(X, U)`
and `V ≅ Spec Γ(Y, V)`. -/
public noncomputable def restrictPullbackTildeIsoOfLE :
    (tilde.functor Γ(X, U) ⋙ Scheme.Modules.restrictFunctor hU.isoSpec.hom) ⋙
        Scheme.Modules.pullback (g.resLE U V hVU) ≅
      ModuleCat.extendScalars (g.appLE U V hVU).hom ⋙
        (tilde.functor Γ(Y, V) ⋙ Scheme.Modules.restrictFunctor hV.isoSpec.hom) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (tilde.functor Γ(X, U)) (restrictIsoSpecPullbackIsoOfLE g hU hV hVU) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (pullbackTildeIso Γ(X, U) Γ(Y, V) (g.appLE U V hVU))
      (Scheme.Modules.restrictFunctor hV.isoSpec.hom) ≪≫
    Functor.associator _ _ _

end AffineOpens

end AlgebraicGeometry
