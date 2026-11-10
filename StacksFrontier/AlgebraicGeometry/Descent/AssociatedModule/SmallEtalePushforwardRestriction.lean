module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleCounit
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleMorphismBaseChange

/-!
# The direct image of a morphism of schemes against the Zariski restriction

Let `a : X ⟶ Y` be a morphism of schemes of a big étale site and let `r` be the underlying
morphism of schemes.  Restriction along the inclusion of the small Zariski site,
`AlgebraicGeometry.SmallEtale.restrictModule`, is the right adjoint of the associated-module
functor of Stacks 03DU (4);
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtaleMorphismBaseChange.lean` shows
that the
*left* adjoints commute with base change, `(r^*𝓕)^a ≅ ε_a^*(𝓕^a)`.  This file is the statement
for the right adjoints:

the restriction to `Y_Zar` of `(ε_a)_* 𝓖` is `r_*` of the restriction of `𝓖` to `X_Zar`,

for an arbitrary `𝒪`-module `𝓖` on the small étale site of `X`.

## Main definitions

* `AlgebraicGeometry.SmallEtale.restrictModulePushforwardSquareIso`: **the square of direct
  images**, as an isomorphism of functors.
* `AlgebraicGeometry.SmallEtale.restrictModulePushforwardObjIso`: the same at one module.

## Implementation notes

Unlike the pullback square this one needs no mate argument and no adjointness: all four
functors round the square are `CategoryTheory.SheafOfModules.pushforward`s — restriction along
a continuous functor of sites — so the identification is `SheafOfModules.pushforwardComp` at
each corner and `SheafOfModules.pushforwardCongr₂` in the middle, over exactly the two halves
of the square that `SmallEtaleMorphismBaseChange` already proves:
`AlgebraicGeometry.SmallEtale.baseChangeOpensIso`, that base-changing an open `V ⊆ Y` along `r`
gives the preimage open `r⁻¹(V)`, and
`AlgebraicGeometry.SmallEtale.structureMap_comp_baseChangeOpensIso`, that the two composite
comparisons of structure sheaves agree.  `AlgebraicGeometry.Scheme.Modules.pushforward` of a
morphism of schemes is `SheafOfModules.pushforward` of its comparison of structure sheaves on
the nose, so the Zariski corner needs no transport either.

**What this does and does not give.**  Together with
`AlgebraicGeometry.Space.representedModulePushforwardSquareIso` and
`AlgebraicGeometry.Space.restrictToChartSchemeIdEtaleChartIso` this identifies the Zariski
restriction, at the identity chart, of the direct image of Stacks 03LU along a morphism of
*represented* algebraic spaces with the scheme-level direct image of the Zariski restriction —
one of the two inputs that the affine case of Stacks 0CU9 needs.  It does **not** by itself give
the other, which is quasi-coherence of the small étale direct image along an affine morphism:
this square says only that the Zariski restriction of that direct image is quasi-coherent, and
restriction to the small Zariski site does not reflect quasi-coherence.  That statement is
`AlgebraicGeometry.SmallEtale.isQuasicoherentOnSite_pushforward` in
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtaleAffinePushforward.lean`, which
consumes `AlgebraicGeometry.SmallEtale.isQuasicoherent_restrictModule_pushforward` below as one
of its two inputs, the other being the cartesian condition between affine objects.

No `@[stacks]` attribute is carried.  The tag the square belongs to, Stacks 070R (2), is about
the morphism of ringed sites `ε_a`, which is already built; this is a compatibility of the
functors formed from it, and the same choice is made for the pullback square in
`SmallEtaleMorphismBaseChange`.

## References

* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 070R](https://stacks.math.columbia.edu/tag/070R)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (a : X ⟶ Y)

/-- **The direct image along `ε_a` commutes with restriction to the small Zariski site.**  For
an `𝒪`-module `𝓖` on the small étale site of `X`, the restriction to `Y_Zar` of the direct image
of `𝓖` along the morphism of ringed sites `ε_a` of Stacks 070R (2) is the direct image along `r`
of the restriction of `𝓖` to `X_Zar`.

Both routes round the square are pushforwards of sheaves of modules, so this is
`CategoryTheory.SheafOfModules.pushforwardComp` at the two corners and
`CategoryTheory.SheafOfModules.pushforwardCongr₂` over
`AlgebraicGeometry.SmallEtale.baseChangeOpensIso` and
`AlgebraicGeometry.SmallEtale.structureMap_comp_baseChangeOpensIso` in the middle. -/
noncomputable def restrictModulePushforwardSquareIso :
    SheafOfModules.pushforward.{u} (smallEtaleStructureMapRing B a) ⋙
        restrictModule B Y.obj Y.property ≅
      restrictModule B X.obj X.property ⋙ Scheme.Modules.pushforward (schemeHom B a) :=
  SheafOfModules.pushforwardComp.{u} (structureMap B Y.obj Y.property)
      (smallEtaleStructureMapRing B a) ≪≫
    SheafOfModules.pushforwardCongr₂.{u}
      (SheafOfModules.comparisonComp (structureMap B Y.obj Y.property)
        (smallEtaleStructureMapRing B a))
      (baseChangeOpensIso B a) (structureMap_comp_baseChangeOpensIso B a) ≪≫
    (SheafOfModules.pushforwardComp.{u} (schemeHom B a).toRingCatSheafHom
      (structureMap B X.obj X.property)).symm

/-- **The direct image along `ε_a` commutes with restriction to the small Zariski site**, at one
module. -/
noncomputable def restrictModulePushforwardObjIso
    (𝓖 : SheafOfModules.{u} (structureSheaf B X.obj X.property)) :
    (restrictModule B Y.obj Y.property).obj
        ((SheafOfModules.pushforward.{u} (smallEtaleStructureMapRing B a)).obj 𝓖) ≅
      (Scheme.Modules.pushforward (schemeHom B a)).obj
        ((restrictModule B X.obj X.property).obj 𝓖) :=
  (restrictModulePushforwardSquareIso B a).app 𝓖

/-- The Zariski restriction of the direct image along `ε_a` of a quasi-coherent module is
quasi-coherent, as soon as `r` is an affine morphism.

This is `AlgebraicGeometry.SmallEtale.restrictModulePushforwardObjIso` together with
`AlgebraicGeometry.SmallEtale.isQuasicoherent_restrictModule` and the Zariski case of
Stacks 02KG.  It is *not* quasi-coherence of the direct image itself: restriction to the small
Zariski site does not reflect quasi-coherence. -/
theorem isQuasicoherent_restrictModule_pushforward
    (𝓖 : SheafOfModules.{u} (structureSheaf B X.obj X.property))
    (h𝓖 : SheafOfModules.IsQuasicoherentOnSite 𝓖) [IsAffineHom (schemeHom B a)] :
    SheafOfModules.IsQuasicoherent (R := Y.obj.ringCatSheaf)
      ((restrictModule B Y.obj Y.property).obj
        ((SheafOfModules.pushforward.{u} (smallEtaleStructureMapRing B a)).obj 𝓖)) := by
  have : SheafOfModules.IsQuasicoherent (R := X.obj.ringCatSheaf)
      ((restrictModule B X.obj X.property).obj 𝓖) :=
    isQuasicoherent_restrictModule B X.obj X.property 𝓖 h𝓖
  exact ObjectProperty.prop_of_iso (SheafOfModules.isQuasicoherent Y.obj.ringCatSheaf)
    (restrictModulePushforwardObjIso B a 𝓖).symm inferInstance

end AlgebraicGeometry.SmallEtale

end
