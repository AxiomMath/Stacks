module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SmallEtaleAssociatedModuleBaseChangeComposition
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleFinalSectionsTop
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleAssociatedModuleUnit

/-!
# The base change of Stacks 03LC (1), read on global sections

`AlgebraicGeometry.SmallEtale.associatedModuleBaseChangeIso` is the identification
`(r^*𝓕)^a ≅ ε_a^*(𝓕^a)` of **Stacks 03LC (1)**.  Nothing computes it: both sides are left
adjoints.  What pins it is
`AlgebraicGeometry.SmallEtale.conjugateEquiv_associatedModuleBaseChangeIso_inv`, which says its
inverse is conjugate, with respect to the two composite adjunctions round the square of ringed
sites, to the comparison `AlgebraicGeometry.SmallEtale.restrictModuleBaseChangeIso` of the two
composite *restrictions* — and that comparison is computed over the opens of the base, by
`AlgebraicGeometry.SmallEtale.restrictModuleBaseChangeIso_inv_app_app`.

This file reads that conjugacy on sections over the open `⊤`.  `CategoryTheory.unit_conjugateEquiv`
is the universal property of the conjugate, and the two composite units unfold by
`CategoryTheory.Adjunction.comp_unit_app`; what is left on the left-hand side is restriction
along the value at `⊤` of `AlgebraicGeometry.SmallEtale.baseChangeOpensIso`, which
`AlgebraicGeometry.SmallEtale.finalToBaseChangeFinal_comp_baseChangeOpensIso_inv_app_top`
identifies with the canonical arrow between the final objects, and what is left on the
right-hand side is the transpose of the identification across the adjunction of sheaves of
modules along `ε_a`, which
`SheafOfModules.homEquiv_sheafificationAdjunction_unit_comp_pullbackIso_inv_app` carries to the
presheaf level.

## Main results

* `AlgebraicGeometry.SmallEtale.associatedModuleBaseChangeIso_inv_unit_sections_top`: **the
  conjugacy pinning the base change of Stacks 03LC (1), read on sections over the open `⊤`.**

## References

* [Stacks Project, Tag 03LC](https://stacks.math.columbia.edu/tag/03LC)
* [Stacks Project, Tag 070S](https://stacks.math.columbia.edu/tag/070S)
* [Stacks Project, Tag 076T](https://stacks.math.columbia.edu/tag/076T)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (a : X ⟶ Y)

/-- **The conjugacy which pins the base change of Stacks 03LC (1), read on sections over the open
`⊤` of the base.**  Going down the left: the unit of pullback--pushforward for the morphism of
schemes below `a`, the unit of the associated-module adjunction of the small étale site of `X`,
and restriction along the value at `⊤` of
`AlgebraicGeometry.SmallEtale.baseChangeOpensIso`.  Going down the right: the unit of the
associated-module adjunction of the small étale site of `Y`, and the transpose across the
adjunction of sheaves of modules along `ε_a` of the inverse of the identification
`(r^*𝓕)^a ≅ ε_a^*(𝓕^a)`.

This is `CategoryTheory.unit_conjugateEquiv` at
`AlgebraicGeometry.SmallEtale.conjugateEquiv_associatedModuleBaseChangeIso_inv`, with the two
composite units unfolded and the comparison of the composite restrictions evaluated at `⊤` by
`AlgebraicGeometry.SmallEtale.restrictModuleBaseChangeIso_inv_app_app`. -/
public theorem associatedModuleBaseChangeIso_inv_unit_sections_top (𝓖 : Y.obj.Modules) :
    (Scheme.Modules.Hom.app
          ((Scheme.Modules.pullbackPushforwardAdjunction (schemeHom B a)).unit.app 𝓖) ⊤ ≫
        Scheme.Modules.Hom.app
          ((Scheme.Modules.pushforward (schemeHom B a)).map
            ((associatedModuleAdjunction B X.obj X.property).unit.app
              ((Scheme.Modules.pullback (schemeHom B a)).obj 𝓖))) ⊤) ≫
      ((associatedModule B X.obj X.property).obj
          ((Scheme.Modules.pullback (schemeHom B a)).obj 𝓖)).val.presheaf.map
        ((baseChangeOpensIso B a).inv.app ⊤).op =
    (Scheme.Modules.Hom.app
          ((associatedModuleAdjunction B Y.obj Y.property).unit.app 𝓖) ⊤ ≫
        Scheme.Modules.Hom.app
          ((restrictModule B Y.obj Y.property).map
            ((SheafOfModules.pullbackPushforwardAdjunction.{u}
                (smallEtaleStructureMapRing B a)).unit.app
              ((associatedModule B Y.obj Y.property).obj 𝓖))) ⊤) ≫
      Scheme.Modules.Hom.app
        ((restrictModule B Y.obj Y.property).map
          ((SheafOfModules.pushforward.{u} (smallEtaleStructureMapRing B a)).map
            ((associatedModuleBaseChangeIso B a).inv.app 𝓖))) ⊤ := by
  have key := CategoryTheory.unit_conjugateEquiv
    ((Scheme.Modules.pullbackPushforwardAdjunction (schemeHom B a)).comp
      (associatedModuleAdjunction B X.obj X.property))
    ((associatedModuleAdjunction B Y.obj Y.property).comp
      (SheafOfModules.pullbackPushforwardAdjunction.{u} (smallEtaleStructureMapRing B a)))
    (associatedModuleBaseChangeIso B a).inv 𝓖
  rw [conjugateEquiv_associatedModuleBaseChangeIso_inv] at key
  have key2 := congrArg (fun t => Scheme.Modules.Hom.app t (⊤ : Y.obj.Opens)) key
  simp only [Adjunction.comp_unit_app, Scheme.Modules.Hom.comp_app, Functor.comp_map,
    Functor.comp_obj, restrictModuleBaseChangeIso_inv_app_app] at key2
  exact key2

end AlgebraicGeometry.SmallEtale

end
