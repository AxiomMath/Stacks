module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleAssociatedModuleSections

/-!
# The associated module on the small étale site is the pullback-sections presheaf

Let `S` be a scheme contained in a big étale site and let `𝓕` be a quasi-coherent
`𝒪_S`-module. `AlgebraicGeometry.SmallEtale.associatedModuleIsoSections` (Stacks 070S on the
small étale site) identifies `𝓕^a` with the sheafification of the pullback-sections presheaf
of Stacks 03DS. On the small étale site that presheaf is already a sheaf, by
`AlgebraicGeometry.SmallEtale.isSheaf_sectionsPresheafOfModules`, so the sheafification unit is
an isomorphism and `𝓕^a` is the pullback-sections presheaf itself.

Hence the sections of `𝓕^a` over a small étale object `W / S` are `Γ(W, W^⁺𝓕)`, with the
restriction maps `AlgebraicGeometry.pullbackSectionsMap` of the presheaf of Stacks 03DS on all
of `Sch/S`. For a morphism `a : X ⟶ S` the projection `X ×_S W ⟶ W` is an arrow of `Sch/S`, so
compatibility with base change is functoriality of that presheaf.

## Main definitions

* `AlgebraicGeometry.SmallEtale.associatedModuleIsoSectionsPresheaf`: `𝓕^a` is the
  pullback-sections presheaf of Stacks 03DS, with no sheafification.
* `AlgebraicGeometry.SmallEtale.associatedModulePresheafIso`: the same on underlying abelian
  presheaves, where the right-hand side is the presheaf of Stacks 03DS restricted along
  `AlgebraicGeometry.SmallEtale.toOver`.

## Main results

* `AlgebraicGeometry.SmallEtale.associatedModulePresheafIso_hom_naturality`: the identification
  carries the restriction maps of `𝓕^a` to the restriction maps
  `AlgebraicGeometry.pullbackSectionsMap` of the presheaf of Stacks 03DS.

## Implementation notes

`CategoryTheory.PresheafOfModules.restrictScalars` along the identity is not the identity
functor. It is the right adjoint of `CategoryTheory.PresheafOfModules.sheafification`, so the
unit of `CategoryTheory.PresheafOfModules.sheafificationAdjunction` lands in it, and the source
of `AlgebraicGeometry.SmallEtale.associatedModuleIsoSectionsPresheaf` is spelled with it. It
changes no sections, so `AlgebraicGeometry.SmallEtale.associatedModulePresheafIso` is a statement
about the abelian presheaf underlying `𝓕^a` itself.

## References

* [Stacks Project, Tag 070S](https://stacks.math.columbia.edu/tag/070S)
* [Stacks Project, Tag 03DS](https://stacks.math.columbia.edu/tag/03DS)
* [Stacks Project, Tag 03DT](https://stacks.math.columbia.edu/tag/03DT)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 076T](https://stacks.math.columbia.edu/tag/076T)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- On the small étale site, `𝓕^a` is the pullback-sections presheaf of Stacks 03DS, with no
sheafification: Stacks 070S identifies `𝓕^a` with the sheafification of that presheaf, which is
already a sheaf, so the unit of the sheafification adjunction at it is an isomorphism. -/
public noncomputable def associatedModuleIsoSectionsPresheaf (F : S.Modules)
    [F.IsQuasicoherent] :
    (PresheafOfModules.restrictScalars (𝟙 (structureSheaf B S hS).obj)).obj
        ((SheafOfModules.forget (structureSheaf B S hS)).obj
          ((associatedModule B S hS).obj F)) ≅
      sectionsPresheafOfModules B S hS F :=
  (SheafOfModules.forget (structureSheaf B S hS) ⋙
      PresheafOfModules.restrictScalars (𝟙 (structureSheaf B S hS).obj)).mapIso
    (associatedModuleIsoSections B S hS F) ≪≫
    (@asIso _ _ _ _ _ (isIso_sheafificationAdjunction_unit_app B S hS
      (sectionsPresheafOfModules B S hS F)
      (isSheaf_sectionsPresheafOfModules B S hS F))).symm

/-- The abelian presheaf underlying `𝓕^a` is the presheaf of Stacks 03DS restricted along
`AlgebraicGeometry.SmallEtale.toOver`. -/
public noncomputable def associatedModulePresheafIso (F : S.Modules) [F.IsQuasicoherent] :
    ((associatedModule B S hS).obj F).val.presheaf ≅
      (toOver B S hS).op ⋙ quasiCoherentPresheafFunctor S F :=
  (PresheafOfModules.toPresheaf (structureSheaf B S hS).obj).mapIso
    (associatedModuleIsoSectionsPresheaf B S hS F)

/-- The identification of `𝓕^a` with the presheaf of Stacks 03DS carries restriction maps to
restriction maps: for an arrow `r` of the small étale site of `S`, restricting a section of
`𝓕^a` along `r` and then reading it as a pullback section is reading it first and then applying
`AlgebraicGeometry.pullbackSectionsMap` for the image of `r` in `Sch/S`. -/
public theorem associatedModulePresheafIso_hom_naturality (F : S.Modules) [F.IsQuasicoherent]
    {W W' : (SmallEtale B S hS)ᵒᵖ} (r : W ⟶ W') :
    ((associatedModule B S hS).obj F).val.presheaf.map r ≫
        (associatedModulePresheafIso B S hS F).hom.app W' =
      (associatedModulePresheafIso B S hS F).hom.app W ≫
        pullbackSectionsMap F ((toOver B S hS).map r.unop) :=
  (associatedModulePresheafIso B S hS F).hom.naturality r

end AlgebraicGeometry.SmallEtale

end
