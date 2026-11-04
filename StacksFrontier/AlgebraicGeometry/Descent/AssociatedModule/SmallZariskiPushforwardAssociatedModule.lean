module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallZariskiPushforwardRestriction

/-!
# The small Zariski direct image of an associated module

Let `f : T ⟶ S` be a morphism of schemes of a big Zariski site and let `𝓕` be an `𝒪_T`-module.
This file is the degree-zero comparison of Stacks 071N at `τ = Zariski`:

`f_{small, *} (𝓕^a) ≅ (f_* 𝓕)^a`,

where `𝓕 ↦ 𝓕^a` is the associated-module functor of Stacks 03DU (4) at `τ = Zariski`,
`AlgebraicGeometry.SmallZariski.associatedModule`, and `f_{small, *}` is the direct image along
the morphism of ringed sites `f_small` of Stacks 070R (2). Unlike its étale counterpart
`AlgebraicGeometry.SmallEtale.pushforwardAssociatedModuleIso`, it holds for an arbitrary morphism
and an arbitrary module, since the associated-module adjunction of the small Zariski site is an
adjoint equivalence.

## Main definitions

* `AlgebraicGeometry.SmallZariski.associatedModuleIsoInverse`: the associated-module functor of
  the small Zariski site is the inverse of the restriction to the opens of the space.
* `AlgebraicGeometry.SmallZariski.pushforwardAssociatedModuleIso`: the comparison
  `f_{small, *}(𝓕^a) ≅ (f_* 𝓕)^a`.

## Main results

* `AlgebraicGeometry.SmallZariski.isEquivalence_restrictModule` and
  `AlgebraicGeometry.SmallZariski.isEquivalence_associatedModule`: both functors of the
  associated-module adjunction of the small Zariski site are equivalences.
* `AlgebraicGeometry.SmallZariski.isIso_unit_associatedModuleAdjunction` and
  `AlgebraicGeometry.SmallZariski.isIso_counit_associatedModuleAdjunction`: that adjunction is an
  adjoint equivalence.

## Implementation notes

No `@[stacks]` attribute is carried: Stacks 071N is the statement for every degree of the
higher direct images, of which this is the degree-zero piece, and the tag belongs on the full
statement.

## References

* [Stacks Project, Tag 071N](https://stacks.math.columbia.edu/tag/071N)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 03FG](https://stacks.math.columbia.edu/tag/03FG)
* [Stacks Project, Tag 070R](https://stacks.math.columbia.edu/tag/070R)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry.SmallZariski

section Site

variable (B : BigZariskiSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Restriction to the opens of the space is an equivalence on the small Zariski site.** It is
the forward functor of `AlgebraicGeometry.smallZariskiModuleEquiv`, the comparison of Tag 03FG of
modules on the small Zariski site of `S` with modules on `S`. -/
public noncomputable instance isEquivalence_restrictModule :
    (restrictModule B S hS).IsEquivalence :=
  inferInstanceAs (smallZariskiModuleEquiv.{u, u} B S hS).functor.IsEquivalence

/-- **The associated-module functor of the small Zariski site is the inverse of restriction.** -/
public noncomputable def associatedModuleIsoInverse :
    associatedModule B S hS ≅ (restrictModule B S hS).inv :=
  (associatedModuleAdjunction B S hS).leftAdjointUniq
    (restrictModule B S hS).asEquivalence.symm.toAdjunction

/-- **The associated-module functor of the small Zariski site is an equivalence.** -/
public noncomputable instance isEquivalence_associatedModule :
    (associatedModule B S hS).IsEquivalence :=
  Functor.isEquivalence_of_iso (associatedModuleIsoInverse B S hS).symm

/-- **The unit `𝓕 ⟶ (𝓕^a)|_{S_Zar}` is an isomorphism at every `𝒪_S`-module**, with no
quasi-coherence hypothesis. -/
public instance isIso_unit_associatedModuleAdjunction (𝓕 : S.Modules) :
    IsIso ((associatedModuleAdjunction B S hS).unit.app 𝓕) :=
  (Adjunction.isIso_unit_app_iff_mem_essImage (associatedModuleAdjunction B S hS)).2
    (Functor.EssSurj.mem_essImage (F := restrictModule B S hS) 𝓕)

/-- **The counit `(𝓜|_{S_Zar})^a ⟶ 𝓜` is an isomorphism at every module on the small Zariski
site.** -/
public instance isIso_counit_associatedModuleAdjunction
    (𝓜 : SheafOfModules.{u} (structureSheaf B S hS)) :
    IsIso ((associatedModuleAdjunction B S hS).counit.app 𝓜) :=
  (Adjunction.isIso_counit_app_iff_mem_essImage (associatedModuleAdjunction B S hS)).2
    (Functor.EssSurj.mem_essImage (F := associatedModule B S hS) 𝓜)

end Site

variable (B : BigZariskiSite.{u}) {S T : B.Schemes} (f : T ⟶ S)

/-- **The direct image along `f_small` of the associated module is the associated module of the
direct image**, for an arbitrary morphism of schemes of a big Zariski site and an arbitrary
`𝒪_T`-module:

`f_{small, *} (𝓕^a) ≅ (f_* 𝓕)^a`.

This is the degree-zero comparison of Stacks 071N at `τ = Zariski`. -/
public noncomputable def pushforwardAssociatedModuleIso (𝓕 : T.1.Modules) :
    (SheafOfModules.pushforward.{u} (structureMapRing B f)).obj
        ((associatedModule B T.1 T.property).obj 𝓕) ≅
      (associatedModule B S.1 S.property).obj
        ((Scheme.Modules.pushforward (schemeHom B f)).obj 𝓕) :=
  (asIso ((associatedModuleAdjunction B S.1 S.property).counit.app
      ((SheafOfModules.pushforward.{u} (structureMapRing B f)).obj
        ((associatedModule B T.1 T.property).obj 𝓕)))).symm ≪≫
    (associatedModule B S.1 S.property).mapIso
      (restrictModulePushforwardObjIso B f ((associatedModule B T.1 T.property).obj 𝓕) ≪≫
        (Scheme.Modules.pushforward (schemeHom B f)).mapIso
          (asIso ((associatedModuleAdjunction B T.1 T.property).unit.app 𝓕)).symm)

end AlgebraicGeometry.SmallZariski

end
