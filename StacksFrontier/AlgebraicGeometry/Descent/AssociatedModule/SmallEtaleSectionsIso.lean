module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleAssociatedModuleSections
public import StacksFrontier.AlgebraicGeometry.Topologies.SmallSiteAssociatedModule

/-!
# The two constructions of `𝓕^a` on the small étale site agree

[Stacks, Tag 03DU] (4) defines the associated module `𝓕^a` of a quasi-coherent `𝒪_S`-module `𝓕`
by its sections: over an object `f : T → S` of the small étale site of `S` it is `Γ(T, f^*𝓕)`.
That is `AlgebraicGeometry.SmallEtale.associatedModuleOfSections`.
`AlgebraicGeometry.SmallEtale.associatedModule` is a second construction carrying the same name:
the pullback of sheaves of modules along the morphism of ringed sites
`id_{small, étale, Zar} : (S_étale, 𝒪) → (S_Zar, 𝒪_S)`.  [Stacks, Remark 03FH] (1) says the two
agree, and the implementation note of
`StacksFrontier.AlgebraicGeometry.Topologies.SmallSiteAssociatedModule` records that the tree held
both constructions side by side with nothing joining them.  This file joins them.

Two steps do it, and the first is in the tree already:

* [Stacks, Tag 070S] (2) on `S_étale`, which presents the pullback as the étale sheafification
  of the pullback-sections presheaf of [Stacks, Tag 03DS].  That is
  `AlgebraicGeometry.SmallEtale.associatedModuleIsoSections` of
  `StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleAssociatedModuleSections`,
  which this module imports and does not restate; it rests on
  `AlgebraicGeometry.SmallEtale.sectionsComparisonSheafifiesToIso`, proved in
  `StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleLocalBijectivity` from the
  two halves of the comparison's local bijectivity.
* [Stacks, Tag 03DT] on `S_étale`, which makes that sections presheaf a sheaf —
  `AlgebraicGeometry.SmallEtale.isSheaf_sectionsPresheafOfModules` — so the sheafification the
  first step leaves on the right can be removed.  This is the step added here.

## Main definitions

* `AlgebraicGeometry.SmallEtale.sheafificationIsoAssociatedModuleOfSections`: the étale
  sheafification of the pullback-sections presheaf of modules is the sections-defined `𝓕^a` of
  [Stacks, Tag 03DU] (4) itself.
* `AlgebraicGeometry.SmallEtale.associatedModuleIsoOfSections`: **[Stacks, Remark 03FH] (1) on
  the small étale site**, [Stacks, Tag 070S] (2) followed by that removal.
* `AlgebraicGeometry.SmallEtale.associatedModuleObjSectionsIso`: the sections of the pullback
  over an object `f : T → S` of `S_étale` are the global sections of `f^*𝓕`.

## Implementation notes

**The scope of the statements here.**  Every declaration below takes `𝓕` quasi-coherent, and
that hypothesis is [Stacks, Tag 03DU] (4)'s own: the construction `𝓕 ↦ 𝓕^a` whose two
descriptions Remark 03FH identifies is defined for a quasi-coherent `𝒪_S`-module, and so is the
sheaf condition [Stacks, Tag 03DT] that removes the sheafification.  The small Zariski
counterpart of this file,
`StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallZariskiSectionsIso`, carries the
same hypothesis for the same reason.

**This file registers no `stacks` attribute for [Stacks, Tag 070S].**  Clause (2) of 070S at
`τ = étale` is registered on
`AlgebraicGeometry.SmallEtale.associatedModuleIsoSections`, the step this file consumes, and on
`AlgebraicGeometry.SmallEtale.sectionsComparisonSheafifiesToIso`, where it is proved; nothing
below restates it.  `SmallZariskiSectionsIso` registers 070S nowhere either.

**What is new here, given that `SmallEtaleLocalBijectivity` already removes a sheafification.**
`AlgebraicGeometry.SmallEtale.associatedModuleIsoSectionsSheafOfModules'` of that module
identifies the pullback with `AlgebraicGeometry.SmallEtale.sectionsSheafOfModules'`, a sheaf
assembled there out of the sections presheaf and [Stacks, Tag 03DT].  Remark 03FH (1) asks for
the identification with the sheaf that [Stacks, Tag 03DU] (4) itself defines, which is
`AlgebraicGeometry.SmallEtale.associatedModuleOfSections` of
`StacksFrontier.AlgebraicGeometry.Topologies.SmallSiteAssociatedModule`, built by
`Stacks.EtaleCohomology.associatedModuleOfIsContinuous` from the continuity of
`AlgebraicGeometry.SmallEtale.toOver`.  Reaching that sheaf is what this file adds, and
`AlgebraicGeometry.SmallEtale.associatedModuleOfSections_val` is what lets it happen with no
transport.

## References

* [Stacks Project, Tag 03DS](https://stacks.math.columbia.edu/tag/03DS), the pullback-sections
  presheaf `(f : T → S) ↦ Γ(T, f^*𝓕)`.
* [Stacks Project, Tag 03DT](https://stacks.math.columbia.edu/tag/03DT), its sheaf condition.
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU), clause (4), the
  sections-defined `𝓕^a`.
* [Stacks Project, Tag 03FH](https://stacks.math.columbia.edu/tag/03FH), part (1).
* [Stacks Project, Tag 070S](https://stacks.math.columbia.edu/tag/070S), part (2).
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (F : S.Modules)
  [F.IsQuasicoherent]

/-- The presheaf of modules underlying the sections-defined `𝓕^a` of [Stacks, Tag 03DU] (4) on
`S_étale` is the pullback-sections presheaf of modules of [Stacks, Tag 03DS].

Both sides are `CategoryTheory.PresheafOfModules.ofPresheaf` on the restriction along
`AlgebraicGeometry.SmallEtale.toOver` of the presheaf of [Stacks, Tag 03DS], with the same
module structures, so this holds by `rfl`. -/
@[simp]
public theorem associatedModuleOfSections_val :
    (associatedModuleOfSections B S hS F).val = sectionsPresheafOfModules B S hS F :=
  rfl

/-- **No sheafification survives on the right of [Stacks, Tag 070S] (2) at `τ = étale`.**  The
étale sheafification of the pullback-sections presheaf of modules of a quasi-coherent `𝓕` is the
sections-defined `𝓕^a` of [Stacks, Tag 03DU] (4) itself.

The sections presheaf is a sheaf on `S_étale` already — that is [Stacks, Tag 03DT], in the form
`AlgebraicGeometry.SmallEtale.isSheaf_sectionsPresheafOfModules` — so the counit of
`CategoryTheory.PresheafOfModules.sheafificationAdjunction` at the sheaf
`AlgebraicGeometry.SmallEtale.associatedModuleOfSections` is the isomorphism wanted.  Its source
is the sheafification of the underlying presheaf of modules of that sheaf, which is the sections
presheaf on the nose by `AlgebraicGeometry.SmallEtale.associatedModuleOfSections_val`, so no
transport along that identification is needed. -/
public noncomputable def sheafificationIsoAssociatedModuleOfSections :
    (PresheafOfModules.sheafification.{u} (𝟙 (structureSheaf B S hS).obj)).obj
        (sectionsPresheafOfModules B S hS F) ≅
      associatedModuleOfSections B S hS F :=
  (asIso (PresheafOfModules.sheafificationAdjunction.{u}
    (𝟙 (structureSheaf B S hS).obj)).counit).app (associatedModuleOfSections B S hS F)

/-- **The two constructions of `𝓕^a` on the small étale site agree**: the pullback of `𝓕` along
the morphism of ringed sites `id_{small, étale, Zar} : (S_étale, 𝒪) → (S_Zar, 𝒪_S)`,
`AlgebraicGeometry.SmallEtale.associatedModule`, is the sheaf
`AlgebraicGeometry.SmallEtale.associatedModuleOfSections` whose sections over an object
`f : T → S` of `S_étale` are `Γ(T, f^*𝓕)`.

This is the content of [Stacks, Remark 03FH] (1) on the small étale site: [Stacks, Tag 03DU] (4)
defines `𝓕^a` by its sections, and the remark observes that it is the pullback along
`id_{small, étale, Zar}`.  It is [Stacks, Tag 070S] (2) in the object form
`AlgebraicGeometry.SmallEtale.associatedModuleIsoSections`, followed by the removal of the
sheafification, `AlgebraicGeometry.SmallEtale.sheafificationIsoAssociatedModuleOfSections`.

**This carries [Stacks, Remark 03FH] (1) for the second of the two morphisms that clause
offers**, `id_{small, étale, Zar} : (S_étale, 𝒪) → (S_Zar, 𝒪_S)`.  Its `τ = Zariski` counterpart
is `AlgebraicGeometry.SmallZariski.associatedModuleIsoOfSections`.  The first morphism of the
clause, `id_{τ, Zar} : ((Sch/S)_τ, 𝒪) → (S_Zar, 𝒪)`, is carried at all five `τ` by
`AlgebraicGeometry.BigFppfOver.baseAssociatedModuleIsoSectionsSheaf`
(`StacksFrontier/AlgebraicGeometry/Descent/QuasiCoherentTopologiesTwo/TopologyIndependence.lean`),
which identifies the pullback with the sections-defined `𝓕^a` of [Stacks, Tag 03DU] (3), the
big-site sheafification being removed by [Stacks, Tag 03DT] exactly as it is removed here;
`AlgebraicGeometry.BigFppfOver.baseAssociatedModuleIsoSections`
(`StacksFrontier/AlgebraicGeometry/Descent/SectionsPullbackComparison/Comparison.lean`) is its
[Stacks, Tag 070S] (1) half, before that removal.  The two morphisms together are the whole of
clause (1).

The quasi-coherence hypothesis is not an addition to 03FH: the construction `𝓕 ↦ 𝓕^a` whose two
descriptions the remark identifies is [Stacks, Tag 03DU] (4), which is stated for a
quasi-coherent `𝒪_S`-module. -/
@[stacks 03FH "part (1), for the morphism id_{small, étale, Zar} : (S_étale, 𝒪) → (S_Zar, 𝒪)"]
public noncomputable def associatedModuleIsoOfSections :
    (associatedModule B S hS).obj F ≅ associatedModuleOfSections B S hS F :=
  associatedModuleIsoSections B S hS F ≪≫
    sheafificationIsoAssociatedModuleOfSections B S hS F

/-- **The sections of `𝓕^a` on the small étale site**, read off the pullback: the sections of
the pullback of `𝓕` along `(S_étale, 𝒪) → (S_Zar, 𝒪_S)` over an object `f : T → S` of
`S_étale` are the global sections of `f^*𝓕`.

This is `AlgebraicGeometry.SmallEtale.associatedModuleIsoOfSections` evaluated at `T`, composed
with the defining equation
`AlgebraicGeometry.SmallEtale.associatedModuleOfSections_presheaf_obj`. -/
public noncomputable def associatedModuleObjSectionsIso (T : (SmallEtale B S hS)ᵒᵖ) :
    ((associatedModule B S hS).obj F).val.presheaf.obj T ≅
      AddCommGrpCat.of Γ((Scheme.Modules.pullback (toOver B S hS |>.obj T.unop).hom).obj F, ⊤) :=
  ((SheafOfModules.forget (structureSheaf B S hS) ⋙
    PresheafOfModules.toPresheaf (structureSheaf B S hS).obj ⋙
      (evaluation (SmallEtale B S hS)ᵒᵖ AddCommGrpCat.{u}).obj T).mapIso
        (associatedModuleIsoOfSections B S hS F))

end AlgebraicGeometry.SmallEtale

end
