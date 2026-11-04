module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleRingedSite
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.UnitQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Descent.FpqcHomSheafRefinement
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SiteAxioms
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.SieveToFamily
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The sections description of the associated module on the small étale site

`AlgebraicGeometry.SmallEtale.associatedModule` is Stacks Definition 03DU (4) at `τ = étale`:
the associated-module functor `𝓕 ↦ 𝓕^a` of the small étale site of a scheme `S`, built as the
pullback of sheaves of modules along the morphism of ringed sites `(S_étale, 𝒪) → (S_Zar, 𝒪_S)`.
Clause (4) does not *define* it that way; it names it by its sections,
`(f : T → S) ↦ Γ(T, f^*𝓕)`.  This file supplies the sections side of that identification on the
small étale site, and the comparison morphism between the two.

The sections presheaf is the site-generic
`AlgebraicGeometry.quasiCoherentSectionsPresheafOfModules` read at the canonical functor
`AlgebraicGeometry.SmallEtale.toOver` from the small étale site to the schemes over `S`.  That
is possible because `AlgebraicGeometry.SmallEtale.structureSheaf` is *literally*
`Stacks.Sites.structurePresheaf S (SmallEtale.toOver B S hS)`, so no coercion intervenes: the
presheaf of modules of Stacks 03DS already lives over the structure sheaf of the small étale
site.  **That presheaf is a sheaf**, which is Stacks 03DT on the small étale site, and here it
is unconditional: the fpqc sheaf condition for the pullback-sections presheaf is transported to
the small étale site by `AlgebraicGeometry.SmallEtale.isSheaf_toOver_op_comp`, and the descent
input it needs is supplied by
`AlgebraicGeometry.fpqcDescentOfQuasicoherentHoms`.

The comparison morphism is the transpose, across the pullback--pushforward adjunction of
presheaves of modules, of the map which pulls a section of `𝓕` over an open `U` of `S` back to
the open subscheme `U`.  Stacks 070S part (2) is the assertion that this comparison is locally
bijective for the small étale topology; **that assertion is not proved here.**  It is proved in
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtaleLocalBijectivity.lean`, which
imports this file, as the unconditional
`AlgebraicGeometry.SmallEtale.sectionsComparisonSheafifiesToIso`.  What is proved here is
everything on either side of it: the comparison itself, the fact that pulling sections back is an
isomorphism, the sheaf condition, and — taking 070S (2) as a hypothesis — the conclusion it is
wanted for, namely that the unit of
`AlgebraicGeometry.SmallEtale.associatedModuleAdjunction` is an isomorphism at a quasi-coherent
module.  That last statement is the small étale half of Stacks 0GN7.

## Main definitions

* `AlgebraicGeometry.SmallEtale.sectionsPresheafOfModules`: **Stacks 03DS on the small étale
  site**, the presheaf of modules `T ↦ Γ(T, T.hom^*𝓕)` over the structure sheaf.
* `AlgebraicGeometry.SmallEtale.sectionsUnitApp` and
  `AlgebraicGeometry.SmallEtale.sectionsUnit`: pulling a section of `𝓕` over an open of `S` back
  to the open subscheme, as a map of modules of sections and as a morphism out of `𝓕`.
* `AlgebraicGeometry.SmallEtale.sectionsComparison`: **the comparison of Stacks 070S (2)**, the
  transpose of `sectionsUnit` across the pullback--pushforward adjunction.
* `AlgebraicGeometry.SmallEtale.associatedModuleSheafificationIso`: the associated-module
  functor of the small étale site, presented as the sheafification of the pullback of
  *presheaves* of modules.

## Main results

* `AlgebraicGeometry.SmallEtale.coverPreserving_toOver`: the canonical functor from the small
  étale site of `S` to the schemes over `S` is cover preserving into the localized étale
  topology.
* `AlgebraicGeometry.SmallEtale.isIso_sectionsUnit`: pulling sections back is an isomorphism.
* `AlgebraicGeometry.SmallEtale.isIso_sheafificationAdjunction_unit_app`: the sheafification map
  of a presheaf of modules on the small étale site which is already a sheaf is an isomorphism.
* `AlgebraicGeometry.SmallEtale.isSheaf_sectionsPresheafOfModules`: **Stacks 03DT on the small
  étale site**, unconditionally — the pullback-sections presheaf of modules of a quasi-coherent
  module is a sheaf on the small étale site of `S`.
* `AlgebraicGeometry.SmallEtale.isIso_unit_app_of_isIso_sheafification_sectionsComparison`: the
  unit of the associated-module adjunction of the small étale site is an isomorphism at a
  quasi-coherent module, granted that the sheafification of the comparison is an isomorphism.
  The hypothesis is Stacks 070S (2); the conclusion is what Stacks 0GN7 needs on the small site.

## Implementation notes

Every declaration here is a port of its big-fppf counterpart in
`StacksFrontier.AlgebraicGeometry.Descent.SectionsPullbackComparison.Comparison` and
`StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.UnitQuasicoherent`, with
`AlgebraicGeometry.BigFppfOver.structureMap` replaced by
`AlgebraicGeometry.SmallEtale.structureMap` and
`AlgebraicGeometry.BigFppfOver.opensToBig` by
`AlgebraicGeometry.SmallEtale.opensToSmallEtale`.  The proof shapes are unchanged, including the
three transparency subtleties that the fppf file documents: the middle object of the cancelled
composite has two definitionally equal spellings, so the cancellation is done through
`CategoryTheory.isIso_left_of_comp_eq_comp` with the objects as variables, and the
identification `hforget` of the two spellings of the unit holds by `rfl` here as it does there.

No new functor to the schemes over `S` is introduced.  `AlgebraicGeometry.SmallEtale.toOver`
already exists, with exactly the body a port would have given it, and so do
`AlgebraicGeometry.SmallEtale.compatiblePreserving_toOver` and the transport of an abelian sheaf
`AlgebraicGeometry.SmallEtale.isSheaf_toOver_op_comp`; the sheaf condition is therefore obtained
from the existing transport rather than from a second copy of it.

`AlgebraicGeometry.SmallEtale.coverPreserving_toOver` is the one argument with no fppf model.
For `AlgebraicGeometry.BigFppfOver` the source topology is a localization, so a covering sieve
can be exhibited in the ambient category and transported by
`CategoryTheory.GrothendieckTopology.mem_over_iff` on *both* sides.  The small étale site is not
a localization, and its covering sieves are only known to *contain* a covering family; the route
is therefore to extract that family with `_root_.exists_isCovering_sieve₀_le` from
`AlgebraicGeometry.SmallEtale.isSite`, push it forward (it is an étale covering of schemes), and
enlarge.  `CategoryTheory.GrothendieckTopology.mem_over_iff` is used on the target side only.

**Nothing in this file is tagged.**  `sectionsComparison` and the unit statement carry 070S (2)
as a hypothesis or are not a covering set for any tag, and the two sheafification lemmas are
infrastructure.  The one exception to flag is
`AlgebraicGeometry.SmallEtale.isSheaf_sectionsPresheafOfModules`, which is Stacks 03DT on the
small étale site with no hypothesis at all; whether it, together with
`AlgebraicGeometry.SmallEtale.sectionsPresheafOfModules` for Stacks 03DS, should carry a
`stacks` attribute is left to the maintainer, and no attribute is placed here.

## References

* [Stacks Project, Tag 03DS](https://stacks.math.columbia.edu/tag/03DS)
* [Stacks Project, Tag 03DT](https://stacks.math.columbia.edu/tag/03DT)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 06VE](https://stacks.math.columbia.edu/tag/06VE)
* [Stacks Project, Tag 070S](https://stacks.math.columbia.edu/tag/070S)
* [Stacks Project, Tag 0GN7](https://stacks.math.columbia.edu/tag/0GN7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The canonical functor to the schemes over `S` is cover preserving -/

/-- **The canonical functor from the small étale site of `S` to the schemes over `S` is cover
preserving** from the small étale topology to the localized étale topology.

Unlike its big-site counterpart `AlgebraicGeometry.BigFppfOver.coverPreserving_toOver` this
cannot read the source side through
`CategoryTheory.GrothendieckTopology.mem_over_iff`: the small étale site is a full subcategory
cut out by an object property, not a localization.  Instead a covering sieve is shown to contain
the sieve generated by a covering *family*, that family is an étale covering of schemes, and the
sieve it generates downstairs is enlarged to the pushforward of the original sieve. -/
public theorem coverPreserving_toOver :
    CoverPreserving (topology B S hS) (Scheme.etaleTopology.{u}.over S)
      (toOver B S hS) := by
  refine ⟨fun {X R} hR => ?_⟩
  obtain ⟨E, hE, hER⟩ :=
    _root_.exists_isCovering_sieve₀_le (SmallEtale.isSite B S hS) (fun _ _ => Iff.rfl) hR
  have hgen : E.sieve₀ = Sieve.generate E.presieve₀ := rfl
  have hcov : Sieve.functorPushforward (toScheme B S hS) E.sieve₀ ∈
      Scheme.etaleTopology ((toScheme B S hS).obj X) := by
    rw [hgen, ← Sieve.generate_map_eq_functorPushforward, ← PreZeroHypercover.presieve₀_map]
    exact Precoverage.generate_mem_toGrothendieck hE.1
  have key : Sieve.overEquiv ((toOver B S hS).obj X)
        (R.functorPushforward (toOver B S hS)) =
      R.functorPushforward (toScheme B S hS) :=
    (Sieve.functorPushforward_comp (toOver B S hS) (Over.forget S) R).symm
  rw [GrothendieckTopology.mem_over_iff, key]
  exact Scheme.etaleTopology.superset_covering
    (Sieve.functorPushforward_monotone (toScheme B S hS) X hER) hcov

/-! ### The sections presheaf of modules -/

/-- **Stacks 03DS on the small étale site.**  For a quasi-coherent module `F` on `S`, the
presheaf on the small étale site of `S` sending an object `T ⟶ S` to `Γ(T, T.hom^*F)`, as a
presheaf of modules over the structure sheaf of that site.

This is the sections description that Stacks Definition 03DU (4) uses to name the
associated-module functor `AlgebraicGeometry.SmallEtale.associatedModule`. -/
public noncomputable def sectionsPresheafOfModules (F : S.Modules) [F.IsQuasicoherent] :
    PresheafOfModules.{u} (structureSheaf B S hS).obj :=
  quasiCoherentSectionsPresheafOfModules S F (toOver B S hS)

/-- The presheaf of abelian groups underlying
`AlgebraicGeometry.SmallEtale.sectionsPresheafOfModules` is the presheaf of Stacks 03DS,
restricted to the small étale site. -/
@[simp]
public theorem sectionsPresheafOfModules_presheaf (F : S.Modules) [F.IsQuasicoherent] :
    (sectionsPresheafOfModules B S hS F).presheaf =
      (toOver B S hS).op ⋙ quasiCoherentPresheafFunctor S F :=
  rfl

/-! ### Pulling sections back -/

/-- Pulling a section of `F` over an open `U` of `S` back to the open subscheme `U`, as a map
of sections over `U`.  This is the component of
`AlgebraicGeometry.SmallEtale.sectionsUnit`. -/
public noncomputable def sectionsUnitApp (F : S.Modules) [F.IsQuasicoherent]
    (U : (S.Opens)ᵒᵖ) :
    ((SheafOfModules.forget S.ringCatSheaf).obj F).obj U ⟶
      ((PresheafOfModules.pushforward.{u} (structureMap B S hS).hom).obj
        (sectionsPresheafOfModules B S hS F)).obj U :=
  ModuleCat.homEquiv.symm {
    toFun := fun a =>
      pullbackSectionHom U.unop.ι F U.unop ⊤ (Scheme.Opens.top_le_ι_preimage le_rfl) a
    map_add' := fun a b => map_add _ a b
    map_smul' := fun r a => by
      refine (pullbackSectionHom_smul U.unop.ι F U.unop ⊤
        (Scheme.Opens.top_le_ι_preimage le_rfl) r a).trans ?_
      exact congrArg
        (fun s : Γ(U.unop.toScheme, ⊤) => s • pullbackSectionHom U.unop.ι F U.unop ⊤
          (Scheme.Opens.top_le_ι_preimage le_rfl) a)
        (congrArg (fun g : Γ(S, U.unop) ⟶ Γ(U.unop, ⊤) => ConcreteCategory.hom g r)
          (Scheme.Opens.ι_appLE_top U.unop (Scheme.Opens.top_le_ι_preimage le_rfl))) }

/-- The value of `AlgebraicGeometry.SmallEtale.sectionsUnitApp` on a section is its pullback to
the open subscheme. -/
@[simp]
public theorem sectionsUnitApp_apply (F : S.Modules) [F.IsQuasicoherent] (U : (S.Opens)ᵒᵖ)
    (a : ((SheafOfModules.forget S.ringCatSheaf).obj F).obj U) :
    sectionsUnitApp B S hS F U a =
      pullbackSectionHom U.unop.ι F U.unop ⊤ (Scheme.Opens.top_le_ι_preimage le_rfl) a :=
  rfl

/-- **Pulling sections back, as a morphism out of `F`.**  A section of `F` over an open `U` of
`S` pulls back to a section of `U.ι^*F` over all of the open subscheme `U`, and this is natural
in `U`: it is a morphism from `F` to the restriction, along the inclusion of the small Zariski
site of `S`, of the pullback-sections presheaf of modules of the small étale site. -/
public noncomputable def sectionsUnit (F : S.Modules) [F.IsQuasicoherent] :
    (SheafOfModules.forget S.ringCatSheaf).obj F ⟶
      (PresheafOfModules.pushforward.{u} (structureMap B S hS).hom).obj
        (sectionsPresheafOfModules B S hS F) where
  app U := sectionsUnitApp B S hS F U
  naturality {U V} h := by
    ext a
    have hUV : V.unop ≤ U.unop := leOfHom h.unop
    refine Eq.trans (pullbackSectionHom_map (Scheme.Opens.ι V.unop) F U.unop V.unop hUV ⊤
      (Scheme.Opens.top_le_ι_preimage le_rfl) (Scheme.Opens.top_le_ι_preimage hUV) a) ?_
    exact (pullbackSectionsMap_pullbackSectionHom F
      ((toOver B S hS).map ((opensToSmallEtale B S hS).map h.unop))
      U.unop (Scheme.Opens.top_le_ι_preimage le_rfl)
      (Scheme.Opens.top_le_ι_preimage hUV) a).symm

/-- **Pulling sections back is an isomorphism.**  The morphism
`AlgebraicGeometry.SmallEtale.sectionsUnit` from `F` to the restriction, along the inclusion of
the small Zariski site of `S`, of the pullback-sections presheaf is an isomorphism: its
component at an open `U` is the map of `AlgebraicGeometry.isIso_pullbackSectionHom_ι`, which is
a statement about an arbitrary module on an arbitrary scheme and sees no site. -/
public theorem isIso_sectionsUnit (F : S.Modules) [F.IsQuasicoherent] :
    IsIso (sectionsUnit B S hS F) := by
  rw [← isIso_iff_of_reflects_iso _ (PresheafOfModules.toPresheaf S.ringCatSheaf.obj),
    NatTrans.isIso_iff_isIso_app]
  intro U
  exact isIso_pullbackSectionHom_ι F U.unop

/-! ### The comparison morphism -/

/-- **The comparison of Stacks 070S (2).**  The canonical morphism from the pullback of
presheaves of modules along the structure-sheaf comparison of the small étale site of `S` to the
pullback-sections presheaf of Stacks 03DS: the transpose, under
`CategoryTheory.PresheafOfModules.pullbackPushforwardAdjunction`, of the map which pulls a
section of `F` over an open `U` of `S` back to the open subscheme `U`.

Stacks Lemma 070S part (2) is the statement that this morphism is locally bijective for the
small étale topology.  That statement is not proved in this file; granted it,
`CategoryTheory.PresheafOfModules.sheafification` turns the comparison into an isomorphism and
`AlgebraicGeometry.SmallEtale.associatedModuleSheafificationIso` identifies the
associated-module functor of the small étale site with the sheafification of the sections
description. -/
public noncomputable def sectionsComparison (F : S.Modules) [F.IsQuasicoherent] :
    (PresheafOfModules.pullback.{u} (structureMap B S hS).hom).obj
        ((SheafOfModules.forget S.ringCatSheaf).obj F) ⟶
      sectionsPresheafOfModules B S hS F :=
  ((PresheafOfModules.pullbackPushforwardAdjunction.{u} (structureMap B S hS).hom).homEquiv
    _ _).symm (sectionsUnit B S hS F)

/-- **The comparison is determined by pulling sections back.**  Transposing
`AlgebraicGeometry.SmallEtale.sectionsComparison` back across the adjunction returns the map
which pulls a section of `F` over an open `U` of `S` back to the open subscheme `U`.  This is
the only property of the comparison that is used below. -/
public theorem unit_comp_map_sectionsComparison (F : S.Modules) [F.IsQuasicoherent] :
    (PresheafOfModules.pullbackPushforwardAdjunction.{u} (structureMap B S hS).hom).unit.app
          ((SheafOfModules.forget S.ringCatSheaf).obj F) ≫
        (PresheafOfModules.pushforward.{u} (structureMap B S hS).hom).map
          (sectionsComparison B S hS F) =
      sectionsUnit B S hS F :=
  ((PresheafOfModules.pullbackPushforwardAdjunction.{u}
      (structureMap B S hS).hom).homEquiv_unit _ _ _).symm.trans (Equiv.apply_symm_apply _ _)

/-! ### Sheafification on the small étale site -/

/-- The identity of the underlying presheaf of rings of the structure sheaf of the small étale
site is locally injective, being injective in each component. -/
public instance isLocallyInjective_id_structureSheaf :
    Presheaf.IsLocallyInjective (topology B S hS) (𝟙 (structureSheaf B S hS).obj) :=
  Presheaf.isLocallyInjective_of_injective _ _ fun _ _ _ h => by exact h

/-- The identity of the underlying presheaf of rings of the structure sheaf of the small étale
site is locally surjective, being an isomorphism. -/
public instance isLocallySurjective_id_structureSheaf :
    Presheaf.IsLocallySurjective (topology B S hS) (𝟙 (structureSheaf B S hS).obj) :=
  inferInstance

/-- The sheafification map of a presheaf of modules on the small étale site of `S` which is
already a sheaf there is an isomorphism.  The underlying map of presheaves of abelian groups is
`CategoryTheory.toSheafify`, and `CategoryTheory.PresheafOfModules.toPresheaf` reflects
isomorphisms. -/
public theorem isIso_sheafificationAdjunction_unit_app
    (Q : PresheafOfModules.{u} (structureSheaf B S hS).obj)
    (hQ : Presheaf.IsSheaf (topology B S hS) Q.presheaf) :
    IsIso ((PresheafOfModules.sheafificationAdjunction
      (𝟙 (structureSheaf B S hS).obj)).unit.app Q) := by
  have h1 : IsIso (CategoryTheory.toSheafify (topology B S hS) Q.presheaf) :=
    CategoryTheory.isIso_toSheafify _ hQ
  rw [← isIso_iff_of_reflects_iso _
      (PresheafOfModules.toPresheaf (structureSheaf B S hS).obj),
    PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app]
  exact h1

/-! ### The sheaf condition, and the unit of the associated-module adjunction -/

/-- **Stacks 03DT on the small étale site of `S`.**  The pullback-sections presheaf of modules
of a quasi-coherent module `F` on `S` is a sheaf on the small étale site of `S`.

The fpqc sheaf condition on the schemes over `S` is `AlgebraicGeometry.isSheaf_presheafHom` read
through `AlgebraicGeometry.quasiCoherentPresheafIsoPresheafHom`, and it is carried to the small
étale site by `AlgebraicGeometry.SmallEtale.isSheaf_toOver_op_comp`.  The descent hypothesis
that the fpqc statement carries is discharged by
`AlgebraicGeometry.fpqcDescentOfQuasicoherentHoms`, so this statement is unconditional. -/
@[sga "4 VII 2.1" "Clause c), special case"]
public theorem isSheaf_sectionsPresheafOfModules (F : S.Modules) [F.IsQuasicoherent] :
    Presheaf.IsSheaf (topology B S hS) (sectionsPresheafOfModules B S hS F).presheaf := by
  have htype : Presheaf.IsSheaf (Scheme.fpqcTopology.{u}.over S)
      (quasiCoherentPresheafFunctor S F ⋙ CategoryTheory.forget AddCommGrpCat) :=
    (Presheaf.isSheaf_of_iso_iff (quasiCoherentPresheafIsoPresheafHom F)).mpr
      (isSheaf_presheafHom fpqcDescentOfQuasicoherentHoms (Scheme.unitModule S) F)
  rw [sectionsPresheafOfModules_presheaf]
  exact isSheaf_toOver_op_comp B S hS (quasiCoherentPresheafFunctor S F)
    ((isSheaf_iff_isSheaf_of_type _ _).1 htype)

/-- The associated-module functor of the small étale site of `S` is the sheafification of the
pullback of *presheaves* of modules along the structure-sheaf comparison.  Both functors are
left adjoint to restriction along the inclusion of the small Zariski site.

This is `CategoryTheory.SheafOfModules.pullbackIso` read at
`AlgebraicGeometry.SmallEtale.structureMap`, mirroring
`AlgebraicGeometry.BigFppfOver.associatedModuleSheafificationIso`. -/
public noncomputable def associatedModuleSheafificationIso :
    associatedModule B S hS ≅
      SheafOfModules.forget S.ringCatSheaf ⋙
        PresheafOfModules.pullback.{u} (structureMap B S hS).hom ⋙
          PresheafOfModules.sheafification (𝟙 (structureSheaf B S hS).obj) :=
  SheafOfModules.pullbackIso.{u} (structureMap B S hS)

/-- **The unit of the associated-module adjunction of the small étale site of `S` is an
isomorphism at a quasi-coherent module**, granted that the sheafification of the comparison of
Stacks 070S (2) is an isomorphism.  The hypothesis is exactly 070S (2) — local bijectivity of
`AlgebraicGeometry.SmallEtale.sectionsComparison` — and nothing else is assumed: the sheaf
condition the fppf form of this statement carries as a hypothesis is
`AlgebraicGeometry.SmallEtale.isSheaf_sectionsPresheafOfModules` here.  The conclusion is what
Stacks 0GN7 needs on the small étale site.

`CategoryTheory.SheafOfModules.pullbackIso` presents the associated-module functor as the
sheafification of the presheaf-level pullback, and
`CategoryTheory.Adjunction.unit_leftAdjointUniq_hom_app` therefore reduces the claim to the unit
of `CategoryTheory.SheafOfModules.PullbackConstruction.adjunction`, which the forgetful functor
carries to the transpose of the sheafification map.  By
`AlgebraicGeometry.SmallEtale.unit_comp_map_sectionsComparison` and
`CategoryTheory.Adjunction.unit_comp_map_unit_comp` that transpose agrees, after composing with
the sheafification of the comparison, with
`AlgebraicGeometry.SmallEtale.sectionsUnit` followed by the sheafification map of the
pullback-sections presheaf; both of those are isomorphisms. -/
public theorem isIso_unit_app_of_isIso_sheafification_sectionsComparison
    (F : S.Modules) [F.IsQuasicoherent]
    (hc : IsIso ((PresheafOfModules.sheafification.{u}
      (𝟙 (structureSheaf B S hS).obj)).map (sectionsComparison B S hS F))) :
    IsIso ((associatedModuleAdjunction B S hS).unit.app F) := by
  have hB : IsIso ((PresheafOfModules.sheafificationAdjunction
      (𝟙 (structureSheaf B S hS).obj)).unit.app (sectionsPresheafOfModules B S hS F)) :=
    isIso_sheafificationAdjunction_unit_app B S hS _
      (isSheaf_sectionsPresheafOfModules B S hS F)
  have hA : IsIso (sectionsUnit B S hS F) := isIso_sectionsUnit B S hS F
  have hc2 : IsIso ((PresheafOfModules.pushforward.{u} (structureMap B S hS).hom).map
      ((SheafOfModules.forget (structureSheaf B S hS) ⋙
          PresheafOfModules.restrictScalars (𝟙 (structureSheaf B S hS).obj)).map
        ((PresheafOfModules.sheafification.{u} (𝟙 (structureSheaf B S hS).obj)).map
            (sectionsComparison B S hS F)))) :=
    inferInstance
  have hB2 : IsIso ((PresheafOfModules.pushforward.{u} (structureMap B S hS).hom).map
      ((PresheafOfModules.sheafificationAdjunction
          (𝟙 (structureSheaf B S hS).obj)).unit.app
        (sectionsPresheafOfModules B S hS F))) := inferInstance
  have hkey := Adjunction.unit_comp_map_unit_comp
      (PresheafOfModules.pullbackPushforwardAdjunction.{u} (structureMap B S hS).hom)
      (PresheafOfModules.sheafificationAdjunction (𝟙 (structureSheaf B S hS).obj))
      ((SheafOfModules.forget S.ringCatSheaf).obj F)
      (sectionsComparison B S hS F)
      (unit_comp_map_sectionsComparison B S hS F)
  have hforget : (SheafOfModules.forget S.ringCatSheaf).map
        ((SheafOfModules.PullbackConstruction.adjunction.{u}
          (structureMap B S hS)).unit.app F) =
      (PresheafOfModules.pullbackPushforwardAdjunction.{u}
          (structureMap B S hS).hom).unit.app
          ((SheafOfModules.forget S.ringCatSheaf).obj F) ≫
        (PresheafOfModules.pushforward.{u} (structureMap B S hS).hom).map
          ((PresheafOfModules.sheafificationAdjunction
              (𝟙 (structureSheaf B S hS).obj)).unit.app
            ((PresheafOfModules.pullback.{u} (structureMap B S hS).hom).obj
              ((SheafOfModules.forget S.ringCatSheaf).obj F))) := rfl
  rw [← hforget] at hkey
  have h2 : IsIso ((SheafOfModules.forget S.ringCatSheaf).map
      ((SheafOfModules.PullbackConstruction.adjunction.{u}
        (structureMap B S hS)).unit.app F)) :=
    isIso_left_of_comp_eq_comp hkey hc2 hA hB2
  have h3 : IsIso ((SheafOfModules.PullbackConstruction.adjunction.{u}
      (structureMap B S hS)).unit.app F) :=
    isIso_of_reflects_iso _ (SheafOfModules.forget S.ringCatSheaf)
  exact Adjunction.isIso_unit_app_of_isIso_unit_app
    (SheafOfModules.pullbackPushforwardAdjunction.{u} (structureMap B S hS))
    (SheafOfModules.PullbackConstruction.adjunction.{u} (structureMap B S hS)) F h3

end AlgebraicGeometry.SmallEtale

end
