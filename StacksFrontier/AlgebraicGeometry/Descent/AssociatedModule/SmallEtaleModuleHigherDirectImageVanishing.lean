module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleDerivedPushforward
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleQuasicoherentKernels
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.CechComparison.SmallEtaleHigherDirectImageVanishing
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.FppfEtaleComparison.ModuleHigherVanishing
public import StacksFrontier.CategoryTheory.Abelian.RightDerivedTransport
public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedSections.RightDerivedSectionsEssentiallySmall

/-!
# The higher direct images of `ε_*` vanish on a quasi-coherent sheaf of modules

Let `S` be a scheme contained in a big étale site `B` and let
`ε : (S_étale, 𝒪) ⟶ (S_Zar, 𝒪_S)` be the morphism of ringed sites of [Stacks, Tag 070R], so
that `ε_*` is `AlgebraicGeometry.SmallEtale.restrictModule`.  This file proves

`R^p ε_* 𝒢 = 0` for `p > 0`

for a sheaf of `𝒪`-modules `𝒢` on the small étale site of [Stacks, Tag 021B] which is
quasi-coherent on the site, **in the module-valued spelling**
`IsZero (((restrictModuleOfSheaf B S hS).rightDerived p).obj 𝒢)`.

## Why this is not the abelian-sheaf statement

`AlgebraicGeometry.SmallEtale.isZero_rightDerived_pushforward_toSheaf` is the same vanishing for
the direct image of *abelian* sheaves along `ε`, applied to the abelian sheaf underlying `𝒢`.
It does not give the statement here: the comparison of the two right derived functors across the
exact forgetful functor `SheafOfModules.toSheaf` is
`Stacks.Cohomology.SiteModulePushforward.AnySite.rightDerivedPushforwardToSheafIso`, whose module
universe is forced to dominate the universe of the objects of the sites, whereas the small étale
site carries its modules one universe *below* its objects.  Only the case `p = 1` of the
comparison is available here, through
`Stacks.Cohomology.RightDerivedDelta.epi_map_g_of_isZero_rightDerived_one`, which is what
`AlgebraicGeometry.SmallEtale.epi_restrictModule_map_g` uses.

So the route is the one of [Stacks, Tag 072W]: the module-valued covering criterion
`Stacks.Cohomology.ModuleDirectImageOnACover.isZero_rightDerived_pushforward_of_presieve`, whose
universes are mutually independent, fed by the vanishing of the cohomology of `𝒢` over the
affine opens of `S` read as objects of the small étale site.  That is the same criterion, at the
same universes, that `AlgebraicGeometry.BigFppfOver.isZero_rightDerived_aPushforward` uses for
clause (7) of [Stacks, Tag 0DEW].

## Main results

* `AlgebraicGeometry.SmallEtale.isZero_sheafCohomology_succ_toSheaf_associatedModule`: the
  higher cohomology of the abelian sheaf underlying `𝓕ᵃ` vanishes over an affine object of the
  small étale site of [Stacks, Tag 021B].
* `AlgebraicGeometry.SmallEtale.isZero_rightDerived_evaluation_associatedModule`: the same
  vanishing for the module-valued cohomology over such an object, which is the right derived
  functor of `CategoryTheory.SheafOfModules.evaluation`.
* `AlgebraicGeometry.SmallEtale.isZero_rightDerived_restrictModuleOfSheaf`: **the
  module-valued vanishing** `R^p ε_* 𝒢 = 0` for `p > 0` and `𝒢` quasi-coherent on the site.

## Implementation notes

The affine vanishing is `AlgebraicGeometry.isZero_sheafCohomology_succ_smallEtaleAffine`, which
is stated on Mathlib's small étale site `AlgebraicGeometry.Scheme.smallEtaleTopology`, and it is
carried over to the size-bounded site of [Stacks, Tag 021B] exactly as
`AlgebraicGeometry.SmallEtale.rightDerivedBoundedZariskiAbelianPushforwardIso` carries the higher
direct images: sections over an object of the bounded site of a sheaf restricted along the
embedding are sections over its image on the nose, so the two right derived functors of sections
are compared by `CategoryTheory.Functor.compRightDerivedIso` applied to the embedding, which is
an equivalence of the two categories of abelian sheaves and so exact and injective preserving.
`CategoryTheory.Sheaf.H'` is turned into a right derived functor of sections, in both
directions, by
`Stacks.Cohomology.FreeYonedaUnivLE.sheafCohomologyIsoRightDerivedSections`.

The `Ext` universe is the morphism universe `u` of the small étale site throughout, as it is in
`AlgebraicGeometry.isZero_sheafCohomology_succ_smallEtaleAffine`; the two hypotheses that the
`Ext`-groups and enough injectives exist there are
`Stacks.Cohomology.FreeYonedaUnivLE.hasExt_essentiallySmallSite` and its companion, the site of
[Stacks, Tag 021B] being essentially small.  The bridge from
`CategoryTheory.Sheaf.H'` to the module-valued derived sections measures at `max (u + 1) u`
instead, and `Stacks.Cohomology.ModuleDirectImageOnACover.isZero_sheafCohomology_chgUniv`
reconciles the two inside
`Stacks.Cohomology.ModuleDirectImageOnACover.isZero_rightDerived_evaluation_of_isZero_H'_chgUniv`;
the two `CategoryTheory.HasExt.{u + 1}` instances that needs are
`Stacks.Cohomology.ModuleDirectImageOnACover.hasExt_morphismUniverse`.

`isZero_rightDerived_evaluation_associatedModule` is the transport that the implementation notes
of
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtaleRestrictModuleHomologyEdge.lean`
record as missing for the source's own route through [Stacks, Tag 0BKZ] at the affine objects of
`S_étale`: `AlgebraicGeometry.isZero_sheafCohomology_succ_smallEtaleAffine` read as a statement
about `(CategoryTheory.SheafOfModules.evaluation _ _).rightDerived` on
`AlgebraicGeometry.SmallEtale`.  It does *not* finish the identification of the cohomology
sheaves of `Rε_*`: that still needs the unbounded truncation apparatus, `τ_{< i}E` being
unbounded.

No `@[stacks]` attribute is attached.  The vanishing of the higher direct images along `ε` is a
step inside the proof of [Stacks, Tag 03DW] and not a part the source delimits, which is also
why `AlgebraicGeometry.SmallEtale.isZero_rightDerived_pushforward_opensToSmallEtale` and
`AlgebraicGeometry.SmallEtale.isZero_rightDerived_pushforward_toSheaf` carry none.

## References

* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
* [Stacks Project, Tag 072W](https://stacks.math.columbia.edu/tag/072W)
* [Stacks Project, Tag 021B](https://stacks.math.columbia.edu/tag/021B)
* [Stacks Project, Tag 070R](https://stacks.math.columbia.edu/tag/070R)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Cohomology.ModuleDirectImageOnACover

universe u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] Stacks.Cohomology.FreeYonedaUnivLE.enoughInjectives_essentiallySmallSite
  Stacks.Cohomology.FreeYonedaUnivLE.hasExt_essentiallySmallSite

/-- **The higher cohomology of the abelian sheaf underlying `𝓕ᵃ` vanishes over an affine object
of the small étale site of [Stacks, Tag 021B].**  This is
`AlgebraicGeometry.isZero_sheafCohomology_succ_smallEtaleAffine`, the same vanishing on Mathlib's
small étale site, transported along the embedding of the size-bounded site into it.

The abelian sheaf underlying `𝓕ᵃ` is the restriction along that embedding of
`AlgebraicGeometry.smallEtaleAssociatedSheaf`, by
`AlgebraicGeometry.SmallEtale.toSheafAssociatedModuleIso`; sections over an object of a
restricted sheaf are sections over its image, so the right derived functors of sections are
compared by `CategoryTheory.Functor.compRightDerivedIso` at the embedding, an equivalence of the
two categories of abelian sheaves. -/
public theorem isZero_sheafCohomology_succ_toSheaf_associatedModule (𝓕 : S.Modules)
    [𝓕.IsQuasicoherent] (X : SmallEtale B S hS) (hX : SmallEtale.IsAffine B S hS X)
    (p : ℕ) (hp : 0 < p) :
    IsZero (Sheaf.H'.{u} ((SheafOfModules.toSheaf (structureSheaf B S hS)).obj
      ((associatedModule B S hS).obj 𝓕)) p X) := by
  have hzero : IsZero ((((sheafSections (Scheme.smallEtaleTopology S) AddCommGrpCat.{u}).obj
      (op ((toEtaleSite B S hS).obj X))).rightDerived p).obj (smallEtaleAssociatedSheaf S 𝓕)) :=
    (isZero_sheafCohomology_succ_smallEtaleAffine S 𝓕 ((toEtaleSite B S hS).obj X) hX p hp).of_iso
      (Stacks.Cohomology.FreeYonedaUnivLE.sheafCohomologyIsoRightDerivedSections
        (Scheme.smallEtaleTopology S) _ p ((toEtaleSite B S hS).obj X)).symm
  refine IsZero.of_iso ?_ (Stacks.Cohomology.FreeYonedaUnivLE.sheafCohomologyIsoRightDerivedSections
    (topology B S hS) _ p X)
  refine IsZero.of_iso ?_ ((((sheafSections (topology B S hS) AddCommGrpCat.{u}).obj
    (op X)).rightDerived p).mapIso (toSheafAssociatedModuleIso B S hS 𝓕))
  exact hzero.of_iso (((toEtaleSiteAbelianPushforward B S hS).compRightDerivedIso
    ((sheafSections (topology B S hS) AddCommGrpCat.{u}).obj (op X)) p).app
      (smallEtaleAssociatedSheaf S 𝓕)).symm

/-- **The module-valued cohomology of `𝓕ᵃ` over an affine object of the small étale site of
[Stacks, Tag 021B] vanishes in positive degrees.**  This is `R^p Γ(X, -)` for `R^p Γ` the right
derived functor of `CategoryTheory.SheafOfModules.evaluation`, so it is the *module-valued*
spelling of the vanishing, whereas
`isZero_sheafCohomology_succ_toSheaf_associatedModule` is the abelian-sheaf one.

The bridge between the two is
`Stacks.Cohomology.ModuleDirectImageOnACover.isZero_rightDerived_evaluation_of_isZero_H'_chgUniv`,
which corepresents module-valued sections over an object and so needs no smallness of the site —
only that its morphisms and the module sections share the universe `u`, as they do here. -/
public theorem isZero_rightDerived_evaluation_associatedModule (𝓕 : S.Modules)
    [𝓕.IsQuasicoherent] (X : SmallEtale B S hS) (hX : SmallEtale.IsAffine B S hS X)
    (p : ℕ) (hp : 0 < p) :
    IsZero (((SheafOfModules.evaluation (structureSheaf B S hS) (op X)).rightDerived p).obj
      ((associatedModule B S hS).obj 𝓕)) := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  have : HasExt.{u + 1} (Sheaf (topology B S hS) AddCommGrpCat.{u}) :=
    hasExt_morphismUniverse _
  have : HasExt.{u + 1} (SheafOfModules.{u} (structureSheaf B S hS)) :=
    hasExt_morphismUniverse _
  exact isZero_rightDerived_evaluation_of_isZero_H'_chgUniv.{u + 1, u, u}
    (topology B S hS) (structureSheaf B S hS) X q _
    (isZero_sheafCohomology_succ_toSheaf_associatedModule B S hS 𝓕 X hX (q + 1) q.succ_pos)

/-- **The higher direct images along `ε : S_étale ⟶ S_Zar` of a quasi-coherent sheaf of
`𝒪`-modules vanish**, in the module-valued spelling: `R^p ε_* 𝒢 = 0` for `p > 0`.

This is [Stacks, Tag 03DW] at `ε` for sheaves of modules, and it is the statement the
abelian-sheaf spelling
`AlgebraicGeometry.SmallEtale.isZero_rightDerived_pushforward_toSheaf` does not give; see the
module documentation.

The route is [Stacks, Tag 072W]: `R^p ε_* 𝒢` is the sheafification of the cohomology presheaf
`V ↦ H^p(V_étale, 𝒢)`, so it vanishes as soon as every open of `S` is covered by opens over
which that cohomology vanishes, which is the criterion
`Stacks.Cohomology.ModuleDirectImageOnACover.isZero_rightDerived_pushforward_of_presieve`.  The
covering family is the affine opens (`AlgebraicGeometry.affineOpensPresieve`); over an affine
open the vanishing is `isZero_rightDerived_evaluation_associatedModule`, read through the
identification `𝒢 ≅ (ε_*𝒢)ᵃ` of
`AlgebraicGeometry.SmallEtale.isIso_counit'` with `ε_*𝒢` quasi-coherent
by `AlgebraicGeometry.SmallEtale.isQuasicoherent_restrictModule`. -/
public theorem isZero_rightDerived_restrictModuleOfSheaf
    (G : SheafOfModules.{u} (structureSheaf B S hS)) (hG : G.IsQuasicoherentOnSite)
    (p : ℕ) (hp : 0 < p) :
    IsZero (((restrictModuleOfSheaf B S hS).rightDerived p).obj G) := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  have : (SheafOfModules.pushforward.{u} (structureMap B S hS)).Additive :=
    additive_restrictModuleOfSheaf B S hS
  have : SheafOfModules.IsQuasicoherent (R := S.ringCatSheaf)
      ((restrictModule B S hS).obj G) := isQuasicoherent_restrictModule B S hS G hG
  have : IsIso ((associatedModuleAdjunction B S hS).counit.app G) :=
    isIso_counit' B S hS G hG
  refine IsZero.of_iso ?_ (((restrictModuleOfSheaf B S hS).rightDerived (q + 1)).mapIso
    (asIso ((associatedModuleAdjunction B S hS).counit.app G)).symm)
  refine isZero_rightDerived_pushforward_of_presieve
    (opensToSmallEtale B S hS) (structureSheaf B S hS) S.ringCatSheaf
    (structureMap B S hS) (q + 1) _ (fun V ↦ ?_)
  exact ⟨affineOpensPresieve S V, generate_affineOpensPresieve_mem S V, fun W g hg ↦
    isZero_rightDerived_evaluation_associatedModule B S hS _
      ((opensToSmallEtale B S hS).obj W) hg (q + 1) q.succ_pos⟩

end AlgebraicGeometry.SmallEtale

end
