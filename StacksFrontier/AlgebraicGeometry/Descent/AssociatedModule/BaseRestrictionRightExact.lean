module

public import StacksCore.Tactic.StacksAttribute
public import
  StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.BaseEquivalencePresentationReduction
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.BaseEssentialSurjectivity
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.BaseExtensionClosure
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.BaseMemberLocalStep
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.FullOnFree
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.GlobalGenerators
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.MemberLocalStep
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.CechComparison.SmallEtaleHigherDirectImageVanishing
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.FppfEtaleComparison.QuasiCoherentPullback
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.FppfEtaleComparison.QuasiCoherentPushforward
public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.ObjectSections.SurjectiveFromFirstVanishing

/-!
# Right exactness of restriction from the big fppf site to the small Zariski site

`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/BaseExtensionClosure.lean` carries out the
whole of the source's argument for clause (4) of Descent, Lemma 0GNC on the big `τ`-site of a
scheme `S` except one step, which it carries as the hypothesis `hepi`: for a short exact sequence
`C` of `𝒪`-modules on `(Sch/S)_τ`, that restriction `ε_* = baseRestrictModule` along the inclusion
of the small Zariski site of `S` carries `C.g` to an epimorphism.  **This file discharges that
hypothesis at `τ = fppf`**, and with it clause (4) of Stacks 0GNC at the big fppf site.

It is the source's `H¹(U, 𝓕₁) = 0` step, Descent, Proposition 03DW.

## The argument

1. A section of `C.X₃` over an object `W` of the big fppf site with **affine** total space lifts
   to `C.X₂`.  The kernel `C.X₁` is quasi-coherent, hence is `𝓕ᵃ` for a quasi-coherent
   `𝒪_S`-module `𝓕` by Descent, Proposition 03DX (1) — which is unconditional at every `τ` since
   `AlgebraicGeometry.BigFppfOver.baseQuasicoherentIsEssImageAssociatedModule` — and the
   positive-degree cohomology of `𝓕ᵃ` vanishes at an affine object of this very site,
   `AlgebraicGeometry.BigFppfOver.isZero_sheafCohomology_baseAssociatedSheaf_affine`
   (Stacks 03P2 at an affine object).  The passage from that vanishing to surjectivity on
   sections is `Stacks.Cohomology.ObjectSections.surjective_val_app_of_isZero_sheafH'`.
2. The affine opens of `S` are a basis of its topology, and an affine open read in the big fppf
   site is an object with affine total space, so step 1 gives local surjectivity of `ε_*C.g` on
   `S` and hence the epimorphism, by
   `Stacks.Cohomology.ObjectSections.epi_of_surjective_on_presieve`.

## Why the big site is no obstacle

`AlgebraicGeometry.BigFppfOver B S hS` has its objects one universe above its morphisms, and the
module notes of `BaseExtensionClosure` record two routes from cohomology vanishing to
surjectivity on sections, neither of which applied: `epi_sections_map_of_extVanishing` is bound by
`[SmallCategory C]`, and the Čech criterion [Stacks, Tag 03F8] wants Čech vanishing on a cofinal
system of coverings, which a big-site object carrying no finiteness condition has no obvious
supply of.

There is a third route, and it has neither defect:
`Stacks.Cohomology.ObjectSections.surjective_val_app_of_isZero_sheafH'` takes `Sheaf.H'`-vanishing
and no smallness hypothesis — only `HasSheafify`, `HasExt`, `EnoughInjectives` and
`WEqualsLocallyBijective` at the *morphism* universe, which the big site has because it is
essentially small there, exactly as
`AlgebraicGeometry.BigFppfOver.isZero_sheafCohomology_baseAssociatedSheaf_affine` already assumes
in order to state its own conclusion.  So the vanishing and the sections criterion
meet with nothing in between, and the Čech development is not needed on the big site at all.

## Main results

* `AlgebraicGeometry.BigFppfOver.isZero_sheafCohomology_isQuasicoherentOnSite_affine`: the
  positive-degree cohomology of a quasi-coherent `𝒪`-module on `(Sch/S)_fppf` vanishes at an
  object with affine total space.
* `AlgebraicGeometry.BigFppfOver.surjective_val_app_of_shortExact_affine`: a section over such an
  object lifts.
* `AlgebraicGeometry.BigFppfOver.epi_baseRestrictModule_map`: **the hypothesis `hepi` of
  `BaseExtensionClosure` at `τ = fppf`, discharged.**
Clause (4) of Stacks 0GNC is **not** stated here. It is stated once, `τ`-indexed, in
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/BaseRestrictionRightExactAll.lean`, as
`AlgebraicGeometry.BigFppfOver.isQuasicoherentOnSite_shortExact_X₂_all` with its
`CategoryTheory.ObjectProperty.IsClosedUnderExtensions` instance; this file supplies that one its
right-exactness step.

## The four coarser topologies

Clause (4) at `τ ∈ {Zariski, étale, smooth, syntomic}` is **not** here, and the reason is narrow.
The reduction of `BaseExtensionClosure` is `τ`-parametric and its essential-surjectivity
hypothesis is discharged at every `τ`, so what a coarser `τ` needs is exactly `hepi` there; step 2
of the argument above is already `τ`-generic and is stated that way below
(`epi_baseRestrictModule_map_of_surjective_on_affineOpens`); only step 1's vanishing is stated for
the localized fppf topology alone.

That vanishing is supplied at every `τ` in
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/BaseRestrictionRightExactAll.lean`, which
bridges `AlgebraicGeometry.BigFppfOver.baseOverTopology B S hS τ` to
`AlgebraicGeometry.overTopology τ' B'` for the coarser big site `B'` that a big fppf site carries
(Stacks 03FF), and so carries clause (4) at all five topologies.  The statements below are kept at
`τ = fppf` because they are the ones the earlier reductions consume.

## References

* [Stacks Project, Tag 0GNC](https://stacks.math.columbia.edu/tag/0GNC)
* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03P2](https://stacks.math.columbia.edu/tag/03P2)
* [Stacks Project, Tag 01LA](https://stacks.math.columbia.edu/tag/01LA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.BigFppfOver

-- A localized big site is essentially small at the universe of its morphisms, so these two supply
-- its `Ext` universe and enough injectives.  `CategoryTheory.Sheaf.H'` is defined through `Ext`,
-- so without them the statements below do not even elaborate.  They are the same two local
-- instances `AlgebraicGeometry.BigFppfOver.isZero_sheafCohomology_baseAssociatedSheaf_affine` is
-- stated under.
attribute [local instance] Stacks.Cohomology.FreeYonedaUnivLE.enoughInjectives_essentiallySmallSite
  Stacks.Cohomology.FreeYonedaUnivLE.hasExt_essentiallySmallSite

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The vanishing input: a quasi-coherent module at an affine object -/

/-- **The positive-degree cohomology of a quasi-coherent `𝒪`-module on `(Sch/S)_fppf` vanishes at
an object with affine total space.**

A quasi-coherent module on the big fppf site is the associated module of a quasi-coherent
`𝒪_S`-module, by Descent, Proposition 03DX (1) in the form
`AlgebraicGeometry.BigFppfOver.baseQuasicoherentIsEssImageAssociatedModule`; the associated
module is the pullback-sections sheaf `𝓕ᵃ` of Stacks 03DS by Stacks 070S (1),
`AlgebraicGeometry.BigFppfOver.baseAssociatedModuleIsoBaseAssociatedSheaf`; and the vanishing for
`𝓕ᵃ` is `AlgebraicGeometry.BigFppfOver.isZero_sheafCohomology_baseAssociatedSheaf_affine`.  The
transport of `IsZero` along the resulting isomorphism of abelian sheaves goes through
`Stacks.Cohomology.FreeYonedaUnivLE.sheafCohomologyIsoRightDerivedSections`, which exhibits
`Sheaf.H' · p W` as a functor of the sheaf. -/
public theorem isZero_sheafCohomology_isQuasicoherentOnSite_affine
    (G : SheafOfModules.{u} (FibredSite.baseRingStructureSheaf B S hS SiteKind.fppf))
    (hG : G.IsQuasicoherentOnSite) (W : BigFppfOver B S hS) (hW : IsAffineOver B S hS W)
    (p : ℕ) (hp : 0 < p) :
    IsZero (Sheaf.H'.{u} ((SheafOfModules.toSheaf
      (FibredSite.baseRingStructureSheaf B S hS SiteKind.fppf)).obj G) p W) := by
  obtain ⟨F, ⟨e⟩⟩ := baseQuasicoherentIsEssImageAssociatedModule B S hS .fppf G hG
  have : F.obj.IsQuasicoherent := F.property
  have ea : baseAssociatedSheaf B S hS F.obj .fppf ≅ G :=
    (baseAssociatedModuleIsoBaseAssociatedSheaf B S hS .fppf F.obj).symm ≪≫ e
  have eab : (SheafOfModules.toSheaf
        (FibredSite.baseRingStructureSheaf B S hS SiteKind.fppf)).obj
        (baseAssociatedSheaf B S hS F.obj .fppf) ≅
      (SheafOfModules.toSheaf
        (FibredSite.baseRingStructureSheaf B S hS SiteKind.fppf)).obj G :=
    (SheafOfModules.toSheaf _).mapIso ea
  refine (isZero_sheafCohomology_baseAssociatedSheaf_affine B S hS F.obj W hW p hp).of_iso ?_
  exact Stacks.Cohomology.FreeYonedaUnivLE.sheafCohomologyIsoRightDerivedSections.{u}
      (topology B S hS) _ p W ≪≫
    (((sheafSections (topology B S hS) AddCommGrpCat.{u}).obj (op W)).rightDerived p).mapIso
      eab.symm ≪≫
    (Stacks.Cohomology.FreeYonedaUnivLE.sheafCohomologyIsoRightDerivedSections.{u}
      (topology B S hS) _ p W).symm

/-! ### Step 1: sections over an object with affine total space -/

/-- **A section of `C.X₃` over an object of `(Sch/S)_fppf` with affine total space lifts to
`C.X₂`**, for `C` a short exact sequence of `𝒪`-modules with `C.X₁` quasi-coherent.

This is the long exact sequence in the object variable: the vanishing of `H¹(W, C.X₁)` is
`AlgebraicGeometry.BigFppfOver.isZero_sheafCohomology_isQuasicoherentOnSite_affine` and the
passage to surjectivity is
`Stacks.Cohomology.ObjectSections.surjective_val_app_of_isZero_sheafH'`. -/
public theorem surjective_val_app_of_shortExact_affine
    {C : ShortComplex (SheafOfModules.{u}
      (FibredSite.baseRingStructureSheaf B S hS SiteKind.fppf))}
    (hC : C.ShortExact) (h₁ : C.X₁.IsQuasicoherentOnSite) (W : BigFppfOver B S hS)
    (hW : IsAffineOver B S hS W) :
    Function.Surjective (C.g.val.app (op W)) :=
  Stacks.Cohomology.ObjectSections.surjective_val_app_of_isZero_sheafH'.{u}
    (topology B S hS) _ hC W
    (isZero_sheafCohomology_isQuasicoherentOnSite_affine B S hS C.X₁ h₁ W hW 1 Nat.one_pos)

/-! ### Step 2: the epimorphism after restriction to the small Zariski site -/

/-- **Step 2 of the argument, at every `τ`.**  If every section of `C.X₃` over an affine open of
`S`, read as an object of the big `τ`-site, lifts to `C.X₂`, then the restriction of `C.g` to the
small Zariski site of `S` is an epimorphism.

The affine opens of `S` form a basis of its topology
(`AlgebraicGeometry.generate_affineOpensPresieve_mem`), so the hypothesis is local surjectivity on
`S`; the sections of `ε_*X` over an open `U` are the sections of `X` over
`AlgebraicGeometry.BigFppfOver.opensObj B S hS U` on the nose. -/
public theorem epi_baseRestrictModule_map_of_surjective_on_affineOpens (τ : SiteKind)
    {M N : SheafOfModules.{u} (FibredSite.baseRingStructureSheaf B S hS τ)} (f : M ⟶ N)
    (hsurj : ∀ U : S.Opens, IsAffineOpen U →
      Function.Surjective (f.val.app (op (opensObj B S hS U)))) :
    Epi ((baseRestrictModule B S hS τ).map f) := by
  refine Stacks.Cohomology.ObjectSections.epi_of_surjective_on_presieve
    (Opens.grothendieckTopology ↥S) S.ringCatSheaf _
    (fun V ↦ affineOpensPresieve S V) (fun V ↦ generate_affineOpensPresieve_mem S V) ?_
  intro V W _ hg
  exact hsurj W hg

/-- **The hypothesis `hepi` of
`StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.BaseExtensionClosure` at `τ = fppf`,
discharged.**  For a short exact sequence `C` of `𝒪`-modules on the big fppf site of `S` with
`C.X₁` quasi-coherent, the restriction of `C.g` along the inclusion of the small Zariski site of
`S` is an epimorphism.

This is the source's `H¹(U, 𝓕₁) = 0` step, Descent, Proposition 03DW: step 1 is
`AlgebraicGeometry.BigFppfOver.surjective_val_app_of_shortExact_affine` and step 2 is
`AlgebraicGeometry.BigFppfOver.epi_baseRestrictModule_map_of_surjective_on_affineOpens`. -/
public theorem epi_baseRestrictModule_map
    {C : ShortComplex (SheafOfModules.{u}
      (FibredSite.baseRingStructureSheaf B S hS SiteKind.fppf))}
    (hC : C.ShortExact) (h₁ : C.X₁.IsQuasicoherentOnSite) :
    Epi ((baseRestrictModule B S hS SiteKind.fppf).map C.g) :=
  epi_baseRestrictModule_map_of_surjective_on_affineOpens B S hS .fppf C.g
    fun _ hU ↦ surjective_val_app_of_shortExact_affine B S hS hC h₁ _ hU

/-! ### Clause (4) of Stacks 0GNC at the big fppf site

Nothing here states clause (4). The `τ = fppf` reading of it, and its
`CategoryTheory.ObjectProperty.IsClosedUnderExtensions` instance, used to live here as
`isQuasicoherentOnSite_shortExact_X₂_fppf` and
`isClosedUnderExtensions_baseIsQuasicoherentOnSite_fppf`; both were strict specialisations, with
the same statement, of the `τ`-indexed forms downstream in
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/BaseRestrictionRightExactAll.lean` —
`AlgebraicGeometry.BigFppfOver.isQuasicoherentOnSite_shortExact_X₂_all` and
`AlgebraicGeometry.BigFppfOver.isClosedUnderExtensions_baseIsQuasicoherentOnSite_all`, whose clause
strings read "at every τ ∈ {Zariski, étale, smooth, syntomic, fppf}, unconditionally". They had no
consumer anywhere in the library, so they were removed rather than kept as a second spelling of one
statement. What this file does supply to that one is
`AlgebraicGeometry.BigFppfOver.epi_baseRestrictModule_map`, the source's right-exactness step. -/

end AlgebraicGeometry.BigFppfOver

end
