module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.BaseEquivalenceFppf
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.BaseOpenCoverQuasicoherence
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedPushforward.QuasicoherentWeakSerre
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.QuasiCoherentSmallEtaleBigSite
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Descent.BaseAssociatedModuleColimits

/-!
# Clause (4) of Stacks 0GNC on a big site, reduced to one cohomological input

Clause (4) of Descent, Lemma 0GNC says that given a short exact sequence of `𝒪`-modules
`0 → 𝓕₁ → 𝓕₂ → 𝓕₃ → 0` on one of the five big sites `(Sch/S)_τ` of a scheme `S`, if `𝓕₁` and
`𝓕₃` are quasi-coherent then so is `𝓕₂`.  **This file does not prove that clause.**  It carries
out the whole of the source's argument for it on the big `τ`-site except one step, which is
carried as a named hypothesis, so that what is left of the clause is a single statement about
the restriction functor rather than the source's prose.

## The argument, and which step is missing

Write `ε^* = (𝓕 ↦ 𝓕^a) = AlgebraicGeometry.BigFppfOver.baseAssociatedModule` and
`ε_* = AlgebraicGeometry.BigFppfOver.baseRestrictModule` for its right adjoint, restriction
along the inclusion of the small Zariski site of `S`.  Given a short exact sequence `C` of
`𝒪`-modules on `(Sch/S)_τ` whose outer terms are quasi-coherent, the source:

1. restricts `C` to `S_Zar`, obtaining `0 → ε_*C.X₁ → ε_*C.X₂ → ε_*C.X₃ → 0`.  Left exactness
   is free, `ε_*` being a right adjoint; **right exactness is the step that is not free** — it
   is where the source invokes the vanishing `H^1(U, 𝓕₁) = 0` on an affine open `U ⊆ S` of
   Descent, Proposition 03DW;
2. concludes that `ε_*C.X₂` is quasi-coherent on `S`, quasi-coherent `𝒪_S`-modules being closed
   under extensions (Schemes, Section 01LA);
3. compares `(ε_*C.X₂)^a` with `C.X₂` and finds the comparison an isomorphism.

Step 1's missing half is exactly `Epi (ε_*.map C.g)`, and that is the hypothesis `hepi` below.
Steps 2 and 3 are proved here outright.

## Step 3 on a big site: the monomorphism is free

On the big site `ε^*` is **not** left exact — that is clause (6) of Stacks 06VE, witnessed in
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/BigSiteNotExact.lean` — so step 3 cannot
be run the way
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtaleExtensionReduction.lean` runs
it at `τ = étale`, where `ε^*` is exact because an étale morphism is flat.  The source's
replacement is its third paragraph: the universal injectivity of `𝓕₁(U) → 𝓔(U)`, tested against
the `A`-algebras `A ⊕ M`.

That paragraph is not needed either.  What step 3 asks of `ε^*(ε_*C)` is that it be short
exact, and the only part of that which `ε^*` being merely right exact does not give is
`Mono (ε^*(ε_* C.f))`.  But the left-hand square of the counit morphism
`ε^*(ε_*C) ⟶ C` reads

```
ε^*(ε_* C.f) ≫ ε_{C.X₂} = ε_{C.X₁} ≫ C.f
```

whose right-hand side is a monomorphism — `C.f` is one because `C` is short exact, and the
counit `ε_{C.X₁}` is an *isomorphism* at a quasi-coherent module.  A morphism whose composite
with something is a monomorphism is itself a monomorphism, so `Mono (ε^*(ε_* C.f))` follows
with no flatness, no universal injectivity and no test algebras.  This is
`AlgebraicGeometry.BigFppfOver.mono_baseAssociatedModule_map_baseRestrictModule_map_f` below,
and it is what makes the big-site argument no longer than the small étale one.

## Main results

* `AlgebraicGeometry.BigFppfOver.isIso_baseCounit_app_of_essImage`: the counit of the
  associated-module adjunction of `(Sch/S)_τ` is an isomorphism at a module in the essential
  image of `𝓕 ↦ 𝓕^a`.
* `AlgebraicGeometry.BigFppfOver.isQuasicoherent_baseRestrictModule_of_essImage`: `ε_*` carries
  such a module to a quasi-coherent `𝒪_S`-module.
* `AlgebraicGeometry.BigFppfOver.shortExact_map_baseRestrictModule`: the source's step 1, over
  `hepi`.
* `AlgebraicGeometry.BigFppfOver.mono_baseAssociatedModule_map_baseRestrictModule_map_f`: the
  monomorphism of step 3, with no hypothesis beyond the counit being invertible at `C.X₁`.
* `AlgebraicGeometry.BigFppfOver.isIso_baseCounit_app_X₂`: the source's step 3.
* `AlgebraicGeometry.BigFppfOver.isQuasicoherentOnSite_X₂_of_shortExact_of_epi_baseRestrictModule`:
  **clause (4) of Stacks 0GNC at `(Sch/S)_τ`, over `hepi` and the essential surjectivity of
  `𝓕 ↦ 𝓕^a`**.
* `BigFppfOver.isQuasicoherentOnSite_X₂_of_shortExact_fppf_of_epi_baseRestrictModule` and
  `BigFppfOver.isClosedUnderExtensions_isQuasicoherentOnSite_fppf_of_epi_baseRestrictModule`:
  the same at `τ = fppf`, where essential surjectivity is a theorem
  (`AlgebraicGeometry.BigFppfOver.quasicoherentIsEssImageAssociatedModule'`), so that
  `hepi` is the single remaining hypothesis.

## No `@[stacks 0GNC]` attribute is carried here

Every statement below has `hepi` as a hypothesis, and a hypothesis is part of a citation: a
clause carrying a hypothesis the source does not have is not that clause.  The convention is the
one of
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtaleExtensionReduction.lean`,
which states the same reduction at `τ = étale` and carries no attribute for it either.  The
unconditional statements are elsewhere: clause (4) at every `τ` is
`AlgebraicGeometry.BigFppfOver.isQuasicoherentOnSite_shortExact_X₂_all`
(`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/BaseRestrictionRightExactAll.lean`),
clauses (1), (2) and (3) at every `τ` are in
`StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Descent.QuasicoherentColimitsBigSites` and
clauses (5) and (6) at every `τ` in
`StacksFrontier/AlgebraicGeometry/Descent/QuasiCoherentTopologiesTwo/BigSiteProperties.lean`.  Part
(10) of Stacks 06VE, the same content read as "the middle term is an `𝓕ᵃ`", is
`AlgebraicGeometry.BigFppfOver.essImage_X₂_of_shortExact_big`
(`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/BaseExtensionEssImage.lean`).

## What `hepi` is, and where it is discharged

**`hepi` is now a theorem at every `τ`**,
`AlgebraicGeometry.BigFppfOver.epi_baseRestrictModule_map_all`
(`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/BaseRestrictionRightExactAll.lean`), so
nothing of this file is conditional in substance; the hypothesis is kept here because this file
is the reduction and not the clause.  Its two halves are
`AlgebraicGeometry.BigFppfOver.isZero_sheafCohomology_isQuasicoherentOnSite_affine_all` for the
vanishing and `Stacks.Cohomology.ObjectSections.surjective_val_app_of_isZero_sheafH'` for the
passage to surjectivity on sections, followed by
`AlgebraicGeometry.BigFppfOver.epi_baseRestrictModule_map_of_surjective_on_affineOpens`.  What
follows explains what the hypothesis means; the two routes it calls inapplicable are not the ones
the proof uses.

`Epi ((baseRestrictModule B S hS τ).map C.g)` is an epimorphism of sheaves of modules on
`S_Zar`, so it is local on `S`: it is enough to lift a section of `C.X₃` over the object
`U ⟶ S` of the big site to `C.X₂`, after shrinking `U` among the affine opens of `S`.  From the
short exact sequence on the site such a lift exists after a `τ`-covering of `U`, and descending
it along that covering is the vanishing of `H^1` of `C.X₁` on it.

The vanishing itself **is** proved at `τ = fppf`, over an arbitrary affine object of this very
site: `AlgebraicGeometry.isZero_sheafCohomology_baseAssociatedSheaf_affine`
(`StacksFrontier/AlgebraicGeometry/EtaleCohomology/FppfEtaleComparison/QuasiCoherentPushforward.lean`
`:364`) gives `IsZero (Sheaf.H' ((SheafOfModules.toSheaf _).obj (baseAssociatedSheaf B S hS 𝓖
.fppf)) p W)` for every `W : BigFppfOver B S hS` with `IsAffineOver B S hS W` and every `p > 0`.
The `@[stacks 03DW]`/`@[stacks 03P2]` carrier
`AlgebraicGeometry.bigOverQuasiCoherentGlobalCohomologyIso` is *not* the useful form here: it
compares cohomology over the **opens of `S`**, not over an arbitrary object of the big site.

What was missing was the step from that vanishing to surjectivity on sections.  Two routes were
in the library and neither applied as it stood:

* `Stacks.Cohomology.ModuleComparison.epi_sections_map_of_extVanishing`
  (`StacksFrontier/Topology/Sheaves/Cohomology/ModuleComparison/AcyclicityAndBoundedBelow.lean:123`)
  is exactly the statement wanted — `Epi` on sections over an object from vanishing of the `Ext`
  groups out of `freeSectionsSheaf`, which is what `Sheaf.H'` is — but its site is bound by
  `[SmallCategory C]`, and `BigFppfOver B S hS` has objects in `Type (u + 1)` and morphisms in
  `Type u`.
* `Stacks.CechSite.surjective_on_sections_of_isZero_cechCohomology`
  (`StacksFrontier/CategoryTheory/Sites/Cohomology/Cech/FirstVanishingAndSections.lean:529`,
  `@[stacks 03F8]`) carries no smallness hypothesis, but wants **Čech** `H^1`-vanishing on a
  cofinal system of coverings together with the product hypotheses, not `Sheaf.H'`-vanishing.
  This is the route `StacksFrontier/AlgebraicGeometry/Spaces/AffineChartSurjectivityFromCech.lean`
  takes for an algebraic space, there against
  `AlgebraicGeometry.isZero_cechCohomology_succ_quasiCoherentPresheaf`
  (`StacksFrontier/AlgebraicGeometry/Topologies/CechVanishingStandardCovering.lean:183`,
  `@[stacks 03FJ]`).

What was taken in the end is neither: the vanishing at every `τ` rather than at fppf alone, and
`Stacks.Cohomology.ObjectSections.surjective_val_app_of_isZero_sheafH'` for the passage, followed
by the passage from objectwise surjectivity over the affine objects
`BigFppfOver.opensObj B S hS U` to an epimorphism of sheaves of modules on `S_Zar`.

## Implementation notes

`CategoryTheory.ShortComplex.map_comp` and `CategoryTheory.ShortComplex.map_id` are `rfl`, so
`CategoryTheory.ShortComplex.mapNatTrans` applied to the counit is already a morphism
`C.map (ε_* ⋙ ε^*) ⟶ C` with no transport.

Right exactness of `ε^*` is not quoted from Stacks 06VE (4),
`AlgebraicGeometry.BigFppfOver.preservesFiniteColimits_baseAssociatedModuleQcoh`, which is about
the functor restricted to `QCoh(𝒪_S)`: `ε_*C` is a short complex of *all* `𝒪_S`-modules, and
`ε^*` preserves every colimit on all of them, being a left adjoint
(`AlgebraicGeometry.BigFppfOver.preservesColimitsOfSize_baseAssociatedModule`).

## References

* [Stacks Project, Tag 0GNC](https://stacks.math.columbia.edu/tag/0GNC)
* [Stacks Project, Tag 06VE](https://stacks.math.columbia.edu/tag/06VE)
* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 01LA](https://stacks.math.columbia.edu/tag/01LA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

namespace BigFppfOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Additivity and left exactness of the two functors -/

/-- `ε^* = (𝓕 ↦ 𝓕^a)` on `(Sch/S)_τ` is additive: it is a left adjoint, hence preserves binary
coproducts, hence binary biproducts. -/
public instance additive_baseAssociatedModule (τ : SiteKind) :
    (baseAssociatedModule B S hS τ).Additive := by
  haveI := preservesBinaryBiproducts_of_preservesBinaryCoproducts
    (baseAssociatedModule B S hS τ)
  exact Functor.additive_of_preservesBinaryBiproducts _

/-- `ε_*`, restriction along the inclusion of the small Zariski site of `S`, is additive, being
the right adjoint of an additive functor. -/
public instance additive_baseRestrictModule (τ : SiteKind) :
    (baseRestrictModule B S hS τ).Additive :=
  (baseAssociatedModuleAdjunction B S hS τ).right_adjoint_additive

/-- `ε_*` is left exact, being a right adjoint. -/
public instance preservesFiniteLimits_baseRestrictModule (τ : SiteKind) :
    PreservesFiniteLimits (baseRestrictModule B S hS τ) :=
  haveI := (baseAssociatedModuleAdjunction B S hS τ).rightAdjoint_preservesLimits
  inferInstance

/-! ### The counit at a module in the essential image -/

/-- The counit of the associated-module adjunction of `(Sch/S)_τ` is an isomorphism at
`𝓖^a` for a quasi-coherent `𝒪_S`-module `𝓖`.

The unit is an isomorphism at `𝓖` (`AlgebraicGeometry.BigFppfOver.isIso_baseUnit_app`, the
content of Stacks 0GN7 for the big site), and the triangle identity exhibits the counit at
`𝓖^a` as a retraction of the image of that unit. -/
public theorem isIso_baseCounit_app_baseAssociatedModule (τ : SiteKind) (𝓖 : S.Modules)
    [𝓖.IsQuasicoherent] :
    IsIso ((baseAssociatedModuleAdjunction B S hS τ).counit.app
      ((baseAssociatedModule B S hS τ).obj 𝓖)) := by
  have : IsIso ((baseAssociatedModuleAdjunction B S hS τ).unit.app 𝓖) :=
    isIso_baseUnit_app B S hS τ 𝓖
  have : IsIso ((baseAssociatedModule B S hS τ).map
      ((baseAssociatedModuleAdjunction B S hS τ).unit.app 𝓖)) := Functor.map_isIso _ _
  exact IsIso.of_isIso_fac_left
    ((baseAssociatedModuleAdjunction B S hS τ).left_triangle_components 𝓖)

/-- The counit of the associated-module adjunction of `(Sch/S)_τ` is an isomorphism at every
module in the essential image of `𝓕 ↦ 𝓕^a`.  Transport of the previous statement along the
isomorphism, by naturality of the counit. -/
public theorem isIso_baseCounit_app_of_essImage (τ : SiteKind)
    {X : SheafOfModules.{u} (FibredSite.baseRingStructureSheaf B S hS τ)}
    (hX : (baseAssociatedModuleQcoh B S hS τ).essImage X) :
    IsIso ((baseAssociatedModuleAdjunction B S hS τ).counit.app X) := by
  obtain ⟨M, ⟨e⟩⟩ := hX
  have : M.obj.IsQuasicoherent := M.property
  have : IsIso ((baseAssociatedModuleAdjunction B S hS τ).counit.app
      ((baseAssociatedModuleQcoh B S hS τ).obj M)) :=
    isIso_baseCounit_app_baseAssociatedModule B S hS τ M.obj
  have : IsIso ((baseRestrictModule B S hS τ ⋙ baseAssociatedModule B S hS τ).map e.hom) :=
    inferInstance
  have : IsIso ((baseAssociatedModuleAdjunction B S hS τ).counit.app
        ((baseAssociatedModuleQcoh B S hS τ).obj M) ≫
      (𝟭 (SheafOfModules.{u} (FibredSite.baseRingStructureSheaf B S hS τ))).map e.hom) :=
    inferInstance
  exact IsIso.of_isIso_fac_left
    ((baseAssociatedModuleAdjunction B S hS τ).counit.naturality e.hom)

/-- Restriction along the inclusion of the small Zariski site carries a module in the essential
image of `𝓕 ↦ 𝓕^a` to a quasi-coherent `𝒪_S`-module: it carries `𝓖^a` to `𝓖` itself, the unit
being an isomorphism there. -/
public theorem isQuasicoherent_baseRestrictModule_of_essImage (τ : SiteKind)
    {X : SheafOfModules.{u} (FibredSite.baseRingStructureSheaf B S hS τ)}
    (hX : (baseAssociatedModuleQcoh B S hS τ).essImage X) :
    SheafOfModules.IsQuasicoherent (R := S.ringCatSheaf)
      ((baseRestrictModule B S hS τ).obj X) := by
  obtain ⟨M, ⟨e⟩⟩ := hX
  have : M.obj.IsQuasicoherent := M.property
  have hu := isIso_baseUnit_app B S hS τ M.obj
  exact (SheafOfModules.isQuasicoherent S.ringCatSheaf).prop_of_iso
    (@asIso _ _ _ _ _ hu ≪≫ (baseRestrictModule B S hS τ).mapIso e) M.property

/-! ### Step 1: restricting the sequence to the small Zariski site of `S` -/

section

variable {B S hS}
variable {τ : SiteKind}
  {C : ShortComplex (SheafOfModules.{u} (FibredSite.baseRingStructureSheaf B S hS τ))}

/-- **The source's step 1.**  The restriction of a short exact sequence of `𝒪`-modules on
`(Sch/S)_τ` along the inclusion of the small Zariski site of `S` is short exact, provided `ε_*`
carries its epimorphism to an epimorphism.

Left exactness is free: `ε_*` is a right adjoint, so it preserves the kernel exhibiting the
middle exactness and preserves the monomorphism.  The epimorphism is `hepi`, and is the half of
this step that the source gets from the vanishing `H^1(U, 𝓕₁) = 0` on the affine opens of `S`,
Descent, Proposition 03DW. -/
public theorem shortExact_map_baseRestrictModule (hC : C.ShortExact)
    (hepi : Epi ((baseRestrictModule B S hS τ).map C.g)) :
    (C.map (baseRestrictModule B S hS τ)).ShortExact := by
  have := hC.mono_f
  have := hC.epi_g
  exact { exact := hC.exact.map_of_mono_of_preservesKernel _ inferInstance inferInstance
          mono_f := (inferInstance : Mono ((baseRestrictModule B S hS τ).map C.f))
          epi_g := hepi }

/-! ### Step 2: the restriction of the middle term is quasi-coherent on `S` -/

/-- **The source's step 2.**  The restriction of the middle term along the inclusion of the
small Zariski site is a quasi-coherent `𝒪_S`-module: it is an extension of the restrictions of
the outer two, which are quasi-coherent by
`AlgebraicGeometry.BigFppfOver.isQuasicoherent_baseRestrictModule_of_essImage`, and
quasi-coherent modules on a scheme are closed under extensions (Schemes, Section 01LA). -/
public theorem isQuasicoherent_baseRestrictModule_X₂ (hC : C.ShortExact)
    (h₁ : (baseAssociatedModuleQcoh B S hS τ).essImage C.X₁)
    (h₃ : (baseAssociatedModuleQcoh B S hS τ).essImage C.X₃)
    (hepi : Epi ((baseRestrictModule B S hS τ).map C.g)) :
    SheafOfModules.IsQuasicoherent (R := S.ringCatSheaf)
      ((baseRestrictModule B S hS τ).obj C.X₂) :=
  Stacks.AlgebraicGeometry.QuasicoherentWeakSerre.isQuasicoherent_X₂_of_shortExact
    (shortExact_map_baseRestrictModule hC hepi)
    (isQuasicoherent_baseRestrictModule_of_essImage B S hS τ h₁)
    (isQuasicoherent_baseRestrictModule_of_essImage B S hS τ h₃)

/-! ### Step 3: the counit at the middle term is an isomorphism -/

/-- **The monomorphism of step 3, with no flatness and no test algebras.**  The image under
`ε^*` of the restricted monomorphism is a monomorphism, because composing it with the counit at
the middle term gives the original monomorphism `C.f` precomposed with the counit at `C.X₁`,
which is an isomorphism.

This is what replaces the source's third paragraph, where the comparison is shown injective by
testing the universal injectivity of `𝓕₁(U) → 𝓔(U)` against the `A`-algebras `A ⊕ M`.  On a big
site `ε^*` is not left exact, so the monomorphism cannot come from exactness of `ε^*`; it comes
from the counit square instead. -/
public theorem mono_baseAssociatedModule_map_baseRestrictModule_map_f (hC : C.ShortExact)
    (h₁ : (baseAssociatedModuleQcoh B S hS τ).essImage C.X₁) :
    Mono ((baseAssociatedModule B S hS τ).map ((baseRestrictModule B S hS τ).map C.f)) := by
  have := hC.mono_f
  have := isIso_baseCounit_app_of_essImage B S hS τ h₁
  have : Mono ((baseAssociatedModuleAdjunction B S hS τ).counit.app C.X₁ ≫
      (𝟭 (SheafOfModules.{u}
        (FibredSite.baseRingStructureSheaf B S hS τ))).map C.f) :=
    @mono_comp _ _ _ _ _ _ (IsIso.mono_of_iso _) _ hC.mono_f
  exact mono_of_mono_fac
    ((baseAssociatedModuleAdjunction B S hS τ).counit.naturality C.f)

/-- **The source's step 3.**  The counit `ε^* ε_* 𝓕₂ → 𝓕₂` is an isomorphism at the middle term.

The restricted sequence is short exact by step 1; applying `ε^*`, which preserves all colimits
being a left adjoint, keeps it exact at the middle and at the right, and
`AlgebraicGeometry.BigFppfOver.mono_baseAssociatedModule_map_baseRestrictModule_map_f` supplies
the monomorphism on the left.  The counit is a morphism from the resulting short exact sequence
to the original one whose outer components are isomorphisms, and the short five lemma does the
rest. -/
public theorem isIso_baseCounit_app_X₂ (hC : C.ShortExact)
    (h₁ : (baseAssociatedModuleQcoh B S hS τ).essImage C.X₁)
    (h₃ : (baseAssociatedModuleQcoh B S hS τ).essImage C.X₃)
    (hepi : Epi ((baseRestrictModule B S hS τ).map C.g)) :
    IsIso ((baseAssociatedModuleAdjunction B S hS τ).counit.app C.X₂) := by
  have := hepi
  have := (shortExact_map_baseRestrictModule hC hepi).epi_g
  have hE : ((C.map (baseRestrictModule B S hS τ)).map
      (baseAssociatedModule B S hS τ)).ShortExact :=
    { exact := (shortExact_map_baseRestrictModule hC hepi).exact.map_of_epi_of_preservesCokernel
        _ inferInstance inferInstance
      mono_f := mono_baseAssociatedModule_map_baseRestrictModule_map_f hC h₁
      epi_g := (inferInstance : Epi ((baseAssociatedModule B S hS τ).map
        ((baseRestrictModule B S hS τ).map C.g))) }
  exact ShortComplex.isIso₂_of_shortExact_of_isIso₁₃'
    (C.mapNatTrans (baseAssociatedModuleAdjunction B S hS τ).counit) hE hC
    (isIso_baseCounit_app_of_essImage B S hS τ h₁)
    (isIso_baseCounit_app_of_essImage B S hS τ h₃)

/-! ### Clause (4) of Stacks 0GNC, over the two hypotheses -/

/-- **Clause (4) of Stacks 0GNC at `(Sch/S)_τ`, over `hepi` and essential surjectivity.**  Given
a short exact sequence `0 → 𝓕₁ → 𝓕₂ → 𝓕₃ → 0` of `𝒪`-modules on the big `τ`-site of `S` with
`𝓕₁` and `𝓕₃` quasi-coherent, the middle term `𝓕₂` is quasi-coherent.

`hsurj` is the essential-surjectivity half of Stacks 03DX (1) at `(Sch/S)_τ`, which is what
turns quasi-coherence of the outer terms into their being `𝓖^a`'s, and `hepi` is the source's
`H^1(U, 𝓕₁) = 0` step; both are now theorems at every `τ`
(`AlgebraicGeometry.BigFppfOver.baseQuasicoherentIsEssImageAssociatedModule` and
`AlgebraicGeometry.BigFppfOver.epi_baseRestrictModule_map_all`), and the clause with them
discharged is `AlgebraicGeometry.BigFppfOver.isQuasicoherentOnSite_shortExact_X₂_all`, which is
where the `@[stacks 0GNC]` attribute sits.  Because this statement still carries them it carries
no attribute. -/
public theorem isQuasicoherentOnSite_X₂_of_shortExact_of_epi_baseRestrictModule
    (hC : C.ShortExact) (h₁ : C.X₁.IsQuasicoherentOnSite) (h₃ : C.X₃.IsQuasicoherentOnSite)
    (hsurj : BaseQuasicoherentIsEssImageAssociatedModule B S hS τ)
    (hepi : Epi ((baseRestrictModule B S hS τ).map C.g)) :
    C.X₂.IsQuasicoherentOnSite := by
  have := isIso_baseCounit_app_X₂ hC (hsurj _ h₁) (hsurj _ h₃) hepi
  exact SheafOfModules.IsQuasicoherentOnSite.of_iso
    (asIso ((baseAssociatedModuleAdjunction B S hS τ).counit.app C.X₂))
    (isQuasicoherentOnSite_baseAssociatedModule_of_isQuasicoherent B S hS τ _
      (isQuasicoherent_baseRestrictModule_X₂ hC (hsurj _ h₁) (hsurj _ h₃) hepi))

end

/-! ### At `τ = fppf`, where essential surjectivity is a theorem -/

section

variable {B S hS}
variable {C : ShortComplex (SheafOfModules.{u}
  (FibredSite.baseRingStructureSheaf B S hS SiteKind.fppf))}

/-- **Clause (4) of Stacks 0GNC at `τ = fppf`, over `hepi` alone.**  The essential-surjectivity
hypothesis of the previous statement is discharged by
`AlgebraicGeometry.BigFppfOver.quasicoherentIsEssImageAssociatedModule'`, leaving `hepi` —
the right exactness of restriction to `S_Zar`, which the source gets from Descent,
Proposition 03DW — as the only hypothesis.  It too is now a theorem, at every `τ`, so this
statement is superseded for citation purposes by
`AlgebraicGeometry.BigFppfOver.isQuasicoherentOnSite_shortExact_X₂_all`. -/
public theorem isQuasicoherentOnSite_X₂_of_shortExact_fppf_of_epi_baseRestrictModule
    (hC : C.ShortExact) (h₁ : C.X₁.IsQuasicoherentOnSite) (h₃ : C.X₃.IsQuasicoherentOnSite)
    (hepi : Epi ((baseRestrictModule B S hS SiteKind.fppf).map C.g)) :
    C.X₂.IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_X₂_of_shortExact_of_epi_baseRestrictModule hC h₁ h₃
    (baseQuasicoherentIsEssImageAssociatedModule_fppf B S hS) hepi

end

/-- The same conclusion as the `CategoryTheory.ObjectProperty.IsClosedUnderExtensions`
instance, at `τ = fppf`, over `hepi` taken for every short exact sequence. -/
public theorem isClosedUnderExtensions_isQuasicoherentOnSite_fppf_of_epi_baseRestrictModule
    (hepi : ∀ C : ShortComplex (SheafOfModules.{u}
        (FibredSite.baseRingStructureSheaf B S hS SiteKind.fppf)),
      C.ShortExact → C.X₁.IsQuasicoherentOnSite → C.X₃.IsQuasicoherentOnSite →
        Epi ((baseRestrictModule B S hS SiteKind.fppf).map C.g)) :
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (FibredSite.baseRingStructureSheaf B S hS SiteKind.fppf)).IsClosedUnderExtensions where
  prop_X₂_of_shortExact hC h₁ h₃ :=
    isQuasicoherentOnSite_X₂_of_shortExact_fppf_of_epi_baseRestrictModule hC h₁ h₃
      (hepi _ hC h₁ h₃)

end BigFppfOver

end AlgebraicGeometry

end
