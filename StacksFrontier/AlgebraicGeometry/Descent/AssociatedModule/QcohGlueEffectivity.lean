module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.RefinementDatum
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.FpqcEffectiveUnconditional
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The effectivity input of Stacks 03DX (1) discharged by Stacks 023T

The gluing step of Stacks 03DX (1) for `τ = fppf` was reduced in
`StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.QcohGlueAssembly` to **two** hypotheses:
the effectivity half of Stacks 023T, spelled out there as

```
∀ {T : Scheme.{u}} (𝒰 : PreZeroHypercover.{u + 1} T),
  𝒰.presieve₀ ∈ Scheme.fpqcPrecoverage.{u} T → ∀ D : QuasicoherentDescentData 𝒰.f, D.IsEffective
```

and the descent datum, `AlgebraicGeometry.BigFppfOver.AssociatedModuleGlueDescentDatum`.  The
first of the two is now a theorem:
`AlgebraicGeometry.QuasicoherentDescentData.isEffective_fpqcPrecoverage` is universe-polymorphic
in the index universe of the covering family, so reading it at `u + 1` — the universe the objects
of `(Sch/S)_fppf` force, as the implementation notes of `QcohGlueAssembly` record — is exactly
that hypothesis.  **This file discharges it**, leaving the descent datum as the only hypothesis of
Stacks 03DX (1)'s essential surjectivity.

## Main results

* `AlgebraicGeometry.BigFppfOver.isEffective_fpqcPrecoverage_siteIndex`: the effectivity
  hypothesis of `QcohGlueAssembly`, as a theorem, at the index universe the big fppf site forces.
* `AlgebraicGeometry.BigFppfOver.essImageAssociatedModuleQcohGlue_of_descentDatum`: **the gluing
  step of Stacks 03DX (1) over the descent datum alone.**
* `AlgebraicGeometry.BigFppfOver.quasicoherentIsEssImageAssociatedModule_of_descentDatum`,
  `…_of_datumOfRefinement` and `…_of_refinedDatum`: **Stacks 03DX (1), essential surjectivity,
  over the descent datum alone**, at each of the three equivalent spellings of that datum.
* `AlgebraicGeometry.BigFppfOver.forall_quasicoherentIsEssImageAssociatedModule_of_descentDatum`:
  the same over every base of the site, which is the shape
  `AlgebraicGeometry.FibredSite.preservesFiniteColimits_quasicoherentInclusion_of_surjective`
  consumes.

## Implementation notes

Nothing here carries a `stacks` attribute, and in particular no `@[stacks 03DX]`.  Every
statement below is still an implication over the descent datum, and a hypothesis is part of a
citation.  Nor is `isEffective_fpqcPrecoverage_siteIndex` tagged `@[stacks 023T]`: it is one
universe instantiation of an assertion already tagged on
`AlgebraicGeometry.QuasicoherentDescentData.isEffective_fpqcPrecoverage`, and a second tag for
the same assertion would duplicate rather than extend the citation.

**Do not read the implications below as a route to the clause.**  Every one of them has a
hypothesis which is *equivalent* to its conclusion — see the docstring of
`AlgebraicGeometry.BigFppfOver.quasicoherentIsEssImageAssociatedModule_of_refinedDatum` — so
discharging one is not easier than proving Stacks 03DX (1) outright.  The datum *is* discharged,
but through the frontier that is not circular,
`AlgebraicGeometry.BigFppfOver.essImage_associatedModuleQcoh_of_agree`, and not through this web:
see `AlgebraicGeometry.BigFppfOver.associatedModuleRefinedDatum` in
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/EffectiveGlueAgreementTransport.lean`.

**What Stacks 023T does not supply.**  The residue is unchanged by this file, and it is not an
effectivity statement.  `AlgebraicGeometry.BigFppfOver.associatedModuleRefinedDatum_iff` and
`AlgebraicGeometry.BigFppfOver.associatedModuleDatumOfRefinement_iff` already show that neither
the refinement of the covering family nor the assembly of the local isomorphisms is part of what
descent supplies; what is left is the construction of the quasi-coherent descent datum out of the
local associated-module data, and its transition isomorphisms
(`AlgebraicGeometry.BigFppfOver.transitionIso`) together with their identity, composition and
pullback laws are unconditional already.  Two things used to stand between those and
`AlgebraicGeometry.BigFppfOver.AssociatedModuleRefinedDatum`, and both were coherence rather than
descent: the term `CategoryTheory.Pseudofunctor.DescentData'` itself, whose constructor exceeds
the kernel's heartbeat budget at these chosen pullbacks (see the implementation notes of
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/MemberDatumPackaging.lean`), and
`AlgebraicGeometry.BigFppfOver.LocalComparisonPseudonatural`.  **Both are now discharged.**  The
first is assembled in the invariant presentation by
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/GlueDescentDatumViaUnprimed.lean`, and
the second is the theorem
`AlgebraicGeometry.BigFppfOver.localComparisonPseudonatural`, proved with no hypothesis in
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SectionsComponentsCocycle.lean`; the
quasi-coherent datum `AlgebraicGeometry.BigFppfOver.memberQcohDatum` and its effectivity
`AlgebraicGeometry.BigFppfOver.isEffective_memberQcohDatum` are therefore unconditional.

The one identity that was left — the agreement, over the fibre products of two members, of the
local isomorphisms that the effectivity of that datum produces, carried as the hypothesis of
`AlgebraicGeometry.BigFppfOver.essImage_associatedModuleQcoh_of_agree` — is now proved too: in the
`objRestrict` spelling by
`AlgebraicGeometry.BigFppfOver.restrictObjRestrictIso_effectiveGlueObjRestrictIso_eq`
(`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/EffectiveGlueAgreement.lean:462`), and in
the `homRestr` spelling by `AlgebraicGeometry.BigFppfOver`
`.homRestr_objRestrictPreimageIso_effectiveGlueObjRestrictIso_eq`
(`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/EffectiveGlueAgreementTransport.lean`).

On the **small étale** site the situation is different again: the residue there,
`AlgebraicGeometry.SmallEtale.EssImageAssociatedModuleGlue`, carries no effectivity hypothesis to
discharge — `AlgebraicGeometry.SmallEtale.essImageAssociatedModuleGlue_iff` shows it is
*equivalent* to the essential surjectivity it reduces, so Stacks 023T has nothing to plug into
there and this file states nothing about `τ = étale`.

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 023T](https://stacks.math.columbia.edu/tag/023T)
* [Stacks Project, Tag 03DV](https://stacks.math.columbia.edu/tag/03DV)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.BigFppfOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The effectivity hypothesis of Stacks 03DX (1), as a theorem.**  Every quasi-coherent
descent datum for an fpqc covering family of an arbitrary scheme, indexed at the universe `u + 1`
of the objects of `(Sch/S)_fppf`, is effective.

This is `AlgebraicGeometry.QuasicoherentDescentData.isEffective_fpqcPrecoverage` — the effectivity
half of Stacks 023T, with no hypothesis — read at the one index universe the big fppf site
forces, and it is the hypothesis `hEff` that
`AlgebraicGeometry.BigFppfOver.essImageAssociatedModuleQcohGlue_of_isEffective` and its companions
carry. -/
@[sga "1 VIII 1.1" "partial", sga "1 VIII 1.3" "more general"]
public theorem isEffective_fpqcPrecoverage_siteIndex {T : Scheme.{u}}
    (𝒰 : PreZeroHypercover.{u + 1} T) (h𝒰 : 𝒰.presieve₀ ∈ Scheme.fpqcPrecoverage.{u} T)
    (D : QuasicoherentDescentData 𝒰.f) : D.IsEffective :=
  QuasicoherentDescentData.isEffective_fpqcPrecoverage 𝒰 h𝒰 D

/-- **The gluing step of Stacks 03DX (1) for `τ = fppf`, over the descent datum alone.**  A sheaf
of modules on `(Sch/S)_fppf` whose restriction to the big fppf site of the scheme of each member
of a covering family of the final object is the associated module of a quasi-coherent sheaf there
is itself an `𝓕^a`.

This is `AlgebraicGeometry.BigFppfOver.essImageAssociatedModuleQcohGlue_of_isEffective` with its
effectivity hypothesis discharged by `isEffective_fpqcPrecoverage_siteIndex`. -/
public theorem essImageAssociatedModuleQcohGlue_of_descentDatum
    (hD : AssociatedModuleGlueDescentDatum B S hS) :
    EssImageAssociatedModuleQcohGlue B S hS :=
  essImageAssociatedModuleQcohGlue_of_isEffective B S hS
    (fun 𝒰 h𝒰 D => isEffective_fpqcPrecoverage_siteIndex 𝒰 h𝒰 D) hD

/-- **Stacks 03DX (1), essential surjectivity, for `τ = fppf`, over the descent datum alone.**
Every quasi-coherent `𝒪`-module on the big fppf site of `S` is isomorphic to `𝓕^a` for a
quasi-coherent `𝒪_S`-module `𝓕`.

This is `AlgebraicGeometry.BigFppfOver.quasicoherentIsEssImageAssociatedModule_of_isEffective`
with its effectivity hypothesis discharged.  It is **not** tagged `@[stacks 03DX]`: the descent
datum is still a hypothesis. -/
public theorem quasicoherentIsEssImageAssociatedModule_of_descentDatum
    (hD : AssociatedModuleGlueDescentDatum B S hS) :
    QuasicoherentIsEssImageAssociatedModule B S hS :=
  quasicoherentIsEssImageAssociatedModule_of_isEffective B S hS
    (fun 𝒰 h𝒰 D => isEffective_fpqcPrecoverage_siteIndex 𝒰 h𝒰 D) hD

/-- **Stacks 03DX (1), essential surjectivity, over every base of the big fppf site**, over the
descent datum at each base alone.  This is the shape in which
`AlgebraicGeometry.FibredSite.preservesFiniteColimits_quasicoherentInclusion_of_surjective`
consumes essential surjectivity: its hypothesis quantifies over every scheme of the site, not
only over `S`. -/
public theorem forall_quasicoherentIsEssImageAssociatedModule_of_descentDatum
    (hD : ∀ (T : Scheme.{u}) (hT : B.Contains T), AssociatedModuleGlueDescentDatum B T hT) :
    ∀ (T : Scheme.{u}) (hT : B.Contains T), QuasicoherentIsEssImageAssociatedModule B T hT :=
  fun T hT => quasicoherentIsEssImageAssociatedModule_of_descentDatum B T hT (hD T hT)

/-- **Stacks 03DX (1), essential surjectivity, over the two-family form of the descent datum
alone.**  `AlgebraicGeometry.BigFppfOver.AssociatedModuleDatumOfRefinement` is the descent datum
with the refinement of the covering family already handed to it; it implies the descent datum by
`AlgebraicGeometry.BigFppfOver.associatedModuleGlueDescentDatum_of_datumOfRefinement`, which is
unconditional. -/
public theorem quasicoherentIsEssImageAssociatedModule_of_datumOfRefinement
    (hD : AssociatedModuleDatumOfRefinement B S hS) :
    QuasicoherentIsEssImageAssociatedModule B S hS :=
  quasicoherentIsEssImageAssociatedModule_of_descentDatum B S hS
    (associatedModuleGlueDescentDatum_of_datumOfRefinement B S hS hD)

/-- **Stacks 03DX (1), essential surjectivity, over the one-family form of the descent datum
alone.**  `AlgebraicGeometry.BigFppfOver.AssociatedModuleRefinedDatum` asks for the datum on a
single family which covers the final object of `(Sch/S)_fppf` and whose structure morphisms are
already an fpqc covering family of `S`; it is *equivalent* to the descent datum by
`AlgebraicGeometry.BigFppfOver.associatedModuleRefinedDatum_iff`.

With Stacks 023T in hand, essential surjectivity of `𝓕 ↦ 𝓕^a` on `(Sch/S)_fppf` stands on the
construction of a quasi-coherent descent datum out of the local associated-module data, and on
nothing else.

**This is not a reduction that can be discharged, because its hypothesis is equivalent to its
conclusion.**  `AlgebraicGeometry.BigFppfOver`
`.associatedModuleGlueDescentDatum_of_quasicoherentIsEssImage`
proves the descent datum *from* the essential surjectivity it is used to prove, and
`AlgebraicGeometry.BigFppfOver.associatedModuleRefinedDatum_iff` carries that back to the
one-family form; so each of the three spellings of the datum is logically equivalent to
`AlgebraicGeometry.BigFppfOver.QuasicoherentIsEssImageAssociatedModule`, and proving one of them
is exactly as hard as proving the clause.  The non-circular frontier is elsewhere:
`AlgebraicGeometry.BigFppfOver.essImage_associatedModuleQcoh_of_agree_app`, whose hypothesis is a
componentwise identity at a fixed effectivity witness rather than a restatement of the
conclusion.  Its `objRestrict` form is the theorem
`AlgebraicGeometry.BigFppfOver.restrictObjRestrictIso_effectiveGlueObjRestrictIso_eq`, proved with
no hypothesis, and the sections-level transport separating the two is `AlgebraicGeometry`
`.BigFppfOver.objRestrictPreimageIso_hom_val_app_over_map`, which is what makes
`AlgebraicGeometry.BigFppfOver.associatedModuleRefinedDatum` in
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/EffectiveGlueAgreementTransport.lean`
a theorem. -/
public theorem quasicoherentIsEssImageAssociatedModule_of_refinedDatum
    (hD : AssociatedModuleRefinedDatum B S hS) :
    QuasicoherentIsEssImageAssociatedModule B S hS :=
  quasicoherentIsEssImageAssociatedModule_of_descentDatum B S hS
    ((associatedModuleRefinedDatum_iff B S hS).1 hD)

end AlgebraicGeometry.BigFppfOver

end
