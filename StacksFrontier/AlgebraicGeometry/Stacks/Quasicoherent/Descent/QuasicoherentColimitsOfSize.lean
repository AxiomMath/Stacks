module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Descent.AssociatedModuleColimits
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Descent.Colimits
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Descent.QuasicoherentColimits
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Descent.QuasicoherentTransfer

/-!
# Colimits of quasi-coherent modules on a big site, at the size of the site

Stacks 0GNC says that quasi-coherence of modules on `(Sch/S)_τ` is preserved by direct sums,
by arbitrary colimits and by cokernels, and Stacks 0GNE (1) and 06WN (1) say that the resulting
colimits are the colimits of all modules.  The source proves all of this by one move: write
each module as `𝓖^a` and transfer the corresponding facts about quasi-coherent modules on `S`
along Lemma 06VE.

That transfer is
`SheafOfModules.isClosedUnderColimitsOfShape_isQuasicoherentOnSite`, which asks for a fully
faithful functor out of a category with the colimits, preserving them, whose essential image is
the quasi-coherent modules.  This file instantiates it at the functor `𝓕 ↦ 𝓕^a` of the big
fppf site of `S`, `AlgebraicGeometry.BigFppfOver.associatedModuleQcoh`: its colimit preservation
is Stacks 06VE (2), (3), proved in
`StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Descent.AssociatedModuleColimits`, and its
source category has the colimits by the same file.  What remains are exactly the two facts the
source gets from Descent, Proposition 03DX and Lemma 03DV, and they are carried as named
hypotheses:

* `AlgebraicGeometry.BigFppfOver.AssociatedModuleIsQuasicoherent` is Stacks 03DV — the
  associated module of a quasi-coherent `𝒪_S`-module is quasi-coherent on `(Sch/S)_fppf`;
* `AlgebraicGeometry.BigFppfOver.QuasicoherentIsEssImageAssociatedModule` is Stacks 03DX (1) —
  every quasi-coherent module on `(Sch/S)_fppf` is an `𝓕^a`;

together with full faithfulness of `𝓕 ↦ 𝓕^a`, which is Stacks 06VE (1) and 0GN7.

## Main definitions

* `AlgebraicGeometry.BigFppfOver.AssociatedModuleIsQuasicoherent` and
  `AlgebraicGeometry.BigFppfOver.QuasicoherentIsEssImageAssociatedModule`: the two hypotheses
  above, named so that the results below can be read off against their sources.

## Main results

* `AlgebraicGeometry.BigFppfOver.isClosedUnderColimitsOfShape_isQuasicoherentOnSite`:
  **Stacks 0GNC (2)** for `τ = fppf`, over those hypotheses — quasi-coherence on `(Sch/S)_fppf`
  is closed under colimits of shape `K`.
* `AlgebraicGeometry.BigFppfOver.isClosedUnderColimitsOfShape_discrete_isQuasicoherentOnSite`
  and its `CategoryTheory.Limits.WalkingParallelPair` companion
  `AlgebraicGeometry.BigFppfOver`
  `.isClosedUnderColimitsOfShape_walkingParallelPair_isQuasicoherentOnSite`:
  **Stacks 0GNC (1)** and **(3)**, the discrete and parallel-pair shapes of the previous result,
  which is how the source derives them.
* `AlgebraicGeometry.BigFppfOver.closedUnderColimitsOfSize_isQuasicoherentOnSite`: the same
  over every shape `K : Type u`, which is the hypothesis the next two results consume.
* `AlgebraicGeometry.BigFppfOver.hasColimitsOfSize_quasicoherentOnSite`: **Stacks 0GNE (1),
  the existence half** — `QCoh((Sch/S)_fppf, 𝒪)` has colimits.
* `AlgebraicGeometry.BigFppfOver.preservesColimitsOfSize_quasicoherentOnSite_ι`: **Stacks
  0GNE (1), the comparison with `Mod((Sch/S)_fppf, 𝒪)`** — those colimits are the colimits of
  all modules on the big fppf site.
* `AlgebraicGeometry.FibredSite.hasColimitsOfSize_quasicoherentModules` and
  `AlgebraicGeometry.FibredSite.preservesColimitsOfSize_quasicoherentInclusion`: the same two
  statements on the associated fppf site of an essentially small category fibred in groupoids,
  which is **Stacks 06WN (1)** for the fppf topology, over the closure hypothesis.

## Implementation notes

Every "has colimits" here is `CategoryTheory.Limits.HasColimitsOfSize.{u, u}` and every
"colimits agree" is `CategoryTheory.Limits.PreservesColimitsOfSize.{u, u}`, with the index
universe equal to the universe of the site.  A bare `CategoryTheory.Limits.HasColimits` would
bind the index universe to the hom universe of the category of module sheaves, which is
unrelated to the universe of the site: on the big fppf site over `S : Scheme.{u}` the site
category lives in `Type (u + 1)` and the source's "has colimits" means small colimits indexed
at the size of `u`.  This is the convention this library already uses for the analogous clause
of Stacks 09JJ.

Quasi-coherence on the big site is `SheafOfModules.IsQuasicoherentOnSite`, the predicate of
Stacks 03DL (6) phrased through `SheafOfModules.HasGlobalPresentation`, and *not* Mathlib's
`SheafOfModules.IsQuasicoherent`.  The choice is load-bearing rather than cosmetic: the two
predicates place their presentations in different universes — over `S : Scheme.{u}` the
presentation universe of `HasGlobalPresentation` on the big site is `u + 1`, while Mathlib's
`SheafOfModules.free` is indexed by `Type u` — so a statement in one notion is not a statement
in the other, and only the first is the notion the big-site categories of this library are built
from (`AlgebraicGeometry.FibredSite.quasicoherentModules`, Stacks 06WG).  The source category
`QCoh(𝒪_S)`, by contrast, uses Mathlib's predicate, which is where the closure of
quasi-coherence under colimits on a scheme is proved; the two sides of
`AlgebraicGeometry.BigFppfOver.associatedModuleQcoh` therefore use different predicates by
design, and the hypothesis `AssociatedModuleIsQuasicoherent` below is exactly the bridge between
them — which is why it is Stacks 03DV and not a formality.

Nothing here carries a `stacks` attribute.  Each statement is conditional on Stacks 03DV and
Stacks 03DX (1), neither of which this library has, so a tag would report the clause as covered
when what is proved is the implication.  The two hypotheses are isolated as `abbrev`s precisely
so that the attributes can be placed, with no change to any proof below, as soon as they are
discharged.

What is *not* asserted, and why: Stacks 0GNE (1) and 06WN (1) also claim that the colimits
agree with those computed in `Mod((Sch/S)_Zar, 𝒪)` and `Mod((Sch/S)_étale, 𝒪)`.  Those colimits
are taken in a different category — sheaves for a coarser topology, where sheafification is a
different functor — so their agreement is not a formal consequence of the results below.  **The
comparison itself is, however, available**, and the sentence that stood here saying it is not was
stale: `AlgebraicGeometry.BigFppfOver.restrictTopologyAssociatedModuleQcohIso`
(`StacksFrontier/AlgebraicGeometry/Descent/QuasiCoherentTopologiesTwo/TopologyIndependence.lean`
`:728`) identifies the associated-module functor of `(Sch/S)_τ` with the fppf one read for the
coarser topology, as an isomorphism of functors, and
`AlgebraicGeometry.BigFppfOver.isColimitMapCoconeRestrictTopologyAssociatedModuleQcoh`
(same file, `:825`, tagged `@[stacks 0GNE]`) concludes that the fppf colimit cocone of a diagram
of associated modules is a colimit cocone in `Mod((Sch/S)_τ, 𝒪)` for every one of the five
topologies.  That file is downstream of this one, which is why the statement is made there and
not here.  The source's own phrasing needs one thing more — the reduction of an *arbitrary*
diagram of quasi-coherent modules on the big site to a diagram of associated modules, which is
the essential surjectivity hypothesis
`AlgebraicGeometry.BigFppfOver.QuasicoherentIsEssImageAssociatedModule` below — and **for
0GNE (1) that is now done**: the hypothesis is discharged by
`AlgebraicGeometry.BigFppfOver.quasicoherentIsEssImageAssociatedModule'` and the three
halves of the clause are stated unconditionally, for an arbitrary diagram and at every `τ`, in
`StacksFrontier/AlgebraicGeometry/Descent/QuasiCoherentTopologiesTwo/BigSiteColimitAgreement.lean`
(`…hasColimitsOfSize_quasicoherentOnSite_fppf`,
`…preservesColimitsOfSize_quasicoherentOnSite_ι_fppf` and
`…preservesColimitsOfSize_quasicoherentOnSite_ι_comp_restrictTopology`).  **06WN (1) is not
covered by that**: its site is the associated `τ`-site of a category fibred in groupoids, and the
reduction used is the equivalence of Stacks 03DX (1) over a scheme.  (An earlier
version of this paragraph said "the library has no
structure sheaf for the four big sites coarser than fppf, so the statement cannot yet be made".
That is **false** — `AlgebraicGeometry.FibredSite.baseStructureSheaf` supplies one for every
`AlgebraicGeometry.SiteKind`, with `baseRingStructureSheaf` its ring-sheaf companion and
`baseRingStructureSheaf_obj` an `rfl`.  **Nor is the functor missing any longer**: `structureMap`
has the analogue `AlgebraicGeometry.BigFppfOver.baseStructureMap`
(`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/BaseRingedSite.lean:206`) at every `τ`,
and the associated-module functor `AlgebraicGeometry.BigFppfOver.baseAssociatedModule`
(`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/BaseRingedSite.lean:232`), with
`baseAssociatedModule .fppf = associatedModule` by `rfl`.  What restricts the result below to
fppf is that its proof routes through `associatedModuleIsoSections`, whose covering steps are
taken at the fppf topology — friction, not an obstruction.)

## References

* [Stacks Project, Tag 0GNC](https://stacks.math.columbia.edu/tag/0GNC)
* [Stacks Project, Tag 0GNE](https://stacks.math.columbia.edu/tag/0GNE)
* [Stacks Project, Tag 06WN](https://stacks.math.columbia.edu/tag/06WN)
* [Stacks Project, Tag 06VE](https://stacks.math.columbia.edu/tag/06VE)
* [Stacks Project, Tag 03DV](https://stacks.math.columbia.edu/tag/03DV)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe uK vK u

namespace AlgebraicGeometry

namespace BigFppfOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 03DV at the big fppf site of `S`**, as a hypothesis: the associated module of a
quasi-coherent `𝒪_S`-module is quasi-coherent on `(Sch/S)_fppf`. -/
public abbrev AssociatedModuleIsQuasicoherent : Prop :=
  ∀ M : (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory,
    ((associatedModuleQcoh B S hS).obj M).IsQuasicoherentOnSite

/-- **Stacks 03DX (1) at the big fppf site of `S`**, as a hypothesis: every quasi-coherent
module on `(Sch/S)_fppf` is isomorphic to an `𝓕^a` for a quasi-coherent `𝒪_S`-module `𝓕`. -/
public abbrev QuasicoherentIsEssImageAssociatedModule : Prop :=
  SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u} (structureSheaf B S hS) ≤
    (associatedModuleQcoh B S hS).essImage

/-- **Stacks 0GNC (1), (2), (3)** for `τ = fppf`, over Stacks 03DV, Stacks 03DX (1) and full
faithfulness of `𝓕 ↦ 𝓕^a`.  Quasi-coherence of modules on the big fppf site of `S` is closed
under colimits of shape `K`; the three clauses of the source are the discrete, the general and
the parallel-pair shapes.

This is the transfer the source performs with Lemma 06VE: the colimit is computed in
`QCoh(𝒪_S)`, where quasi-coherence is closed under colimits, and carried across by
`𝓕 ↦ 𝓕^a`, which preserves colimits because it is a left adjoint. -/
public theorem isClosedUnderColimitsOfShape_isQuasicoherentOnSite
    [(associatedModuleQcoh B S hS).Full] [(associatedModuleQcoh B S hS).Faithful]
    (K : Type uK) [Category.{uK} K]
    [∀ R : CommRingCat.{u}, HasColimitsOfShape K (ModuleCat.{u} R)]
    [HasColimitsOfShape K (SheafOfModules.{u} S.ringCatSheaf)]
    (hF : AssociatedModuleIsQuasicoherent B S hS)
    (hsurj : QuasicoherentIsEssImageAssociatedModule B S hS) :
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (structureSheaf B S hS)).IsClosedUnderColimitsOfShape K := by
  have := hasColimitsOfShape_isQuasicoherent S K
  have := preservesColimitsOfShape_associatedModuleQcoh B S hS K
  exact SheafOfModules.isClosedUnderColimitsOfShape_isQuasicoherentOnSite
    (associatedModuleQcoh B S hS) K hF hsurj

/-- **Stacks 0GNC (1)** for `τ = fppf`, over the same hypotheses: a direct sum of quasi-coherent
modules on the big fppf site of `S` is quasi-coherent.  A direct sum is a colimit over a
discrete index category. -/
public theorem isClosedUnderColimitsOfShape_discrete_isQuasicoherentOnSite
    [(associatedModuleQcoh B S hS).Full] [(associatedModuleQcoh B S hS).Faithful]
    (I : Type u)
    (hF : AssociatedModuleIsQuasicoherent B S hS)
    (hsurj : QuasicoherentIsEssImageAssociatedModule B S hS) :
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (structureSheaf B S hS)).IsClosedUnderColimitsOfShape (Discrete I) :=
  isClosedUnderColimitsOfShape_isQuasicoherentOnSite B S hS (Discrete I) hF hsurj

/-- **Stacks 0GNC (3)** for `τ = fppf`, over the same hypotheses: the cokernel of a morphism of
quasi-coherent modules on the big fppf site of `S` is quasi-coherent.  A cokernel is a colimit
over `CategoryTheory.Limits.WalkingParallelPair`, which is how the source argues it. -/
public theorem isClosedUnderColimitsOfShape_walkingParallelPair_isQuasicoherentOnSite
    [(associatedModuleQcoh B S hS).Full] [(associatedModuleQcoh B S hS).Faithful]
    (hF : AssociatedModuleIsQuasicoherent B S hS)
    (hsurj : QuasicoherentIsEssImageAssociatedModule B S hS) :
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (structureSheaf B S hS)).IsClosedUnderColimitsOfShape WalkingParallelPair :=
  isClosedUnderColimitsOfShape_isQuasicoherentOnSite B S hS WalkingParallelPair hF hsurj

/-- Closure of quasi-coherence on the big fppf site of `S` under colimits of every shape
`K : Type u`, taken over all shapes.  This is the hypothesis of
`SheafOfModules.hasColimitsOfSize_quasicoherentOnSite`, and it is the previous result
instantiated at the size of the site. -/
public theorem closedUnderColimitsOfSize_isQuasicoherentOnSite
    [(associatedModuleQcoh B S hS).Full] [(associatedModuleQcoh B S hS).Faithful]
    (hF : AssociatedModuleIsQuasicoherent B S hS)
    (hsurj : QuasicoherentIsEssImageAssociatedModule B S hS) :
    SheafOfModules.ClosedUnderColimitsOfSize.{u, u + 1, u, u, u} (structureSheaf B S hS) :=
  fun K _ ↦ isClosedUnderColimitsOfShape_isQuasicoherentOnSite B S hS K hF hsurj

/-- **Stacks 0GNE (1), the existence half.**  The category of quasi-coherent modules on the big
fppf site of `S` has all colimits indexed at the size of the site: the ambient category of
module sheaves has them, the big fppf site being essentially small, and quasi-coherence is
closed under them. -/
public theorem hasColimitsOfSize_quasicoherentOnSite
    (hclosed : SheafOfModules.ClosedUnderColimitsOfSize.{u, u + 1, u, u, u}
      (structureSheaf B S hS)) :
    HasColimitsOfSize.{u, u}
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (structureSheaf B S hS)).FullSubcategory := by
  have : HasColimitsOfSize.{u, u} (SheafOfModules.{u} (structureSheaf B S hS)) :=
    hasColimits_sheafOfModules_structureSheaf B S hS
  exact SheafOfModules.hasColimitsOfSize_quasicoherentOnSite hclosed

/-- **Stacks 0GNE (1), the comparison with the modules of the big fppf site.**  Colimits of
quasi-coherent modules on `(Sch/S)_fppf` are the colimits of the same diagram taken in all
modules on `(Sch/S)_fppf`: the inclusion preserves them. -/
public theorem preservesColimitsOfSize_quasicoherentOnSite_ι
    (hclosed : SheafOfModules.ClosedUnderColimitsOfSize.{u, u + 1, u, u, u}
      (structureSheaf B S hS)) :
    PreservesColimitsOfSize.{u, u}
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (structureSheaf B S hS)).ι := by
  have : HasColimitsOfSize.{u, u} (SheafOfModules.{u} (structureSheaf B S hS)) :=
    hasColimits_sheafOfModules_structureSheaf B S hS
  exact SheafOfModules.preservesColimitsOfSize_quasicoherentOnSite_ι hclosed

end BigFppfOver

namespace FibredSite

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type (u + 1)} [Category.{u} 𝒳] [EssentiallySmall.{u} 𝒳]
  (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)

/-- **Stacks 06WN (1), the existence half**, for the fppf topology and over the closure of
quasi-coherence under colimits.  Quasi-coherent modules on the associated fppf site of an
essentially small category fibred in groupoids have all colimits indexed at the size of the
site.

This is the `CategoryTheory.Limits.HasColimitsOfSize` form of
`AlgebraicGeometry.FibredSite.hasColimitsOfShape_quasicoherentModules`, which is the spelling
the source's "has colimits" asks for: the index categories range over `Type u`, the universe of
the site, not over the hom universe of the category of module sheaves. -/
public theorem hasColimitsOfSize_quasicoherentModules
    (hclosed : SheafOfModules.ClosedUnderColimitsOfSize.{u, u + 1, u, u, u}
      (ringStructureSheafCore B S hS p hp .fppf)) :
    HasColimitsOfSize.{u, u} (quasicoherentModules.{u, u + 1, u, u} B S hS p hp) := by
  have : HasColimitsOfSize.{u, u}
      (SheafOfModules.{u} (ringStructureSheafCore B S hS p hp .fppf)) :=
    hasColimits_sheafOfModules_ringStructureSheafCore B S hS p hp .fppf
  exact SheafOfModules.hasColimitsOfSize_quasicoherentOnSite hclosed

/-- **Stacks 06WN (1), the comparison with the fppf modules**, over the closure of
quasi-coherence under colimits: the inclusion of the quasi-coherent modules into all module
sheaves on the associated fppf site preserves colimits indexed at the size of the site. -/
public theorem preservesColimitsOfSize_quasicoherentInclusion
    (hclosed : SheafOfModules.ClosedUnderColimitsOfSize.{u, u + 1, u, u, u}
      (ringStructureSheafCore B S hS p hp .fppf)) :
    PreservesColimitsOfSize.{u, u}
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (ringStructureSheafCore B S hS p hp .fppf)).ι := by
  have : HasColimitsOfSize.{u, u}
      (SheafOfModules.{u} (ringStructureSheafCore B S hS p hp .fppf)) :=
    hasColimits_sheafOfModules_ringStructureSheafCore B S hS p hp .fppf
  exact SheafOfModules.preservesColimitsOfSize_quasicoherentOnSite_ι hclosed

end FibredSite

end AlgebraicGeometry

end
