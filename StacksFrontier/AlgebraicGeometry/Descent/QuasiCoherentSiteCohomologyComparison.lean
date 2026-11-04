module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CechComparison.BigSiteQuasiCoherentCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CechComparison.SmallEtaleQuasiCoherentCohomology
public import StacksFrontier.AlgebraicGeometry.Topologies.Zariski.SmallZariskiQuasiCoherentCohomology
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.CohomologyAtTheTerminalObject
public import StacksCore.Tactic.StacksAttribute

/-!
# Cohomology of a quasi-coherent module is the cohomology of its associated module on a site

Let `S` be a scheme, let `ℱ` be a quasi-coherent `𝒪_S`-module and let `ℱᵃ` be the associated
module of [Stacks, Tag 03DU].  This file states the two clauses of [Stacks, Tag 03DW] in the
shape the source states them, namely as comparisons of the cohomology **of a site**:

  `H^q(S, ℱ) ≅ H^q((Sch/S)_τ, ℱᵃ)`      for `τ ∈ {Zariski, étale, smooth, syntomic, fppf}`,
  `H^q(S, ℱ) ≅ H^q(S_Zar, ℱᵃ) ≅ H^q(S_étale, ℱᵃ)`,

in every degree `q`.

## Main definitions

* `AlgebraicGeometry.bigOverQuasiCoherentSiteCohomologyAddEquiv`: **clause (1) of
  [Stacks, Tag 03DW]**, for all five `τ` at once.
* `AlgebraicGeometry.smallZariskiQuasiCoherentSiteCohomologyAddEquiv`: the first link of
  **clause (2)**, `H^q(S, ℱ) ≅ H^q(S_Zar, ℱᵃ)`.
* `AlgebraicGeometry.smallEtaleQuasiCoherentSiteCohomologyAddEquiv`: the second link of
  **clause (2)**, `H^q(S, ℱ) ≅ H^q(S_étale, ℱᵃ)`.
* `AlgebraicGeometry.smallZariskiEtaleQuasiCoherentSiteCohomologyAddEquiv`: the composite
  `H^q(S_Zar, ℱᵃ) ≅ H^q(S_étale, ℱᵃ)`, the middle equality of clause (2) as the source writes
  the chain.

## Implementation notes

The mathematics is already in the library, in the three modules

* `StacksFrontier.AlgebraicGeometry.EtaleCohomology.CechComparison.BigSiteQuasiCoherentCohomology`,
* `StacksFrontier.AlgebraicGeometry.Topologies.Zariski.SmallZariskiQuasiCoherentCohomology`,
* `StacksFrontier.AlgebraicGeometry.EtaleCohomology.CechComparison.SmallEtaleQuasiCoherentCohomology`,

each of which proves its case as a comparison of `CategoryTheory.Sheaf.H'`, Mathlib's cohomology
*over an object* of a site, at the object that the whole of `S` becomes.  What this file adds is
the one step from there to the statement of the tag: for a **terminal** object the two models of
sheaf cohomology agree, by `Stacks.Cohomology.TerminalCohomology.h'AddEquivH`, and the objects
in question are terminal —

* `AlgebraicGeometry.isTerminal_opensBelowToOver_top` on a localized big `τ`-site,
* `AlgebraicGeometry.isTerminal_opensToSmallZariski_top` on the small Zariski site,
* `AlgebraicGeometry.isTerminal_opensToEtale_top` on the small étale site,

and `Stacks.Cohomology.TerminalCohomology.topIsTerminal` on the Zariski site of opens of `S`.
So each statement below is a terminal-object comparison, the corresponding `Sheaf.H'`
isomorphism, and a second terminal-object comparison, composed.

`CategoryTheory.HasExt` and `CategoryTheory.EnoughInjectives` are `Prop`-valued classes, so the
witnesses that the three source modules bake into the types of their conclusions and the ones
supplied here are definitionally equal and no transport is needed; only the `Ext` universe has to
match, and it is the morphism universe `u` of each site on both sides throughout.  The local
instances of each section are therefore exactly those of the module it consumes, including the
priority flip of `CategoryTheory.IsGrothendieckAbelian.hasExt` that the small étale site needs
in order to measure its `Ext` groups at `u` rather than at `u + 1`.

**The `@[stacks 03DW]` attribute is attached to the three links.**  The covering set of the tag
is one declaration per site: `bigOverQuasiCoherentSiteCohomologyAddEquiv` for clause (1), whose
`τ` is a bound variable so that the one declaration covers all five big sites, together with
`smallZariskiQuasiCoherentSiteCohomologyAddEquiv` and
`smallEtaleQuasiCoherentSiteCohomologyAddEquiv` for the two links of clause (2).  These do not
retire the tag from the three `Sheaf.H'` carriers it already sits on: those are the comparison
over an *arbitrary* open of `S` specialized to `⊤`, a strictly stronger statement than the tag,
and each remains part of the covering set of [Stacks, Tag 03P2] as well.

No `@[stacks 03P2]` attribute is attached here.  That tag's `𝒞` ranges over the big `τ`-sites
and `S_étale` and does not include `S_Zar`, and its carriers are the two `Sheaf.H'` declarations
already in the library.

## References

* [Stacks Project, Tag 020T](https://stacks.math.columbia.edu/tag/020T)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Adequate
open Stacks.Cohomology.TerminalCohomology
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-! ### Clause (1): the five big sites -/

section BigSite

variable (S : Scheme.{u}) (F : S.Modules) [F.IsQuasicoherent] (τ : CoveringTopology)
  (B : BigSite.{u} τ) (hS : S.size < cutoff τ B)

attribute [local instance] Stacks.Topology.hasExt_sheafOpens
  Stacks.Topology.enoughInjectives_sheafOpens
  Stacks.Cohomology.FreeYonedaUnivLE.enoughInjectives_essentiallySmallSite
  Stacks.Cohomology.FreeYonedaUnivLE.hasExt_essentiallySmallSite

/-- **[Stacks, Tag 03DW], clause (1).**  Let `S` be a scheme, let `ℱ` be a quasi-coherent
`𝒪_S`-module and let `τ ∈ {Zariski, étale, smooth, syntomic, fppf}`.  In every degree `q` there
is a canonical isomorphism

```
H^q(S, ℱ)  ≅  H^q((Sch/S)_τ, ℱᵃ),
```

the right-hand side being the cohomology of the localized big `τ`-site of `S` with values in the
associated module of [Stacks, Tag 03DU].

`τ` is a bound variable, so this one declaration is all five topologies.  It is
`AlgebraicGeometry.bigOverQuasiCoherentGlobalCohomologyIso` — the same comparison stated for
cohomology over the object of the site that `⊤` becomes — read through the identification of
cohomology over a terminal object with cohomology of the site, on both sides. -/
@[stacks 03DW "clause (1), in EVERY degree q and for all five τ at once (τ is a bound \
variable), in the source's own shape: both sides are the cohomology of a SITE, \
CategoryTheory.Sheaf.H, and not cohomology over an object of it.  The Sheaf.H' carrier \
bigOverQuasiCoherentGlobalCohomologyIso states the same comparison over the object of the big \
site that ⊤ becomes; this is that statement composed with the terminal-object identification \
Stacks.Cohomology.TerminalCohomology.h'AddEquivH on both sides, the two objects being terminal \
by topIsTerminal and isTerminal_opensBelowToOver_top.  Clause (2) is \
smallZariskiQuasiCoherentSiteCohomologyAddEquiv together with \
smallEtaleQuasiCoherentSiteCohomologyAddEquiv"]
public def bigOverQuasiCoherentSiteCohomologyAddEquiv (p : ℕ) :
    Sheaf.H.{u} ((SheafOfModules.toSheaf S.ringCatSheaf).obj F) p ≃+
      Sheaf.H.{u} (bigOverAssociatedSheaf S F τ B hS) p :=
  (h'AddEquivH (Opens.grothendieckTopology ↥S)
        ((SheafOfModules.toSheaf S.ringCatSheaf).obj F) p ⊤ topIsTerminal).symm.trans
    (((bigOverQuasiCoherentGlobalCohomologyIso S F τ B hS p).addCommGroupIsoToAddEquiv).trans
      (h'AddEquivH (overTopology τ B S hS) (bigOverAssociatedSheaf S F τ B hS) p _
        (isTerminal_opensBelowToOver_top (κ := cutoff τ B) hS)))

end BigSite

/-! ### Clause (2), first link: the small Zariski site -/

section SmallZariski

variable (B : BigZariskiSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (F : S.Modules)
  [F.IsQuasicoherent]

attribute [local instance] Stacks.Topology.hasExt_sheafOpens
  Stacks.Topology.enoughInjectives_sheafOpens
  Stacks.Cohomology.FreeYonedaUnivLE.enoughInjectives_essentiallySmallSite
  Stacks.Cohomology.FreeYonedaUnivLE.hasExt_essentiallySmallSite

/-- **[Stacks, Tag 03DW], clause (2), the small Zariski link.**  For a scheme `S` in a big
Zariski site, a quasi-coherent `𝒪_S`-module `ℱ` and a degree `q` there is a canonical
isomorphism

```
H^q(S, ℱ)  ≅  H^q(S_Zar, ℱᵃ),
```

the right-hand side being the cohomology of the small Zariski site of [Stacks, Tag 020T] (2)
with values in the associated module of [Stacks, Tag 03DU] (4) at `τ = Zariski`.

This is `AlgebraicGeometry.smallZariskiQuasiCoherentGlobalCohomologyIso` read through the
identification of cohomology over a terminal object with cohomology of the site. -/
@[stacks 03DW "clause (2), the small ZARISKI link H^q(S, F) = H^q(S_Zar, Fᵃ), in EVERY degree \
q, in the source's own shape: both sides are the cohomology of a SITE, CategoryTheory.Sheaf.H.  \
The Sheaf.H' carrier smallZariskiQuasiCoherentGlobalCohomologyIso states the same comparison \
over the object of S_Zar that ⊤ becomes; this is that statement composed with \
Stacks.Cohomology.TerminalCohomology.h'AddEquivH on both sides, the two objects being terminal \
by topIsTerminal and isTerminal_opensToSmallZariski_top.  The other link of clause (2) is \
smallEtaleQuasiCoherentSiteCohomologyAddEquiv and clause (1) is \
bigOverQuasiCoherentSiteCohomologyAddEquiv"]
public def smallZariskiQuasiCoherentSiteCohomologyAddEquiv (p : ℕ) :
    Sheaf.H.{u} ((SheafOfModules.toSheaf S.ringCatSheaf).obj F) p ≃+
      Sheaf.H.{u} (smallZariskiAssociatedSheaf B S hS F) p :=
  (h'AddEquivH (Opens.grothendieckTopology S.carrier)
        ((SheafOfModules.toSheaf S.ringCatSheaf).obj F) p ⊤ topIsTerminal).symm.trans
    (((smallZariskiQuasiCoherentGlobalCohomologyIso B S hS F p).addCommGroupIsoToAddEquiv).trans
      (h'AddEquivH (SmallZariski.topology B S hS) (smallZariskiAssociatedSheaf B S hS F) p _
        (isTerminal_opensToSmallZariski_top B S hS)))

end SmallZariski

/-! ### Clause (2), second link: the small étale site -/

section SmallEtale

variable (S : Scheme.{u}) (F : S.Modules) [F.IsQuasicoherent]

attribute [local instance] Stacks.Topology.hasExt_sheafOpens
  Stacks.Topology.enoughInjectives_sheafOpens

attribute [local instance 2000] CategoryTheory.IsGrothendieckAbelian.hasExt in
/-- **[Stacks, Tag 03DW], clause (2), the small étale link.**  For a scheme `S`, a
quasi-coherent `𝒪_S`-module `ℱ` and a degree `q` there is a canonical isomorphism

```
H^q(S, ℱ)  ≅  H^q(S_étale, ℱᵃ),
```

the right-hand side being the cohomology of the small étale site of `S` with values in the
associated module of [Stacks, Tag 03DU].

This is `AlgebraicGeometry.smallEtaleQuasiCoherentGlobalCohomologyIso` read through the
identification of cohomology over a terminal object with cohomology of the site. -/
@[stacks 03DW "clause (2), the small ÉTALE link H^q(S, F) = H^q(S_étale, Fᵃ), in EVERY degree \
q, in the source's own shape: both sides are the cohomology of a SITE, CategoryTheory.Sheaf.H.  \
The Sheaf.H' carrier smallEtaleQuasiCoherentGlobalCohomologyIso states the same comparison over \
the object of S_étale that ⊤ becomes; this is that statement composed with \
Stacks.Cohomology.TerminalCohomology.h'AddEquivH on both sides, the two objects being terminal \
by topIsTerminal and isTerminal_opensToEtale_top.  The other link of clause (2) is \
smallZariskiQuasiCoherentSiteCohomologyAddEquiv and clause (1) is \
bigOverQuasiCoherentSiteCohomologyAddEquiv"]
public def smallEtaleQuasiCoherentSiteCohomologyAddEquiv (p : ℕ) :
    Sheaf.H.{u} ((SheafOfModules.toSheaf S.ringCatSheaf).obj F) p ≃+
      Sheaf.H.{u} (smallEtaleAssociatedSheaf S F) p :=
  (h'AddEquivH (Opens.grothendieckTopology S)
        ((SheafOfModules.toSheaf S.ringCatSheaf).obj F) p ⊤ topIsTerminal).symm.trans
    (((smallEtaleQuasiCoherentGlobalCohomologyIso S F p).addCommGroupIsoToAddEquiv).trans
      (h'AddEquivH (Scheme.smallEtaleTopology S) (smallEtaleAssociatedSheaf S F) p _
        (isTerminal_opensToEtale_top S)))

end SmallEtale

/-! ### Clause (2) as a chain -/

section Chain

variable (B : BigZariskiSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (F : S.Modules)
  [F.IsQuasicoherent]

attribute [local instance] Stacks.Topology.hasExt_sheafOpens
  Stacks.Topology.enoughInjectives_sheafOpens
  Stacks.Cohomology.FreeYonedaUnivLE.enoughInjectives_essentiallySmallSite
  Stacks.Cohomology.FreeYonedaUnivLE.hasExt_essentiallySmallSite

attribute [local instance 2000] CategoryTheory.IsGrothendieckAbelian.hasExt in
/-- **The middle equality of clause (2) of [Stacks, Tag 03DW].**  The cohomology of the
associated module on the small Zariski site of `S` agrees with its cohomology on the small étale
site, in every degree:

```
H^q(S_Zar, ℱᵃ)  ≅  H^q(S_étale, ℱᵃ).
```

The source writes clause (2) as the chain
`H^q(S, ℱ) = H^q(S_Zar, ℱᵃ) = H^q(S_étale, ℱᵃ)`; this is that chain's second equality, obtained
by comparing both ends with `H^q(S, ℱ)`.  It carries no attribute: the covering set of clause
(2) is the two links through `H^q(S, ℱ)`,
`AlgebraicGeometry.smallZariskiQuasiCoherentSiteCohomologyAddEquiv` and
`AlgebraicGeometry.smallEtaleQuasiCoherentSiteCohomologyAddEquiv`, of which this is a
consequence. -/
public def smallZariskiEtaleQuasiCoherentSiteCohomologyAddEquiv (p : ℕ) :
    Sheaf.H.{u} (smallZariskiAssociatedSheaf B S hS F) p ≃+
      Sheaf.H.{u} (smallEtaleAssociatedSheaf S F) p :=
  (smallZariskiQuasiCoherentSiteCohomologyAddEquiv B S hS F p).symm.trans
    (smallEtaleQuasiCoherentSiteCohomologyAddEquiv S F p)

end Chain

end AlgebraicGeometry

end
