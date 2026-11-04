module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf
public import StacksFrontier.AlgebraicGeometry.Topologies.Smooth.BigSiteOver
public import StacksFrontier.AlgebraicGeometry.Topologies.Syntomic.BigSiteOver
public import StacksFrontier.AlgebraicGeometry.Topologies.ZariskiTopology.Sites

/-!
# The Zariski, smooth, syntomic and fppf topoi of a scheme

A *topos* attached to a scheme `S` and a topology is the category of set-valued sheaves on
the corresponding site of `S`. This file collects the small Zariski topos of `S` and the big
Zariski, smooth, syntomic and fppf topoi of `S`; the small and big étale topoi are
`AlgebraicGeometry.smallEtaleTopos` and `AlgebraicGeometry.bigEtaleTopos` in
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/SmallEtaleTopos.lean`, next to the étale
sites they are built from.

## Main definitions

* `AlgebraicGeometry.smallZariskiTopos` — the small Zariski topos of `S`.
* `AlgebraicGeometry.bigZariskiTopos` — the big Zariski topos of `S`.
* `AlgebraicGeometry.bigSmoothTopos` — the big smooth topos of `S`.
* `AlgebraicGeometry.bigSyntomicTopos` — the big syntomic topos of `S`.
* `AlgebraicGeometry.bigFppfTopos` — the big fppf topos of `S`.

## Implementation notes

Each topos is taken on the localization at `S` of a chosen big site, so each definition
carries that site as a parameter together with the containment of `S` in it; for the smooth
site that containment is the size bound `S.size < B.cutoff`, which is how
`AlgebraicGeometry.BigSmoothOver` is indexed.

The universe of the values is left free and independent of the universe of the schemes, as
it is for the two étale topoi; clients may in particular specialize it to the universe of
the schemes. All five are abbreviations, so that the sheaf category's existing instances and
API apply directly.

## References

* [Stacks Project, Tag 04HQ](https://stacks.math.columbia.edu/tag/04HQ)
-/

@[expose] public section

open CategoryTheory

universe u v

namespace AlgebraicGeometry

/-- **Stacks 04HQ, part (2).** The small Zariski topos of `S` is the category of set-valued
sheaves on the small Zariski site of `S`. -/
@[stacks 04HQ "part (2): the small Zariski topos"]
public abbrev smallZariskiTopos (B : BigZariskiSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) := Sheaf (SmallZariski.topology B S hS) (Type v)

/-- **Stacks 04HQ, part (3), the Zariski case.** The big Zariski topos of `S` is the
category of set-valued sheaves on the big Zariski site over `S`. -/
@[stacks 04HQ "part (3): the big Zariski topos"]
public abbrev bigZariskiTopos (B : BigZariskiSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) := Sheaf (BigZariskiOver.topology B S hS) (Type v)

/-- **Stacks 04HQ, part (3), the smooth case.** The big smooth topos of `S` is the category
of set-valued sheaves on the big smooth site over `S`. -/
@[stacks 04HQ "part (3): the big smooth topos"]
public abbrev bigSmoothTopos (B : BigSmoothSite.{u}) (S : Scheme.{u})
    (hS : S.size < B.cutoff) := Sheaf (BigSmoothOver.topology B S hS) (Type v)

/-- **Stacks 04HQ, part (3), the syntomic case.** The big syntomic topos of `S` is the
category of set-valued sheaves on the big syntomic site over `S`. -/
@[stacks 04HQ "part (3): the big syntomic topos"]
public abbrev bigSyntomicTopos (B : BigSyntomicSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) := Sheaf (BigSyntomicOver.topology B S hS) (Type v)

/-- **Stacks 04HQ, part (3), the fppf case.** The big fppf topos of `S` is the category of
set-valued sheaves on the big fppf site over `S`. -/
@[stacks 04HQ "part (3): the big fppf topos"]
public abbrev bigFppfTopos (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) := Sheaf (BigFppfOver.topology B S hS) (Type v)

end AlgebraicGeometry

end
