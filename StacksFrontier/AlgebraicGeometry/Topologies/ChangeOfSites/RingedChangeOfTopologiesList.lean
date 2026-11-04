module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleRingedSiteHomGeneral
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.RecoveringMorphisms.RingedSiteHom
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.RingedProjectionAndIf
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.SmallZariskiRingedSiteHom
public import StacksFrontier.AlgebraicGeometry.Topologies.ChangeOfSites.RingedChangeOfTopologies
public import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 070R for every entry of the change-of-topologies list

Topologies, Section 03FE lists twenty-seven morphisms of sites, and says of them: "in the
sections above we have seen the morphisms `f_{big}` and `f_{small}`, we also have seen the
morphisms of sites `π_Y : (\Sch/Y)_τ ⟶ Y_τ`, and it is clear that the identity functor
`(\Sch/X)_τ ⟶ (\Sch/X)_{τ'}` defines a morphism of sites when `τ` is a stronger topology than
`τ'`; hence composing these gives the list of possible morphisms above."  Stacks 070R asserts
that every one of them is a morphism of ringed sites.

This file performs that composition.  The four generators are
`AlgebraicGeometry.BigFppfSite.bigBaseChangeRingedSiteHom` (`f_{big}`),
`AlgebraicGeometry.BigFppfSite.idRingedSiteHom` (`id_{τ, τ'}`),
`AlgebraicGeometry.smallZariskiPiRingedSiteHom` / `AlgebraicGeometry.smallEtalePiRingedSiteHom`
(`π_Y`), and `AlgebraicGeometry.smallZariskiRingedSiteHom` /
`AlgebraicGeometry.smallEtaleRingedSiteHom` (`f_{small}`); the composition is
`AlgebraicGeometry.RingedSite.HomGeneral.comp`, Stacks 03AD part (3).

## Main definitions

* `AlgebraicGeometry.BigFppfSite.bigToSmallEtaleRingedSiteHom`: **entries (16)–(19)**,
  `(\Sch/T)_τ ⟶ S_\etale` for `τ ∈ \{fppf, syntomic, smooth, \etale\}`.
* `AlgebraicGeometry.BigFppfSite.bigToSmallZariskiRingedSiteHom`: **entries (20)–(24)**,
  `(\Sch/T)_τ ⟶ S_{Zar}` for every one of the five `τ`.
* `AlgebraicGeometry.smallEtaleToSmallZariskiRingedSiteHom`: **entry (26)**,
  `T_\etale ⟶ S_{Zar}`.

## The list, entry by entry

With `f : T ⟶ S` a morphism of schemes of a chosen big fppf site `B`:

* (1), (6), (10), (13), (15): `(\Sch/T)_τ ⟶ (\Sch/S)_τ` --
  `BigFppfSite.bigBaseChangeRingedSiteHom`, and `AlgebraicGeometry.bigSiteRingedSiteHom`
  uniformly in `τ`.
* (2)–(5), (7)–(9), (11), (12), (14): `(\Sch/T)_τ ⟶ (\Sch/S)_{τ'}` with `τ` finer than `τ'` --
  `BigFppfSite.bigRingedSiteHom`.
* (16)–(19): `(\Sch/T)_τ ⟶ S_\etale` -- `BigFppfSite.bigToSmallEtaleRingedSiteHom`.
* (20)–(24): `(\Sch/T)_τ ⟶ S_{Zar}` -- `BigFppfSite.bigToSmallZariskiRingedSiteHom`.
* (25): `T_\etale ⟶ S_\etale` -- `AlgebraicGeometry.smallEtaleRingedSiteHom`.
* (26): `T_\etale ⟶ S_{Zar}` -- `AlgebraicGeometry.smallEtaleToSmallZariskiRingedSiteHom`.
* (27): `T_{Zar} ⟶ S_{Zar}` -- `AlgebraicGeometry.smallZariskiRingedSiteHom`.

Entries (1)–(15) are `BigFppfSite.bigRingedSiteHom` in full: it is stated for every pair
`τ` finer than `τ'`, which is exactly the fifteen big-to-big entries.

## Implementation notes

Entry (26) is the one entry whose target is taken in the *opens* model of the small Zariski
site.  Its second factor is `AlgebraicGeometry.SmallEtale.toZariskiRingedSiteHom`, the
`id_{small, \etale, Zar} : S_\etale ⟶ S_{Zar}` of Stacks 08H7, whose target is
`AlgebraicGeometry.Scheme.zariskiRingedSite` — the site of opens of `S` with its structure
sheaf.  That is the small Zariski site read through the equivalence of Topologies, Lemma 020X,
which Stacks 03FG records, and it is the model in which the library already has that generator.
Entry (27), by contrast, is stated on `AlgebraicGeometry.SmallZariski`, so the two entries use
the two models; no bridge between them is constructed here.

The composites are given in the order "first the morphism of big sites, then the projection",
which is one of the two factorizations of Topologies, Section 03FE; the other,
`π_T` followed by `f_{small}`, has the same underlying continuous functor because base change
commutes with the small-site inclusion, and is not separately constructed.

## References

* [Stacks Project, Tag 070R](https://stacks.math.columbia.edu/tag/070R)
* [Stacks Project, Tag 03AD](https://stacks.math.columbia.edu/tag/03AD)
* [Stacks Project, Tag 03FE](https://stacks.math.columbia.edu/tag/03FE)
* [Stacks Project, Tag 020X](https://stacks.math.columbia.edu/tag/020X)
* [Stacks Project, Tag 03FG](https://stacks.math.columbia.edu/tag/03FG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

namespace BigFppfSite

variable (B : BigFppfSite.{u}) {τ : CoveringTopology} {S T : Scheme.{u}} {hS : B.Contains S}
  {hT : B.Contains T}

/-- **Stacks 070R, entries (16)–(19) of the change-of-topologies list.**  For `τ` finer than the
étale topology, the morphism of sites `f_{sites} : (\Sch/T)_τ ⟶ S_\etale` is a morphism of
ringed sites.  It is `π_S ∘ f_{sites}`, with `f_{sites} : (\Sch/T)_τ ⟶ (\Sch/S)_\etale` the
big-site entry and `π_S : (\Sch/S)_\etale ⟶ S_\etale` the projection of Topologies,
Lemma 021G. -/
@[stacks 070R "entries (16)-(19) of the 03FE list: `(Sch/T)_τ ⟶ S_étale`"]
public noncomputable def bigToSmallEtaleRingedSiteHom (h : τ.IsFiner .etale)
    (f : B.obj hT ⟶ B.obj hS) :
    RingedSite.HomGeneral (B.carriedOverRingedSite T hT τ)
      (smallEtaleRingedSite B.toBigEtaleSite S hS) :=
  (B.bigRingedSiteHom h f).comp
    (smallEtalePiRingedSiteHom B.toBigEtaleSite (S := ⟨S, hS⟩))

/-- **Stacks 070R, entries (20)–(24) of the change-of-topologies list.**  For every one of the
five topologies, the morphism of sites `f_{sites} : (\Sch/T)_τ ⟶ S_{Zar}` is a morphism of
ringed sites.  It is `π_S ∘ f_{sites}`, with `π_S : (\Sch/S)_{Zar} ⟶ S_{Zar}` the projection of
Topologies, Lemma 020Z. -/
@[stacks 070R "entries (20)-(24) of the 03FE list: `(Sch/T)_τ ⟶ S_Zar`"]
public noncomputable def bigToSmallZariskiRingedSiteHom (h : τ.IsFiner .zariski)
    (f : B.obj hT ⟶ B.obj hS) :
    RingedSite.HomGeneral (B.carriedOverRingedSite T hT τ)
      (smallZariskiRingedSite B.toBigZariskiSite S hS) :=
  (B.bigRingedSiteHom h f).comp
    (smallZariskiPiRingedSiteHom B.toBigZariskiSite (S := ⟨S, hS⟩))

/-- Every topology of the chain is finer than the Zariski topology, so entries (20)–(24) are
available for all five. -/
public theorem isFiner_zariski (τ : CoveringTopology) : τ.IsFiner .zariski := by
  cases τ <;> decide

end BigFppfSite

/-- **Stacks 070R, entry (26) of the change-of-topologies list.**  The morphism of sites
`T_\etale ⟶ S_{Zar}` is a morphism of ringed sites: it is
`id_{small, \etale, Zar} ∘ f_{small}`, with `f_{small} : T_\etale ⟶ S_\etale` the morphism of
ringed small étale sites of Stacks 070R part (2) and `id_{small, \etale, Zar}` the inclusion of
the small Zariski site of `S` into its small étale site.

The target is the opens model of the small Zariski site of `S`, which is the model in which
`AlgebraicGeometry.SmallEtale.toZariskiRingedSiteHom` is stated; see the implementation notes. -/
@[stacks 070R "entry (26) of the 03FE list: `T_étale ⟶ S_Zar`"]
public noncomputable def smallEtaleToSmallZariskiRingedSiteHom (B : BigEtaleSite.{u})
    {X Y : B.Scheme} (a : X ⟶ Y) :
    RingedSite.HomGeneral (smallEtaleRingedSite B X.obj X.property)
      Y.obj.zariskiRingedSite :=
  (smallEtaleRingedSiteHom B a).comp
    (SmallEtale.toZariskiRingedSiteHom B Y.obj Y.property)

end AlgebraicGeometry

end
