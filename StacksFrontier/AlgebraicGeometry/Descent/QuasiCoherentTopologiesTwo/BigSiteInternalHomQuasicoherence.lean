module

public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherentTopologiesTwo.BigSiteProperties
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherentTopologiesTwo.TopologyIndependence
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.InternalHom

/-!
# Part (3) of Stacks 0GNE at the big sites of a scheme: the internal homs agree, and are
quasi-coherent, at 0GNE's own hypothesis

Descent, Lemma 0GNE (3) says that for quasi-coherent `𝒪`-modules `𝓕`, `𝓖` on `(Sch/S)_fppf` with
`𝓕` finite locally free the internal homs `𝓗om_𝒪(𝓕, 𝓖)` computed in `Mod((Sch/S)_Zar, 𝒪)`,
`Mod((Sch/S)_étale, 𝒪)` and `Mod((Sch/S)_fppf, 𝒪)` agree, and that the common value is an object
of `QCoh((Sch/S)_fppf, 𝒪)`.

The *agreement* holds for arbitrary sheaves of modules on an arbitrary ringed site read with a
coarser topology, `AlgebraicGeometry.RingedSite.coarsenModules_internalHomSheaf`. **This file
instantiates it at the source's own objects**, the big `τ`-sites of a scheme: the ringed site
`(Sch/S)_fppf` read with the `τ`-topology is the ringed site `(Sch/S)_τ`, so the coarsening of
`𝓗om_𝒪(𝓕, 𝓖)` computed on `(Sch/S)_fppf` *is* the internal hom of the readings computed on
`(Sch/S)_τ`.  The *quasi-coherence of the common value* is Stacks 0GNC,
`AlgebraicGeometry.RingedSite.internalHomSheaf_isQuasicoherent`.

**This file states that clause at 0GNE's own hypothesis.**  0GNC is formalized with finite local
freeness in the local-generators sense of Stacks 01C6 (2),
`AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree`, whereas "finite locally free" in the
statement of 0GNE (3) — and in its parenthetical, which is the three-way equivalence across the
topologies — is Modules on Sites, Definition 03DL (2),
`SheafOfModules.IsFiniteLocallyFreeOnSite`.  The two are equivalent in this library, in both
directions (`Stacks.SheafOfModules.isFiniteLocallyFreeOnSite_of_isFiniteLocallyFree` and
`AlgebraicGeometry.SheafOfModules.isFiniteLocallyFree_of_isFiniteLocallyFreeOnSite`), so nothing
is added to the mathematics; the clause is stated at the big `τ`-sites of a scheme with the
hypothesis 0GNE actually writes.

## Main results

* `BigFppfOver.restrictTopology_internalHomSheaf`: **Stacks 0GNE (3), the agreement, at the big
  sites of a scheme** — the internal hom computed on `(Sch/S)_fppf` and read for the coarser
  topology is the internal hom of the readings computed on `(Sch/S)_τ`, at every one of the five
  topologies, for arbitrary `𝒪`-modules and as an equality of sheaves of modules.
* `BigFppfOver.isQuasicoherentOnSite_internalHomSheaf_of_isFiniteLocallyFreeOnSite`:
  **Stacks 0GNE (3), the quasi-coherence of the common value**, at the big `τ`-site for every one
  of the five topologies, with finite local freeness taken in the sense of Modules on Sites,
  Definition 03DL (2).

## The parenthetical of part (3)

The parenthetical — that `𝓕` is finite locally free for the fppf topology if and only if for the
étale, if and only if for the Zariski topology — is
`AlgebraicGeometry.BigFppfOver.isFiniteLocallyFreeOnSite_restrictTopology_iff`, proved at every
one of the five topologies.  Nothing in this file depends on it: the hypothesis below is finite
local freeness at the one topology `τ` whose site the conclusion is about, so the clause is
available at each of the five topologies separately, independently of the parenthetical.

## References

* [Stacks Project, Tag 0GNE](https://stacks.math.columbia.edu/tag/0GNE)
* [Stacks Project, Tag 0GNC](https://stacks.math.columbia.edu/tag/0GNC)
* [Stacks Project, Tag 01C6](https://stacks.math.columbia.edu/tag/01C6)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03EM](https://stacks.math.columbia.edu/tag/03EM)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

namespace BigFppfOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0GNE (3), the agreement, at the big sites of a scheme.**  For arbitrary `𝒪`-modules
`𝓕`, `𝓖` on `(Sch/S)_fppf`, the internal hom `𝓗om_𝒪(𝓕, 𝓖)` computed in `Mod((Sch/S)_fppf, 𝒪)`
and read for the coarser topology *is* the internal hom of the readings computed in
`Mod((Sch/S)_τ, 𝒪)`, at every one of the five topologies — so in particular the Zariski, étale
and fppf values of the source's statement agree.

This is `AlgebraicGeometry.RingedSite.coarsenModules_internalHomSheaf`, the statement for an
arbitrary ringed site read with a coarser topology, at `(Sch/S)_fppf` and
`AlgebraicGeometry.BigFppfOver.baseOverTopology_le_fppf`: the ringed site `(Sch/S)_fppf` read
with the `τ`-topology is `(Sch/S)_τ`, the structure sheaves having the same underlying presheaf
and a sheaf condition that is a proposition.

An *equality* of sheaves of modules, not an isomorphism: the internal hom of Stacks 03EM is a
construction on presheaves of modules and the topology enters only in the proof that the result
is a sheaf, so there is nothing to compare.  No quasi-coherence and no finite local freeness are
needed for the agreement; they are the hypotheses of the quasi-coherence clause below. -/
@[stacks 0GNE "part (3), the internal homs computed on (Sch/S)_fppf and on (Sch/S)_tau agree, \
for arbitrary O-modules, at every one of the five topologies"]
public theorem restrictTopology_internalHomSheaf (τ : SiteKind)
    (F G : SheafOfModules.{u} (structureSheaf B S hS)) :
    (restrictTopology B S hS τ).obj
        (RingedSite.internalHomSheaf (baseRingedSite B S hS .fppf) F G) =
      RingedSite.internalHomSheaf (baseRingedSite B S hS τ)
        ((restrictTopology B S hS τ).obj F) ((restrictTopology B S hS τ).obj G) :=
  RingedSite.coarsenModules_internalHomSheaf (baseRingedSite B S hS .fppf)
    (baseOverTopology_le_fppf B S hS τ) F G

/-- **Stacks 0GNE (3), the quasi-coherence of the common value**, on the big `τ`-site of `S` for
every `τ ∈ {Zariski, étale, smooth, syntomic, fppf}`, with finite local freeness in the sense of
Modules on Sites, Definition 03DL (2) — the sense in which the source's part (3) states it.

At `τ = fppf` this is the source's "the common value is an object of `QCoh((Sch/S)_fppf, 𝒪)`";
the agreement of the values computed at the five topologies, which is what makes "the common
value" a legitimate phrase, is
`AlgebraicGeometry.BigFppfOver.restrictTopology_internalHomSheaf` above, an equality of sheaves
of modules and not merely an isomorphism.

This is `AlgebraicGeometry.BigFppfOver.isQuasicoherentOnSite_internalHomSheaf` — Stacks 0GNC on
the big `τ`-site — with its finite-local-freeness hypothesis supplied from the 03DL (2) form by
`AlgebraicGeometry.SheafOfModules.isFiniteLocallyFree_of_isFiniteLocallyFreeOnSite`, whose two
sheafification hypotheses on the slices of the big site are the instances
`AlgebraicGeometry.BigFppfOver.hasSheafify_baseOver` and
`…wEqualsLocallyBijective_baseOver`. -/
@[stacks 0GNE "part (3), quasi-coherence of the common value, on the big tau-site for every one \
of the five topologies, with finite local freeness in the sense of Modules on Sites 03DL (2)"]
public theorem isQuasicoherentOnSite_internalHomSheaf_of_isFiniteLocallyFreeOnSite
    (τ : SiteKind)
      (F G : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
        (baseRingedSite B S hS τ).O))
    [SheafOfModules.IsQuasicoherentOnSite F] [SheafOfModules.IsQuasicoherentOnSite G]
    (hF : SheafOfModules.IsFiniteLocallyFreeOnSite F) :
    (RingedSite.internalHomSheaf (baseRingedSite B S hS τ) F G).IsQuasicoherentOnSite :=
  have := SheafOfModules.isFiniteLocallyFree_of_isFiniteLocallyFreeOnSite F hF
  isQuasicoherentOnSite_internalHomSheaf B S hS τ F G

end BigFppfOver

end AlgebraicGeometry

end
