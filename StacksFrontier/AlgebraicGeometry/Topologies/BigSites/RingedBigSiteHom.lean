module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigFppfStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Topologies.BigEtaleStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.CohomologyAfterRestriction
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSmoothStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSyntomicStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Topologies.BigZariskiStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Topologies.ChangeOfSites.RingedSiteHom
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Precoverage
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.ZariskiPrecoverage
public import StacksFrontier.CategoryTheory.Sites.MorphismOfSites.SmallModel
public import StacksCore.Tactic.StacksAttribute

/-!
# `f_big` as a morphism of ringed big sites, uniformly in the topology

Stacks 070R, part (1) says that a morphism of schemes `f : X ⟶ Y` makes the morphism of big
sites `f_big : (\Sch/X)_{fppf} ⟶ (\Sch/Y)_{fppf}` a morphism of ringed sites

```
  (f_big, f_big^♯) : ((\Sch/X)_{fppf}, 𝒪_X) ⟶ ((\Sch/Y)_{fppf}, 𝒪_Y),
```

and adds "similarly for the big syntomic, smooth, étale and Zariski sites".  The source says
"similarly" because nothing in the assertion mentions the topology: the underlying continuous
functor is base change `Y'/Y ↦ X ×_Y Y'/X`, the structure sheaf is `T ↦ Γ(T, 𝒪_T)`, and the
structure map is pullback of global functions along the projection, whichever of the five
topologies the covering families were chosen from.

This file follows the source and states the five cases once, over
`AlgebraicGeometry.BigSite τ`, which already selects a big Zariski, étale, smooth, syntomic or
fppf site according to `τ : AlgebraicGeometry.CoveringTopology`.

## Main definitions

* `AlgebraicGeometry.bigSiteToOver`: a localized big site presented as in Stacks 03DU, by the
  functor to the schemes over the base recording the structure morphism of each object.
* `AlgebraicGeometry.bigSiteRingedSite`: the localization at `S` of a big `τ`-site, with its
  structure sheaf, as a ringed site.
* `AlgebraicGeometry.bigSiteBaseChangeProjections`: the projections `T ×_S S' ⟶ S'` of the
  underlying schemes.
* `AlgebraicGeometry.bigSiteStructureSharp`: the structure map `f_big^♯ : 𝒪_S ⟶ f_{big, *}𝒪_T`.
* `AlgebraicGeometry.bigSiteRingedSiteHom`: **the five cases of part (1)**, the pair
  `(f_big, f_big^♯)` as a morphism of ringed sites.

## Main results

* `AlgebraicGeometry.overTopology_eq_over'`: the topology of a localized big site is the
  localization of the topology of the big site, in each of the five topologies.
* `AlgebraicGeometry.bigSite_structure_isSheaf`: global functions are a sheaf of rings on the
  localization of a big `τ`-site — Stacks 03DU, uniformly in `τ`.
* `AlgebraicGeometry.isContinuous_bigSiteBaseChange` and
  `AlgebraicGeometry.isMorphismOfSites_bigSiteBaseChange`: base change is continuous and defines
  a morphism of sites at the universe of the structure rings.

## Implementation notes

`AlgebraicGeometry.overTopology` dispatches on `τ` and so is opaque to instance search; the two
facts that have to be transported across the dispatch are the identification of the localized
topology with `CategoryTheory.GrothendieckTopology.over` — which is how the slice instances for
base change are stated — and the sheaf condition of Stacks 03DU.  Both are a five-case match on
existing per-topology results, not five new proofs: `overTopology_eq_over'` is `rfl` for
smooth, syntomic and fppf and the bridge lemma for Zariski and étale, and
`bigSite_structure_isSheaf` is the five `structure_isSheaf` theorems.

The underlying functor of `f_big` is `CategoryTheory.Over.pullback`, with no wrapper: the
underlying category of a big site is closed under fibre products
(`AlgebraicGeometry.hasFiniteLimits_siteCategory`), so the localized site is a slice on the
nose and base change is the slice pullback.  Its site condition is read at the universe of the
sections of the structure sheaf, as a morphism of ringed sites requires, and comes from
`isMorphismOfSites_of_essentiallySmall` together with
`AlgebraicGeometry.essentiallySmall_overBase`; flatness of `Over.pullback` is flatness of a
right adjoint.

The structure map is assembled from `AlgebraicGeometry.ChangeOfSites.structureSharp`, which is
the statement of the remark for an arbitrary pair of sites of schemes, so the only thing this
file contributes to it is the projection transformation
`CategoryTheory.Over.pullbackForget`.

`AlgebraicGeometry.BigFppfOver.baseChange` and `AlgebraicGeometry.BigFppfOver.structureComparison`
are the fppf case written out separately, in
`StacksFrontier/AlgebraicGeometry/Descent/BigFppfRingedMorphism.lean`, with the site condition at
`Type (u + 1)` and the structure sheaf in `RingCat`.  They are left in place; what is added here
is the uniform statement and, for fppf as for the other four, the bundled morphism of ringed
sites, which the `Type (u + 1)` site condition cannot carry.

## References

* [Stacks Project, Tag 070R](https://stacks.math.columbia.edu/tag/070R)
* [Stacks Project, Tag 03AD](https://stacks.math.columbia.edu/tag/03AD)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 03FE](https://stacks.math.columbia.edu/tag/03FE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

variable {τ : CoveringTopology} (B : BigSite.{u} τ)

/-- The inclusion of the chosen category of schemes of a big site into all schemes, uniformly
in the topology. -/
public abbrev bigSiteInclusion : siteCategory B ⥤ Scheme.{u} :=
  schemeBelowInclusion (cutoff τ B)

variable (S : Scheme.{u}) (hS : S.size < cutoff τ B)

/-- The localization at `S` of a big site, presented as in Stacks 03DU by the functor to the
schemes over `S` recording the structure morphism of each object. -/
public abbrev bigSiteToOver : Over (base B S hS) ⥤ Over S :=
  Over.post (bigSiteInclusion B)

/-- The topology of a localized big site is the localization of the topology of the big site.
This is `rfl` for the smooth, syntomic and fppf sites, whose localized topology is defined as
that localization, and the bridge lemma for the Zariski and étale sites, whose localized
topology is generated by the chosen covering families of the slice. -/
public alias overTopology_eq_over' := overTopology_eq_over

/-- **Stacks 03DU, uniformly in the topology.**  The presheaf of global functions
`T/S ↦ Γ(T, 𝒪_T)` is a sheaf of rings on the localization at `S` of a big `τ`-site, for each of
the five topologies. -/
@[stacks 03DU "the structure sheaf of a localized big site, uniformly in the topology"]
public theorem bigSite_structure_isSheaf :
    Presheaf.IsSheaf (overTopology τ B S hS)
      (Stacks.Sites.structurePresheaf S (bigSiteToOver B S hS)) := by
  cases τ with
  | zariski => exact BigZariskiOver.structure_isSheaf B S hS
  | etale => exact BigEtaleOver.structure_isSheaf B S hS
  | smooth => exact BigSmoothOver.structure_isSheaf B S hS
  | syntomic => exact BigSyntomicOver.structure_isSheaf B S hS
  | fppf => exact BigFppfOver.structure_isSheaf B S hS

/-- The localization at `S` of a big `τ`-site, together with its sheaf of global functions, as a
ringed site in the sense of Stacks 03AD. -/
public noncomputable abbrev bigSiteRingedSite : RingedSite.{u + 1, u, u} :=
  ChangeOfSites.ringedSite S (overTopology τ B S hS) (bigSiteToOver B S hS)
    (bigSite_structure_isSheaf B S hS)

variable {S} {T : Scheme.{u}} {hS} {hT : T.size < cutoff τ B}
  (f : base B T hT ⟶ base B S hS)

/-- Base change along `f` is continuous for the two localized topologies: a localized big site
is a slice of the chosen category of schemes with the localized topology, so this is the general
slice instance. -/
public instance isContinuous_bigSiteBaseChange :
    (Over.pullback f).IsContinuous (overTopology τ B S hS) (overTopology τ B T hT) := by
  rw [overTopology_eq_over' B S hS, overTopology_eq_over' B T hT]
  infer_instance

/-- Base change along `f` is representably flat, being a right adjoint. -/
public instance representablyFlat_bigSiteBaseChange :
    RepresentablyFlat (Over.pullback f) :=
  have : (Over.pullback f).IsRightAdjoint := ⟨_, ⟨Over.mapPullbackAdj f⟩⟩
  inferInstance

/-- **Stacks 070R, part (1): `f_big` is a morphism of sites**, at the universe of the sections
of the structure sheaves, which is the universe at which a morphism of ringed sites reads its
site condition.

A localized big site is essentially small at the universe of its morphisms
(`AlgebraicGeometry.essentiallySmall_overBase`) and base change is continuous and flat, so this
is `isMorphismOfSites_of_essentiallySmall`. -/
@[stacks 070R "part (1): `f_big` is a morphism of sites, in each of the five topologies"]
public theorem isMorphismOfSites_bigSiteBaseChange :
    IsMorphismOfSites.{u} (Over.pullback f) (overTopology τ B S hS) (overTopology τ B T hT) :=
  let _ : EssentiallySmall.{u} (Over (base B S hS)) := essentiallySmall_overBase B S hS
  let _ : EssentiallySmall.{u} (Over (base B T hT)) := essentiallySmall_overBase B T hT
  isMorphismOfSites_of_essentiallySmall _ _ _

/-- The projections `T ×_S S' ⟶ S'` of underlying schemes out of the base change of an object
`S'/S` of the localization at `S` of a big site, natural in `S'/S`. -/
public noncomputable def bigSiteBaseChangeProjections :
    Over.pullback f ⋙ bigSiteToOver B T hT ⋙ Over.forget T ⟶
      bigSiteToOver B S hS ⋙ Over.forget S :=
  Functor.whiskerRight (Over.pullbackForget f) (bigSiteInclusion B)

/-- At an object `S'/S`, the projection transformation is the first projection
`T ×_S S' ⟶ S'` of the underlying schemes. -/
@[simp]
public theorem bigSiteBaseChangeProjections_app (X : Over (base B S hS)) :
    (bigSiteBaseChangeProjections B f).app X =
      (bigSiteInclusion B).map (pullback.fst X.hom f) := rfl

/-- **Stacks 070R, part (1): the structure map `f_big^♯ : 𝒪_S ⟶ f_{big, *}𝒪_T`**, in each of
the five topologies.  On an object `S'/S` it is the map on global functions induced by the
projection `T ×_S S' ⟶ S'`, that is, the usual `pr_{S'}^♯`. -/
@[stacks 070R "part (1): `f_big^♯`, in each of the five topologies"]
public noncomputable def bigSiteStructureSharp :
    commStructureSheaf S (overTopology τ B S hS) (bigSiteToOver B S hS)
        (bigSite_structure_isSheaf B S hS) ⟶
      ((Over.pullback f).sheafPushforwardContinuous CommRingCat.{u} (overTopology τ B S hS)
        (overTopology τ B T hT)).obj
      (commStructureSheaf T (overTopology τ B T hT) (bigSiteToOver B T hT)
        (bigSite_structure_isSheaf B T hT)) :=
  ChangeOfSites.structureSharp (overTopology τ B S hS) (overTopology τ B T hT)
    (bigSiteToOver B S hS) (bigSiteToOver B T hT) (Over.pullback f)
    (bigSiteBaseChangeProjections B f) (bigSite_structure_isSheaf B S hS)
    (bigSite_structure_isSheaf B T hT)

/-- At an object `S'/S`, the structure map `f_big^♯` is the map on global functions induced by
the projection `T ×_S S' ⟶ S'`. -/
@[simp]
public theorem bigSiteStructureSharp_hom_app (X : Over (base B S hS)) :
    (bigSiteStructureSharp B f).hom.app (op X) =
      Scheme.Γ.map (op ((bigSiteInclusion B).map (pullback.fst X.hom f))) := rfl

/-- **Stacks 070R, part (1), in all five topologies at once.**  A morphism of schemes of a big
`τ`-site makes the morphism of big sites `f_big : (\Sch/T)_τ ⟶ (\Sch/S)_τ` a morphism of ringed
sites

```
  (f_big, f_big^♯) : ((\Sch/T)_τ, 𝒪_T) ⟶ ((\Sch/S)_τ, 𝒪_S)
```

in the sense of Stacks 03AD, for `τ` the fppf, syntomic, smooth, étale or Zariski topology. -/
@[stacks 070R "part (1): `(f_big, f_big^♯)` for the big fppf, syntomic, smooth, étale and \
Zariski sites"]
public noncomputable def bigSiteRingedSiteHom :
    RingedSite.HomGeneral (bigSiteRingedSite B T hT) (bigSiteRingedSite B S hS) :=
  ChangeOfSites.ringedSiteHom (overTopology τ B S hS) (overTopology τ B T hT)
    (bigSiteToOver B S hS) (bigSiteToOver B T hT) (Over.pullback f)
    (isMorphismOfSites_bigSiteBaseChange B f) (bigSiteBaseChangeProjections B f)
    (bigSite_structure_isSheaf B S hS) (bigSite_structure_isSheaf B T hT)

/-- The underlying functor of `(f_big, f_big^♯)` is base change along `f`. -/
@[simp]
public theorem bigSiteRingedSiteHom_u :
    (bigSiteRingedSiteHom B f).u = Over.pullback f := rfl

/-- The structure map of `(f_big, f_big^♯)` is `AlgebraicGeometry.bigSiteStructureSharp`. -/
public theorem bigSiteRingedSiteHom_fsharp :
    (bigSiteRingedSiteHom B f).fsharp = bigSiteStructureSharp B f := rfl

end AlgebraicGeometry

end
