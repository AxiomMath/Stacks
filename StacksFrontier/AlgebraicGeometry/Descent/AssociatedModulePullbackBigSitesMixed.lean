module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModulePullbackBigSites
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherentTopologiesTwo.TopologyIndependence
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.ChosenCoveringsComparison

/-!
# The associated module commutes with pullback along the mixed-topology `f_sites`

Stacks 03FH (2) is a statement about **every** morphism of ringed sites `f_sites` of
Remark 070R, and 070R takes its list from Topologies, Section 03FE.  That list has twenty-seven
entries, of which fifteen go between two big sites, `(Sch/X)_τ ⟶ (Sch/Y)_{τ'}`, one for each
pair with `τ'` coarser than `τ` among `Zariski, étale, smooth, syntomic, fppf`.  Five of those
fifteen have `τ = τ'`, and
`AlgebraicGeometry.BigFppfOver.associatedModuleBasePullbackIso`
(`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModulePullbackBigSites.lean`) proves the
clause for them.  **This file proves it for the remaining ten, the mixed-topology ones**:

`(Sch/X)_fppf ⟶ (Sch/Y)_syntomic`, `(Sch/X)_fppf ⟶ (Sch/Y)_smooth`,
`(Sch/X)_fppf ⟶ (Sch/Y)_étale`, `(Sch/X)_fppf ⟶ (Sch/Y)_Zar`,
`(Sch/X)_syntomic ⟶ (Sch/Y)_smooth`, `(Sch/X)_syntomic ⟶ (Sch/Y)_étale`,
`(Sch/X)_syntomic ⟶ (Sch/Y)_Zar`, `(Sch/X)_smooth ⟶ (Sch/Y)_étale`,
`(Sch/X)_smooth ⟶ (Sch/Y)_Zar`, `(Sch/X)_étale ⟶ (Sch/Y)_Zar`.

## What `f_sites` is, for a mixed pair

Section 03FE says where its list comes from: "the identity functor
`(Sch/X)_τ → (Sch/X)_{τ'}` defines a morphism of sites when `τ` is a stronger topology than
`τ'`.  Hence composing these gives the list of possible morphisms above."  So for a mixed pair
the morphism of ringed sites is, by definition, the composite

`(Sch/X)_τ --id_{τ,τ'}--> (Sch/X)_{τ'} --f_big--> (Sch/Y)_{τ'}`,

and 03FH's own proof of clause (2) is "this follows from (1) and the fact that pullbacks are
compatible with compositions of morphisms of ringed sites, see Modules on Sites, Lemma 03D8".
Accordingly `f_sites^*` is `AlgebraicGeometry.BigFppfOver.baseMixedPullback`, the composite of
the pullback along `f_big : (Sch/X)_{τ'} ⟶ (Sch/Y)_{τ'}` with the pullback along
`id_{τ,τ'} : (Sch/X)_τ ⟶ (Sch/X)_{τ'}`, taken in that order.  Both factors are pullbacks of
sheaves of modules along a single morphism of ringed sites: the first is
`SheafOfModules.pullback` of `AlgebraicGeometry.BigFppfOver.baseStructureComparison`, and the
second is `Stacks.SheafOfModules.comparisonPullback`, which unfolds to
`SheafOfModules.pullback` along the identity functor with the identity comparison of structure
sheaves — the identity functor being continuous from the coarser topology to the finer one by
`Stacks.SheafOfModules.isContinuous_id_of_le`.

## The hypothesis

The one hypothesis is `baseOverTopology B X hX τ' ≤ baseOverTopology B X hX τ`: the `τ'`-topology
on the big category over `X` is coarser than the `τ`-topology.  This is 03FE's own condition for
`f_sites` to be on its list — "`τ` is a stronger topology than `τ'`" — and nothing else is
assumed: no quasi-coherence of the module, and nothing of `f` beyond `X` and `Y` lying in the
chosen big fppf site.

It is satisfied by each of the ten mixed pairs, and this file records that: four of them from
`AlgebraicGeometry.BigFppfOver.baseOverTopology_le_fppf`, the other six by chaining
`AlgebraicGeometry.BigFppfSite.zariskiTopology_le_etaleTopology`,
`.etaleTopology_le_smoothTopology` and `.smoothTopology_le_syntomicTopology` through
`AlgebraicGeometry.BigFppfOver.baseOverTopology_le_of_baseTopology_le`.

## Main definitions

* `AlgebraicGeometry.BigFppfOver.baseTopologyPullback`: `id_{τ,τ'}^*`, the pullback of sheaves
  of modules along the morphism of ringed sites
  `id_{τ,τ'} : ((Sch/S)_τ, 𝒪) ⟶ ((Sch/S)_{τ'}, 𝒪)` given by the identity functor.
* `AlgebraicGeometry.BigFppfOver.baseMixedPullback`: `f_sites^*` for a mixed pair, the composite
  of `f_big^*` at `τ'` with `id_{τ,τ'}^*`.
* `AlgebraicGeometry.BigFppfOver.associatedModuleBaseMixedPullbackIso` and
  `AlgebraicGeometry.BigFppfOver.associatedModuleBaseMixedObjPullbackIso`:
  **Stacks 03FH (2)** for the mixed-topology `f_sites : ((Sch/X)_τ, 𝒪_X) ⟶ ((Sch/Y)_{τ'}, 𝒪_Y)`
  of Remark 070R, as functors and at one module.

## Main results

* `AlgebraicGeometry.BigFppfOver.baseOverTopology_le_of_baseTopology_le`: an inequality of the
  topologies of the big category of schemes localizes to the big categories over a scheme.
* `AlgebraicGeometry.BigFppfOver.baseAssociatedModuleTopologyPullbackIso`: the associated module
  of `(Sch/S)_τ` is `id_{τ,τ'}^*` of the associated module of `(Sch/S)_{τ'}`.  This is the step
  that moves the clause between topologies, and it is where the inequality of topologies is
  used.

## Implementation notes

`AlgebraicGeometry.BigFppfOver.baseAssociatedModuleTopologyPullbackIso` is the generalization
from the pair `(τ, fppf)` to an arbitrary comparable pair of
`AlgebraicGeometry.BigFppfOver.comparisonPullbackBaseAssociatedModuleIso`, and has the same
one-line proof: both functors are left adjoint to one and the same functor, because restriction
along the inclusion of the small Zariski site of `S` does not see the topology of the big site,
and `Stacks.SheafOfModules.comparisonPushforward` changes neither the underlying presheaf of
modules nor the coefficient presheaf of rings.  So
`CategoryTheory.Adjunction.leftAdjointUniq` applies to
`AlgebraicGeometry.BigFppfOver.baseAssociatedModuleAdjunction` at `τ'` composed with
`Stacks.SheafOfModules.comparisonAdjunction`, against the same adjunction at `τ`; the equality
of the two right adjoints holds by `rfl`, so no bridge between two restriction functors is
needed.  Nothing is said about quasi-coherence: the comparison exists and is invertible for an
arbitrary `𝒪_S`-module.

Everything else is bookkeeping with whiskerings and associators, over the same-topology clause
at `τ'`.

`AlgebraicGeometry.BigFppfOver.baseTopologyPullback` is stated with the coefficient sheaf
`AlgebraicGeometry.FibredSite.baseRingStructureSheaf B S hS τ'` on its source rather than
`Stacks.SheafOfModules.ringOfLe` of the one at `τ`; the two are the same term, the five
structure sheaves having the same underlying presheaf
(`AlgebraicGeometry.FibredSite.baseRingStructureSheaf_obj` is `rfl`) and the sheaf conditions
being propositions.  This is the same identification
`AlgebraicGeometry.BigFppfOver.restrictTopology` already relies on at the pair `(τ, fppf)`.

At `τ' = τ` the hypothesis holds by `le_rfl` and the statement is the same-topology clause
again, up to the sheafification-for-the-same-topology factor `id_{τ,τ}^*`; the five
same-topology entries of the list keep their own carrier
`AlgebraicGeometry.BigFppfOver.associatedModuleBasePullbackIso`, which states them without that
factor.

## What this file does not claim

Of the twenty-seven entries of Section 03FE, nine go from a big site to a small one and one is
the mixed small pair `X_étale ⟶ Y_{Zar}`.  No statement here is about those.  The four
`(Sch/X)_τ ⟶ Y_étale` among them are entries (16) to (19), and
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModulePullbackBigToSmallEtale.lean` proves the
clause for those; the five `(Sch/X)_τ ⟶ Y_{Zar}`, entries (20) to (24), and the mixed small
pair, entry (26), are proved in
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModulePullbackToSmallZariski.lean`.  The two
small same-topology entries, (25) and (27), are
`AlgebraicGeometry.SmallEtale.associatedModuleBaseChangeIso` and
`AlgebraicGeometry.SmallZariski.lcAssociatedModulePullbackIso`.

## References

* [Stacks Project, Tag 03FH](https://stacks.math.columbia.edu/tag/03FH)
* [Stacks Project, Tag 070R](https://stacks.math.columbia.edu/tag/070R)
* [Stacks Project, Tag 03FE](https://stacks.math.columbia.edu/tag/03FE)
* [Stacks Project, Tag 03FF](https://stacks.math.columbia.edu/tag/03FF)
* [Stacks Project, Tag 03D8](https://stacks.math.columbia.edu/tag/03D8)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.BigFppfOver

variable (B : BigFppfSite.{u})

/-! ### Comparing the localized topologies -/

/-- An inequality between two of the five topologies of the big category of schemes localizes to
the big categories over a scheme: a sieve is covering for the localization exactly when the
sieve it generates upstairs is covering, so the inequality transports verbatim.

This is `AlgebraicGeometry.BigFppfOver.baseOverTopology_le_fppf` with the fppf topology on the
right replaced by an arbitrary one of the five. -/
public theorem baseOverTopology_le_of_baseTopology_le (S : Scheme.{u}) (hS : B.Contains S)
    {τ τ' : SiteKind} (h : B.baseTopology τ' ≤ B.baseTopology τ) :
    baseOverTopology B S hS τ' ≤ baseOverTopology B S hS τ := by
  intro X R hR
  rw [GrothendieckTopology.mem_over_iff] at hR ⊢
  exact h _ hR

/-! ### The ten mixed pairs of Topologies, Section 03FE satisfy the hypothesis

Each of the ten entries `(Sch/X)_τ ⟶ (Sch/Y)_{τ'}` of Section 03FE with `τ' ≠ τ` is recorded
here, so that the clause below is instantiated at every one of them and at none vacuously.
Four come from `AlgebraicGeometry.BigFppfOver.baseOverTopology_le_fppf` and six by chaining the
three inequalities of
`StacksFrontier/AlgebraicGeometry/Topologies/Fppf/ChosenCoveringsComparison.lean`. -/

section TenPairs

variable (S : Scheme.{u}) (hS : B.Contains S)

/-- Entry (14) of Section 03FE: `(Sch/X)_étale ⟶ (Sch/Y)_{Zar}`. -/
public theorem baseOverTopology_zariski_le_etale :
    baseOverTopology B S hS .zariski ≤ baseOverTopology B S hS .etale :=
  baseOverTopology_le_of_baseTopology_le B S hS B.zariskiTopology_le_etaleTopology

/-- Entry (11) of Section 03FE: `(Sch/X)_smooth ⟶ (Sch/Y)_étale`. -/
public theorem baseOverTopology_etale_le_smooth :
    baseOverTopology B S hS .etale ≤ baseOverTopology B S hS .smooth :=
  baseOverTopology_le_of_baseTopology_le B S hS B.etaleTopology_le_smoothTopology

/-- Entry (7) of Section 03FE: `(Sch/X)_syntomic ⟶ (Sch/Y)_smooth`. -/
public theorem baseOverTopology_smooth_le_syntomic :
    baseOverTopology B S hS .smooth ≤ baseOverTopology B S hS .syntomic :=
  baseOverTopology_le_of_baseTopology_le B S hS B.smoothTopology_le_syntomicTopology

/-- Entry (12) of Section 03FE: `(Sch/X)_smooth ⟶ (Sch/Y)_{Zar}`. -/
public theorem baseOverTopology_zariski_le_smooth :
    baseOverTopology B S hS .zariski ≤ baseOverTopology B S hS .smooth :=
  (baseOverTopology_zariski_le_etale B S hS).trans (baseOverTopology_etale_le_smooth B S hS)

/-- Entry (9) of Section 03FE: `(Sch/X)_syntomic ⟶ (Sch/Y)_{Zar}`. -/
public theorem baseOverTopology_zariski_le_syntomic :
    baseOverTopology B S hS .zariski ≤ baseOverTopology B S hS .syntomic :=
  (baseOverTopology_zariski_le_smooth B S hS).trans (baseOverTopology_smooth_le_syntomic B S hS)

/-- Entry (8) of Section 03FE: `(Sch/X)_syntomic ⟶ (Sch/Y)_étale`. -/
public theorem baseOverTopology_etale_le_syntomic :
    baseOverTopology B S hS .etale ≤ baseOverTopology B S hS .syntomic :=
  (baseOverTopology_etale_le_smooth B S hS).trans (baseOverTopology_smooth_le_syntomic B S hS)

/-- Entry (5) of Section 03FE: `(Sch/X)_fppf ⟶ (Sch/Y)_{Zar}`. -/
public theorem baseOverTopology_zariski_le_fppf :
    baseOverTopology B S hS .zariski ≤ baseOverTopology B S hS .fppf :=
  baseOverTopology_le_fppf B S hS .zariski

/-- Entry (4) of Section 03FE: `(Sch/X)_fppf ⟶ (Sch/Y)_étale`. -/
public theorem baseOverTopology_etale_le_fppf :
    baseOverTopology B S hS .etale ≤ baseOverTopology B S hS .fppf :=
  baseOverTopology_le_fppf B S hS .etale

/-- Entry (3) of Section 03FE: `(Sch/X)_fppf ⟶ (Sch/Y)_smooth`. -/
public theorem baseOverTopology_smooth_le_fppf :
    baseOverTopology B S hS .smooth ≤ baseOverTopology B S hS .fppf :=
  baseOverTopology_le_fppf B S hS .smooth

/-- Entry (2) of Section 03FE: `(Sch/X)_fppf ⟶ (Sch/Y)_syntomic`. -/
public theorem baseOverTopology_syntomic_le_fppf :
    baseOverTopology B S hS .syntomic ≤ baseOverTopology B S hS .fppf :=
  baseOverTopology_le_fppf B S hS .syntomic

end TenPairs

/-! ### `id_{τ,τ'}^*`, the pullback along the identity functor -/

variable (S : Scheme.{u}) (hS : B.Contains S) {τ τ' : SiteKind}

/-- **`id_{τ,τ'}^*`.**  The pullback of sheaves of modules along the morphism of ringed sites

`id_{τ,τ'} : ((Sch/S)_τ, 𝒪) ⟶ ((Sch/S)_{τ'}, 𝒪)`

of Topologies, Section 03FE, for `τ'` coarser than `τ`: the identity functor of the big category
over `S`, which is continuous from the coarser topology to the finer one, together with the
identity comparison of structure sheaves — the five structure sheaves having one and the same
underlying presheaf `T/S ↦ Γ(T, 𝒪_T)`.  Concretely it is `τ`-sheafification of a `τ'`-sheaf of
modules.

The source of this functor is written with the coefficient sheaf at `τ'` rather than with
`Stacks.SheafOfModules.ringOfLe` of the one at `τ`; the two are the same term. -/
public noncomputable abbrev baseTopologyPullback
    (h : baseOverTopology B S hS τ' ≤ baseOverTopology B S hS τ) :
    SheafOfModules.{u} (FibredSite.baseRingStructureSheaf B S hS τ') ⥤
      SheafOfModules.{u} (FibredSite.baseRingStructureSheaf B S hS τ) :=
  Stacks.SheafOfModules.comparisonPullback h (FibredSite.baseRingStructureSheaf B S hS τ)

/-- **The associated module of `(Sch/S)_τ` is `id_{τ,τ'}^*` of the associated module of
`(Sch/S)_{τ'}`**, naturally in the `𝒪_S`-module and with no hypothesis on it:

`(-)^a_{(Sch/S)_{τ'}} ⋙ id_{τ,τ'}^* ≅ (-)^a_{(Sch/S)_τ}`.

Both sides are left adjoint to one and the same functor.  The associated-module functor of
either big site is left adjoint to restriction along the inclusion of the small Zariski site of
`S` (`AlgebraicGeometry.BigFppfOver.baseAssociatedModuleAdjunction`), and that restriction does
not see the topology of the big site; `id_{τ,τ'}^*` is left adjoint to reading a `τ`-sheaf of
modules for `τ'` (`Stacks.SheafOfModules.comparisonAdjunction`), which changes neither the
underlying presheaf of modules nor the coefficient presheaf of rings.  So the right adjoint of
the composite *is* the right adjoint at `τ`, by `rfl`, and
`CategoryTheory.Adjunction.leftAdjointUniq` finishes.

This is the generalization of
`AlgebraicGeometry.BigFppfOver.comparisonPullbackBaseAssociatedModuleIso` from the pair
`(τ, fppf)` to an arbitrary comparable pair, and it is the one step of
`AlgebraicGeometry.BigFppfOver.associatedModuleBaseMixedPullbackIso` that moves the clause
between two topologies.  A helper, carrying no `stacks` attribute: the clause of Remark 03FH it
serves is stated on that declaration. -/
public noncomputable def baseAssociatedModuleTopologyPullbackIso
    (h : baseOverTopology B S hS τ' ≤ baseOverTopology B S hS τ) :
    baseAssociatedModule B S hS τ' ⋙ baseTopologyPullback B S hS h ≅
      baseAssociatedModule B S hS τ :=
  Adjunction.leftAdjointUniq
    ((baseAssociatedModuleAdjunction B S hS τ').comp
      (Stacks.SheafOfModules.comparisonAdjunction h
        (FibredSite.baseRingStructureSheaf B S hS τ)))
    (baseAssociatedModuleAdjunction B S hS τ)

/-! ### `f_sites^*` for a mixed pair of topologies -/

variable {X Y : Scheme.{u}} (hX : B.Contains X) (hY : B.Contains Y) (f : X ⟶ Y)

/-- **`f_sites^*` for the mixed-topology `f_sites`.**  The pullback of sheaves of modules along
the morphism of ringed sites

`f_sites : ((Sch/X)_τ, 𝒪_X) ⟶ ((Sch/Y)_{τ'}, 𝒪_Y)`

of Remark 070R, for `τ'` coarser than `τ`.  Topologies, Section 03FE obtains that morphism by
composing the two it has already constructed,

`(Sch/X)_τ --id_{τ,τ'}--> (Sch/X)_{τ'} --f_big--> (Sch/Y)_{τ'}`,

so its pullback is the composite of their pullbacks in the opposite order, by Modules on Sites,
Lemma 03D8: first `f_big^*` at `τ'`, which is `SheafOfModules.pullback` of
`AlgebraicGeometry.BigFppfOver.baseStructureComparison`, then
`AlgebraicGeometry.BigFppfOver.baseTopologyPullback`.

Both factors are already pullbacks along a single morphism of ringed sites, and the underlying
continuous functor of the composite is the base-change functor
`AlgebraicGeometry.BigFppfOver.baseChange` of 070R — `S'/Y ↦ X ×_Y S'/X` — composed with the
identity, as the remark describes. -/
public noncomputable abbrev baseMixedPullback
    (h : baseOverTopology B X hX τ' ≤ baseOverTopology B X hX τ) :
    SheafOfModules.{u} (FibredSite.baseRingStructureSheaf B Y hY τ') ⥤
      SheafOfModules.{u} (FibredSite.baseRingStructureSheaf B X hX τ) :=
  SheafOfModules.pullback.{u} (baseStructureComparison B hX hY f τ') ⋙
    baseTopologyPullback B X hX h

/-! ### Stacks 03FH (2) for the mixed-topology `f_sites` -/

/-- **Stacks 03FH, part (2), for the mixed-topology morphisms of ringed sites
`f_sites : ((Sch/X)_τ, 𝒪_X) ⟶ ((Sch/Y)_{τ'}, 𝒪_Y)` of Remark 070R**, one for each of the ten
pairs with `τ'` strictly coarser than `τ` among `Zariski, étale, smooth, syntomic, fppf` that
Topologies, Section 03FE lists.  The associated module of a pullback is the pullback of the
associated module,

`(f^*𝓕)^a ≅ f_sites^*(𝓕^a)`,

naturally in the `𝒪_Y`-module `𝓕`.

The hypothesis is Section 03FE's own condition for `f_sites` to be on its list, that `τ` is a
stronger topology than `τ'`; nothing is assumed of `𝓕`, and nothing of `f` beyond `X` and `Y`
lying in the chosen big fppf site.  The ten pairs all satisfy it, which
`AlgebraicGeometry.BigFppfOver.baseOverTopology_le_of_baseTopology_le` and the three inequalities
`AlgebraicGeometry.BigFppfSite.zariskiTopology_le_etaleTopology`,
`.etaleTopology_le_smoothTopology`, `.smoothTopology_le_syntomicTopology` supply, together with
`AlgebraicGeometry.BigFppfOver.baseOverTopology_le_fppf`.

The proof is the source's: `f_sites` is `f_big ∘ id_{τ,τ'}`, so `f_sites^*` is
`id_{τ,τ'}^* ∘ f_big^*` by Lemma 03D8, and then

`(f^*𝓕)^a_τ ≅ id_{τ,τ'}^*((f^*𝓕)^a_{τ'}) ≅ id_{τ,τ'}^*(f_big^*(𝓕^a_{τ'}))`,

the first step being
`AlgebraicGeometry.BigFppfOver.baseAssociatedModuleTopologyPullbackIso` and the second the
same-topology clause at `τ'`,
`AlgebraicGeometry.BigFppfOver.associatedModuleBasePullbackIso`.

Together with that same-topology clause, which covers the five entries of Section 03FE with
`τ = τ'`, this covers every one of the fifteen entries that go between two big sites.

The clause for the single morphism of ringed sites registered for Remark 070R, on the big sites
carried by the chosen big fppf site, is
`AlgebraicGeometry.BigFppfSite.associatedModuleBigRingedSiteHomPullbackIso`; this declaration
states it for the pullback written out above and carries no `stacks` attribute. -/
public noncomputable def associatedModuleBaseMixedPullbackIso
    (h : baseOverTopology B X hX τ' ≤ baseOverTopology B X hX τ) :
    Scheme.Modules.pullback f ⋙ baseAssociatedModule B X hX τ ≅
      baseAssociatedModule B Y hY τ' ⋙ baseMixedPullback B hX hY f h :=
  Functor.isoWhiskerLeft (Scheme.Modules.pullback f)
      (baseAssociatedModuleTopologyPullbackIso B X hX h).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (associatedModuleBasePullbackIso B hX hY f τ')
      (baseTopologyPullback B X hX h) ≪≫
    Functor.associator _ _ _

/-- **Stacks 03FH, part (2), at one module**, for the mixed-topology
`f_sites : ((Sch/X)_τ, 𝒪_X) ⟶ ((Sch/Y)_{τ'}, 𝒪_Y)` of Remark 070R at each of the ten pairs with
`τ'` coarser than `τ`: `(f^*𝓕)^a ≅ f_sites^*(𝓕^a)`, read off from
`AlgebraicGeometry.BigFppfOver.associatedModuleBaseMixedPullbackIso`.

The clause for the single morphism of ringed sites registered for Remark 070R, on the big sites
carried by the chosen big fppf site, is
`AlgebraicGeometry.BigFppfSite.associatedModuleBigRingedSiteHomPullbackIso`; this declaration
states it for the pullback written out above and carries no `stacks` attribute. -/
public noncomputable def associatedModuleBaseMixedObjPullbackIso
    (h : baseOverTopology B X hX τ' ≤ baseOverTopology B X hX τ) (𝓕 : Y.Modules) :
    (baseAssociatedModule B X hX τ).obj ((Scheme.Modules.pullback f).obj 𝓕) ≅
      (baseMixedPullback B hX hY f h).obj ((baseAssociatedModule B Y hY τ').obj 𝓕) :=
  (associatedModuleBaseMixedPullbackIso B hX hY f h).app 𝓕

end AlgebraicGeometry.BigFppfOver

end
