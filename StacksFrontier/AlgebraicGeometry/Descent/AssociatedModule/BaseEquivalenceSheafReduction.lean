module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.BaseEquivalenceFppf
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherentTopologiesTwo.TopologyIndependence

/-!
# Clause (1) of Stacks 03DX at a coarser `τ`, reduced to the fppf sheaf condition

`StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.BaseEquivalenceFppf` records that
clause (1) of Stacks 03DX is short of the four topologies `τ ∈ {Zariski, étale, smooth,
syntomic}` by exactly four instances of one predicate,
`AlgebraicGeometry.BigFppfOver.BaseQuasicoherentIsEssImageAssociatedModule τ` — essential
surjectivity of `𝓕 ↦ 𝓕^a` onto `QCoh((Sch/S)_τ, 𝒪)`.  **This file reduces that predicate, at
every `τ`, to the sheaf condition alone**: if every quasi-coherent `𝒪`-module on `(Sch/S)_τ` is
a sheaf for the *fppf* topology, then `𝓕 ↦ 𝓕^a` is essentially surjective onto
`QCoh((Sch/S)_τ, 𝒪)`, and hence an equivalence there.

Nothing beyond that sheaf condition is missing, and the three steps that carry it are each
already in the library:

* quasi-coherence passes from the coarser topology to the finer one for a module that *is* an
  fppf sheaf, `Stacks.SheafOfModules.isQuasicoherentOnSite_of_le`;
* essential surjectivity at `τ = fppf` is unconditional,
  `AlgebraicGeometry.BigFppfOver.quasicoherentIsEssImageAssociatedModule'`;
* and `𝓕 ↦ 𝓕^a` on `(Sch/S)_τ` *is* `𝓕 ↦ 𝓕^a` on `(Sch/S)_fppf` read for the coarser
  topology, as an isomorphism of functors:
  `AlgebraicGeometry.BigFppfOver.restrictTopologyAssociatedModuleQcohIso`, the key to
  Stacks 0GNE.

The converse holds too, and is proved below, so the reduction is not a weakening: the
outstanding predicate at `τ` and the fppf sheaf condition for the quasi-coherent modules of
`(Sch/S)_τ` are **equivalent**.  That is the precise size of the remaining gap in clause (1):
one sheaf condition, not a second run of fpqc descent.

## Main definitions

* `AlgebraicGeometry.BigFppfOver.IsSheafFppfOfIsQuasicoherentOnSite`: the sheaf condition in
  question — every quasi-coherent `𝒪`-module on `(Sch/S)_τ` is a sheaf for the localized fppf
  topology.  This is the instance at the big `τ`-site of `S` of
  `AlgebraicGeometry.FibredSite.IsSheafFppfOfQuasicoherentOnSite`, the first of the two inputs
  of Stacks 0EM8 that
  `StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SiteEquivalence` carries as a hypothesis.

## Main results

* `AlgebraicGeometry.BigFppfOver.isSheafFppfOfIsQuasicoherentOnSite_fppf`: the condition holds
  at `τ = fppf`, where it is the sheaf condition the module already carries.
* `AlgebraicGeometry.BigFppfOver.baseQuasicoherentIsEssImageAssociatedModule_of_isSheafFppf`:
  **the reduction** — the condition at `τ` gives the outstanding predicate of clause (1) at
  `τ`.
* `AlgebraicGeometry.BigFppfOver.isEquivalence_baseAssociatedModuleQcohOnSite_of_isSheafFppf`
  and `AlgebraicGeometry.BigFppfOver.baseAssociatedModuleEquivalenceOnSite_of_isSheafFppf`:
  **clause (1) of Stacks 03DX at `τ`, over that sheaf condition alone.**
* `AlgebraicGeometry.BigFppfOver.isSheafFppfOfIsQuasicoherentOnSite_of_essImage`: the converse,
  so that the two are equivalent;
  `AlgebraicGeometry.BigFppfOver.isSheafFppfOfIsQuasicoherentOnSite_iff` states the
  equivalence.

## Implementation notes

No `stacks` attribute is placed.  Everything below carries the hypothesis
`AlgebraicGeometry.BigFppfOver.IsSheafFppfOfIsQuasicoherentOnSite`, which is not discharged
here at any `τ` other than fppf, and a hypothesis is part of a citation.  The hypothesis is
discharged at **every** `τ` in
`StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.BaseEssentialSurjectivity`
(`AlgebraicGeometry.BigFppfOver.isSheaf_fppf_of_isQuasicoherentOnSite`), where clause (1) is
registered for every `τ`.
Clause (1) at `τ = fppf` is also registered, on
`AlgebraicGeometry.BigFppfOver.isEquivalence_associatedModuleQcohOnSite_fppf` and
`AlgebraicGeometry.BigFppfOver.associatedModuleEquivalence_fppf`, and the `τ = fppf` instances
below add no scope to it.

**Why the three transports are all `rfl`.**  Reading a module sheaf for a coarser topology
changes neither the underlying presheaf of modules nor the coefficient presheaf of rings
(`AlgebraicGeometry.FibredSite.baseRingStructureSheaf_obj`), and a sheaf condition is a
proposition, so `Stacks.SheafOfModules.ringOfLe` applied to the fppf structure sheaf *is* the
`τ`-structure sheaf and `AlgebraicGeometry.BigFppfOver.restrictTopology` applied to the fppf
reading of a `τ`-sheaf *is* that `τ`-sheaf.  Neither identification is stated as a lemma below
because neither is ever invoked: both hold by `rfl` and the elaborator discharges them.

**Why the converse needs the functor isomorphism and not the objectwise one.**  It does not;
the objectwise `AlgebraicGeometry.BigFppfOver.restrictTopologyAssociatedModuleIso` would do.
The functor form is used in both directions only because it is the form in which the
quasi-coherent subcategories are already compared, so the two proofs share one comparison.

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 0EM8](https://stacks.math.columbia.edu/tag/0EM8)
* [Stacks Project, Tag 0GNE](https://stacks.math.columbia.edu/tag/0GNE)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.BigFppfOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The fppf sheaf condition for the quasi-coherent modules of `(Sch/S)_τ`**: every
`𝒪`-module on the big `τ`-site of `S` which is quasi-coherent there, in the sense of
Stacks 03DL (6), has an underlying presheaf of modules which is a sheaf for the localized fppf
topology.

This is the instance at the big `τ`-site of `S` of
`AlgebraicGeometry.FibredSite.IsSheafFppfOfQuasicoherentOnSite`. -/
public abbrev IsSheafFppfOfIsQuasicoherentOnSite (τ : SiteKind) : Prop :=
  ∀ M : SheafOfModules.{u} (FibredSite.baseRingStructureSheaf B S hS τ),
    M.IsQuasicoherentOnSite → Presheaf.IsSheaf (topology B S hS) M.val.presheaf

/-- The condition holds at `τ = fppf`: there the localized `τ`-topology *is* the localized fppf
topology, so the assertion is the sheaf condition the module carries. -/
public theorem isSheafFppfOfIsQuasicoherentOnSite_fppf :
    IsSheafFppfOfIsQuasicoherentOnSite B S hS .fppf := fun M _ => M.isSheaf

/-- **The reduction of clause (1) of Stacks 03DX at `τ` to the fppf sheaf condition.**  If every
quasi-coherent `𝒪`-module on `(Sch/S)_τ` is a sheaf for the localized fppf topology, then every
such module is isomorphic to an `𝓕^a` for a quasi-coherent `𝒪_S`-module `𝓕`.

Read the module as an fppf sheaf; quasi-coherence survives the reading
(`Stacks.SheafOfModules.isQuasicoherentOnSite_of_le`); essential surjectivity at `τ = fppf`
produces the `𝓕` (`AlgebraicGeometry.BigFppfOver.quasicoherentIsEssImageAssociatedModule'`);
and `AlgebraicGeometry.BigFppfOver.restrictTopologyAssociatedModuleQcohIso` turns the fppf
`𝓕^a`, read back for `τ`, into the `τ`-associated module. -/
public theorem baseQuasicoherentIsEssImageAssociatedModule_of_isSheafFppf (τ : SiteKind)
    (h : IsSheafFppfOfIsQuasicoherentOnSite B S hS τ) :
    BaseQuasicoherentIsEssImageAssociatedModule B S hS τ := by
  intro G hG
  have hG' : (⟨G.val, h G hG⟩ :
      SheafOfModules.{u} (structureSheaf B S hS)).IsQuasicoherentOnSite :=
    Stacks.SheafOfModules.isQuasicoherentOnSite_of_le
      (baseOverTopology_le_fppf B S hS τ) (structureSheaf B S hS) _ hG
  obtain ⟨F, ⟨e⟩⟩ := quasicoherentIsEssImageAssociatedModule' B S hS _ hG'
  exact ⟨F, ⟨(restrictTopologyAssociatedModuleQcohIso B S hS τ).app F ≪≫
    (restrictTopology B S hS τ).mapIso e⟩⟩

/-- **Clause (1) of Stacks 03DX at `τ`, over the fppf sheaf condition alone**: `𝓕 ↦ 𝓕^a` is an
equivalence `QCoh(𝒪_S) ⥤ QCoh((Sch/S)_τ, 𝒪)`.  Full faithfulness is unconditional at every `τ`
(Stacks 0GN7, `AlgebraicGeometry.BigFppfOver.fullyFaithfulBaseAssociatedModuleQcoh`). -/
public theorem isEquivalence_baseAssociatedModuleQcohOnSite_of_isSheafFppf (τ : SiteKind)
    (h : IsSheafFppfOfIsQuasicoherentOnSite B S hS τ) :
    (baseAssociatedModuleQcohOnSite B S hS τ).IsEquivalence :=
  isEquivalence_baseAssociatedModuleQcohOnSite B S hS τ
    (baseQuasicoherentIsEssImageAssociatedModule_of_isSheafFppf B S hS τ h)

/-- **The equivalence of categories of clause (1) of Stacks 03DX at `τ`, over the fppf sheaf
condition alone**, `QCoh(𝒪_S) ≌ QCoh((Sch/S)_τ, 𝒪)`, with `𝓕 ↦ 𝓕^a` as its functor. -/
public noncomputable def baseAssociatedModuleEquivalenceOnSite_of_isSheafFppf (τ : SiteKind)
    (h : IsSheafFppfOfIsQuasicoherentOnSite B S hS τ) :
    (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory ≌
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (FibredSite.baseRingStructureSheaf B S hS τ)).FullSubcategory :=
  baseAssociatedModuleEquivalenceOnSite B S hS τ
    (baseQuasicoherentIsEssImageAssociatedModule_of_isSheafFppf B S hS τ h)

/-- **The converse of the reduction.**  If `𝓕 ↦ 𝓕^a` is essentially surjective onto
`QCoh((Sch/S)_τ, 𝒪)` then every quasi-coherent `𝒪`-module on `(Sch/S)_τ` is a sheaf for the
localized fppf topology: it is isomorphic to a `τ`-associated module, which by
`AlgebraicGeometry.BigFppfOver.restrictTopologyAssociatedModuleQcohIso` is an fppf associated
module read for `τ` — and that is an fppf sheaf on the nose. -/
public theorem isSheafFppfOfIsQuasicoherentOnSite_of_essImage (τ : SiteKind)
    (h : BaseQuasicoherentIsEssImageAssociatedModule B S hS τ) :
    IsSheafFppfOfIsQuasicoherentOnSite B S hS τ := by
  intro M hM
  obtain ⟨F, ⟨e⟩⟩ := h M hM
  have i : (associatedModuleQcoh B S hS ⋙ restrictTopology B S hS τ).obj F ≅ M :=
    ((restrictTopologyAssociatedModuleQcohIso B S hS τ).app F).symm ≪≫ e
  have i' : ((associatedModule B S hS).obj F.obj).val.presheaf ≅ M.val.presheaf :=
    (PresheafOfModules.toPresheaf _).mapIso
      ((SheafOfModules.forget (FibredSite.baseRingStructureSheaf B S hS τ)).mapIso i)
  exact (Presheaf.isSheaf_of_iso_iff i').1 ((associatedModule B S hS).obj F.obj).isSheaf

/-- **The outstanding predicate of clause (1) of Stacks 03DX at `τ` and the fppf sheaf
condition for the quasi-coherent modules of `(Sch/S)_τ` are equivalent.**  So the remaining gap
in clause (1) at `τ ∈ {Zariski, étale, smooth, syntomic}` is exactly one sheaf condition. -/
public theorem isSheafFppfOfIsQuasicoherentOnSite_iff (τ : SiteKind) :
    IsSheafFppfOfIsQuasicoherentOnSite B S hS τ ↔
      BaseQuasicoherentIsEssImageAssociatedModule B S hS τ :=
  ⟨baseQuasicoherentIsEssImageAssociatedModule_of_isSheafFppf B S hS τ,
    isSheafFppfOfIsQuasicoherentOnSite_of_essImage B S hS τ⟩

end AlgebraicGeometry.BigFppfOver

end
