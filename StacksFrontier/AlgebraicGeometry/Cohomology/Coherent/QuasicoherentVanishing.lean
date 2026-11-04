module

import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoherentFinitePresentation
import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Basic
import StacksFrontier.AlgebraicGeometry.CoherentTFAE.Basic
public import StacksFrontier.AlgebraicGeometry.ModuleGlobalSections
import StacksFrontier.AlgebraicGeometry.QuasiCoherent.FinitePresentationColimit
import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.CohomologyFilteredColimits
public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.Cohomology
import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.CohomologyComparison
public import StacksFrontier.Topology.Sheaves.Cohomology.Locality.CohomologyVanishesLocally
import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.GlobalSheafCohomologyComparison
import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.VanishingTransfer

/-!
# Cohomology vanishing in a fixed degree: coherent against quasi-coherent modules

On a Noetherian scheme `X`, and in any fixed degree `d`, the cohomology group `Hᵈ(X, F)`
vanishes for every coherent `𝒪_X`-module `F` if and only if it vanishes for every quasi-coherent
`𝒪_X`-module `F`. This is the equivalence (1) ⇔ (2) of [Stacks, Tag 0G5F], whose proof in the
source is the last paragraph of that theorem: it uses nothing about `X` being of finite type over
a field, nor about `d` being the dimension, so it is stated here for an arbitrary Noetherian
scheme and an arbitrary degree.

One direction is trivial, a coherent module being quasi-coherent. For the other, a
quasi-coherent module is a filtered colimit of coherent ones and cohomology on a quasi-compact
quasi-separated scheme commutes with filtered colimits ([Stacks, Tag 01FF]), so the colimit
inherits the vanishing of its members.

## Main results

* `AlgebraicGeometry.isZero_rightDerived_moduleGlobalSections_of_forall_isFinitePresentation`: on a
  quasi-compact quasi-separated scheme, if `Hᵈ(X, G)` vanishes for every module `G` of finite
  presentation then it vanishes for every quasi-coherent module. This is the general form of the
  nontrivial implication; no Noetherian hypothesis is needed.
* **[Stacks, Tag 0G5F], (1) ⇔ (2)**:
  `forall_isZero_rightDerived_moduleGlobalSections_isCoherent_iff_isQuasicoherent`,
  for the module-valued cohomology
  `((AlgebraicGeometry.moduleGlobalSections X).rightDerived d).obj F`.
* `AlgebraicGeometry.forall_isZero_hgroup_top_isCoherent_iff_isQuasicoherent`: the same for the
  abelian-group-valued cohomology `Hgroup X.ringCatSheaf ⊤ d F`.
* `AlgebraicGeometry.forall_isZero_cohomologyOverField_isCoherent_iff_isQuasicoherent`: the same
  for `AlgebraicGeometry.cohomologyOverField`, the cohomology over a ground field in which
  [Stacks, Tag 0FVV] part (6) is stated.
* `AlgebraicGeometry.forall_subsingleton_sheafH_isCoherent_iff_isQuasicoherent`: the same for
  Mathlib's `Ext`-theoretic sheaf cohomology `Sheaf.H` of the underlying abelian sheaf, at an
  arbitrary `Ext` universe.

## Implementation notes

**The colimit used is that of [Stacks, Tag 01PK], not of [Stacks, Tag 01PG].** The source writes
a quasi-coherent module as the filtered colimit of its coherent submodules (Tag 01PG on a
Noetherian scheme). That diagram is indexed by subobjects of `F` in `X.Modules`, a category one
universe too large for [Stacks, Tag 01FF], which needs an index category in `Type u`. Tag 01PK
supplies a directed system indexed in `Type u` of modules of finite presentation with colimit
`F`, and on a locally Noetherian scheme a module of finite presentation is coherent
(`Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isFinitePresentation`, Tag 01XZ). The
mathematics is the source's; only the indexing of the colimit differs.

**The four cohomology models.** The module-valued spelling is primary because it is the one
[Stacks, Tag 01FF] is stated in on schemes, as `Stacks.AlgebraicGeometry.TopDegreeBaseChange`'s
`preservesColimitsOfShape_rightDerived_moduleGlobalSections_of_isFiltered`, and the one the
dévissage of (3) ⇒ (1) of [Stacks, Tag 0G5F] is written in. It derives sections as a functor
on `AlgebraicGeometry.Scheme.Modules`, whose category structure is a separate instance from that
of `SheafOfModules X.ringCatSheaf`, over which `AlgebraicGeometry.cohomologyOverField` and
`Hgroup` derive; the two derived functors agree by definitional unfolding, which the comparison
with `Hgroup` crosses once.
The other three are obtained from it by the existing vanishing comparisons:
`Stacks.Cohomology.ModuleComparison.isZero_rightDerived_evaluation_iff_isZero_hgroup`,
`AlgebraicGeometry.isZero_cohomologyOverField_iff_isZero_hgroup` and
`Stacks.Cohomology.ModuleComparison.isZero_schemeHgroupTop_iff_subsingleton_sheafH`, the last of
which is at the `Ext` universe `u`; Mathlib's `CategoryTheory.Abelian.Ext.chgUniv` moves it to an
arbitrary `Ext` universe, `HasExt.{u}` itself being supplied by
`CategoryTheory.hasExt_of_enoughInjectives`.

## References

* [Stacks Project, Tag 0G5F](https://stacks.math.columbia.edu/tag/0G5F)
* [Stacks Project, Tag 01FF](https://stacks.math.columbia.edu/tag/01FF)
* [Stacks Project, Tag 01PG](https://stacks.math.columbia.edu/tag/01PG)
* [Stacks Project, Tag 01PK](https://stacks.math.columbia.edu/tag/01PK)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe w' u

namespace AlgebraicGeometry

noncomputable section

/-- **Vanishing for modules of finite presentation gives vanishing for all quasi-coherent
modules.** On a quasi-compact quasi-separated scheme `X`, if `Hᵈ(X, G)` vanishes for every
`𝒪_X`-module `G` of finite presentation then `Hᵈ(X, F)` vanishes for every quasi-coherent `F`.

`F` is a directed colimit of modules of finite presentation ([Stacks, Tag 01PK],
`AlgebraicGeometry.exists_directed_system_of_isFinitePresentation`), and `Hᵈ(X, -)` preserves
that colimit ([Stacks, Tag 01FF]); a colimit of zero objects is zero. This is the ℕ-indexed
form of `Stacks.AlgebraicGeometry.TopDegreeBaseChange`'s
`isZero_rightDerivedPlus_moduleGlobalSections_of_forall_isFinitePresentation`. -/
theorem isZero_rightDerived_moduleGlobalSections_of_forall_isFinitePresentation
    {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X] (d : ℕ)
    (h : ∀ G : X.Modules, G.IsFinitePresentation →
      IsZero (((moduleGlobalSections X).rightDerived d).obj G))
    (F : X.Modules) [F.IsQuasicoherent] :
    IsZero (((moduleGlobalSections X).rightDerived d).obj F) := by
  obtain ⟨I, _, _, _, D, φ, hFP, ⟨hc⟩⟩ := exists_directed_system_of_isFinitePresentation X F
  have : PreservesColimitsOfShape I ((moduleGlobalSections X).rightDerived d) := by
    open Stacks.AlgebraicGeometry.TopDegreeBaseChange in
    exact preservesColimitsOfShape_rightDerived_moduleGlobalSections_of_isFiltered X d I
  exact (Stacks.Cohomology.ModuleColimit.isZero_colimit_of_isZero
      (D ⋙ (moduleGlobalSections X).rightDerived d) fun i => h (D.obj i) (hFP i)).of_iso
    ((isColimitOfPreserves ((moduleGlobalSections X).rightDerived d)
      hc).coconePointUniqueUpToIso (colimit.isColimit _))

/-- **[Stacks, Tag 0G5F], (1) ⇔ (2), for the module-valued cohomology.** On a Noetherian scheme
`X` and in any degree `d`, the `Γ(X, 𝒪_X)`-module `Hᵈ(X, F)` vanishes for every coherent
`𝒪_X`-module `F` if and only if it vanishes for every quasi-coherent `𝒪_X`-module `F`.

The source states this for `X` separated of finite type over a field and `d = dim X`; its proof
uses neither, so it is stated for every Noetherian scheme and every degree. The forward
direction is `isZero_rightDerived_moduleGlobalSections_of_forall_isFinitePresentation`, a module
of finite presentation on a locally Noetherian scheme being coherent ([Stacks, Tag 01XZ]); the
backward direction holds because a coherent module is quasi-coherent. -/
theorem forall_isZero_rightDerived_moduleGlobalSections_isCoherent_iff_isQuasicoherent
    (X : Scheme.{u}) [IsNoetherian X] (d : ℕ) :
    (∀ (F : X.Modules) [F.IsCoherent],
      IsZero (((moduleGlobalSections X).rightDerived d).obj F)) ↔
    (∀ (F : X.Modules) [F.IsQuasicoherent],
      IsZero (((moduleGlobalSections X).rightDerived d).obj F)) := by
  refine ⟨fun h F _ => isZero_rightDerived_moduleGlobalSections_of_forall_isFinitePresentation d
    (fun G hG => ?_) F, fun h F _ => ?_⟩
  · have := Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isFinitePresentation G hG
    exact h G
  · have := (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent F).1
    exact h F

/-- A coherent-versus-quasi-coherent vanishing equivalence transfers along a pointwise
equivalence of the vanishing predicates. -/
private theorem forall_isCoherent_iff_isQuasicoherent_of_iff {X : Scheme.{u}}
    {P Q : X.Modules → Prop} (e : ∀ F, P F ↔ Q F)
    (h : (∀ (F : X.Modules) [F.IsCoherent], P F) ↔ (∀ (F : X.Modules) [F.IsQuasicoherent], P F)) :
    (∀ (F : X.Modules) [F.IsCoherent], Q F) ↔ (∀ (F : X.Modules) [F.IsQuasicoherent], Q F) := by
  simp only [← e]
  exact h

/-- **[Stacks, Tag 0G5F], (1) ⇔ (2), for the abelian-group-valued cohomology** `Hgroup`. On a
Noetherian scheme and in any degree `d`, `Hᵈ(X, F)` vanishes for every coherent module exactly
when it vanishes for every quasi-coherent module. This is
`forall_isZero_rightDerived_moduleGlobalSections_isCoherent_iff_isQuasicoherent` read through
`Stacks.Cohomology.ModuleComparison.isZero_rightDerived_evaluation_iff_isZero_hgroup`. -/
theorem forall_isZero_hgroup_top_isCoherent_iff_isQuasicoherent
    (X : Scheme.{u}) [IsNoetherian X] (d : ℕ) :
    (∀ (F : X.Modules) [F.IsCoherent], IsZero (Hgroup X.ringCatSheaf ⊤ d F)) ↔
    (∀ (F : X.Modules) [F.IsQuasicoherent], IsZero (Hgroup X.ringCatSheaf ⊤ d F)) := by
  exact forall_isCoherent_iff_isQuasicoherent_of_iff
    (Stacks.Cohomology.ModuleComparison.isZero_rightDerived_evaluation_iff_isZero_hgroup
      X.ringCatSheaf ⊤ d)
    (forall_isZero_rightDerived_moduleGlobalSections_isCoherent_iff_isQuasicoherent X d)

/-- **[Stacks, Tag 0G5F], (1) ⇔ (2), for the cohomology over a ground field.** For a Noetherian
scheme `X` with a morphism `f : X ⟶ Spec k` to the spectrum of a field and any degree `d`, the
`k`-vector space `Hᵈ(X, F)` of `AlgebraicGeometry.cohomologyOverField` vanishes for every
coherent module exactly when it vanishes for every quasi-coherent module. This is the spelling
of cohomology in which [Stacks, Tag 0FVV] part (6) is stated. -/
theorem forall_isZero_cohomologyOverField_isCoherent_iff_isQuasicoherent
    (k : Type u) [Field k] {X : Scheme.{u}} [IsNoetherian X] (f : X ⟶ Spec (.of k)) (d : ℕ) :
    (∀ (F : X.Modules) [F.IsCoherent], IsZero (cohomologyOverField k f F d)) ↔
    (∀ (F : X.Modules) [F.IsQuasicoherent], IsZero (cohomologyOverField k f F d)) := by
  exact forall_isCoherent_iff_isQuasicoherent_of_iff
    (fun F => (isZero_cohomologyOverField_iff_isZero_hgroup k f (i := d) F).symm)
    (forall_isZero_hgroup_top_isCoherent_iff_isQuasicoherent X d)

/-- On a scheme, the global cohomology `Sheaf.H` of the underlying abelian sheaf of a module, at
any `Ext` universe, vanishes exactly when `Hgroup X.ringCatSheaf ⊤ d F` does. The comparison
`Stacks.Cohomology.ModuleComparison.isZero_schemeHgroupTop_iff_subsingleton_sheafH` is at the
`Ext` universe `u`, which exists by `hasExt_of_enoughInjectives`, and `Abelian.Ext.chgUniv`
moves the vanishing to the universe `w'`. -/
private theorem subsingleton_sheafH_iff_isZero_hgroup_top (X : Scheme.{u})
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
    [HasExt.{w'} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]
    (d : ℕ) (F : X.Modules) :
    Subsingleton (Sheaf.H.{w', u} ((SheafOfModules.toSheaf X.ringCatSheaf).obj F) d) ↔
      IsZero (Hgroup X.ringCatSheaf ⊤ d F) := by
  have := hasExt_of_enoughInjectives.{u} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
  rw [Stacks.Cohomology.ModuleComparison.isZero_schemeHgroupTop_iff_subsingleton_sheafH]
  exact (Abelian.Ext.chgUniv.{w', u}).subsingleton_congr.symm

/-- **[Stacks, Tag 0G5F], (1) ⇔ (2), for Mathlib's sheaf cohomology** `Sheaf.H`. On a
Noetherian scheme `X` and in any degree `d`, the sheaf cohomology `Hᵈ(X, F)` of the underlying
abelian sheaf vanishes for every coherent `𝒪_X`-module `F` if and only if it vanishes for every
quasi-coherent `𝒪_X`-module `F`. The `Ext` universe `w'` is arbitrary.

The source states this for `X` separated of finite type over a field and `d = dim X`; its proof
uses neither. -/
theorem forall_subsingleton_sheafH_isCoherent_iff_isQuasicoherent
    (X : Scheme.{u}) [IsNoetherian X]
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
    [HasExt.{w'} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]
    (d : ℕ) :
    (∀ (F : X.Modules) [F.IsCoherent],
      Subsingleton (Sheaf.H.{w', u} ((SheafOfModules.toSheaf X.ringCatSheaf).obj F) d)) ↔
    (∀ (F : X.Modules) [F.IsQuasicoherent],
      Subsingleton (Sheaf.H.{w', u} ((SheafOfModules.toSheaf X.ringCatSheaf).obj F) d)) := by
  exact forall_isCoherent_iff_isQuasicoherent_of_iff
    (fun F => (subsingleton_sheafH_iff_isZero_hgroup_top X d F).symm)
    (forall_isZero_hgroup_top_isCoherent_iff_isQuasicoherent X d)

end

end AlgebraicGeometry
