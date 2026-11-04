module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleCounit
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentCartesianOnAffineCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedModuleComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.RingedSite
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleChartSheaves
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRepresentableEquivalence
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentSiteEquivalence
public import StacksFrontier.AlgebraicGeometry.Topologies.SmallEtaleStructureSheaf

/-!
# Quasi-coherent modules on a representable algebraic space

Let `B` be a big fppf site containing a scheme `S` and let `U` be an object of the big fppf site
over `S`.  The small étale site of the algebraic space `yoneda.obj U` is equivalent to the small
étale site of the scheme underlying `U`, taken in the big étale site carried by the same category
of schemes (`AlgebraicGeometry.Space.representedSmallEtaleEquivalence`).  This file matches the
two structure sheaves across that equivalence — on the nose, by `rfl` — and transports modules
and quasi-coherence along it.  Composing with Descent, Proposition 03DX (2) for a scheme then
identifies the quasi-coherent modules on the small étale site of `yoneda.obj U` with the
quasi-coherent `AlgebraicGeometry.Scheme.Modules` on the scheme underlying `U`.

## Main definitions

* `AlgebraicGeometry.Space.representedSchemeStructureSheaf` is the structure sheaf of the small
  étale site of the scheme underlying `U`, and
  `AlgebraicGeometry.Space.representedStructureRingSheaf` is the structure sheaf of the small
  étale site of `yoneda.obj U`, with commutativity forgotten.
* `AlgebraicGeometry.Space.representedSmallEtaleModule` reads a module on the small étale site
  of the scheme underlying `U` as an `𝒪`-module on the small étale site of `yoneda.obj U`, and
  `AlgebraicGeometry.Space.representedSmallEtaleModuleEquivalence` is the equivalence of the two
  module categories.
* `AlgebraicGeometry.Space.representedQuasicoherentEquivalence`,
  `AlgebraicGeometry.Space.representedQuasicoherentSchemeEquivalence` and
  `AlgebraicGeometry.Space.representedQuasicoherentSheavesEquivalence` are the induced
  equivalences of the categories of quasi-coherent modules.

## Main results

* `AlgebraicGeometry.Space.reindexRing_representedSmallEtaleEquivalence`: **the two structure
  sheaves agree**, by `rfl`.
* `AlgebraicGeometry.Space.isDenseSubsite_representedSmallEtaleEquivalence_functor`: the
  comparison functor is a dense subsite inclusion.  The hypothesis under which quasi-coherence is
  invariant is the same property of the *inverse*, which is proved as
  `AlgebraicGeometry.Space.isDenseSubsite_representedSmallEtaleEquivalence_inverse` in
  `StacksFrontier/AlgebraicGeometry/Spaces/SheafOfDifferentialsQuasicoherent.lean` and is imported
  rather than reproved here.
* `AlgebraicGeometry.Space.isQuasicoherentOnSite_representedSmallEtaleModule_iff`: a module on
  the small étale site of the scheme underlying `U` is quasi-coherent exactly when the
  `𝒪`-module it becomes on the small étale site of `yoneda.obj U` is.
* `AlgebraicGeometry.Space.representedQuasicoherentSchemeHomEquiv`: the Hom-sets of
  `QCoh(𝒪_{yoneda.obj U})` and of `QCoh(𝒪_T)`, for `T` the scheme underlying `U`, agree.
* `AlgebraicGeometry.Space.chartSpace_eq_yoneda`: the algebraic space represented by an étale
  chart is the Yoneda algebraic space of the chart's object, definitionally.
* `AlgebraicGeometry.Space.chartSchemeModule` and
  `AlgebraicGeometry.Space.isQuasicoherent_chartSchemeModule`: **a quasi-coherent `𝒪_X`-module on
  an algebraic space restricts, on each étale scheme chart, to a quasi-coherent
  `AlgebraicGeometry.Scheme.Modules` on the chart's scheme.**  This is the composite of the
  localization of Stacks 04M0 at the chart with the equivalence above.

## Implementation notes

**The comparison between `AlgebraicGeometry.Scheme.Modules` of a scheme and the modules on the
small étale site of the algebraic space it represents exists, and it is
`AlgebraicGeometry.Space.representedQuasicoherentSchemeEquivalence` below.**  This is worth
saying plainly, because the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/CoherentPushforwardReduction.lean` state both that
`AlgebraicGeometry.Space.representedSmallEtaleEquivalence` "carries no structure sheaf" and that
no such comparison exists anywhere; the first is what this file supplies and the second is false
once it does.  The general point is worth keeping in mind when reading any such remark: a comment
saying the library *has* no comparison records what had been written when it was written, not
what is true or what is reachable.  Here the transport turned out to hold by `rfl`.

**The chart space and the Yoneda algebraic space of its object are the same term.**  For an
étale chart `V` of an algebraic space `X`, `AlgebraicGeometry.Space.chartSpace B S hS X V` and
`yoneda.obj ((AlgebraicGeometry.Space.SmallEtale.toOver B S hS X.1).obj V)` are definitionally
equal — `AlgebraicGeometry.Space.chartSpace_eq_yoneda` — so the equivalence of this file composes
directly with the localization of Stacks 04M0 at a chart, and no comparison between the two
readings of the chart space has to be built.

The structure sheaf of the small étale site of an algebraic space sends an étale chart to the
global regular functions on its underlying scheme, and so does the structure sheaf of the small
étale site of a scheme; the comparison equivalence leaves the underlying object of the category
of size-bounded schemes unchanged, because
`AlgebraicGeometry.associatedBigEtaleSite` is carried by the *same* category of schemes as `B`
and with the same size cutoff.  The match of the two structure sheaves is therefore an equality,
not merely an isomorphism — which is what makes the transport possible at all:
`Stacks.SheafOfModules.isQuasicoherentOnSite_reindex_iff` compares a module over the transported
sheaf of rings with a module over the sheaf of rings of the target site, and the invariance of
quasi-coherence under restriction of scalars along an isomorphism of sheaves of rings is not
available.  This is the same mechanism as for Stacks 04M0, where
`AlgebraicGeometry.Space.reindexRing_chartLocalizationEquivalence` is likewise `rfl`.

Both sites have objects in `Type (u + 1)` and morphisms in `Type u`, which is what
`Stacks.SheafOfModules.isQuasicoherentOnSite_reindex_iff` asks for, its transport of a global
presentation being stated for two sites in the same pair of universes.

**The module universe is pinned to `u`, not free.**  Descent, Proposition 03DX (2) at
`τ = étale` is available only at the module universe of the structure rings
(`AlgebraicGeometry.SmallEtale.associatedModuleEquivalence'`), so every statement below which
crosses it — `AlgebraicGeometry.Space.representedQuasicoherentSchemeEquivalence` and the chart
restrictions built from it — is at module universe `u`.  A consumer working at a module universe
other than `u` cannot use these; the equivalences of the small étale sites themselves
(`AlgebraicGeometry.Space.representedSmallEtaleModuleEquivalence` and the quasi-coherence
criterion beside it) carry no such restriction.

`AlgebraicGeometry.Space.representedStructureRingSheaf` is typed at
`AlgebraicGeometry.Space.SmallEtale.topology` rather than at the projection
`(AlgebraicGeometry.Space.smallEtaleRingedSite ‹_›).J`, to which it is definitionally equal:
with the ringed-site reading, instance search does not find the continuity of the comparison
functor, the topology being hidden behind a structure projection.  An
`AlgebraicGeometry.Space.Modules` is accepted everywhere below, the two sheaves of rings being
the same — `AlgebraicGeometry.Space.modules_eq_sheafOfModules_representedStructureRingSheaf` and
`AlgebraicGeometry.Space.quasicoherentSheaves_eq_fullSubcategory_representedStructureRingSheaf`
record this.

The hypothesis of `Stacks.SheafOfModules.isQuasicoherentOnSite_reindex_iff` is a dense-subsite
property of the *inverse* of the equivalence, whereas what records the comparison of the sites is
the match of the two topologies
(`AlgebraicGeometry.Space.representedSmallEtaleEquivalence_topology`).  The passage from one to
the other is proved —
`AlgebraicGeometry.Space.isDenseSubsite_representedSmallEtaleEquivalence_inverse`, in
`StacksFrontier/AlgebraicGeometry/Spaces/SheafOfDifferentialsQuasicoherent.lean` — so that instance
is imported, not reproved.  Its statement is at the written-out spelling of the scheme's small
étale topology; `AlgebraicGeometry.Space.representedSchemeSmallEtaleTopology` is an `abbrev` for
exactly that term, so that instance fires at the spelling used below.  Likewise the
continuity of the comparison functor is proved in
`StacksFrontier/AlgebraicGeometry/Spaces/RepresentedModuleComparison.lean` as
`AlgebraicGeometry.Space.isContinuous_representedSmallEtaleEquivalence_functor`, together with
the continuity of the inverse.

The dense-subsite property of the comparison *functor*, and the cocontinuity of its inverse, are
proved here: Mathlib supplies the first for the topology induced by a cover-dense functor, and
the second is cover preservation of the functor read through the adjunction
`CategoryTheory.Adjunction.isCocontinuous_iff_coverPreserving`.

No essential-surjectivity hypothesis is carried: Descent, Proposition 03DX (2) at `τ = étale`
for a scheme is proved unconditionally as
`AlgebraicGeometry.SmallEtale.associatedModuleEquivalence'`.

No declaration here carries a `stacks` tag: this is an input to the reduction of Stacks 07UM to
an affine étale chart, not an assertion of any tag, and the clauses of Stacks 03ED, 03DM and
03DX used are already covered in the tree.

## References

* [Stacks Project, Tag 03ED](https://stacks.math.columbia.edu/tag/03ED)
* [Stacks Project, Tag 03DM](https://stacks.math.columbia.edu/tag/03DM)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (U : BigFppfOver B S hS)

/-- The small étale topology of the scheme underlying an object `U` of the big fppf site over
`S`, taken in the big étale site carried by the same category of schemes. -/
abbrev representedSchemeSmallEtaleTopology :=
  _root_.AlgebraicGeometry.SmallEtale.topology (associatedBigEtaleSite B)
    ((BigFppfOver.toScheme B S hS).obj U) U.left.property

/-- The structure sheaf of the small étale site of the scheme underlying an object `U` of the
big fppf site over `S`: a sheaf of rings on that site, sending an étale `T` to `Γ(T, 𝒪_T)`. -/
noncomputable abbrev representedSchemeStructureSheaf :
    Sheaf (representedSchemeSmallEtaleTopology B S hS U) RingCat.{u} :=
  _root_.AlgebraicGeometry.SmallEtale.structureSheaf (associatedBigEtaleSite B)
    ((BigFppfOver.toScheme B S hS).obj U) U.left.property

/-- The structure sheaf of the small étale site of the algebraic space `yoneda.obj U`, with
commutativity forgotten; this is the sheaf of rings in which its sheaves of modules are
indexed. -/
noncomputable abbrev representedStructureRingSheaf :
    Sheaf (SmallEtale.topology B S hS (yoneda.obj U)) RingCat.{u} :=
  (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS (yoneda.obj U)
    (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U)).O)

/-- The comparison functor is a dense subsite inclusion: it is cover dense, being an
equivalence, and the small étale topology of `yoneda.obj U` is the topology it induces. -/
instance isDenseSubsite_representedSmallEtaleEquivalence_functor :
    (representedSmallEtaleEquivalence B S hS U).functor.IsDenseSubsite
      (SmallEtale.topology B S hS (yoneda.obj U))
      (representedSchemeSmallEtaleTopology B S hS U) := by
  rw [← representedSmallEtaleEquivalence_topology B S hS U]
  infer_instance

/-- The inverse of the comparison equivalence is cocontinuous: through the adjunction it
provides, this is cover preservation of the comparison functor. -/
instance isCocontinuous_representedSmallEtaleEquivalence_inverse :
    (representedSmallEtaleEquivalence B S hS U).inverse.IsCocontinuous
      (representedSchemeSmallEtaleTopology B S hS U)
      (SmallEtale.topology B S hS (yoneda.obj U)) :=
  (Adjunction.isCocontinuous_iff_coverPreserving
      (representedSchemeSmallEtaleTopology B S hS U)
      (SmallEtale.topology B S hS (yoneda.obj U))
      (representedSmallEtaleEquivalence B S hS U).symm.toAdjunction).2
    (Functor.IsDenseSubsite.coverPreserving
      (G := (representedSmallEtaleEquivalence B S hS U).functor)
      (J := SmallEtale.topology B S hS (yoneda.obj U))
      (K := representedSchemeSmallEtaleTopology B S hS U))

/-- **The two structure sheaves of the comparison equivalence agree.**  The direct image, along
the comparison functor, of the structure sheaf of the small étale site of the scheme underlying
`U` is the structure sheaf of the small étale site of the algebraic space `yoneda.obj U`: the
comparison leaves the underlying object of the category of size-bounded schemes unchanged, and
both structure sheaves are the global regular functions on it. -/
theorem reindexRing_representedSmallEtaleEquivalence :
    Stacks.SheafOfModules.reindexRing (SmallEtale.topology B S hS (yoneda.obj U))
        (representedSmallEtaleEquivalence B S hS U)
        (representedSchemeStructureSheaf B S hS U) =
      representedStructureRingSheaf B S hS U := rfl

/-- The `𝒪`-modules on the small étale site of `yoneda.obj U` are the sheaves of modules over
`AlgebraicGeometry.Space.representedStructureRingSheaf`: the two readings of the structure sheaf
of rings, through the ringed site and through the small étale topology, are the same. -/
theorem modules_eq_sheafOfModules_representedStructureRingSheaf :
    Space.Modules.{u, u} B S hS (yoneda.obj U)
        (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U) =
      SheafOfModules.{u} (representedStructureRingSheaf B S hS U) := rfl

/-- A module on the small étale site of the scheme underlying `U`, read as an `𝒪`-module on the
small étale site of the algebraic space `yoneda.obj U` through the comparison equivalence.

This is available because the two structure sheaves agree, by
`AlgebraicGeometry.Space.reindexRing_representedSmallEtaleEquivalence`. -/
noncomputable def representedSmallEtaleModule
    (M : SheafOfModules.{u} (representedSchemeStructureSheaf B S hS U)) :
    SheafOfModules.{u} (representedStructureRingSheaf B S hS U) :=
  (SheafOfModules.pushforward.{u}
    (𝟙 (Stacks.SheafOfModules.reindexRing (SmallEtale.topology B S hS (yoneda.obj U))
      (representedSmallEtaleEquivalence B S hS U)
      (representedSchemeStructureSheaf B S hS U)))).obj M

/-- **The modules on the two small étale sites correspond.**  Reindexing along the comparison
equivalence is an equivalence from the modules on the small étale site of the scheme underlying
`U` to the `𝒪`-modules on the small étale site of the algebraic space `yoneda.obj U`. -/
noncomputable def representedSmallEtaleModuleEquivalence :
    SheafOfModules.{u} (representedSchemeStructureSheaf B S hS U) ≌
      SheafOfModules.{u} (representedStructureRingSheaf B S hS U) :=
  Stacks.SheafOfModules.reindexEquivalence (representedSmallEtaleEquivalence B S hS U)
    (representedSchemeStructureSheaf B S hS U)

/-- The functor of `AlgebraicGeometry.Space.representedSmallEtaleModuleEquivalence` is the
reading of a module as an `𝒪`-module on the small étale site of `yoneda.obj U`. -/
theorem representedSmallEtaleModuleEquivalence_functor_obj
    (M : SheafOfModules.{u} (representedSchemeStructureSheaf B S hS U)) :
    (representedSmallEtaleModuleEquivalence B S hS U).functor.obj M =
      representedSmallEtaleModule B S hS U M := rfl

/-- **Quasi-coherence is invariant under the comparison equivalence.**  A module on the small
étale site of the scheme underlying `U` is quasi-coherent exactly when the `𝒪`-module it becomes
on the small étale site of the algebraic space `yoneda.obj U` is.

This is `Stacks.SheafOfModules.isQuasicoherentOnSite_reindex_iff` — Stacks 03DM for clause (6)
of Stacks 03DL — at the equivalence of ringed sites established above. -/
theorem isQuasicoherentOnSite_representedSmallEtaleModule_iff
    (M : SheafOfModules.{u} (representedSchemeStructureSheaf B S hS U)) :
    (representedSmallEtaleModule B S hS U M).IsQuasicoherentOnSite ↔
      M.IsQuasicoherentOnSite :=
  Stacks.SheafOfModules.isQuasicoherentOnSite_reindex_iff
    (representedSmallEtaleEquivalence B S hS U) (representedSchemeStructureSheaf B S hS U) M

/-- Quasi-coherence on the small étale site of the scheme underlying `U` is the inverse image,
along the equivalence of module categories, of quasi-coherence on the small étale site of
`yoneda.obj U`.  This is the equality of object properties which cuts the equivalence down to
the quasi-coherent modules. -/
theorem inverseImage_isQuasicoherentOnSite_representedSmallEtaleModuleEquivalence :
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
          (representedStructureRingSheaf B S hS U)).inverseImage
        (representedSmallEtaleModuleEquivalence B S hS U).functor =
      SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (representedSchemeStructureSheaf B S hS U) := by
  funext M
  exact propext (isQuasicoherentOnSite_representedSmallEtaleModule_iff B S hS U M)

/-- The category `QCoh(𝒪_{yoneda.obj U})` of Stacks 03G9 is the full subcategory of the sheaves
of modules over `AlgebraicGeometry.Space.representedStructureRingSheaf` cut out by
quasi-coherence on the site. -/
theorem quasicoherentSheaves_eq_fullSubcategory_representedStructureRingSheaf :
    Space.QuasicoherentSheaves.{u, u} B S hS (yoneda.obj U)
        (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U) =
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (representedStructureRingSheaf B S hS U)).FullSubcategory := rfl

/-- **The quasi-coherent modules on the two small étale sites correspond.**  The equivalence of
module categories restricts to an equivalence between the quasi-coherent modules on the small
étale site of the scheme underlying `U` and `QCoh(𝒪_{yoneda.obj U})`. -/
noncomputable def representedQuasicoherentEquivalence :
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (representedSchemeStructureSheaf B S hS U)).FullSubcategory ≌
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (representedStructureRingSheaf B S hS U)).FullSubcategory :=
  (representedSmallEtaleModuleEquivalence B S hS U).congrFullSubcategory
    (inverseImage_isQuasicoherentOnSite_representedSmallEtaleModuleEquivalence B S hS U)

/-- **A quasi-coherent module on the small étale site of a representable algebraic space is a
quasi-coherent module on the underlying scheme.**  The quasi-coherent
`AlgebraicGeometry.Scheme.Modules` on the scheme `T` underlying `U` — quasi-coherent modules on
the *Zariski* site of `T` — are equivalent to `QCoh(𝒪_{yoneda.obj U})`.

The scheme-level half is Descent, Proposition 03DX (2) at `τ = étale` for a scheme,
`AlgebraicGeometry.SmallEtale.associatedModuleEquivalence'`, and the passage from the small
étale site of `T` to the small étale site of `yoneda.obj U` is
`AlgebraicGeometry.Space.representedQuasicoherentEquivalence`. -/
noncomputable def representedQuasicoherentSchemeEquivalence :
    (SheafOfModules.isQuasicoherent
        ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory ≌
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (representedStructureRingSheaf B S hS U)).FullSubcategory :=
  (_root_.AlgebraicGeometry.SmallEtale.associatedModuleEquivalence' (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj U) U.left.property).trans
    (representedQuasicoherentEquivalence B S hS U)

/-- **The modules on the small étale site of a representable algebraic space are the modules on
the small étale site of the underlying scheme**, stated with the target read as
`AlgebraicGeometry.Space.Modules`, to which
`AlgebraicGeometry.Space.representedSmallEtaleModuleEquivalence` is typed definitionally equal by
`AlgebraicGeometry.Space.modules_eq_sheafOfModules_representedStructureRingSheaf`. -/
noncomputable def representedSpaceModulesEquivalence :
    SheafOfModules.{u} (representedSchemeStructureSheaf B S hS U) ≌
      Space.Modules.{u, u} B S hS (yoneda.obj U)
        (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U) :=
  representedSmallEtaleModuleEquivalence B S hS U

/-- **The quasi-coherent modules on a representable algebraic space are the quasi-coherent
modules on the underlying scheme**, stated with the target read as the category `QCoh(𝒪_F)` of
Stacks 03G9, `AlgebraicGeometry.Space.QuasicoherentSheaves`, to which
`AlgebraicGeometry.Space.representedQuasicoherentSchemeEquivalence` is typed definitionally equal
by `AlgebraicGeometry.Space.quasicoherentSheaves_eq_fullSubcategory_representedStructureRingSheaf`.

This is the statement that a quasi-coherent module on the small étale site of the representable
algebraic space `yoneda.obj U` is the same thing as a quasi-coherent
`AlgebraicGeometry.Scheme.Modules` on the scheme underlying `U`. -/
noncomputable def representedQuasicoherentSheavesEquivalence :
    (SheafOfModules.isQuasicoherent
        ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory ≌
      Space.QuasicoherentSheaves.{u, u} B S hS (yoneda.obj U)
        (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U) :=
  representedQuasicoherentSchemeEquivalence B S hS U

/-- **The Hom-sets of the two categories of quasi-coherent modules agree.**  Morphisms of
quasi-coherent `AlgebraicGeometry.Scheme.Modules` on the scheme underlying `U` are exactly
morphisms of the corresponding quasi-coherent `𝒪`-modules on the small étale site of the
algebraic space `yoneda.obj U`. -/
noncomputable def representedQuasicoherentSchemeHomEquiv
    (M N : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory) :
    (M ⟶ N) ≃
      ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj M ⟶
        (representedQuasicoherentSchemeEquivalence B S hS U).functor.obj N) :=
  (representedQuasicoherentSchemeEquivalence B S hS U).fullyFaithfulFunctor.homEquiv

/-- **The algebraic space represented by an étale chart is the Yoneda algebraic space of the
chart's object**, definitionally.

This is what makes the equivalence of this file composable with the localization of Stacks 04M0
at a chart: the two readings of the chart space are the same term, so a reader should not look
for, or build, a comparison between them. -/
theorem chartSpace_eq_yoneda (X : AlgebraicSpaces B S hS) (V : SmallEtale B S hS X.1) :
    (chartSpace B S hS X V).1 = yoneda.obj ((SmallEtale.toOver B S hS X.1).obj V) := rfl

end AlgebraicGeometry.Space

/-! ### Restricting a quasi-coherent module to the Zariski site of a chart -/

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS)

/-- The restriction of a quasi-coherent `𝒪_X`-module to an étale chart, read on the small étale
site of that chart as an object of the category of quasi-coherent modules there. -/
noncomputable def chartSmallEtaleQcoh
    (M : SheafOfModules.{u} (structureRingSheaf B S hS X))
    (hM : M.IsQuasicoherentOnSite) (V : SmallEtale B S hS X.1) :
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (chartStructureRingSheaf B S hS X V)).FullSubcategory :=
  ⟨chartSmallEtaleRestriction B S hS X M V,
    isQuasicoherentOnSite_chartSmallEtaleRestriction B S hS X M hM V⟩

/-- **A quasi-coherent `𝒪_X`-module restricts, on each étale scheme chart, to a quasi-coherent
sheaf of modules on the Zariski site of the chart's scheme.**

This is the composite of the localization of Stacks 04M0 at the chart with the equivalence of
this file, available because `AlgebraicGeometry.Space.chartSpace_eq_yoneda` makes the chart space
the Yoneda algebraic space of the chart's object definitionally.  It is the transport that lets a
statement about `AlgebraicGeometry.Scheme.Modules` — such as the scheme case of Stacks 01YB — be
applied to the restriction of a module on an algebraic space. -/
noncomputable def chartSchemeQcoh
    (M : SheafOfModules.{u} (structureRingSheaf B S hS X))
    (hM : M.IsQuasicoherentOnSite) (V : SmallEtale B S hS X.1) :
    (SheafOfModules.isQuasicoherent (chartScheme V).ringCatSheaf).FullSubcategory :=
  (representedQuasicoherentSchemeEquivalence B S hS
      ((SmallEtale.toOver B S hS X.1).obj V)).inverse.obj
    (chartSmallEtaleQcoh B S hS X M hM V)

/-- The chart restriction of a quasi-coherent `𝒪_X`-module, as an
`AlgebraicGeometry.Scheme.Modules` on the chart's scheme. -/
noncomputable def chartSchemeModule
    (M : SheafOfModules.{u} (structureRingSheaf B S hS X))
    (hM : M.IsQuasicoherentOnSite) (V : SmallEtale B S hS X.1) :
    AlgebraicGeometry.Scheme.Modules (chartScheme V) :=
  (chartSchemeQcoh B S hS X M hM V).obj

/-- The chart restriction of a quasi-coherent `𝒪_X`-module is quasi-coherent on the Zariski site
of the chart's scheme. -/
theorem isQuasicoherent_chartSchemeModule
    (M : SheafOfModules.{u} (structureRingSheaf B S hS X))
    (hM : M.IsQuasicoherentOnSite) (V : SmallEtale B S hS X.1) :
    SheafOfModules.IsQuasicoherent (chartSchemeModule B S hS X M hM V) :=
  (chartSchemeQcoh B S hS X M hM V).property

end AlgebraicGeometry.Space

end
