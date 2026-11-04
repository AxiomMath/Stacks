module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Picard.SmallEtalePicardIsomorphism
public import StacksFrontier.AlgebraicGeometry.Picard.SmallEtaleSiteFirstCohomology
public import StacksFrontier.AlgebraicGeometry.Picard.ZariskiSiteFirstCohomology

/-!
# The étale leg of Stacks 03P8: `H¹_étale(S, 𝐆_m) = H¹_Zar(S, 𝐆_m) = Pic(S)`

Let `S` be a scheme of a big étale site `B`.  Three identifications are already available:

* `Stacks.Picard.SmallEtaleSite.etaleH1UnitsAddEquivPicardGroup`, Tag 040E on the small étale
  site: `H¹_étale(S, 𝐆_m) = Pic(𝒪_{S_étale})`;
* `Stacks.Picard.ZariskiSite.zariskiH1UnitsAddEquivPicardGroup`, Tag 040E on the site of opens:
  `H¹_Zar(S, 𝐆_m) = Pic(S)`;
* `AlgebraicGeometry.SmallEtale.associatedModulePicardAddEquiv`, Descent, Proposition 03DX (2)
  read on Picard groups: `Pic(S) = Pic(𝒪_{S_étale})`.

Composing them gives the étale comparison of Tag 03P8,

`H¹_étale(S, 𝐆_m) = H¹_Zar(S, 𝐆_m) = Pic(S)`,

for any scheme `S`, with no hypothesis beyond the `HasExt` instance binder that the étale side
already carries (the universe of the `Ext`-groups is a parameter of `HasExt` and is not determined
by the site, exactly as in
`StacksFrontier/AlgebraicGeometry/Picard/SmallEtaleSiteFirstCohomology.lean`).

## Where Tag 03P8 is registered

Tag 03P8 asserts six identifications, `H¹_fppf = H¹_syntomic = H¹_smooth = H¹_étale = H¹_Zar =
Pic(X) = H¹(X, 𝒪_X^*)`, and all six are proved for an arbitrary scheme by
`Stacks.Picard.AllTopologies.identifications`
(`StacksFrontier/AlgebraicGeometry/Picard/MultiplicativeGroupFirstCohomology.lean`), which is where
the tag is registered.  The chain there is read on the five big `τ`-sites; what the declarations
below add is the *small* étale site, whose first cohomology of the units is identified with
`Pic(S)` and with the cohomology on the site of opens.  No `stacks` attribute is claimed here:
the tag belongs on the statement of the whole chain and nowhere else.

## Main definitions

* `Stacks.Picard.SmallEtaleSite.etaleH1UnitsAddEquivZariskiPicardGroup`:
  **`H¹_étale(S, 𝐆_m) = Pic(S)`.**
* `Stacks.Picard.SmallEtaleSite.etaleH1UnitsAddEquivZariskiH1Units`:
  **`H¹_étale(S, 𝐆_m) = H¹_Zar(S, 𝐆_m)`.**

## Main results

* `Stacks.Picard.SmallEtaleSite.etaleH1UnitsAddEquivZariskiPicardGroup_symm_classOf`: the
  identification with `Pic(S)` carries the class of an invertible `𝒪_S`-module `𝓛` to the first
  cohomology class of the torsor of local generators of `𝓛^a`, which fixes it rather than only
  asserting that an isomorphism exists.
* `Stacks.Picard.SmallEtaleSite.etaleH1UnitsAddEquivZariskiH1Units_symm_classOf`: likewise, the
  comparison of the two first cohomology groups matches the torsor of generators of `𝓛^a` with
  the torsor of generators of `𝓛`.

## Implementation notes

The Picard group of `S` appears in two spellings: `Pic` of the ringed site
`Stacks.AlgebraicGeometry.ReflexiveModules.schemeRingedSite`, which Tag 040E is stated for, and
`Pic` of `AlgebraicGeometry.SmallEtale.zariskiStructureIsSheaf`, which the associated-module
comparison is stated for.  The two ring sheaves are equal by `rfl` and the two sheaf conditions
are proofs of one proposition, so the groups are the same and nothing is transported; the
abelian group structures of the two files are activated together for the same reason.

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03P8](https://stacks.math.columbia.edu/tag/03P8)
* [Stacks Project, Tag 040E](https://stacks.math.columbia.edu/tag/040E)
* [Stacks Project, Tag 04HZ](https://stacks.math.columbia.edu/tag/04HZ)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe t u

namespace Stacks.Picard.SmallEtaleSite

open Stacks.AlgebraicGeometry.ReflexiveModules (schemeRingedSite)
open AlgebraicGeometry.SmallEtale (associatedModule associatedModulePicardAddEquiv
  associatedModulePicardAddEquiv_classOf commRingStructureSheaf isInvertible_associatedModule
  structure_isSheaf zariskiStructureIsSheaf)

attribute [local instance] etalePicardGroupAddCommGroup
  Stacks.Picard.ZariskiSite.zariskiPicardGroupAddCommGroup
  AlgebraicGeometry.SmallEtale.zariskiPicardAddCommGroup
  AlgebraicGeometry.SmallEtale.etalePicardAddCommGroup

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  [HasExt.{t} (Sheaf (smallEtaleRingedSite B S hS).J AddCommGrpCat.{u})]

/-- **Stacks Project, Tag 03P8, the étale identification with the Picard group.** For any scheme
`S` of a big étale site there is a canonical isomorphism of abelian groups

`H¹_étale(S, 𝐆_m) = Pic(S)`.

It is Tag 040E on the small étale site,
`Stacks.Picard.SmallEtaleSite.etaleH1UnitsAddEquivPicardGroup`, followed by the inverse of the
Picard isomorphism of the associated-module functor,
`AlgebraicGeometry.SmallEtale.associatedModulePicardAddEquiv`, which is Descent,
Proposition 03DX (2) read on Picard groups. -/
def etaleH1UnitsAddEquivZariskiPicardGroup :
    Sheaf.H (Stacks.Cohomology.Torsors.Generators.unitsAddSheaf
        (smallEtaleRingedSite B S hS)) 1 ≃+
      Stacks.SheafOfModules.Picard.PicardGroup S.presheaf (zariskiStructureIsSheaf S) :=
  (etaleH1UnitsAddEquivPicardGroup B S hS).trans
    (associatedModulePicardAddEquiv B S hS).symm

/-- **Stacks Project, Tag 03P8, the étale comparison of first cohomology.** For any scheme `S` of
a big étale site there is a canonical isomorphism of abelian groups

`H¹_étale(S, 𝐆_m) = H¹_Zar(S, 𝐆_m)`,

namely `H¹_étale(S, 𝐆_m) = Pic(S) = H¹_Zar(S, 𝐆_m)` through
`Stacks.Picard.SmallEtaleSite.etaleH1UnitsAddEquivZariskiPicardGroup` and Tag 040E on the site of
opens, `Stacks.Picard.ZariskiSite.zariskiH1UnitsAddEquivPicardGroup`. -/
def etaleH1UnitsAddEquivZariskiH1Units :
    Sheaf.H (Stacks.Cohomology.Torsors.Generators.unitsAddSheaf
        (smallEtaleRingedSite B S hS)) 1 ≃+
      Sheaf.H (Stacks.Cohomology.Torsors.Generators.unitsAddSheaf (schemeRingedSite S)) 1 :=
  (etaleH1UnitsAddEquivZariskiPicardGroup B S hS).trans
    (Stacks.Picard.ZariskiSite.zariskiH1UnitsAddEquivPicardGroup S).symm

/-- The class in `Pic(S)` of an invertible `𝒪_S`-module is carried, by the inverse of the étale
identification, to the first cohomology class of the torsor of local generators of its associated
module.  This fixes
`Stacks.Picard.SmallEtaleSite.etaleH1UnitsAddEquivZariskiPicardGroup` rather than only asserting
that an isomorphism exists. -/
theorem etaleH1UnitsAddEquivZariskiPicardGroup_symm_classOf
    (L : SheafOfModules.{u} (Stacks.SheafOfModules.TensorSheafification.structureSheaf S.presheaf
      (zariskiStructureIsSheaf S)))
    (hL : Stacks.SheafOfModules.IsInvertible S.presheaf (zariskiStructureIsSheaf S) L) :
    (etaleH1UnitsAddEquivZariskiPicardGroup B S hS).symm
        (Stacks.SheafOfModules.Picard.classOf S.presheaf (zariskiStructureIsSheaf S) L hL) =
      Stacks.Cohomology.Torsors.torsorIsoClassesEquivH1
        (Stacks.Cohomology.Torsors.Generators.unitsAddSheaf (smallEtaleRingedSite B S hS))
        (Quotient.mk (Stacks.Cohomology.Torsors.torsorSetoid
            (Stacks.Cohomology.Torsors.Generators.unitsAddSheaf (smallEtaleRingedSite B S hS)))
          (Stacks.Cohomology.Torsors.Generators.generatorTorsor' (smallEtaleRingedSite B S hS)
            (smallEtaleRingedSite_isLocallyRinged B S hS) ((associatedModule B S hS).obj L)
            (isInvertible_associatedModule B S hS L hL)).torsor) := by
  rw [← etaleH1UnitsAddEquivPicardGroup_symm_classOf B S hS ((associatedModule B S hS).obj L)
    (isInvertible_associatedModule B S hS L hL)]
  show (etaleH1UnitsAddEquivPicardGroup B S hS).symm
      ((associatedModulePicardAddEquiv B S hS) _) = _
  rw [associatedModulePicardAddEquiv_classOf B S hS L hL]

/-- The comparison of the two first cohomology groups matches the torsor of local generators of
`𝓛^a` on the small étale site with the torsor of local generators of `𝓛` on the site of opens.
This fixes `Stacks.Picard.SmallEtaleSite.etaleH1UnitsAddEquivZariskiH1Units`. -/
theorem etaleH1UnitsAddEquivZariskiH1Units_symm_classOf
    (L : SheafOfModules.{u} (Stacks.SheafOfModules.TensorSheafification.structureSheaf S.presheaf
      (zariskiStructureIsSheaf S)))
    (hL : Stacks.SheafOfModules.IsInvertible S.presheaf (zariskiStructureIsSheaf S) L) :
    etaleH1UnitsAddEquivZariskiH1Units B S hS
        (Stacks.Cohomology.Torsors.torsorIsoClassesEquivH1
          (Stacks.Cohomology.Torsors.Generators.unitsAddSheaf (smallEtaleRingedSite B S hS))
          (Quotient.mk (Stacks.Cohomology.Torsors.torsorSetoid
              (Stacks.Cohomology.Torsors.Generators.unitsAddSheaf (smallEtaleRingedSite B S hS)))
            (Stacks.Cohomology.Torsors.Generators.generatorTorsor' (smallEtaleRingedSite B S hS)
              (smallEtaleRingedSite_isLocallyRinged B S hS) ((associatedModule B S hS).obj L)
              (isInvertible_associatedModule B S hS L hL)).torsor)) =
      Stacks.Cohomology.Torsors.torsorIsoClassesEquivH1
        (Stacks.Cohomology.Torsors.Generators.unitsAddSheaf (schemeRingedSite S))
        (Quotient.mk (Stacks.Cohomology.Torsors.torsorSetoid
            (Stacks.Cohomology.Torsors.Generators.unitsAddSheaf (schemeRingedSite S)))
          (Stacks.Cohomology.Torsors.Generators.generatorTorsor (schemeRingedSite S)
            (ZariskiSite.schemeRingedSite_isLocallyRinged S) L hL).torsor) := by
  rw [← ZariskiSite.zariskiH1UnitsAddEquivPicardGroup_symm_classOf S L hL,
    ← etaleH1UnitsAddEquivZariskiPicardGroup_symm_classOf B S hS L hL]
  show (Stacks.Picard.ZariskiSite.zariskiH1UnitsAddEquivPicardGroup S).symm
      ((etaleH1UnitsAddEquivZariskiPicardGroup B S hS)
        ((etaleH1UnitsAddEquivZariskiPicardGroup B S hS).symm _)) = _
  rw [AddEquiv.apply_symm_apply]
  rfl

end Stacks.Picard.SmallEtaleSite

end
