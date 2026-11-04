module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Picard.BaseSitePicardComparison
public import StacksFrontier.AlgebraicGeometry.Picard.SmallEtaleFirstCohomologyComparison
public import StacksFrontier.AlgebraicGeometry.Picard.ZariskiSiteFirstCohomology
public import StacksFrontier.AlgebraicGeometry.Picard.BaseSitesFirstCohomology

/-!
# Stacks 03P8: `H¹_fppf = H¹_syntomic = H¹_smooth = H¹_étale = H¹_Zar = Pic = H¹(X, 𝒪_X^*)`

For **any** scheme `X` there are canonical identifications

`H¹_fppf(X, 𝐆_m) = H¹_syntomic(X, 𝐆_m) = H¹_smooth(X, 𝐆_m) = H¹_étale(X, 𝐆_m)
  = H¹_Zar(X, 𝐆_m) = Pic(X) = H¹(X, 𝒪_X^*)`.

The first five groups are the first cohomology of the sheaf of units on the big `τ`-site of `X`,
for `τ` running through the five standard topologies, which in this library are five
Grothendieck topologies on one category `(Sch/X)`
(`AlgebraicGeometry.BigFppfOver.baseOverTopology`); `Pic(X)` is the Picard group of Tag 01CX of
the scheme; and the last group is the cohomology of the units of the structure sheaf on the
site of opens of `X`.

## How the six identifications are obtained

Every one of them factors through `Pic(X)`:

* **`H¹_τ(X, 𝐆_m) = Pic(𝒪_τ)`** is Tag 040E on the big `τ`-site,
  `Stacks.Picard.BaseSites.baseH1UnitsAddEquivPicardGroup`, which rests on the local ringedness
  of that site, `AlgebraicGeometry.baseRingedSite_isLocallyRinged`.
* **`Pic(𝒪_τ) = Pic(X)`** is Descent, Proposition 03DX clause (1) at `τ` read on Picard groups,
  `AlgebraicGeometry.BigFppfOver.basePicardAddEquiv`.
* **`Pic(X) = H¹(X, 𝒪_X^*)`** is Tag 040E on the site of opens of `X`,
  `Stacks.Picard.ZariskiSite.zariskiH1UnitsAddEquivPicardGroup`.

Composing, `H¹_τ(X, 𝐆_m) = Pic(X)` for every `τ`
(`Stacks.Picard.AllTopologies.baseH1UnitsAddEquivSchemePicardGroup`), and the chain of the tag
is read off that family: consecutive topologies are compared through `Pic(X)`, the Zariski one
*is* the comparison with `Pic(X)`, and the last link is the site of opens.

All of it is unconditional: no affineness, quasi-compactness, Noetherian, reduced or separatedness
hypothesis, and no restriction on the universe of the scheme.  The `smooth` identification is not
obtained by rewriting along the equality of the smooth and étale topologies
(`AlgebraicGeometry.BigFppfOver.baseOverTopology_smooth_eq_etale`); it is the instance at
`τ = smooth` of a family proved uniformly in `τ`, so no transport is needed.

## Main definitions

* `Stacks.Picard.AllTopologies.baseH1UnitsAddEquivSchemePicardGroup`: `H¹_τ(X, 𝐆_m) = Pic(X)`,
  at every one of the five topologies.
* `Stacks.Picard.AllTopologies.Identifications`: the six identifications of Tag 03P8, as the
  six links of its chain.
* `Stacks.Picard.AllTopologies.identifications`: **Tag 03P8** — the six identifications, for an
  arbitrary scheme.
* `Stacks.Picard.AllTopologies.bigEtaleH1UnitsAddEquivSmallEtaleH1Units`: the big étale group of
  the chain agrees with the first cohomology of the units on the *small* étale site, so the tag
  holds under either reading of `H¹_étale(X, 𝐆_m)`.

## Main results

* `Stacks.Picard.AllTopologies.baseH1UnitsAddEquivSchemePicardGroup_symm_classOf`: the
  identification with `Pic(X)` carries the class of an invertible `𝒪_X`-module `𝓛` to the first
  cohomology class of the torsor of local generators of `𝓛^a`, which fixes it rather than only
  asserting that an isomorphism exists.
* `Stacks.Picard.AllTopologies.identifications_fppfSyntomic` and its five siblings: each link of
  the chain is the composite of the two normalized identifications with `Pic(X)`.

## Implementation notes

`HasExt` is an instance binder rather than an instance, as in `Stacks.Picard.BigSites` and
`Stacks.Picard.SmallEtaleSite`: the universe in which the `Ext`-groups live is a parameter of
`HasExt` and is not determined by the site, so it cannot be inferred from the scheme.  One
binder, quantified over `τ`, serves all five topologies.  At the universe of the morphisms of the
sheaf category the instance is a theorem,
`AlgebraicGeometry.BigFppfOver.hasExt_sheaf_baseOverTopology`.  Nothing else is assumed.

The Picard group is `Stacks.SheafOfModules.Picard.PicardGroup`, the group Tag 040E produces, in
the two spellings `Stacks.SheafOfModules.Picard.PicardGroup X.presheaf
(AlgebraicGeometry.SmallEtale.zariskiStructureIsSheaf X)` and
`Stacks.SheafOfModules.Picard.PicardGroup (schemeRingedSite X).O.obj
(schemeRingedSite X).ringSheaf.2`.  The two ring presheaves are equal by `rfl` and the two sheaf
conditions are proofs of one proposition, so the groups are the same type and nothing is
transported; the abelian group structures of the two files are activated together for the same
reason.

## References

* [Stacks Project, Tag 01CX](https://stacks.math.columbia.edu/tag/01CX)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03P8](https://stacks.math.columbia.edu/tag/03P8)
* [Stacks Project, Tag 040E](https://stacks.math.columbia.edu/tag/040E)
* [Stacks Project, Tag 09NU](https://stacks.math.columbia.edu/tag/09NU)
-/

@[expose] public noncomputable section

open CategoryTheory

universe t u

namespace Stacks.Picard.AllTopologies

open _root_.AlgebraicGeometry
open Stacks.AlgebraicGeometry.ReflexiveModules (schemeRingedSite)
open _root_.AlgebraicGeometry.SmallEtale (zariskiStructureIsSheaf)
open Stacks.Cohomology.Torsors.Generators (unitsAddSheaf generatorTorsor')

attribute [local instance] _root_.AlgebraicGeometry.SmallEtale.zariskiPicardAddCommGroup
  Stacks.Picard.ZariskiSite.zariskiPicardGroupAddCommGroup

variable (B : BigFppfSite.{u}) (X : Scheme.{u}) (hX : B.Contains X)

/-- `Pic(X)`, the Picard group of Tag 01CX of the scheme `X`. -/
@[sga "4 IX 3.3"]
public abbrev schemePicardGroup : Type u :=
  Stacks.SheafOfModules.Picard.PicardGroup X.presheaf (zariskiStructureIsSheaf X)

/-- `H¹(X, 𝒪_X^*)`, the first cohomology of the units of the structure sheaf on the site of
opens of `X`. -/
public abbrev spaceH1Units : Type u :=
  Sheaf.H (unitsAddSheaf (schemeRingedSite X)) 1

variable [∀ τ : SiteKind,
  HasExt.{t} (Sheaf (BigFppfOver.baseOverTopology B X hX τ) AddCommGrpCat.{u})]

/-- `H¹_τ(X, 𝐆_m)`, the first cohomology of the sheaf of units on the big `τ`-site of `X`. -/
@[sga "4 XII 8.6"]
public abbrev bigH1Units (τ : SiteKind) : Type t :=
  Sheaf.H (unitsAddSheaf (BigFppfOver.baseRingedSite B X hX τ)) 1

/-- **`H¹_τ(X, 𝐆_m) = Pic(X)`, at every one of the five topologies and for any scheme `X`.**

It is Tag 040E on the big `τ`-site, `Stacks.Picard.BaseSites.baseH1UnitsAddEquivPicardGroup`,
followed by the inverse of the Picard isomorphism of the associated-module functor,
`AlgebraicGeometry.BigFppfOver.basePicardAddEquiv`, which is Descent, Proposition 03DX clause
(1) at `τ` read on Picard groups. -/
@[sga "4 XII 8.6" "more general", sga "4½ Arcata 3.3.1" "more general"]
public def baseH1UnitsAddEquivSchemePicardGroup (τ : SiteKind) :
    bigH1Units B X hX τ ≃+ schemePicardGroup X :=
  (Stacks.Picard.BaseSites.baseH1UnitsAddEquivPicardGroup B X hX τ).trans
    (BigFppfOver.basePicardAddEquiv B X hX τ).symm

/-- The class in `Pic(X)` of an invertible `𝒪_X`-module is carried, by the inverse of the
identification at `τ`, to the first cohomology class of the torsor of local generators of its
associated module.  This fixes
`Stacks.Picard.AllTopologies.baseH1UnitsAddEquivSchemePicardGroup` rather than only asserting
that an isomorphism exists. -/
@[sga "3 VIII 4.4" "partial", sga "7 VIII 6.3" "partial"]
public theorem baseH1UnitsAddEquivSchemePicardGroup_symm_classOf (τ : SiteKind)
    (L : SheafOfModules.{u} (Stacks.SheafOfModules.TensorSheafification.structureSheaf
      X.presheaf (zariskiStructureIsSheaf X)))
    (hL : Stacks.SheafOfModules.IsInvertible X.presheaf (zariskiStructureIsSheaf X) L) :
    (baseH1UnitsAddEquivSchemePicardGroup B X hX τ).symm
        (Stacks.SheafOfModules.Picard.classOf X.presheaf (zariskiStructureIsSheaf X) L hL) =
      Stacks.Cohomology.Torsors.torsorIsoClassesEquivH1
        (unitsAddSheaf (BigFppfOver.baseRingedSite B X hX τ))
        (Quotient.mk (Stacks.Cohomology.Torsors.torsorSetoid
            (unitsAddSheaf (BigFppfOver.baseRingedSite B X hX τ)))
          (generatorTorsor' (BigFppfOver.baseRingedSite B X hX τ)
            (baseRingedSite_isLocallyRinged B X hX τ)
            ((BigFppfOver.baseAssociatedModule B X hX τ).obj L)
            (BigFppfOver.isInvertible_baseAssociatedModule B X hX τ L hL)).torsor) := by
  rw [← Stacks.Picard.BaseSites.baseH1UnitsAddEquivPicardGroup_symm_classOf B X hX τ
    ((BigFppfOver.baseAssociatedModule B X hX τ).obj L)
    (BigFppfOver.isInvertible_baseAssociatedModule B X hX τ L hL)]
  show (Stacks.Picard.BaseSites.baseH1UnitsAddEquivPicardGroup B X hX τ).symm
      ((BigFppfOver.basePicardAddEquiv B X hX τ) _) = _
  rw [BigFppfOver.basePicardAddEquiv_classOf B X hX τ L hL]

/-! ### The six identifications of Tag 03P8 -/

/-- **The six identifications of Stacks Project, Tag 03P8**, as the six links of its chain

`H¹_fppf(X, 𝐆_m) = H¹_syntomic(X, 𝐆_m) = H¹_smooth(X, 𝐆_m) = H¹_étale(X, 𝐆_m)
  = H¹_Zar(X, 𝐆_m) = Pic(X) = H¹(X, 𝒪_X^*)`.

Each field is an isomorphism of abelian groups between two named groups; none of them is a
hypothesis, and `Stacks.Picard.AllTopologies.identifications` constructs all six for an
arbitrary scheme. -/
public structure Identifications where
  /-- `H¹_fppf(X, 𝐆_m) = H¹_syntomic(X, 𝐆_m)`. -/
  fppfSyntomic : bigH1Units B X hX .fppf ≃+ bigH1Units B X hX .syntomic
  /-- `H¹_syntomic(X, 𝐆_m) = H¹_smooth(X, 𝐆_m)`. -/
  syntomicSmooth : bigH1Units B X hX .syntomic ≃+ bigH1Units B X hX .smooth
  /-- `H¹_smooth(X, 𝐆_m) = H¹_étale(X, 𝐆_m)`. -/
  smoothEtale : bigH1Units B X hX .smooth ≃+ bigH1Units B X hX .etale
  /-- `H¹_étale(X, 𝐆_m) = H¹_Zar(X, 𝐆_m)`. -/
  etaleZariski : bigH1Units B X hX .etale ≃+ bigH1Units B X hX .zariski
  /-- `H¹_Zar(X, 𝐆_m) = Pic(X)`. -/
  zariskiPicard : bigH1Units B X hX .zariski ≃+ schemePicardGroup X
  /-- `Pic(X) = H¹(X, 𝒪_X^*)`. -/
  picardSpace : schemePicardGroup X ≃+ spaceH1Units X

/-- **Stacks Project, Tag 03P8.** For any scheme `X` there are canonical identifications

`H¹_fppf(X, 𝐆_m) = H¹_syntomic(X, 𝐆_m) = H¹_smooth(X, 𝐆_m) = H¹_étale(X, 𝐆_m)
  = H¹_Zar(X, 𝐆_m) = Pic(X) = H¹(X, 𝒪_X^*)`.

The five big-site groups are identified with `Pic(X)` by
`Stacks.Picard.AllTopologies.baseH1UnitsAddEquivSchemePicardGroup`, which is Tag 040E on the big
`τ`-site followed by clause (1) of Descent, Proposition 03DX at `τ` read on Picard groups; the
last link is Tag 040E on the site of opens of `X`,
`Stacks.Picard.ZariskiSite.zariskiH1UnitsAddEquivPicardGroup`.

Every identification is normalized on invertible modules:
`Stacks.Picard.AllTopologies.baseH1UnitsAddEquivSchemePicardGroup_symm_classOf` and
`Stacks.Picard.ZariskiSite.zariskiH1UnitsAddEquivPicardGroup_symm_classOf` send the class of an
invertible module to the first cohomology class of its torsor of local generators, and the six
`identifications_*` lemmas below express each field in those terms. -/
@[stacks 03P8,
  sga "1 XI 5.3" "G_m clause, special case",
  sga "1 XI 6.4" "picardSpace field",
  sga "3 VIII 4.4" "partial",
  sga "4 VII 4.2.1" "special case",
  sga "4 XII 8.6" "more general",
  sga "4½ Arcata 3.3.1" "more general"]
public def identifications : Identifications.{t} B X hX where
  fppfSyntomic := (baseH1UnitsAddEquivSchemePicardGroup B X hX .fppf).trans
    (baseH1UnitsAddEquivSchemePicardGroup B X hX .syntomic).symm
  syntomicSmooth := (baseH1UnitsAddEquivSchemePicardGroup B X hX .syntomic).trans
    (baseH1UnitsAddEquivSchemePicardGroup B X hX .smooth).symm
  smoothEtale := (baseH1UnitsAddEquivSchemePicardGroup B X hX .smooth).trans
    (baseH1UnitsAddEquivSchemePicardGroup B X hX .etale).symm
  etaleZariski := (baseH1UnitsAddEquivSchemePicardGroup B X hX .etale).trans
    (baseH1UnitsAddEquivSchemePicardGroup B X hX .zariski).symm
  zariskiPicard := baseH1UnitsAddEquivSchemePicardGroup B X hX .zariski
  picardSpace := (Stacks.Picard.ZariskiSite.zariskiH1UnitsAddEquivPicardGroup X).symm

/-- The identification `H¹_fppf(X, 𝐆_m) = H¹_syntomic(X, 𝐆_m)` of `identifications` is the
identification of `H¹_fppf(X, 𝐆_m)` with `Pic(X)` followed by the inverse of that of
`H¹_syntomic(X, 𝐆_m)`. -/
@[simp]
public theorem identifications_fppfSyntomic :
    (identifications.{t} B X hX).fppfSyntomic =
      (baseH1UnitsAddEquivSchemePicardGroup B X hX .fppf).trans
        (baseH1UnitsAddEquivSchemePicardGroup B X hX .syntomic).symm := rfl

/-- The identification `H¹_syntomic(X, 𝐆_m) = H¹_smooth(X, 𝐆_m)` of `identifications` is the
identification of `H¹_syntomic(X, 𝐆_m)` with `Pic(X)` followed by the inverse of that of
`H¹_smooth(X, 𝐆_m)`. -/
@[simp]
public theorem identifications_syntomicSmooth :
    (identifications.{t} B X hX).syntomicSmooth =
      (baseH1UnitsAddEquivSchemePicardGroup B X hX .syntomic).trans
        (baseH1UnitsAddEquivSchemePicardGroup B X hX .smooth).symm := rfl

/-- The identification `H¹_smooth(X, 𝐆_m) = H¹_étale(X, 𝐆_m)` of `identifications` is the
identification of `H¹_smooth(X, 𝐆_m)` with `Pic(X)` followed by the inverse of that of
`H¹_étale(X, 𝐆_m)`. -/
@[simp]
public theorem identifications_smoothEtale :
    (identifications.{t} B X hX).smoothEtale =
      (baseH1UnitsAddEquivSchemePicardGroup B X hX .smooth).trans
        (baseH1UnitsAddEquivSchemePicardGroup B X hX .etale).symm := rfl

/-- The identification `H¹_étale(X, 𝐆_m) = H¹_Zar(X, 𝐆_m)` of `identifications` is the
identification of `H¹_étale(X, 𝐆_m)` with `Pic(X)` followed by the inverse of that of
`H¹_Zar(X, 𝐆_m)`. -/
@[simp]
public theorem identifications_etaleZariski :
    (identifications.{t} B X hX).etaleZariski =
      (baseH1UnitsAddEquivSchemePicardGroup B X hX .etale).trans
        (baseH1UnitsAddEquivSchemePicardGroup B X hX .zariski).symm := rfl

/-- The identification `H¹_Zar(X, 𝐆_m) = Pic(X)` of `identifications` is
`baseH1UnitsAddEquivSchemePicardGroup` for the Zariski topology. -/
@[simp]
public theorem identifications_zariskiPicard :
    (identifications.{t} B X hX).zariskiPicard =
      baseH1UnitsAddEquivSchemePicardGroup B X hX .zariski := rfl

/-- The identification `Pic(X) = H¹(X, 𝒪_X^*)` of `identifications` is the inverse of
`Stacks.Picard.ZariskiSite.zariskiH1UnitsAddEquivPicardGroup`. -/
@[simp]
public theorem identifications_picardSpace :
    (identifications.{t} B X hX).picardSpace =
      (Stacks.Picard.ZariskiSite.zariskiH1UnitsAddEquivPicardGroup X).symm := rfl

/-! ### The small étale reading of `H¹_étale(X, 𝐆_m)` -/

/-- **The big étale group of the chain is the first cohomology of the units on the *small* étale
site of `X`.**  So the fourth identification of Tag 03P8 holds under either reading of
`H¹_étale(X, 𝐆_m)`: both are `Pic(X)`, the small-site one by
`Stacks.Picard.SmallEtaleSite.etaleH1UnitsAddEquivZariskiPicardGroup`. -/
public def bigEtaleH1UnitsAddEquivSmallEtaleH1Units (BE : BigEtaleSite.{u}) (hE : BE.Contains X)
    [HasExt.{t} (Sheaf (smallEtaleRingedSite BE X hE).J AddCommGrpCat.{u})] :
    bigH1Units B X hX .etale ≃+
      Sheaf.H (unitsAddSheaf (smallEtaleRingedSite BE X hE)) 1 :=
  (baseH1UnitsAddEquivSchemePicardGroup B X hX .etale).trans
    (Stacks.Picard.SmallEtaleSite.etaleH1UnitsAddEquivZariskiPicardGroup BE X hE).symm

end Stacks.Picard.AllTopologies

end
