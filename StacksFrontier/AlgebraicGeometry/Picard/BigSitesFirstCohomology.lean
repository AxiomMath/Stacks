module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.LocallyRingedBigSites
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.AbelianSheaves
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.EssentiallySmallInternalHom
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.PicardGroupOfARingedSiteGeneral

/-!
# First cohomology of the units on the big sites of a scheme

Let `S` be a scheme and let `τ` be one of the Zariski, étale, smooth, syntomic or fppf
topologies. The big `τ`-site of `S`, carrying the sheaf of global functions as its structure
sheaf, is a locally ringed site; feeding that to the identification of the first cohomology of
the units with the Picard group of a locally ringed site gives `H¹_τ(S, 𝐆_m) = Pic(𝒪_τ)`,
normalized on every invertible `𝒪_τ`-module by its torsor of local generators.

## Main results

* `Stacks.Picard.BigSites.bigZariskiH1UnitsAddEquivPicardGroup` and its étale, smooth, syntomic and
  fppf counterparts: the identifications `H¹_τ(S, 𝐆_m) = Pic(𝒪_τ)`.
* `Stacks.Picard.BigSites.bigZariskiH1UnitsAddEquivPicardGroup_symm_classOf` and its four
  counterparts: each identification sends the class of an invertible module to the cohomology
  class of its torsor of generators, which fixes the identification rather than only asserting
  that one exists.

## Implementation notes

These are instantiations of `Stacks.Cohomology.Torsors.Generators.h1UnitsAddEquivPicardGroup'`,
the registered form of Tag 040E, which is stated for an arbitrary
`AlgebraicGeometry.RingedSite.{u, v, w}`; nothing about it is restated here. Its locally ringed
hypothesis is `AlgebraicGeometry.bigZariskiOverRingedSite_isLocallyRinged` and its four
counterparts.

A big site over `S` is an `AlgebraicGeometry.RingedSite.{u + 1, u, u}`: its objects form a
`Type (u + 1)` while its morphisms and the sections of its structure sheaf are in `Type u`. The
three-universe form of Tag 040E asks the site to be essentially small in the universe of the
sections, which a slice of a cutoff category of schemes is. Sheafification of abelian presheaves
with sections in that universe, and the identification of the morphisms sheafification inverts
with the locally bijective ones, are already available for the five topologies; they are
restated here at the projections of the ringed sites, which instance search does not unfold, and
supplied on the slices, which is the form the Picard group of Tag 040B consumes.

`HasExt` is an instance binder rather than an instance, as in
`Stacks.Picard.SmallEtaleSite`: the universe in which the `Ext`-groups live is a parameter of
`HasExt` and is not determined by the site.

## References

* [Stacks Project, Tag 040E](https://stacks.math.columbia.edu/tag/040E)
* [Stacks Project, Tag 04EU](https://stacks.math.columbia.edu/tag/04EU)
* [Stacks Project, Tag 0GZV](https://stacks.math.columbia.edu/tag/0GZV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe t u

namespace Stacks.Picard.BigSites

/-! ### Sheafification on the slices of an essentially small site -/

/-- Abelian presheaves with sections in the smaller universe sheafify on every slice of an
essentially small site: a slice of an essentially small category is again essentially small. -/
public theorem hasSheafify_over_addCommGrp {C : Type (u + 1)} [Category.{u} C]
    [EssentiallySmall.{u} C] (J : GrothendieckTopology C) (U : C) :
    HasSheafify (J.over U) AddCommGrpCat.{u} :=
  have : EssentiallySmall.{u} (Over U) := Stacks.essentiallySmall_over.{u} U
  hasSheafifyEssentiallySmallSite.{u} _ _

/-- On every slice of an essentially small site, the morphisms of abelian presheaves with
sections in the smaller universe which sheafification inverts are the locally bijective ones. -/
public theorem wEqualsLocallyBijective_over_addCommGrp {C : Type (u + 1)} [Category.{u} C]
    [EssentiallySmall.{u} C] (J : GrothendieckTopology C) (U : C) :
    (J.over U).WEqualsLocallyBijective AddCommGrpCat.{u} :=
  have : EssentiallySmall.{u} (Over U) := Stacks.essentiallySmall_over.{u} U
  .ofEssentiallySmall.{u} _

/-! ### The big Zariski site -/

section Zariski

variable (B : BigZariskiSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The big Zariski site over `S` is essentially small in the universe of the schemes. -/
public instance zariskiEssentiallySmall :
    EssentiallySmall.{u} (bigZariskiOverRingedSite B S hS).C :=
  Stacks.essentiallySmall_over.{u} _

/-- Abelian presheaves with sections in the universe of the schemes sheafify on the big Zariski
ringed site over `S`. -/
public instance zariskiHasSheafify :
    HasSheafify (bigZariskiOverRingedSite B S hS).J AddCommGrpCat.{u} :=
  BigZariskiOver.hasSheafify' B S hS

/-- Sheafification on the big Zariski ringed site over `S` inverts exactly the locally bijective
morphisms of abelian presheaves. -/
public instance zariskiWEqualsLocallyBijective :
    (bigZariskiOverRingedSite B S hS).J.WEqualsLocallyBijective AddCommGrpCat.{u} :=
  BigZariskiOver.wEqualsLocallyBijective' B S hS

/-- Abelian presheaves sheafify on every slice of the big Zariski ringed site over `S`. -/
public instance zariskiHasSheafifyOver (U : (bigZariskiOverRingedSite B S hS).C) :
    HasSheafify ((bigZariskiOverRingedSite B S hS).J.over U) AddCommGrpCat.{u} :=
  hasSheafify_over_addCommGrp _ U

/-- Sheafification on every slice of the big Zariski ringed site over `S` inverts exactly the
locally bijective morphisms of abelian presheaves. -/
public instance zariskiWEqualsLocallyBijectiveOver (U : (bigZariskiOverRingedSite B S hS).C) :
    ((bigZariskiOverRingedSite B S hS).J.over U).WEqualsLocallyBijective AddCommGrpCat.{u} :=
  wEqualsLocallyBijective_over_addCommGrp _ U

/-- The abelian group structure on the Picard group of the big Zariski ringed site, named
because instance search does not find it through the universe constraints of a ringed site. -/
local instance zariskiPicardGroupAddCommGroup :
    AddCommGroup (Stacks.SheafOfModules.Picard.PicardGroup
      (bigZariskiOverRingedSite B S hS).O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf (bigZariskiOverRingedSite B S hS).O).2) :=
  Stacks.SheafOfModules.Picard.instAddCommGroupPicardGroup
    (bigZariskiOverRingedSite B S hS).O.obj
    (Stacks.SheafOfModules.Tensor.ringSheaf (bigZariskiOverRingedSite B S hS).O).2

variable [HasExt.{t} (Sheaf (bigZariskiOverRingedSite B S hS).J AddCommGrpCat.{u})]

/-- **Tag 040E on the big Zariski site.** For a scheme `S` in a big Zariski site containing it
there is a canonical isomorphism of abelian groups `H¹_{Zar}(S, 𝐆_m) = Pic(𝒪_{Zar})` on the big
Zariski site over `S`. -/
public def bigZariskiH1UnitsAddEquivPicardGroup :
    Sheaf.H (Stacks.Cohomology.Torsors.Generators.unitsAddSheaf
        (bigZariskiOverRingedSite B S hS)) 1 ≃+
      Stacks.SheafOfModules.Picard.PicardGroup (bigZariskiOverRingedSite B S hS).O.obj
        (Stacks.SheafOfModules.Tensor.ringSheaf (bigZariskiOverRingedSite B S hS).O).2 :=
  Stacks.Cohomology.Torsors.Generators.h1UnitsAddEquivPicardGroup'
    (bigZariskiOverRingedSite B S hS) (bigZariskiOverRingedSite_isLocallyRinged B S hS)

/-- The identification on the big Zariski site is the canonical one: its inverse sends the class
of an invertible module to the first cohomology class of its torsor of local generators. -/
public theorem bigZariskiH1UnitsAddEquivPicardGroup_symm_classOf
    (L : SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (bigZariskiOverRingedSite B S hS).O))
    (hL : Stacks.SheafOfModules.IsInvertible (bigZariskiOverRingedSite B S hS).O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf (bigZariskiOverRingedSite B S hS).O).2 L) :
    (bigZariskiH1UnitsAddEquivPicardGroup B S hS).symm
        (Stacks.SheafOfModules.Picard.classOf (bigZariskiOverRingedSite B S hS).O.obj
          (Stacks.SheafOfModules.Tensor.ringSheaf (bigZariskiOverRingedSite B S hS).O).2 L hL) =
      Stacks.Cohomology.Torsors.torsorIsoClassesEquivH1
        (Stacks.Cohomology.Torsors.Generators.unitsAddSheaf
          (bigZariskiOverRingedSite B S hS))
        (Quotient.mk (Stacks.Cohomology.Torsors.torsorSetoid
            (Stacks.Cohomology.Torsors.Generators.unitsAddSheaf
              (bigZariskiOverRingedSite B S hS)))
          (Stacks.Cohomology.Torsors.Generators.generatorTorsor'
            (bigZariskiOverRingedSite B S hS)
            (bigZariskiOverRingedSite_isLocallyRinged B S hS) L hL).torsor) :=
  Stacks.Cohomology.Torsors.Generators.h1UnitsAddEquivPicardGroup_symm_classOf'
    (bigZariskiOverRingedSite B S hS) (bigZariskiOverRingedSite_isLocallyRinged B S hS) L hL

end Zariski

/-! ### The big étale site -/

section Etale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The big étale site over `S` is essentially small in the universe of the schemes. -/
public instance etaleEssentiallySmall :
    EssentiallySmall.{u} (bigEtaleOverRingedSite B S hS).C :=
  Stacks.essentiallySmall_over.{u} _

/-- Abelian presheaves with sections in the universe of the schemes sheafify on the big étale
ringed site over `S`. -/
public instance etaleHasSheafify :
    HasSheafify (bigEtaleOverRingedSite B S hS).J AddCommGrpCat.{u} :=
  BigEtaleOver.hasSheafify' B S hS

/-- Sheafification on the big étale ringed site over `S` inverts exactly the locally bijective
morphisms of abelian presheaves. -/
public instance etaleWEqualsLocallyBijective :
    (bigEtaleOverRingedSite B S hS).J.WEqualsLocallyBijective AddCommGrpCat.{u} :=
  BigEtaleOver.wEqualsLocallyBijective' B S hS

/-- Abelian presheaves sheafify on every slice of the big étale ringed site over `S`. -/
public instance etaleHasSheafifyOver (U : (bigEtaleOverRingedSite B S hS).C) :
    HasSheafify ((bigEtaleOverRingedSite B S hS).J.over U) AddCommGrpCat.{u} :=
  hasSheafify_over_addCommGrp _ U

/-- Sheafification on every slice of the big étale ringed site over `S` inverts exactly the
locally bijective morphisms of abelian presheaves. -/
public instance etaleWEqualsLocallyBijectiveOver (U : (bigEtaleOverRingedSite B S hS).C) :
    ((bigEtaleOverRingedSite B S hS).J.over U).WEqualsLocallyBijective AddCommGrpCat.{u} :=
  wEqualsLocallyBijective_over_addCommGrp _ U

/-- The abelian group structure on the Picard group of the big étale ringed site, named because
instance search does not find it through the universe constraints of a ringed site. -/
local instance etalePicardGroupAddCommGroup :
    AddCommGroup (Stacks.SheafOfModules.Picard.PicardGroup
      (bigEtaleOverRingedSite B S hS).O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf (bigEtaleOverRingedSite B S hS).O).2) :=
  Stacks.SheafOfModules.Picard.instAddCommGroupPicardGroup
    (bigEtaleOverRingedSite B S hS).O.obj
    (Stacks.SheafOfModules.Tensor.ringSheaf (bigEtaleOverRingedSite B S hS).O).2

variable [HasExt.{t} (Sheaf (bigEtaleOverRingedSite B S hS).J AddCommGrpCat.{u})]

/-- **Tag 040E on the big étale site.** For a scheme `S` in a big étale site containing it there
is a canonical isomorphism of abelian groups `H¹_{étale}(S, 𝐆_m) = Pic(𝒪_{étale})` on the big
étale site over `S`. -/
public def bigEtaleH1UnitsAddEquivPicardGroup :
    Sheaf.H (Stacks.Cohomology.Torsors.Generators.unitsAddSheaf
        (bigEtaleOverRingedSite B S hS)) 1 ≃+
      Stacks.SheafOfModules.Picard.PicardGroup (bigEtaleOverRingedSite B S hS).O.obj
        (Stacks.SheafOfModules.Tensor.ringSheaf (bigEtaleOverRingedSite B S hS).O).2 :=
  Stacks.Cohomology.Torsors.Generators.h1UnitsAddEquivPicardGroup'
    (bigEtaleOverRingedSite B S hS) (bigEtaleOverRingedSite_isLocallyRinged B S hS)

/-- The identification on the big étale site is the canonical one: its inverse sends the class of
an invertible module to the first cohomology class of its torsor of local generators. -/
public theorem bigEtaleH1UnitsAddEquivPicardGroup_symm_classOf
    (L : SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (bigEtaleOverRingedSite B S hS).O))
    (hL : Stacks.SheafOfModules.IsInvertible (bigEtaleOverRingedSite B S hS).O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf (bigEtaleOverRingedSite B S hS).O).2 L) :
    (bigEtaleH1UnitsAddEquivPicardGroup B S hS).symm
        (Stacks.SheafOfModules.Picard.classOf (bigEtaleOverRingedSite B S hS).O.obj
          (Stacks.SheafOfModules.Tensor.ringSheaf (bigEtaleOverRingedSite B S hS).O).2 L hL) =
      Stacks.Cohomology.Torsors.torsorIsoClassesEquivH1
        (Stacks.Cohomology.Torsors.Generators.unitsAddSheaf (bigEtaleOverRingedSite B S hS))
        (Quotient.mk (Stacks.Cohomology.Torsors.torsorSetoid
            (Stacks.Cohomology.Torsors.Generators.unitsAddSheaf
              (bigEtaleOverRingedSite B S hS)))
          (Stacks.Cohomology.Torsors.Generators.generatorTorsor' (bigEtaleOverRingedSite B S hS)
            (bigEtaleOverRingedSite_isLocallyRinged B S hS) L hL).torsor) :=
  Stacks.Cohomology.Torsors.Generators.h1UnitsAddEquivPicardGroup_symm_classOf'
    (bigEtaleOverRingedSite B S hS) (bigEtaleOverRingedSite_isLocallyRinged B S hS) L hL

end Etale

/-! ### The big smooth site -/

section Smooth

variable (B : BigSmoothSite.{u}) (S : Scheme.{u}) (hS : S.size < B.cutoff)

/-- The big smooth site over `S` is essentially small in the universe of the schemes. -/
public instance smoothEssentiallySmall :
    EssentiallySmall.{u} (bigSmoothOverRingedSite B S hS).C :=
  Stacks.essentiallySmall_over.{u} _

/-- Abelian presheaves with sections in the universe of the schemes sheafify on the big smooth
ringed site over `S`. -/
public instance smoothHasSheafify :
    HasSheafify (bigSmoothOverRingedSite B S hS).J AddCommGrpCat.{u} :=
  BigSmoothOver.hasSheafify' B S hS

/-- Sheafification on the big smooth ringed site over `S` inverts exactly the locally bijective
morphisms of abelian presheaves. -/
public instance smoothWEqualsLocallyBijective :
    (bigSmoothOverRingedSite B S hS).J.WEqualsLocallyBijective AddCommGrpCat.{u} :=
  BigSmoothOver.wEqualsLocallyBijective' B S hS

/-- Abelian presheaves sheafify on every slice of the big smooth ringed site over `S`. -/
public instance smoothHasSheafifyOver (U : (bigSmoothOverRingedSite B S hS).C) :
    HasSheafify ((bigSmoothOverRingedSite B S hS).J.over U) AddCommGrpCat.{u} :=
  hasSheafify_over_addCommGrp _ U

/-- Sheafification on every slice of the big smooth ringed site over `S` inverts exactly the
locally bijective morphisms of abelian presheaves. -/
public instance smoothWEqualsLocallyBijectiveOver (U : (bigSmoothOverRingedSite B S hS).C) :
    ((bigSmoothOverRingedSite B S hS).J.over U).WEqualsLocallyBijective AddCommGrpCat.{u} :=
  wEqualsLocallyBijective_over_addCommGrp _ U

/-- The abelian group structure on the Picard group of the big smooth ringed site, named because
instance search does not find it through the universe constraints of a ringed site. -/
local instance smoothPicardGroupAddCommGroup :
    AddCommGroup (Stacks.SheafOfModules.Picard.PicardGroup
      (bigSmoothOverRingedSite B S hS).O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf (bigSmoothOverRingedSite B S hS).O).2) :=
  Stacks.SheafOfModules.Picard.instAddCommGroupPicardGroup
    (bigSmoothOverRingedSite B S hS).O.obj
    (Stacks.SheafOfModules.Tensor.ringSheaf (bigSmoothOverRingedSite B S hS).O).2

variable [HasExt.{t} (Sheaf (bigSmoothOverRingedSite B S hS).J AddCommGrpCat.{u})]

/-- **Tag 040E on the big smooth site.** For a scheme `S` in a big smooth site containing it
there is a canonical isomorphism of abelian groups `H¹_{smooth}(S, 𝐆_m) = Pic(𝒪_{smooth})` on the
big smooth site over `S`. -/
public def bigSmoothH1UnitsAddEquivPicardGroup :
    Sheaf.H (Stacks.Cohomology.Torsors.Generators.unitsAddSheaf
        (bigSmoothOverRingedSite B S hS)) 1 ≃+
      Stacks.SheafOfModules.Picard.PicardGroup (bigSmoothOverRingedSite B S hS).O.obj
        (Stacks.SheafOfModules.Tensor.ringSheaf (bigSmoothOverRingedSite B S hS).O).2 :=
  Stacks.Cohomology.Torsors.Generators.h1UnitsAddEquivPicardGroup'
    (bigSmoothOverRingedSite B S hS) (bigSmoothOverRingedSite_isLocallyRinged B S hS)

/-- The identification on the big smooth site is the canonical one: its inverse sends the class
of an invertible module to the first cohomology class of its torsor of local generators. -/
public theorem bigSmoothH1UnitsAddEquivPicardGroup_symm_classOf
    (L : SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (bigSmoothOverRingedSite B S hS).O))
    (hL : Stacks.SheafOfModules.IsInvertible (bigSmoothOverRingedSite B S hS).O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf (bigSmoothOverRingedSite B S hS).O).2 L) :
    (bigSmoothH1UnitsAddEquivPicardGroup B S hS).symm
        (Stacks.SheafOfModules.Picard.classOf (bigSmoothOverRingedSite B S hS).O.obj
          (Stacks.SheafOfModules.Tensor.ringSheaf (bigSmoothOverRingedSite B S hS).O).2 L hL) =
      Stacks.Cohomology.Torsors.torsorIsoClassesEquivH1
        (Stacks.Cohomology.Torsors.Generators.unitsAddSheaf (bigSmoothOverRingedSite B S hS))
        (Quotient.mk (Stacks.Cohomology.Torsors.torsorSetoid
            (Stacks.Cohomology.Torsors.Generators.unitsAddSheaf
              (bigSmoothOverRingedSite B S hS)))
          (Stacks.Cohomology.Torsors.Generators.generatorTorsor' (bigSmoothOverRingedSite B S hS)
            (bigSmoothOverRingedSite_isLocallyRinged B S hS) L hL).torsor) :=
  Stacks.Cohomology.Torsors.Generators.h1UnitsAddEquivPicardGroup_symm_classOf'
    (bigSmoothOverRingedSite B S hS) (bigSmoothOverRingedSite_isLocallyRinged B S hS) L hL

end Smooth

/-! ### The big syntomic site -/

section Syntomic

variable (B : BigSyntomicSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The big syntomic site over `S` is essentially small in the universe of the schemes. -/
public instance syntomicEssentiallySmall :
    EssentiallySmall.{u} (bigSyntomicOverRingedSite B S hS).C :=
  Stacks.essentiallySmall_over.{u} _

/-- Abelian presheaves with sections in the universe of the schemes sheafify on the big syntomic
ringed site over `S`. -/
public instance syntomicHasSheafify :
    HasSheafify (bigSyntomicOverRingedSite B S hS).J AddCommGrpCat.{u} :=
  BigSyntomicOver.hasSheafify' B S hS

/-- Sheafification on the big syntomic ringed site over `S` inverts exactly the locally bijective
morphisms of abelian presheaves. -/
public instance syntomicWEqualsLocallyBijective :
    (bigSyntomicOverRingedSite B S hS).J.WEqualsLocallyBijective AddCommGrpCat.{u} :=
  BigSyntomicOver.wEqualsLocallyBijective' B S hS

/-- Abelian presheaves sheafify on every slice of the big syntomic ringed site over `S`. -/
public instance syntomicHasSheafifyOver (U : (bigSyntomicOverRingedSite B S hS).C) :
    HasSheafify ((bigSyntomicOverRingedSite B S hS).J.over U) AddCommGrpCat.{u} :=
  hasSheafify_over_addCommGrp _ U

/-- Sheafification on every slice of the big syntomic ringed site over `S` inverts exactly the
locally bijective morphisms of abelian presheaves. -/
public instance syntomicWEqualsLocallyBijectiveOver (U : (bigSyntomicOverRingedSite B S hS).C) :
    ((bigSyntomicOverRingedSite B S hS).J.over U).WEqualsLocallyBijective AddCommGrpCat.{u} :=
  wEqualsLocallyBijective_over_addCommGrp _ U

/-- The abelian group structure on the Picard group of the big syntomic ringed site, named
because instance search does not find it through the universe constraints of a ringed site. -/
local instance syntomicPicardGroupAddCommGroup :
    AddCommGroup (Stacks.SheafOfModules.Picard.PicardGroup
      (bigSyntomicOverRingedSite B S hS).O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf (bigSyntomicOverRingedSite B S hS).O).2) :=
  Stacks.SheafOfModules.Picard.instAddCommGroupPicardGroup
    (bigSyntomicOverRingedSite B S hS).O.obj
    (Stacks.SheafOfModules.Tensor.ringSheaf (bigSyntomicOverRingedSite B S hS).O).2

variable [HasExt.{t} (Sheaf (bigSyntomicOverRingedSite B S hS).J AddCommGrpCat.{u})]

/-- **Tag 040E on the big syntomic site.** For a scheme `S` in a big syntomic site containing it
there is a canonical isomorphism of abelian groups `H¹_{syntomic}(S, 𝐆_m) = Pic(𝒪_{syntomic})` on
the big syntomic site over `S`. -/
public def bigSyntomicH1UnitsAddEquivPicardGroup :
    Sheaf.H (Stacks.Cohomology.Torsors.Generators.unitsAddSheaf
        (bigSyntomicOverRingedSite B S hS)) 1 ≃+
      Stacks.SheafOfModules.Picard.PicardGroup (bigSyntomicOverRingedSite B S hS).O.obj
        (Stacks.SheafOfModules.Tensor.ringSheaf (bigSyntomicOverRingedSite B S hS).O).2 :=
  Stacks.Cohomology.Torsors.Generators.h1UnitsAddEquivPicardGroup'
    (bigSyntomicOverRingedSite B S hS) (bigSyntomicOverRingedSite_isLocallyRinged B S hS)

/-- The identification on the big syntomic site is the canonical one: its inverse sends the class
of an invertible module to the first cohomology class of its torsor of local generators. -/
public theorem bigSyntomicH1UnitsAddEquivPicardGroup_symm_classOf
    (L : SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (bigSyntomicOverRingedSite B S hS).O))
    (hL : Stacks.SheafOfModules.IsInvertible (bigSyntomicOverRingedSite B S hS).O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf (bigSyntomicOverRingedSite B S hS).O).2 L) :
    (bigSyntomicH1UnitsAddEquivPicardGroup B S hS).symm
        (Stacks.SheafOfModules.Picard.classOf (bigSyntomicOverRingedSite B S hS).O.obj
          (Stacks.SheafOfModules.Tensor.ringSheaf (bigSyntomicOverRingedSite B S hS).O).2 L hL) =
      Stacks.Cohomology.Torsors.torsorIsoClassesEquivH1
        (Stacks.Cohomology.Torsors.Generators.unitsAddSheaf (bigSyntomicOverRingedSite B S hS))
        (Quotient.mk (Stacks.Cohomology.Torsors.torsorSetoid
            (Stacks.Cohomology.Torsors.Generators.unitsAddSheaf
              (bigSyntomicOverRingedSite B S hS)))
          (Stacks.Cohomology.Torsors.Generators.generatorTorsor'
            (bigSyntomicOverRingedSite B S hS)
            (bigSyntomicOverRingedSite_isLocallyRinged B S hS) L hL).torsor) :=
  Stacks.Cohomology.Torsors.Generators.h1UnitsAddEquivPicardGroup_symm_classOf'
    (bigSyntomicOverRingedSite B S hS) (bigSyntomicOverRingedSite_isLocallyRinged B S hS) L hL

end Syntomic

/-! ### The big fppf site -/

section Fppf

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The big fppf site over `S` is essentially small in the universe of the schemes. -/
public instance fppfEssentiallySmall :
    EssentiallySmall.{u} (bigFppfOverRingedSite B S hS).C :=
  Stacks.essentiallySmall_over.{u} _

/-- Abelian presheaves with sections in the universe of the schemes sheafify on the big fppf
ringed site over `S`. -/
public instance fppfHasSheafify :
    HasSheafify (bigFppfOverRingedSite B S hS).J AddCommGrpCat.{u} :=
  BigFppfOver.hasSheafify' B S hS

/-- Sheafification on the big fppf ringed site over `S` inverts exactly the locally bijective
morphisms of abelian presheaves. -/
public instance fppfWEqualsLocallyBijective :
    (bigFppfOverRingedSite B S hS).J.WEqualsLocallyBijective AddCommGrpCat.{u} :=
  BigFppfOver.wEqualsLocallyBijective' B S hS

/-- Abelian presheaves sheafify on every slice of the big fppf ringed site over `S`. -/
public instance fppfHasSheafifyOver (U : (bigFppfOverRingedSite B S hS).C) :
    HasSheafify ((bigFppfOverRingedSite B S hS).J.over U) AddCommGrpCat.{u} :=
  hasSheafify_over_addCommGrp _ U

/-- Sheafification on every slice of the big fppf ringed site over `S` inverts exactly the
locally bijective morphisms of abelian presheaves. -/
public instance fppfWEqualsLocallyBijectiveOver (U : (bigFppfOverRingedSite B S hS).C) :
    ((bigFppfOverRingedSite B S hS).J.over U).WEqualsLocallyBijective AddCommGrpCat.{u} :=
  wEqualsLocallyBijective_over_addCommGrp _ U

/-- The abelian group structure on the Picard group of the big fppf ringed site, named because
instance search does not find it through the universe constraints of a ringed site. -/
local instance fppfPicardGroupAddCommGroup :
    AddCommGroup (Stacks.SheafOfModules.Picard.PicardGroup
      (bigFppfOverRingedSite B S hS).O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf (bigFppfOverRingedSite B S hS).O).2) :=
  Stacks.SheafOfModules.Picard.instAddCommGroupPicardGroup
    (bigFppfOverRingedSite B S hS).O.obj
    (Stacks.SheafOfModules.Tensor.ringSheaf (bigFppfOverRingedSite B S hS).O).2

variable [HasExt.{t} (Sheaf (bigFppfOverRingedSite B S hS).J AddCommGrpCat.{u})]

/-- **Tag 040E on the big fppf site.** For a scheme `S` in a big fppf site containing it there is
a canonical isomorphism of abelian groups `H¹_{fppf}(S, 𝐆_m) = Pic(𝒪_{fppf})` on the big fppf
site over `S`. -/
public def bigFppfH1UnitsAddEquivPicardGroup :
    Sheaf.H (Stacks.Cohomology.Torsors.Generators.unitsAddSheaf
        (bigFppfOverRingedSite B S hS)) 1 ≃+
      Stacks.SheafOfModules.Picard.PicardGroup (bigFppfOverRingedSite B S hS).O.obj
        (Stacks.SheafOfModules.Tensor.ringSheaf (bigFppfOverRingedSite B S hS).O).2 :=
  Stacks.Cohomology.Torsors.Generators.h1UnitsAddEquivPicardGroup'
    (bigFppfOverRingedSite B S hS) (bigFppfOverRingedSite_isLocallyRinged B S hS)

/-- The identification on the big fppf site is the canonical one: its inverse sends the class of
an invertible module to the first cohomology class of its torsor of local generators. -/
public theorem bigFppfH1UnitsAddEquivPicardGroup_symm_classOf
    (L : SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (bigFppfOverRingedSite B S hS).O))
    (hL : Stacks.SheafOfModules.IsInvertible (bigFppfOverRingedSite B S hS).O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf (bigFppfOverRingedSite B S hS).O).2 L) :
    (bigFppfH1UnitsAddEquivPicardGroup B S hS).symm
        (Stacks.SheafOfModules.Picard.classOf (bigFppfOverRingedSite B S hS).O.obj
          (Stacks.SheafOfModules.Tensor.ringSheaf (bigFppfOverRingedSite B S hS).O).2 L hL) =
      Stacks.Cohomology.Torsors.torsorIsoClassesEquivH1
        (Stacks.Cohomology.Torsors.Generators.unitsAddSheaf (bigFppfOverRingedSite B S hS))
        (Quotient.mk (Stacks.Cohomology.Torsors.torsorSetoid
            (Stacks.Cohomology.Torsors.Generators.unitsAddSheaf
              (bigFppfOverRingedSite B S hS)))
          (Stacks.Cohomology.Torsors.Generators.generatorTorsor' (bigFppfOverRingedSite B S hS)
            (bigFppfOverRingedSite_isLocallyRinged B S hS) L hL).torsor) :=
  Stacks.Cohomology.Torsors.Generators.h1UnitsAddEquivPicardGroup_symm_classOf'
    (bigFppfOverRingedSite B S hS) (bigFppfOverRingedSite_isLocallyRinged B S hS) L hL

end Fppf

end Stacks.Picard.BigSites

end
