module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleRingedSite
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleRingedSiteInternalHom
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.PicardGroupOfARingedSiteGeneral

/-!
# First cohomology of the units on the small étale site of a scheme

The small étale site of a scheme, carrying the sheaf of global functions, is a locally ringed
site (Stacks 04HZ). Feeding this to the identification of first cohomology of the units with the
Picard group of a locally ringed site gives `H¹_{étale}(S, 𝐆_m) = Pic(𝒪_étale)`, normalized on
every invertible `𝒪_étale`-module by its torsor of local generators.

## Main results

* `Stacks.Picard.SmallEtaleSite.etaleH1UnitsAddEquivPicardGroup`: the identification
  `H¹_{étale}(S, 𝐆_m) = Pic(𝒪_étale)`.
* `Stacks.Picard.SmallEtaleSite.etaleH1UnitsAddEquivPicardGroup_symm_classOf`: it sends the class
  of an invertible `𝒪_étale`-module to the cohomology class of its torsor of generators, which
  fixes the identification rather than only asserting that one exists.

## Implementation notes

The small étale ringed site is an `AlgebraicGeometry.RingedSite.{u + 1, u, u}`: its objects form
a `Type (u + 1)` while its morphisms and the sections of its structure sheaf are in `Type u`. The
development of Tag 040E is therefore used in its three-universe form, whose inverse half asks the
site to be essentially small in the universe of the sections
(`AlgebraicGeometry.SmallEtale.essentiallySmall`, restated for the projection of the ringed site
as `AlgebraicGeometry.smallEtaleRingedSite_essentiallySmall`).

`HasExt` is an instance binder rather than an instance: the universe in which the `Ext`-groups
live is a parameter of `HasExt` and is not determined by the site, exactly as in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.InverseImage`. Sheafification and
local bijectivity on the site and on each of its slices are instances, found through
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleRingedSiteInternalHom`.

The comparison with `H¹_{Zar}(S, 𝐆_m)` is not here: it needs `Pic(𝒪_étale) = Pic(S)`, which is
Descent, Proposition 03DX (2) read on Picard groups, and is
`AlgebraicGeometry.SmallEtale.associatedModulePicardAddEquiv` in
`StacksFrontier/AlgebraicGeometry/Picard/SmallEtalePicardIsomorphism.lean`. The composite,
`H¹_{étale}(S, 𝐆_m) = H¹_{Zar}(S, 𝐆_m) = Pic(S)`, is
`Stacks.Picard.SmallEtaleSite.etaleH1UnitsAddEquivZariskiH1Units` in
`StacksFrontier/AlgebraicGeometry/Picard/SmallEtaleFirstCohomologyComparison.lean`; no monoidal
structure on `AlgebraicGeometry.SmallEtale.associatedModule` enters, the transport going through
the object-level comparisons of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/PicardTransport.lean` instead. The `fppf`,
`syntomic` and `smooth` identifications of Tag 03P8 remain open.

## References

* [Stacks Project, Tag 040E](https://stacks.math.columbia.edu/tag/040E)
* [Stacks Project, Tag 04HZ](https://stacks.math.columbia.edu/tag/04HZ)
* [Stacks Project, Tag 03P8](https://stacks.math.columbia.edu/tag/03P8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe t u

namespace Stacks.Picard.SmallEtaleSite

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The abelian group structure on the Picard group of the small étale ringed site of a scheme,
named because instance search does not find it through the universe constraints of a ringed
site. -/
local instance etalePicardGroupAddCommGroup :
    AddCommGroup (Stacks.SheafOfModules.Picard.PicardGroup (smallEtaleRingedSite B S hS).O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS).O).2) :=
  Stacks.SheafOfModules.Picard.instAddCommGroupPicardGroup (smallEtaleRingedSite B S hS).O.obj
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS).O).2

variable [HasExt.{t} (Sheaf (smallEtaleRingedSite B S hS).J AddCommGrpCat.{u})]

/-- **Stacks Project, Tag 040E, at `τ = étale` on the small site.** For a scheme `S` in a big
étale site containing it there is a canonical isomorphism of abelian groups
`H¹_{étale}(S, 𝐆_m) = Pic(𝒪_étale)`. -/
@[stacks 040E "the identification H¹_étale(S, 𝐆_m) = Pic(𝒪_étale), on the small étale site"]
def etaleH1UnitsAddEquivPicardGroup :
    Sheaf.H
        (Stacks.Cohomology.Torsors.Generators.unitsAddSheaf (smallEtaleRingedSite B S hS)) 1 ≃+
      Stacks.SheafOfModules.Picard.PicardGroup (smallEtaleRingedSite B S hS).O.obj
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS).O).2 :=
  Stacks.Cohomology.Torsors.Generators.h1UnitsAddEquivPicardGroup'
    (smallEtaleRingedSite B S hS) (smallEtaleRingedSite_isLocallyRinged B S hS)

/-- **Stacks Project, Tag 040E at `τ = étale`, the identification is the canonical one.** Its
inverse sends the class of an invertible `𝒪_étale`-module to the first cohomology class of its
torsor of local generators. -/
@[stacks 040E "the étale identification is normalized on invertible modules"]
theorem etaleH1UnitsAddEquivPicardGroup_symm_classOf
    (L : SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS).O))
    (hL : Stacks.SheafOfModules.IsInvertible (smallEtaleRingedSite B S hS).O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS).O).2 L) :
    (etaleH1UnitsAddEquivPicardGroup B S hS).symm
        (Stacks.SheafOfModules.Picard.classOf (smallEtaleRingedSite B S hS).O.obj
          (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS).O).2 L hL) =
      Stacks.Cohomology.Torsors.torsorIsoClassesEquivH1
        (Stacks.Cohomology.Torsors.Generators.unitsAddSheaf (smallEtaleRingedSite B S hS))
        (Quotient.mk (Stacks.Cohomology.Torsors.torsorSetoid
            (Stacks.Cohomology.Torsors.Generators.unitsAddSheaf (smallEtaleRingedSite B S hS)))
          (Stacks.Cohomology.Torsors.Generators.generatorTorsor' (smallEtaleRingedSite B S hS)
            (smallEtaleRingedSite_isLocallyRinged B S hS) L hL).torsor) :=
  Stacks.Cohomology.Torsors.Generators.h1UnitsAddEquivPicardGroup_symm_classOf'
    (smallEtaleRingedSite B S hS) (smallEtaleRingedSite_isLocallyRinged B S hS) L hL

end Stacks.Picard.SmallEtaleSite

end
