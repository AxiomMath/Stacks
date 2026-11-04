module

public import Mathlib.Topology.Sheaves.Points
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Picard.FirstCohomologyNaturality
public import StacksFrontier.AlgebraicGeometry.ReflexiveHull.LocalKernelPresentation
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.PicardGroupOfARingedSite
public import StacksFrontier.CategoryTheory.Sites.Point.OpensPointFiberStalk

/-!
# First cohomology of the units on the Zariski site of a scheme

The site of opens of a scheme, carrying the structure sheaf, is a locally ringed site: the fibre
of the structure sheaf at the point of that site attached to a point of the space is the local
ring there. Feeding this to the identification of first cohomology of the units with the Picard
group of a locally ringed site gives `H¹_{Zar}(X, 𝐆_m) = Pic(X)`, normalized on every line
bundle by its torsor of local generators.

## Main results

* `Stacks.Picard.ZariskiSite.schemeRingedSite_isLocallyRinged`: the ringed site of opens of a
  scheme is locally ringed.
* `Stacks.Picard.ZariskiSite.zariskiH1UnitsAddEquivPicardGroup`: the identification
  `H¹_{Zar}(X, 𝐆_m) = Pic(X)`.
* `Stacks.Picard.ZariskiSite.zariskiH1UnitsAddEquivPicardGroup_symm_classOf`: it sends the class
  of an invertible module to the cohomology class of its torsor of generators, which fixes the
  identification rather than only asserting that one exists.

## Implementation notes

The ringed site used is `Stacks.AlgebraicGeometry.ReflexiveModules.schemeRingedSite`, the only
ringed site built from a scheme whose three universes agree, which is what the development of
Tag 040E is stated for. The ringed sites of the big and small sites of schemes are
`AlgebraicGeometry.RingedSite.{u + 1, u, u}` and so are out of its reach.

Local ringedness is read off the stalks through
`AlgebraicGeometry.RingedSite.isLocallyRinged_of_local_stalks`. The conservative family of
points is Mathlib's family attached to the points of the space, whose membership predicate is an
equality of points, so the stalk computation is needed only at those points and no comparison of
site points enters.

The sheafification and `Ext` instances for abelian sheaves on the site of opens are found by
instance search, so the identification is unconditional: unlike on the big sites of schemes, no
`HasSheafify` or `HasExt` hypothesis has to be carried.

The identification of Tag 03P8 with the cohomology of the other topologies is not here. Four of
the six identifications of that tag — the comparisons of `H¹_{fppf}`, `H¹_{syntomic}`,
`H¹_{smooth}` and `H¹_{étale}` with `H¹_{Zar}` — need `Pic(𝒪_τ) = Pic(X)`, which is
Tag 03DX.  Its essential-surjectivity half is available at `τ = fppf`,
`AlgebraicGeometry.BigFppfOver.quasicoherentIsEssImageAssociatedModule'` (in
`StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.EffectiveGlueAgreementTransport`), so the
`H¹_{fppf}` comparison is not blocked on it; at the syntomic, smooth and étale topologies it is
still open, carried as the hypothesis
`AlgebraicGeometry.BigFppfOver.BaseQuasicoherentIsEssImageAssociatedModule τ` (in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.QuasiCoherentSmallEtaleBigSite`).

## References

* [Stacks Project, Tag 03P8](https://stacks.math.columbia.edu/tag/03P8)
* [Stacks Project, Tag 040E](https://stacks.math.columbia.edu/tag/040E)
* [Stacks Project, Tag 04EU](https://stacks.math.columbia.edu/tag/04EU)
* [Stacks Project, Tag 09NU](https://stacks.math.columbia.edu/tag/09NU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

universe u

namespace Stacks.Picard.ZariskiSite

open Stacks.AlgebraicGeometry.ReflexiveModules (schemeRingedSite)

/-- The fibre of the structure sheaf of a scheme at the point of the site of its opens attached
to a point of the space is the local ring of the scheme there. -/
theorem isLocalRing_presheafFiber_structurePresheaf (X : Scheme.{u}) (x : ↥X) :
    IsLocalRing ↥(((Opens.pointGrothendieckTopology x).presheafFiber
      (A := CommRingCat.{u})).obj (schemeRingedSite X).O.obj) := by
  have h : IsLocalRing ↥(X.presheaf.stalk x) := inferInstance
  exact (Opens.pointFiberStalkIso x X.presheaf).commRingCatIsoToRingEquiv.symm.isLocalRing

/-- **The ringed site of opens of a scheme is locally ringed.** Every point of the site is
attached to a point of the space, where the stalk of the structure sheaf is a local ring. -/
theorem schemeRingedSite_isLocallyRinged (X : Scheme.{u}) :
    RingedSite.IsLocallyRinged (schemeRingedSite X) := by
  refine RingedSite.isLocallyRinged_of_local_stalks (schemeRingedSite X)
    (Opens.pointsGrothendieckTopology ↥X)
    (Opens.isConservativeFamilyOfPoints_pointsGrothendieckTopology ↥X) ?_
  intro p hp
  obtain ⟨x, rfl⟩ := (ObjectProperty.ofObj_iff _ p).1 hp
  exact isLocalRing_presheafFiber_structurePresheaf X x

variable (X : Scheme.{u})

/-- The abelian group structure on the Picard group of the ringed site of opens of a scheme,
named because instance search does not find it through the universe constraints of a ringed
site. -/
local instance zariskiPicardGroupAddCommGroup :
    AddCommGroup (Stacks.SheafOfModules.Picard.PicardGroup (schemeRingedSite X).O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf (schemeRingedSite X).O).2) :=
  Stacks.SheafOfModules.Picard.instAddCommGroupPicardGroup (schemeRingedSite X).O.obj
    (Stacks.SheafOfModules.Tensor.ringSheaf (schemeRingedSite X).O).2

/-- **Stacks Project, Tag 03P8, the Zariski identification.** For any scheme `X` there is a
canonical isomorphism of abelian groups `H¹_{Zar}(X, 𝐆_m) = Pic(X)`. -/
@[stacks 03P8 "the identification H¹_Zar(X, 𝐆_m) = Pic(X); the four comparisons of H¹_fppf, \
H¹_syntomic, H¹_smooth and H¹_étale with H¹_Zar are not covered"]
def zariskiH1UnitsAddEquivPicardGroup :
    Sheaf.H (Stacks.Cohomology.Torsors.Generators.unitsAddSheaf (schemeRingedSite X)) 1 ≃+
      Stacks.SheafOfModules.Picard.PicardGroup (schemeRingedSite X).O.obj
        (Stacks.SheafOfModules.Tensor.ringSheaf (schemeRingedSite X).O).2 :=
  Stacks.Cohomology.Torsors.Generators.h1UnitsAddEquivPicardGroup (schemeRingedSite X)
    (schemeRingedSite_isLocallyRinged X)

/-- **Stacks Project, Tag 03P8, the Zariski identification is the canonical one.** Its inverse
sends the class of an invertible module to the first cohomology class of its torsor of local
generators. -/
@[stacks 03P8 "the Zariski identification is the canonical one, normalized on line bundles"]
theorem zariskiH1UnitsAddEquivPicardGroup_symm_classOf
    (L : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (schemeRingedSite X).O))
    (hL : Stacks.SheafOfModules.IsInvertible (schemeRingedSite X).O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf (schemeRingedSite X).O).2 L) :
    (zariskiH1UnitsAddEquivPicardGroup X).symm
        (Stacks.SheafOfModules.Picard.classOf (schemeRingedSite X).O.obj
          (Stacks.SheafOfModules.Tensor.ringSheaf (schemeRingedSite X).O).2 L hL) =
      Stacks.Cohomology.Torsors.torsorIsoClassesEquivH1
        (Stacks.Cohomology.Torsors.Generators.unitsAddSheaf (schemeRingedSite X))
        (Quotient.mk (Stacks.Cohomology.Torsors.torsorSetoid
            (Stacks.Cohomology.Torsors.Generators.unitsAddSheaf (schemeRingedSite X)))
          (Stacks.Cohomology.Torsors.Generators.generatorTorsor (schemeRingedSite X)
            (schemeRingedSite_isLocallyRinged X) L hL).torsor) :=
  Stacks.Cohomology.Torsors.Generators.h1UnitsAddEquivPicardGroup_symm_classOf
    (schemeRingedSite X) (schemeRingedSite_isLocallyRinged X) L hL

end Stacks.Picard.ZariskiSite

/-! ### The identification of the Picard group with the cohomology of the units of the space

The last identification of Tag 03P8, `Pic(X) = H¹(X, 𝒪_X^*)`, is the identification of Tag 09NU
over the Picard group of a scheme, which the library already carries. The tag is recorded on it
here. -/

add_to_stacks 03P8 "the identification Pic(X) = H¹(X, 𝒪_X^*)"
  Stacks.Picard.FirstCohomology.h1UnitsAddEquivPicard

add_to_stacks 03P8 "the identification Pic(X) = H¹(X, 𝒪_X^*) is the canonical one"
  Stacks.Picard.FirstCohomology.h1UnitsAddEquivPicard_symm_classOf

end
