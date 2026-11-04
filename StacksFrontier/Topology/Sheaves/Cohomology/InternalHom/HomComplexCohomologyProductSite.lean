module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.CompositionCohomologyProduct
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.HomComplexCohomologyProduct

/-!
# The composition product of a ringed space is the one of its ringed site

`StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.HomComplexCohomologyProduct` builds the
composition product on the cohomology sheaves of an internal Hom complex for a ringed *space*,
and `StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.CompositionCohomologyProduct` builds
it for a ringed *site*. This file records that the first is the second, read along
`Stacks.SheafOfModules.ringedSite`: every identification below is `rfl`.

That is not a formality. The graded algebra of the cohomology sheaves of `SheafHom^•(P, P)` is
the object whose restriction to the members of a cover the local-to-global step of
[Stacks, Tag 0BQY] (`SheafOfModules.GradedAlgebra.IsExteriorAlgebra.isIso_desc_app_of_coversTop`)
has to recognise, and the restriction of a sheaf of modules on a space to a member of a cover is
a sheaf of modules on a **slice site**, which is a ringed site and not a ringed space. So the
side of the comparison that the gluing primitive produces can only be spoken of at the site-level
generality, while the side the Koszul development produces is spelled on a space; these lemmas
are what lets a statement about one be used as a statement about the other.

## Main results

* `Stacks.SheafOfModules.homologyComposition_eq_ringedSite`,
  `Stacks.SheafOfModules.homologyMul_eq_ringedSite`,
  `Stacks.SheafOfModules.homologyOne_eq_ringedSite` and
  `Stacks.SheafOfModules.homologyGradedAlgebra_eq_ringedSite`: the space-level composition
  pairing, its bilinear form on local sections, its unit and the graded algebra they assemble into
  are the ringed-site ones at `Stacks.SheafOfModules.ringedSite`.

## Implementation notes

The two developments are stated over different spellings of the same sheaf of rings —
`Stacks.SheafOfModules.structureSheaf Rc` on the space and
`AlgebraicGeometry.RingedSite.ringSheaf (ringedSite Rc)` on the site — and over two different
named local instances carrying the same monoidal structure on `Mod(O_X)`. Both pairs are
definitionally equal and neither is syntactically equal, which is why the statements below have
to be made at all rather than being invisible: a `rw` whose motive passes through a plain
definition is checked at `implicit` transparency, and there the two spellings are two terms.

## References

* [Stacks Project, Tag 0A91](https://stacks.math.columbia.edu/tag/0A91)
* [Stacks Project, Tag 0BQY](https://stacks.math.columbia.edu/tag/0BQY)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory Category Limits TopologicalSpace Opposite
open AlgebraicGeometry

universe u

namespace Stacks.SheafOfModules

attribute [local instance] SheafOfModules.monoidalCategorySheafTensor
  SheafOfModules.symmetricCategorySheafTensor SheafOfModules.monoidalPreadditiveSheafTensor
  SheafOfModules.monoidalClosedSheafTensor
  SheafOfModules.preservesColimit_tensorRight_sheafTensor
  Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorObjAdditive monoidalSpace' symmetricSpace'
  monoidalPreadditiveSpace' monoidalClosedSpace' preservesColimitTensorRightSpace'
  preservesFiniteColimitsTensorRight' preservesFiniteColimitsTensorLeft'

attribute [local instance] RingedSite.ringSheafSectionsCommRing
  RingedSite.presheafOfModulesMonoidalCategory
  RingedSite.curriedTensorPreservesZeroMorphisms
  RingedSite.curriedTensorObjPreservesZeroMorphisms

variable {X : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} X)
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The composition morphism read on the total tensor product, on a space, is the one on its
ringed site. -/
theorem compositionTotalMap_eq_ringedSite
    (K L M : CochainComplex (StructureSheafModules Rc) ℤ) :
    compositionTotalMap Rc K L M = RingedSite.compositionTotalMap (ringedSite Rc) K L M :=
  rfl

/-- **The composition pairing on cohomology sheaves of a ringed space is the one of its ringed
site.** -/
theorem homologyComposition_eq_ringedSite
    (K L M : CochainComplex (StructureSheafModules Rc) ℤ) (i j : ℤ) :
    homologyComposition Rc K L M i j =
      RingedSite.homologyComposition (ringedSite Rc) K L M i j :=
  rfl

/-- **The composition pairing as a bilinear map on local sections is the ringed-site one.** -/
theorem homologyMul_eq_ringedSite (K L M : CochainComplex (StructureSheafModules Rc) ℤ)
    (i j : ℤ) :
    homologyMul Rc K L M i j = RingedSite.homologyMul (ringedSite Rc) K L M i j :=
  rfl

/-- The cycle-level composition pairing is the ringed-site one. -/
theorem cycleComposition_eq_ringedSite (K L M : CochainComplex (StructureSheafModules Rc) ℤ)
    (i j : ℤ) :
    cycleComposition Rc K L M i j = RingedSite.cycleComposition (ringedSite Rc) K L M i j :=
  rfl

/-- **The unit of the composition product is the ringed-site one.** -/
theorem homologyOne_eq_ringedSite (P : CochainComplex (StructureSheafModules Rc) ℤ) :
    homologyOne Rc P = RingedSite.homologyOne (ringedSite Rc) P :=
  rfl

/-- **The graded algebra on the cohomology sheaves of `SheafHom(P, P)` over a ringed space is the
graded algebra of its ringed site.** This is the identification the local-to-global step of
Stacks 0BQY needs: the gluing primitive speaks of the restriction of a sheaf of graded algebras
to a slice site, and a slice site is a ringed site. -/
theorem homologyGradedAlgebra_eq_ringedSite
    (P : CochainComplex (StructureSheafModules Rc) ℤ) :
    homologyGradedAlgebra Rc P = RingedSite.homologyGradedAlgebra (ringedSite Rc) P :=
  rfl

end Stacks.SheafOfModules

end
