module

public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.SheafOfModules
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import StacksFrontier.AlgebraicGeometry.LeraySectionsCollapse.Leray
public import StacksFrontier.Topology.Sheaves.Cohomology.Locality.CohomologyVanishesLocally
public import StacksFrontier.Topology.Sheaves.Functors.Module.RingedSpace

/-!
# Vanishing higher direct images

For a morphism of ringed spaces `f : X ⟶ Y`, a sheaf of `O_X`-modules `F` whose positive
higher direct images `R^q f_* F` all vanish has the same cohomology as its direct image:
`H^p(X, F) ≅ H^p(Y, f_* F)` in every degree `p`.  This is part (1) of [Stacks, Tag 01F4], and
it is proved — with the isomorphism named rather than merely asserted to exist — by
`Stacks.LeraySections.cohomologyIsoOfVanishingHigherDirectImages`, which carries the tag.

## Main results

* `cohomology_iso_pushforward_of_isZero_rightDerived` — the same statement with the isomorphism
  wrapped in `Nonempty`.

## Implementation notes

Cohomology is expressed by `Hgroup` of Tag 01E3, the right derived functors of sections on the
top open.  Higher direct images use the canonical module pushforward
`RingedSpaceModuleAdjunction.modulePushforward` attached to a morphism of ringed spaces.

The conclusion is `Nonempty (· ≅ ·)`, asserting that an isomorphism exists rather than naming
one.  That is the shape the statements depending on it use, and it is kept so that they apply
it directly.  It is strictly weaker than the source, which gives a
canonical comparison, so it is a one-line corollary of the named isomorphism and not a second
development of the same mathematics.

## References

* [Stacks Project, Tag 01F4](https://stacks.math.columbia.edu/tag/01F4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry

universe u

namespace Stacks.Cohomology.VanishingDirectImages

/-- **Part (1) of [Stacks, Tag 01F4], as a bare existence statement.**  If every positive higher
direct image of a sheaf of modules along a morphism of ringed spaces vanishes, then the
cohomology of the sheaf is isomorphic to the cohomology of its direct image in every degree.

Which isomorphism this is, the source says and this statement does not: it is
`Stacks.LeraySections.cohomologyIsoOfVanishingHigherDirectImages`, the one assembled from the
uniqueness isomorphism of right derived functors and the unit of `R f_*`.  A faithfulness review
of the tag should read this `Nonempty` as weaker than the source and look there. -/
theorem cohomology_iso_pushforward_of_isZero_rightDerived
    {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    (F : SheafOfModules.{u} (structureSheafRing X))
    (hF : ∀ q > 0,
      IsZero (((RingedSpaceModuleAdjunction.modulePushforward f).rightDerived q).obj F))
    (p : ℕ) :
    Nonempty
      (Hgroup (structureSheafRing X) ⊤ p F ≅
        Hgroup (structureSheafRing Y) ⊤ p
          ((RingedSpaceModuleAdjunction.modulePushforward f).obj F)) :=
  ⟨Stacks.LeraySections.cohomologyIsoOfVanishingHigherDirectImages f hF p⟩

end Stacks.Cohomology.VanishingDirectImages
