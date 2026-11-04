module

public import
  StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.AffineColimitPresentations
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentLocality

/-!
# Arbitrary direct sums of quasi-coherent modules on a site

Quasi-coherence of a sheaf of modules is a local condition, but the covering it produces depends
on the module, so closure under *arbitrary* direct sums does not follow from the definition: an
infinite family supplies infinitely many coverings, and a Grothendieck topology is not closed
under infinite intersections of covering sieves.  What repairs this is a single family of objects
covering the final object on whose members *every* summand is already globally presented; on such
a family the direct sum is globally presented too, because a coproduct of globally presented
modules is globally presented (`SheafOfModules.HasGlobalPresentation.of_isColimit_cofan`, which
assumes nothing), and quasi-coherence of the direct sum then follows from the clause of
Stacks 03DN for quasi-coherence.

This is the same reduction as `Stacks.SheafOfModules.isQuasicoherentOnSite_of_isColimit`, which
packages the covering family as a `Stacks.SheafOfModules.PresentingCover`; the difference is the
universes.  `Stacks.SheafOfModules.PresentingCover` ties the universe of the module sections to
the universe of the coefficient rings, and the construction of the largest quasi-coherent
submodule, Stacks 04CK, needs the sections in a universe containing the site while the structure
sheaf of the site stays where it is.  The statements below only ask that the universe of the
sections contain the site, which is the hypothesis every global presentation carries anyway.

## Main results

* `Stacks.SheafOfModules.hasGlobalPresentation_over_of_isColimit_cofan`: **a direct sum of
  sheaves of modules which are globally presented on an object is globally presented on that
  object.**
* `Stacks.SheafOfModules.isQuasicoherentOnSite_of_coversTop_isColimit_cofan`: **a direct sum of
  sheaves of modules which are globally presented on each member of a family covering the final
  object is quasi-coherent.**

## Implementation notes

The direct sum is given by a cofan and the assertion that it is a colimit, so no cocompleteness
instance is assumed; the index type lies in the universe `max u v r m` in which global
presentations are indexed, with `u` and `v` the universes of the objects and the morphisms of the
site, `r` that of the coefficient rings and `m` a free parameter.  That is also the universe of
the sections, because `SheafOfModules.HasGlobalPresentation.of_isColimit_cofan` reads a
presentation of a coproduct off presentations of the summands by raising the universe of the
sections, which preserves colimits only when the enlarged universe contains the coefficient
rings.

Restriction to the slice site at a member carries the cofan to a cofan, by
`Stacks.SheafOfModules.overFunctor_preservesColimits`; the two sheafification data that
`SheafOfModules.HasGlobalPresentation.of_isColimit_cofan` consumes on the slice hold with no
hypothesis, since the universe of the sections contains the slice site.

## References

* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03DE](https://stacks.math.columbia.edu/tag/03DE)
* [Stacks Project, Tag 03DN](https://stacks.math.columbia.edu/tag/03DN)
* [Stacks Project, Tag 0GNB](https://stacks.math.columbia.edu/tag/0GNB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v r m

namespace Stacks.SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{r}}

/-- A direct sum of sheaves of modules each of which has a global presentation after restriction
to an object `W` of the site has a global presentation after restriction to `W`.

Restriction to the slice site at `W` preserves colimits, so the restricted cofan is again a
colimit, and a coproduct of globally presented modules is globally presented by
`SheafOfModules.HasGlobalPresentation.of_isColimit_cofan`.  This is the local step of the
direct-sum clause of Stacks 0GNB(3). -/
theorem hasGlobalPresentation_over_of_isColimit_cofan (W : C)
    {Jdx : Type (max u v r m)} {Mj : Jdx → _root_.SheafOfModules.{max u v r m} R}
    {c : Cofan Mj} (hc : IsColimit c)
    (hP : ∀ j, ((Mj j).over W).HasGlobalPresentation) :
    (c.pt.over W).HasGlobalPresentation := by
  have hs : HasSheafify (J.over W) AddCommGrpCat.{max u v r m} :=
    GrothendieckTopology.hasSheafify_addCommGrpCat.{max u v r m, v, max u v} (J.over W)
  have hw : (J.over W).WEqualsLocallyBijective AddCommGrpCat.{max u v r m} :=
    AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_addCommGrpCat.{max u v r m,
      max u v, v} (J.over W)
  have hpc : PreservesColimitsOfSize.{max u v r m, max u v r m}
      (_root_.SheafOfModules.overFunctor.{max u v r m} R W) :=
    overFunctor_preservesColimits.{u, v, r, m} R W
  exact _root_.SheafOfModules.HasGlobalPresentation.of_isColimit_cofan.{max u v, v, r,
    max u v r m} ((Cofan.isColimitMapCoconeEquiv _ Mj c) (isColimitOfPreserves _ hc)) hP

/-- **A direct sum of sheaves of modules which are globally presented on each member of a family
covering the final object is quasi-coherent.**

This is the direct-sum clause of Stacks 0GNB(3) reduced to its affine input: what has to be
supplied is one family covering the final object on whose members every quasi-coherent module is
globally presented, and the clause of Stacks 03DN for quasi-coherence does the rest.  The
universe of the module sections is independent of the universe of the coefficient rings. -/
theorem isQuasicoherentOnSite_of_coversTop_isColimit_cofan
    {I : Type u} {W : I → C} (hW : J.CoversTop W)
    {Jdx : Type (max u v r m)} {Mj : Jdx → _root_.SheafOfModules.{max u v r m} R}
    {c : Cofan Mj} (hc : IsColimit c)
    (hP : ∀ (i : I) (j : Jdx), ((Mj j).over (W i)).HasGlobalPresentation) :
    c.pt.IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_of_coversTop_hasGlobalPresentation c.pt hW
    fun i ↦ hasGlobalPresentation_over_of_isColimit_cofan.{u, v, r, m} (W i) hc (hP i)

end Stacks.SheafOfModules

end
