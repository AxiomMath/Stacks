module
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Sites
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmallEtaleProjection
import all StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmallEtaleProjection

public import Mathlib.CategoryTheory.Functor.Flat
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.LeftKanExtensionExactness
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Limits
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmallToBigTopos
public import StacksFrontier.CategoryTheory.Sites.Continuous
public import StacksFrontier.CategoryTheory.Sites.MorphismOfSites.MorphismDefs
public import StacksFrontier.CategoryTheory.Sites.MorphismOfSitesLimits
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Continuity of the inclusion of the small étale site

The full inclusion of the small étale site of a scheme `S` into the big étale site over `S` is
a continuous functor for the étale topologies.

This file holds stronger forms of declarations of
`StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmallEtaleProjection`, stated as separate
declarations beside the ones there: over more general coefficient universes, or with inputs that
are carried there as hypotheses discharged, together with the new results built on them.

## Main results

* `AlgebraicGeometry.smallEtaleInclusion_isContinuous_unconditional`: the inclusion
  `SmallEtale.inclusion B S hS` is continuous.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable (B : AlgebraicGeometry.BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The full inclusion of the small étale site into the big étale slice is continuous: it is
a morphism of sites. -/
@[sga "4 VII 4.0" "partial"]
public instance smallEtaleInclusion_isContinuous_unconditional :
    (SmallEtale.inclusion B S hS).IsContinuous
      (SmallEtale.topology B S hS) (BigEtaleOver.topology B S hS) :=
  (smallEtaleInclusion_isMorphismOfSites B S hS).toIsContinuous

end AlgebraicGeometry
