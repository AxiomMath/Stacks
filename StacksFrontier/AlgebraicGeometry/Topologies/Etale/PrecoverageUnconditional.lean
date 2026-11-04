module
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleAffineRefinement
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Precoverage
import all StacksFrontier.AlgebraicGeometry.Topologies.Etale.Precoverage

public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Limits
public import StacksFrontier.CategoryTheory.Sites.Localization.PushforwardAdjunction

/-!
# PrecoverageUnconditional

Stronger forms of declarations of `StacksFrontier.AlgebraicGeometry.Topologies.Etale.Precoverage`,
stated as separate declarations beside the ones there: over more general coefficient universes, or
with inputs that are carried there as hypotheses discharged, together with the new results built on
them.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

attribute [instance] AlgebraicGeometry.Scheme.etalePrecoverage_isStableUnderComposition

namespace AlgebraicGeometry

end AlgebraicGeometry
