module
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ComparingBigSmall.Restriction
import all StacksFrontier.AlgebraicGeometry.EtaleCohomology.ComparingBigSmall.Restriction

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Abelian.Injective.Basic
public import Mathlib.CategoryTheory.Limits.Constructions.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Constructions.Equalizers
public import Mathlib.CategoryTheory.Sites.Abelian
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjective
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Limits
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Precoverage
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.PrecoverageUnconditional
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmallEtaleProjection
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmallEtaleProjectionUnconditional
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmallToBigTopos
public import StacksFrontier.CategoryTheory.Preadditive.Injective.Adjunction
public import StacksFrontier.CategoryTheory.Sites.Cocontinuous.LowerShriekExactness
public import StacksFrontier.CategoryTheory.Sites.AbelianSheafificationExistence

/-!
# RestrictionUnconditional

Stronger forms of declarations of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.ComparingBigSmall.Restriction`, stated as separate
declarations beside the ones there: over more general coefficient universes, or with inputs that
are carried there as hypotheses discharged, together with the new results built on them.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u})

end AlgebraicGeometry
