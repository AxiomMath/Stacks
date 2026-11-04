module
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.AffineEtaleSites
import all StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.AffineEtaleSites.BaseChange

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Connected
public import Mathlib.CategoryTheory.Sites.DenseSubsite.SheafEquiv
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PointsOtherTopologies.SmallEtale
public import StacksFrontier.AlgebraicGeometry.LimitDescent.Faithfulness
public import StacksFrontier.AlgebraicGeometry.LimitDescentFull.Fullness
public import StacksFrontier.AlgebraicGeometry.LimitDescentGlueing.GeneralStages
public import StacksFrontier.AlgebraicGeometry.LimitDescentGlueing.Glueing
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Etale
public import StacksFrontier.AlgebraicGeometry.Size.FiniteType
public import StacksFrontier.AlgebraicGeometry.Topologies.AffineRefinement
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.BigSiteCoverings
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Limits
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Sites
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmallEtaleBaseChange
public import StacksFrontier.CategoryTheory.Sites.InverseSystem.ColimitsOfSites
public import StacksFrontier.CategoryTheory.Sites.Topos.ToposMorphismComp
-- Not a `public import`: the survivor is named only inside a private proof below.
import StacksFrontier.AlgebraicGeometry.Limits.Descending.ConstructibleImage

/-!
# AffineEtaleSitesUnconditional

Stronger forms of declarations of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.AffineEtaleSites`, stated as separate
declarations beside the ones there: over more general coefficient universes, or with inputs that
are carried there as hypotheses discharged, together with the new results built on them.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace Stacks.EtaleCohomology

open AlgebraicGeometry

attribute [local instance] AlgebraicGeometry.Etale.isStableUnderComposition

variable {I : Type v} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
  (D : Iᵒᵖ ⥤ Scheme.{max u v}) (c : Cone D)
  (B : AlgebraicGeometry.BigEtaleSite.{max u v})
  (hD : ∀ i, B.Contains (D.obj i)) (hX : B.Contains c.pt)

attribute [local simp] Scheme.Hom.resLE_comp_resLE

attribute [local instance] limitOpensDiagramι_isOpenImmersion limitOpensDiagram_isAffineHom
  CategoryTheory.isConnected_of_hasTerminal

universe u₁ v₁ u₂ v₂ w₁

section Models


variable [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]

end Models

section Construction

variable (hc : IsLimit c)
  [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]

end Construction

end Stacks.EtaleCohomology

end
