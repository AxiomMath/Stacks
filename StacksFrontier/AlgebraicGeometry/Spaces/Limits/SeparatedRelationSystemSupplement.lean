module

public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.SeparatedRelationSystem
public import StacksFrontier.AlgebraicGeometry.Spaces.ApproximationChartsBounded
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.AffineChartSystemSizeBound
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.StagesReindex
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.AffineDiagonal
import all StacksFrontier.AlgebraicGeometry.Spaces.Limits.SeparatedRelationSystem
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.LimitSituationChartsBounded
public import StacksFrontier.AlgebraicGeometry.Spaces.Points
public import StacksFrontier.Topology.Dimension.KrullSupplement

/-!
# Size-bounded chart systems of a limit situation

`AlgebraicGeometry.Space.LimitSituation.ChartsBounded` is the condition that every system of
affine charts of the inverse system of a limit situation is size-bounded; it holds when the index
type is smaller than the cofinality of the site's size cutoff, and it gives a limit bridge for the
system of affine charts at the chosen stage
(`AlgebraicGeometry.Space.LimitSituation.chartLimitBridgeOfChartsBounded`).
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Cardinal Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (hZ : B.Contains (⊤_ Scheme.{u}))

namespace LimitSituation

variable {B S hS hZ} {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (A : LimitSituation B S hS hZ X)

variable (V : BigAffineFppf B S hS)
    (g : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj V) ⟶ A.system.obj (op A.base))

end LimitSituation

end AlgebraicGeometry.Space

end

universe u

@[expose] public section

open CategoryTheory CategoryTheory.Limits Cardinal Opposite


namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (hZ : B.Contains (⊤_ Scheme.{u}))

namespace LimitSituation

variable {B S hS hZ} {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (A : LimitSituation B S hS hZ X)

variable (V : BigAffineFppf B S hS)
    (g : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj V) ⟶ A.system.obj (op A.base))

/-- **The size bound the chart systems of a limit situation need**, namely
`AlgebraicGeometry.Space.ChartsBounded` for the situation's own inverse system: every system
of affine charts of it is size-bounded.

The condition on the morphisms of the index category that
`AlgebraicGeometry.Space.chartsBounded_of_lt_cof_ord` asks for is automatic here, the index
category of a limit situation being a preorder and hence thin
(`AlgebraicGeometry.Space.LimitSituation.mk_hom_lt_aleph0`), and the condition on the index
set itself has two possible sources: that same declaration from `#A.I < B.cutoff.ord.cof`, and
`AlgebraicGeometry.Space.chartsBounded_of_size_le` from `#A.I < B.cutoff` together with a
uniform bound on the charts of each system. -/
abbrev ChartsBounded : Prop := Space.ChartsBounded B S hS A.system

/-- A limit situation indexed by a type smaller than the cofinality of the site's size cutoff
has size-bounded chart systems, the index category being thin. -/
theorem ChartsBounded.of_lt_cof_ord (hI : #A.I < B.cutoff.ord.cof) : A.ChartsBounded :=
  Space.chartsBounded_of_lt_cof_ord B S hS A.system (A.mk_op ▸ hI)
    fun i j => (A.mk_hom_lt_aleph0 i j).trans B.aleph0_lt_cutoff_cof

/-- **The limit of the system of affine charts of a limit situation at its chosen stage**, as a
limit bridge: a limit cone in the site whose underlying schemes form a limit cone too.

This is `AlgebraicGeometry.Space.AffineChartSystem.limitBridgeOfSizeBound` (Stacks 07SF), whose
size hypothesis is `AlgebraicGeometry.Space.LimitSituation.ChartsBounded` here. -/
noncomputable def chartLimitBridgeOfChartsBounded (hI : A.ChartsBounded) :
    AffineChartSystem.LimitBridge (A.chartSystem V g) :=
  AffineChartSystem.limitBridgeOfSizeBound (A.chartSystem V g) (hI.sizeBound (A.chartSystem V g))

end LimitSituation

end AlgebraicGeometry.Space

end

