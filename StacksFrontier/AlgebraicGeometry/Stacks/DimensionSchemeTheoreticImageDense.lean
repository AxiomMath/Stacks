module

public import StacksFrontier.AlgebraicGeometry.Stacks.ConstancyOfStackDimension
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.Topology.JacobsonSpace
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteType.UniversallyCatenary
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.NowhereDenseFibres.Topology
public import StacksFrontier.AlgebraicGeometry.Properties.SchemeTypesAndCatenary.Catenary
public import StacksFrontier.AlgebraicGeometry.Stacks.Criteria.ConstancyOfDimension
public import StacksFrontier.AlgebraicGeometry.Stacks.DimensionAtFiniteTypePoint
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDimensionFiniteness
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDimensionStackLocalConstancy
public import StacksFrontier.RingTheory.JacobsonPuncturedSpectrum.Basic
public import StacksFrontier.Topology.Dimension.CatenaryAdditive
public import StacksFrontier.Topology.Dimension.ClosedSubsetDimension
public import StacksFrontier.Topology.Dimension.CodimensionOpen
public import StacksFrontier.Topology.Dimension.Krull
public import StacksFrontier.Topology.Dimension.LocalKrullDim
public import StacksFrontier.AlgebraicGeometry.Stacks.DimensionSchemeTheoreticImage

/-!
# The generic equality of Stacks 0DS4 on a dense open

Stacks 0DS4 asserts its generic equality `dim(𝒯) = dim(𝒵) + dim_t(𝒯_{f(t)})` on a "non-empty
(equivalently, dense)" open subset of the irreducible space `|𝒯|`. This file records that
equivalence: a nonempty open subset of an irreducible space of points is dense. It then states
the generic equality with its locus asserted to be dense as well as nonempty, from the form of
`AlgebraicGeometry.Stack.exists_isOpen_dimension_eq_add_relativeStackDimensionAt` in which the
constancy of Stacks 0DRX is discharged by
`AlgebraicGeometry.Stack.isConstant_dimensionAtPoint_of_irreducibleSpace`.

## Main results

* `AlgebraicGeometry.Stack.dense_of_isOpen_of_nonempty_points`: a nonempty open subset of `|𝒲|`
  is dense when `|𝒲|` is irreducible.
* `AlgebraicGeometry.Stack.exists_isOpen_dense_dimension_eq_add_relativeStackDimensionAt`: the
  generic equality of Stacks 0DS4 on a dense open, from its pointwise form.

## References

* [Stacks Project, Tag 0DS4](https://stacks.math.columbia.edu/tag/0DS4)
* [Stacks Project, Tag 0DRX](https://stacks.math.columbia.edu/tag/0DRX)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A nonempty open subset of `|𝒲|` is dense as soon as `|𝒲|` is irreducible.

This is the parenthesis "non-empty (equivalently, dense)" of Stacks 0DS4: the source asserts its
generic equality on a nonempty open subset of the irreducible `|𝒯|` and records that such a
subset is automatically dense, so the two readings of its conclusion agree. Unlike the two
statements above, this needs no hypothesis beyond irreducibility. -/
theorem dense_of_isOpen_of_nonempty_points (𝒲 : AlgebraicStacks.{u, w} B S hS)
    (h𝒲Irreducible : @IrreducibleSpace _ (pointTopology B S hS 𝒲.val))
    {V : Set (points B S hS 𝒲.val.val 𝒲.val.property)}
    (hVopen : @IsOpen _ (pointTopology B S hS 𝒲.val) V) (hVne : V.Nonempty) :
    @Dense _ (pointTopology B S hS 𝒲.val) V :=
  let := pointTopology B S hS 𝒲.val
  hVopen.dense hVne

variable (𝒯 𝒳 : AlgebraicStacks.{u, w} B S hS) (f : 𝒯 ⟶ 𝒳)
  (h𝒯 : IsLocallyNoetherianStack.{u, w} B S hS 𝒯)
  (h𝒳 : IsLocallyNoetherianStack.{u, w} B S hS 𝒳)
  (P : ObjectProperty 𝒳.val.val.obj) (hP : IsSchemeTheoreticImage f P)
  (hA : IsAlgebraicStack.{u, w} B S hS (fullSubcategoryBased 𝒳 P))
  (relativeDimension : points B S hS 𝒯.val.val 𝒯.val.property → EInt)

/-- The generic equality of Stacks 0DS4 with its locus asserted to be dense as well as nonempty,
which on the irreducible `|𝒯|` is the same assertion by
`AlgebraicGeometry.Stack.dense_of_isOpen_of_nonempty_points`.

As for `AlgebraicGeometry.Stack.exists_isOpen_dimension_eq_add_relativeStackDimensionAt`, the
pointwise equality is a hypothesis, so no `@[stacks 0DS4]` attribute is attached. -/
theorem exists_isOpen_dense_dimension_eq_add_relativeStackDimensionAt
    (hf : AlgebraicStacks.IsLocallyOfFiniteType B S hS f)
    (h𝒯Jacobson : AlgebraicStacks.IsJacobson B S hS 𝒯)
    (h𝒳Jacobson : AlgebraicStacks.IsJacobson B S hS 𝒳)
    (h𝒯Catenary : AlgebraicStacks.IsPseudoCatenary B S hS 𝒯)
    (h𝒳Catenary : AlgebraicStacks.IsPseudoCatenary B S hS 𝒳)
    (h𝒯Irreducible : @IrreducibleSpace _ (pointTopology B S hS 𝒯.val))
    (h𝒳QuasiSeparated : IsQuasiSeparatedAbs.{u, w, w} B S hS 𝒳)
    (hpointwise : ∃ V : Set (points B S hS 𝒯.val.val 𝒯.val.property),
      @IsOpen _ (pointTopology B S hS 𝒯.val) V ∧ V.Nonempty ∧
        ∀ t ∈ V, dimensionAtPoint B S hS 𝒯 h𝒯 t =
          closedSubstackDimension B S hS 𝒳 P hP.1 hA h𝒳 +
            relativeStackDimensionAt B S hS f hf h𝒯 h𝒳 t) :
    ∃ V : Set (points B S hS 𝒯.val.val 𝒯.val.property),
      @IsOpen _ (pointTopology B S hS 𝒯.val) V ∧ V.Nonempty ∧
        @Dense _ (pointTopology B S hS 𝒯.val) V ∧
        ∀ t ∈ V, dimension B S hS 𝒯 h𝒯 =
          closedSubstackDimension B S hS 𝒳 P hP.1 hA h𝒳 +
            relativeStackDimensionAt B S hS f hf h𝒯 h𝒳 t := by
  obtain ⟨V, hVopen, hVne, hVeq⟩ := exists_isOpen_dimension_eq_add_relativeStackDimensionAt
    B S hS 𝒯 𝒳 f h𝒯 h𝒳 P hP hA hf h𝒯Jacobson h𝒳Jacobson h𝒯Catenary h𝒳Catenary h𝒯Irreducible
    h𝒳QuasiSeparated
    (isConstant_dimensionAtPoint_of_irreducibleSpace.{u, w} B S hS 𝒯 h𝒯 h𝒯Jacobson h𝒯Catenary
      h𝒯Irreducible) hpointwise
  exact ⟨V, hVopen, hVne,
    dense_of_isOpen_of_nonempty_points B S hS 𝒯 h𝒯Irreducible hVopen hVne, hVeq⟩

end AlgebraicGeometry.Stack

end
