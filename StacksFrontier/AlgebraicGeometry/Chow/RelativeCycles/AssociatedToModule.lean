module

public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Fibre
public import StacksFrontier.AlgebraicGeometry.Chow.CoherentCycle.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.CoherentSupportDimension
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.ModuleFamily
public import StacksFrontier.AlgebraicGeometry.Chow.Setup.JacobsonDimension
public import StacksFrontier.AlgebraicGeometry.CoherentOfFiniteType
public import StacksFrontier.AlgebraicGeometry.Modules.FiniteTypePullbackScheme
public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentPullbackScheme

/-!
# The family of cycles associated to a module

Let `f : X ⟶ S` be a morphism of schemes locally of finite type and let `F` be a quasi-coherent
`𝒪_X`-module of finite type whose support on every scheme-theoretic fibre of `f` has dimension at
most `r`. The pullback of `F` to a fibre `X_s` is coherent, because `X_s` is locally Noetherian
over the residue field `κ(s)`, and the dimension bound on its support is exactly the bound that
lets the associated cycle `[F_s]_r` of that coherent module be formed. The resulting choice of an
`r`-cycle on every fibre is a family of `r`-cycles on the fibres of `f`.

The family is `Stacks.Chow.familyAssociatedToModule`. This module adds the comparison of the
relative dimension of a point with the topological dimension of a closed subset containing it.

## Main results

* `Stacks.Chow.relativeDimension_le_of_topologicalKrullDim_le` — a point of a closed subset of
  topological dimension at most `r` has relative dimension at most `r`.

## Implementation notes

The dimension hypothesis is stated as a bound on `topologicalKrullDim` of the support, a subset
of the fibre, while the associated cycle of a coherent module asks for a bound on the
delta-dimension of the reduced closed subscheme carried by that support. Over `Spec κ(s)` the
dimension function vanishes, so the delta-dimension of an integral closed subscheme is its
topological dimension; passing between the two is
`Stacks.Chow.topologicalKrullDim_eq_relativeDimension_toNat` applied to the reduced structure on
the closure of a point, and the bound then transfers to the delta-dimension of the whole support
by `Stacks.Chow.schemeDeltaDimension_reducedSupport_le`. Because the dimension of the empty space
is `⊥`, the empty support is covered with no separate argument.

## References

* [Stacks Project, Tag 0H4Q](https://stacks.math.columbia.edu/tag/0H4Q)
* [Stacks Project, Tag 0H4U](https://stacks.math.columbia.edu/tag/0H4U)
* [Stacks Project, Tag 01XZ](https://stacks.math.columbia.edu/tag/01XZ)
* [Stacks Project, Tag 02QO](https://stacks.math.columbia.edu/tag/02QO)
* [Stacks Project, Tag 02QX](https://stacks.math.columbia.edu/tag/02QX)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

variable {X S : Scheme.{u}}

/-! ### Topological dimension and relative dimension -/

/-- A point of a closed subset of topological dimension at most `r` has relative dimension at
most `r`, provided the dimension function of the base vanishes at closed points. -/
theorem relativeDimension_le_of_topologicalKrullDim_le (C : ChowSituation.{u}) [JacobsonSpace C.S]
    (hδ : ∀ t : C.S, IsClosed ({t} : Set C.S) → C.dimensionFunction t = 0) {Y : Scheme.{u}}
    (g : Y ⟶ C.S) [LocallyOfFiniteType g] {T : Set Y} (hT : IsClosed T) {r : ℕ}
    (hdim : topologicalKrullDim T ≤ (r : WithBot ℕ∞)) {x : Y} (hx : x ∈ T) :
    relativeDimension C.dimensionFunction g x ≤ (r : ℤ) := by
  have := isIntegral_integralComponentAt x
  have hgen : IsGenericPoint (genericPoint (integralComponentAt x).subscheme)
      (Set.univ : Set (integralComponentAt x).subscheme) :=
    (IrreducibleSpace.isIrreducible_univ _).isGenericPoint_genericPoint isClosed_univ
  have hmem : ∀ z : (integralComponentAt x).subscheme,
      (integralComponentAt x).subschemeι.base z ∈ T := by
    intro z
    have hz : (integralComponentAt x).subschemeι.base z ∈
        Set.range (integralComponentAt x).subschemeι.base := ⟨z, rfl⟩
    rw [Scheme.IdealSheafData.range_subschemeι, coe_support_integralComponentAt] at hz
    exact hT.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hx) hz
  have hind : Topology.IsInducing
      (Set.codRestrict (integralComponentAt x).subschemeι.base T hmem) :=
    (integralComponentAt x).subschemeι.isClosedEmbedding.isEmbedding.isInducing.codRestrict hmem
  have hle : topologicalKrullDim (integralComponentAt x).subscheme ≤ (r : WithBot ℕ∞) :=
    hind.topologicalKrullDim_le.trans hdim
  rw [topologicalKrullDim_eq_relativeDimension_toNat C hδ g (integralComponentAt x).subschemeι
      (genericPoint (integralComponentAt x).subscheme) hgen,
    show (integralComponentAt x).subschemeι.base (genericPoint (integralComponentAt x).subscheme)
      = genericPointOf (integralComponentAt x) (isIntegral_integralComponentAt x) from rfl,
    genericPointOf_integralComponentAt x] at hle
  have hnat : (relativeDimension C.dimensionFunction g x).toNat ≤ r := by exact_mod_cast hle
  have hnonneg : 0 ≤ relativeDimension C.dimensionFunction g x := relativeDimension_nonneg C hδ g x
  omega

end Stacks.Chow

end
