module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ClosedSubspaceFamilySums
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatChartSectionOrderGenericPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatFibreChartColength
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatPullbackOfCycles
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatPullbackSectionChartOrder
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatPullbackSectionComponentChart
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatPullbackSectionComponents
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormulaComponentDivisor
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrimeDivisorDeltaDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.RegularMeromorphicSectionNeZero
public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianIrreducibleComponents
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ComponentMultiplicityBranchIndexing

/-!
# The two sides of Stacks 0EQQ, read at one prime divisor on a chart

In Situation 0EDT let `X/B` and `Y/B` be good, let `f : X ⟶ Y` be flat of relative dimension `r`,
let `Y` be integral with `n = dim_δ(Y)`, let `ℒ` be an invertible `𝒪_Y`-module and `s` a nonzero
meromorphic section of `ℒ`. Stacks 0EQQ is the identity

  `f^* div_ℒ(s) = ∑ n_i div_{f^*ℒ|_{X_i}}(s_i)`

of `(n + r - 1)`-cycles on `X`, the sum running over the irreducible components `X_i` of `X` of
δ-dimension `n + r`, with `s_i = f|_{X_i}^*(s)` and `n_i = m_{X_i, X}`.

This file defines the objects of the right-hand side and computes both sides at an integral
closed subspace `Z ⊆ X` of δ-dimension `n + r - 1` on a diagram `U ⟶ V` of affine étale charts
over `f` through the generic point of `Z`, with `ℒ` free over `V` on `e`: both are the order of
vanishing in `O = 𝒪_{U, u}` of the image `φ(s / e)` of the chart ratio of `s`.

## Main definitions

* `AlgebraicGeometry.Space.topDimensionalComponents`: the irreducible components of `X` of a
  given δ-dimension, as integral closed subspaces.
* `AlgebraicGeometry.Space.componentMorphism`, `AlgebraicGeometry.Space.componentModule`,
  `AlgebraicGeometry.Space.componentSection`: `f|_W`, `f|_W^*ℒ` and `f|_W^*(s)`.
* `AlgebraicGeometry.Space.componentDivisor`: `div_{f^*ℒ|_W}(f|_W^*(s))` of Stacks 0EQE on `W`.

## References

* [Stacks Project, Tag 0EE9](https://stacks.math.columbia.edu/tag/0EE9)
* [Stacks Project, Tag 0EQE](https://stacks.math.columbia.edu/tag/0EQE)
* [Stacks Project, Tag 0EQQ](https://stacks.math.columbia.edu/tag/0EQQ)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace IsLocalRing
open scoped nonZeroDivisors

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology
attribute [local instance] chartMeromorphicFunctionAlgebra

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY)
    (f : X ⟶ Y) (hbase : f ≫ sY = sX) (r : ℕ) (hflat : IsFlat D.site D.base D.base_mem f)
    (hr : HasRelativeDimension r D.site D.base D.base_mem f)
    (hintY : IsIntegralSpace D.site D.base D.base_mem Y) {n : ℤ}
    (hn : deltaDimensionClosed D sY hY Set.univ isClosed_univ = (n : EInt))
    (L : Modules.{u, u} D.site D.base D.base_mem Y hY.1) (hL : IsInvertibleSheaf D sY hY L)
    (s : MeromorphicSection.{u, u} D.site D.base D.base_mem Y hY.1 L) (hs : s ≠ 0)

/-! ### The objects of the right-hand side -/

/-- The irreducible components of `X` of δ-dimension `k`, as integral closed subspaces: those
whose set of points is an irreducible component of `|X|`. -/
abbrev topDimensionalComponents (k : ℤ) :=
  {W : IntegralClosedSubspace D.site D.base D.base_mem X //
    subspacePointSet D.site D.base D.base_mem X W.subspace ∈
        irreducibleComponents (points D.site D.base D.base_mem X) ∧
      deltaDimension D sX W = k}

/-- The restriction `f|_W : W ⟶ Y` of `f` to an integral closed subspace, as a morphism of
algebraic spaces. -/
abbrev componentMorphism (W : IntegralClosedSubspace D.site D.base D.base_mem X) :
    (⟨W.subspace.toFunctor, W.isClosedSubspace.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶
      ⟨Y, hY.1⟩ :=
  ObjectProperty.homMk (W.subspace.ι ≫ f)

/-- The restriction `f^*ℒ|_W = f|_W^*ℒ` of the pullback of `ℒ` to an integral closed
subspace. -/
abbrev componentModule (W : IntegralClosedSubspace D.site D.base D.base_mem X) :
    Modules.{u, u} D.site D.base D.base_mem W.subspace.toFunctor W.isClosedSubspace.1 :=
  (modulePullback D.site D.base D.base_mem (componentMorphism D sY hY f W)).obj L

include hX hflat hintY in
/-- Meromorphic sections pull back along `f|_W` for an irreducible component `W` of `X`. -/
theorem pullbacksMeromorphicSections_componentMorphism
    (W : IntegralClosedSubspace D.site D.base D.base_mem X)
    (hW : subspacePointSet D.site D.base D.base_mem X W.subspace ∈
      irreducibleComponents (points D.site D.base D.base_mem X)) :
    PullbacksMeromorphicSections D.site D.base D.base_mem (componentMorphism D sY hY f W).hom :=
  pullbacksMeromorphicSections_ι_comp_of_isFlat D sX hX sY hY f hflat hintY W hW

/-- **The section `s_i = f|_{X_i}^*(s)`**, the pullback of Stacks 0ENC, part (1), of `s` along
the restriction of `f` to an irreducible component. -/
def componentSection (W : IntegralClosedSubspace D.site D.base D.base_mem X)
    (hW : subspacePointSet D.site D.base D.base_mem X W.subspace ∈
      irreducibleComponents (points D.site D.base D.base_mem X)) :
    MeromorphicSection.{u, u} D.site D.base D.base_mem W.subspace.toFunctor W.isClosedSubspace.1
      (componentModule D sY hY f L W) :=
  pullbackMeromorphicSection D.site D.base D.base_mem (componentMorphism D sY hY f W) L
    (pullbacksMeromorphicSections_componentMorphism D sX hX sY hY f hflat hintY W hW) s

include hL in
/-- `f^*ℒ|_W` is invertible (Stacks 0B8P). -/
theorem isInvertibleSheaf_componentModule
    (W : IntegralClosedSubspace D.site D.base D.base_mem X) :
    IsInvertibleSheaf D (W.subspace.ι ≫ sX) (isGood_integralClosedSubspace D sX hX W)
      (componentModule D sY hY f L W) :=
  isInvertible_modulePullback_obj D.site D.base D.base_mem (componentMorphism D sY hY f W) L hL

include hL hs in
/-- The pulled back section is nonzero: `s` is regular, `Y` being integral, and so is its
pullback (Stacks 0ENC, part (2)). -/
theorem componentSection_ne_zero (W : IntegralClosedSubspace D.site D.base D.base_mem X)
    (hW : subspacePointSet D.site D.base D.base_mem X W.subspace ∈
      irreducibleComponents (points D.site D.base D.base_mem X)) :
    componentSection D sX hX sY hY f hflat hintY L s W hW ≠ 0 := by
  have hYN := hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sY hY
  have hWN := hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D (W.subspace.ι ≫ sX)
    (isGood_integralClosedSubspace D sX hX W)
  have hreg : IsRegularMeromorphicSection.{u, u} D.site D.base D.base_mem Y hY.1 L s :=
    (isRegularMeromorphicSection_iff_ne_zero D.site D.base D.base_mem hY.1 hintY hYN L
      (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hL) s).mpr hs
  have hpull := isRegularMeromorphicSection_pullbackMeromorphicSection D.site D.base D.base_mem
    (componentMorphism D sY hY f W)
    (pullbacksMeromorphicSections_componentMorphism D sX hX sY hY f hflat hintY W hW) L hL s hreg
  exact (isRegularMeromorphicSection_iff_ne_zero D.site D.base D.base_mem W.isClosedSubspace.1
    W.isIntegralSpace hWN _ (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _
      (isInvertibleSheaf_componentModule D sX hX sY hY f L hL W)) _).mp hpull

/-- **The divisor `div_{f^*ℒ|_{X_i}}(s_i)` of Stacks 0EQE** on an irreducible component `X_i` of
δ-dimension `n + r`, an `(n + r - 1)`-cycle on `X_i`. -/
def componentDivisor (W : IntegralClosedSubspace D.site D.base D.base_mem X)
    (hW : subspacePointSet D.site D.base D.base_mem X W.subspace ∈
      irreducibleComponents (points D.site D.base D.base_mem X))
    (hWd : deltaDimension D sX W = n + r) :
    CycleGroup D (W.subspace.ι ≫ sX) (n + r - 1) :=
  sectionWeilDivisor D (W.subspace.ι ≫ sX) (isGood_integralClosedSubspace D sX hX W)
    W.isIntegralSpace (componentModule D sY hY f L W)
    (isInvertibleSheaf_componentModule D sX hX sY hY f L hL W)
    (by rw [deltaDimensionClosed_univ_integralClosedSubspace D sX hX W, hWd])
    (componentSection D sX hX sY hY f hflat hintY L s W hW)
    (componentSection_ne_zero D sX hX sY hY f hflat hintY L hL s hs W hW)

include hX in
/-- The irreducible components of `X` of a given δ-dimension form a locally finite family
(Stacks 0EE5). -/
theorem locallyFinite_topDimensionalComponents (k : ℤ) :
    LocallyFinite fun j : topDimensionalComponents D sX k =>
      subspacePointSet D.site D.base D.base_mem X j.1.subspace := by
  have hN := hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sX hX
  have hlf := (isLocallyNoetherianSpace_of_isLocallyNoetherian D.site D.base D.base_mem X hX.1
    hN).locallyFinite_image_irreducibleComponents Topology.IsClosedEmbedding.id
  have hinj : Function.Injective fun j : topDimensionalComponents D sX k =>
      (⟨subspacePointSet D.site D.base D.base_mem X j.1.subspace, j.2.1⟩ :
        irreducibleComponents (points D.site D.base D.base_mem X)) := by
    intro j j' h
    exact Subtype.ext (injective_integralClosedSubspaceSupport D.site D.base D.base_mem hX.1
      (IrreducibleCloseds.ext (congrArg Subtype.val h)))
  have := hlf.comp_injective hinj
  simpa [Function.comp_def] using this

/-- **The right-hand side of Stacks 0EQQ**: the `(n + r - 1)`-cycle
`∑ m_{X_i, X} (X_i → X)_* div_{f^*ℒ|_{X_i}}(s_i)` on `X`, the sum over the irreducible components
`X_i` of `X` of δ-dimension `n + r` (a locally finite family, so that the sum is a cycle by
Stacks 0EQ6, part (1)). -/
def componentDivisorSum : CycleGroup D sX (n + r - 1) :=
  cycleFamilySum D sX hX (fun j : topDimensionalComponents D sX (n + r) => j.1)
    (locallyFinite_topDimensionalComponents D sX hX (n + r)) (n + r - 1)
    fun j => spaceMultiplicity D X hX.1 j.1 •
      componentDivisor D sX hX sY hY f r hflat hintY L hL s hs j.1 j.2.1 j.2.2

end AlgebraicGeometry.Space

end
