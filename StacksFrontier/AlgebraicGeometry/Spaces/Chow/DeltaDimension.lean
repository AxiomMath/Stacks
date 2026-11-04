module

public import Mathlib.Data.Int.ConditionallyCompleteOrder
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Order.WithBotTop
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.IntegralGoodSpace

/-!
# The delta-dimension of a closed subset of a good algebraic space

Over the fixed base of the theory of cycles, a good algebraic space `X` carries the dimension
function induced by the dimension function `δ` of the base. The *`δ`-dimension* of an
irreducible closed subset of the space of points of `X` is the value of that function at the
generic point of the subset; the `δ`-dimension of an arbitrary closed subset is the supremum of
the `δ`-dimensions of its irreducible components, and the `δ`-dimension of a closed subspace is
that of its set of points.

## Main definitions

* `AlgebraicGeometry.Space.deltaDimensionIrreducible`: **Stacks 0EDX**, the `δ`-dimension of an
  irreducible closed subset of the space of points.
* `AlgebraicGeometry.Space.deltaDimensionClosed`: **Stacks 0EDX**, the `δ`-dimension of an
  arbitrary closed subset of the space of points.
* `AlgebraicGeometry.Space.deltaDimensionSubspace`: **Stacks 0EDX**, the `δ`-dimension of a
  closed subspace.

## Main results

* `AlgebraicGeometry.Space.quasiSober_points_of_isGood`: the space of points of a good
  algebraic space has generic points for its irreducible closed subsets.
* `AlgebraicGeometry.Space.deltaDimensionIrreducible_eq_of_isGenericPoint`: the `δ`-dimension
  of an irreducible closed subset is the induced dimension at any of its generic points.
* `AlgebraicGeometry.Space.deltaDimensionClosed_eq_deltaDimensionIrreducible`: the two
  definitions agree on an irreducible closed subset.

## Implementation notes

The generic point of an irreducible closed subset exists because the space of points of a good
algebraic space is sober: a good space is decent, by
`AlgebraicGeometry.Space.isDecentSpace_of_isGood`, and the space of points of a decent
algebraic space is sober by Stacks 03K6. Only the existence half, `QuasiSober`, enters the
definitions; uniqueness, the Kolmogorov property of Stacks 03K3, is what makes the value
independent of the choice of generic point. Soberness of `|X|` for good `X` is Stacks 0EDU,
whose statement is not formed here; `AlgebraicGeometry.Space.quasiSober_points_of_isGood`
carries no `@[stacks]` attribute because it is only the existence half of it.

The supremum over the irreducible components takes values in the extended integers `EInt`,
which accommodate both the empty closed subset and a closed subset whose components have
unbounded `δ`-dimension; the value on an irreducible closed subset is an honest integer, as in
the source. The components of a closed subset `T` are the irreducible components of the
topological space `T`, and their generic points are taken there and then viewed in `|X|`,
which `AlgebraicGeometry.Space.deltaDimensionClosed_eq_deltaDimensionIrreducible` reconciles
with the first definition.

A closed subspace is a subfunctor whose inclusion is a closed immersion; its set of points is
the range of the induced map on points, which is closed by Stacks 04CD.

## References

* [Stacks Project, Tag 03K3](https://stacks.math.columbia.edu/tag/03K3)
* [Stacks Project, Tag 03K6](https://stacks.math.columbia.edu/tag/03K6)
* [Stacks Project, Tag 04CD](https://stacks.math.columbia.edu/tag/04CD)
* [Stacks Project, Tag 0EDN](https://stacks.math.columbia.edu/tag/0EDN)
* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
* [Stacks Project, Tag 0EDU](https://stacks.math.columbia.edu/tag/0EDU)
* [Stacks Project, Tag 0EDX](https://stacks.math.columbia.edu/tag/0EDX)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

/-- A point of a closed subset which is generic for the whole subset is a generic point of that
subset in the ambient space. -/
private theorem isGenericPoint_val_of_isGenericPoint_univ {α : Type*} [TopologicalSpace α]
    {T : Set α} (hT : IsClosed T) {x : T} (hx : IsGenericPoint x (Set.univ : Set T)) :
    IsGenericPoint (x : α) T := by
  simpa only [Set.image_univ, Subtype.range_coe, hT.closure_eq] using
    hx.image continuous_subtype_val

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}

/-- Every irreducible closed subset of the space of points of a good algebraic space over the
fixed base has a generic point: a good space is decent, and the space of points of a decent
algebraic space is sober. -/
theorem quasiSober_points_of_isGood (f : X ⟶ D.space) (hf : D.IsGood f) :
    QuasiSober (points D.site D.base D.base_mem X) :=
  quasiSober_points_of_isDecentSpace D.site D.base D.base_mem hf.1
    (isDecentSpace_of_isGood D f hf)

/-- **Stacks 0EDX.** The `δ`-dimension of an irreducible closed subset of the space of points
of a good algebraic space: the induced dimension function at the generic point of the
subset. -/
@[stacks 0EDX "irreducible closed subsets"]
noncomputable def deltaDimensionIrreducible (f : X ⟶ D.space) (hf : D.IsGood f)
    (T : IrreducibleCloseds (points D.site D.base D.base_mem X)) : ℤ :=
  have _hsober : QuasiSober (points D.site D.base D.base_mem X) :=
    quasiSober_points_of_isGood D f hf
  inducedDimensionValue D.site D.base D.base_mem D.delta f T.isIrreducible.genericPoint

/-- **Stacks 0EDX.** The `δ`-dimension of an arbitrary closed subset of the space of points of
a good algebraic space: the supremum, among the extended integers, of the `δ`-dimensions of its
irreducible components. -/
@[stacks 0EDX "closed subsets"]
noncomputable def deltaDimensionClosed (f : X ⟶ D.space) (hf : D.IsGood f)
    (T : Set (points D.site D.base D.base_mem X)) (hT : IsClosed T) : EInt :=
  have _hsober : QuasiSober (points D.site D.base D.base_mem X) :=
    quasiSober_points_of_isGood D f hf
  have _hTsober : QuasiSober T := hT.isClosedEmbedding_subtypeVal.quasiSober
  ⨆ Z : irreducibleComponents T,
    (inducedDimensionValue D.site D.base D.base_mem D.delta f Z.2.1.genericPoint.1 : EInt)

/-- **Stacks 0EDX.** The `δ`-dimension of a closed subspace of a good algebraic space: the
`δ`-dimension of its set of points. -/
@[stacks 0EDX "closed subspaces"]
noncomputable def deltaDimensionSubspace (f : X ⟶ D.space) (hf : D.IsGood f) (Z : Subfunctor X)
    (hZ : IsClosedSubspace D.site D.base D.base_mem Z) : EInt :=
  deltaDimensionClosed D f hf (Set.range (pointsMap D.site D.base D.base_mem Z.toFunctor Z.ι))
    ((isClosedImmersion_iff_isClosed_range_pointsMap D.site D.base D.base_mem hf.1 Z.ι
      (isImmersion_of_isClosedImmersion D.site D.base D.base_mem hZ.2)).1 hZ.2)

/-- The `δ`-dimension of an irreducible closed subset is the induced dimension function at any
of its generic points: the space of points is Kolmogorov, so there is only one. -/
theorem deltaDimensionIrreducible_eq_of_isGenericPoint (f : X ⟶ D.space) (hf : D.IsGood f)
    (T : IrreducibleCloseds (points D.site D.base D.base_mem X))
    {x : points D.site D.base D.base_mem X}
    (hx : IsGenericPoint x (T : Set (points D.site D.base D.base_mem X))) :
    deltaDimensionIrreducible D f hf T =
      inducedDimensionValue D.site D.base D.base_mem D.delta f x := by
  have hsober : QuasiSober (points D.site D.base D.base_mem X) :=
    quasiSober_points_of_isGood D f hf
  have ht0 : T0Space (points D.site D.base D.base_mem X) :=
    t0Space_points_of_isDecentSpace D.site D.base D.base_mem hf.1 (isDecentSpace_of_isGood D f hf)
  have hxe : x = T.isIrreducible.genericPoint :=
    hx.eq (T.isIrreducible.isGenericPoint_genericPoint T.isClosed)
  show inducedDimensionValue D.site D.base D.base_mem D.delta f
    T.isIrreducible.genericPoint = _
  rw [hxe]

/-- On an irreducible closed subset the two `δ`-dimensions agree: the subset is its own single
irreducible component, so the supremum is the value at its generic point. -/
theorem deltaDimensionClosed_eq_deltaDimensionIrreducible (f : X ⟶ D.space) (hf : D.IsGood f)
    (T : IrreducibleCloseds (points D.site D.base D.base_mem X)) :
    deltaDimensionClosed D f hf (T : Set (points D.site D.base D.base_mem X)) T.isClosed =
      (deltaDimensionIrreducible D f hf T : EInt) := by
  have hsober : QuasiSober (points D.site D.base D.base_mem X) :=
    quasiSober_points_of_isGood D f hf
  have hTspace : IrreducibleSpace (T : Set (points D.site D.base D.base_mem X)) :=
    Subtype.irreducibleSpace T.isIrreducible
  have hTsober : QuasiSober (T : Set (points D.site D.base D.base_mem X)) :=
    T.isClosed.isClosedEmbedding_subtypeVal.quasiSober
  have hcomp : irreducibleComponents (T : Set (points D.site D.base D.base_mem X)) =
      {Set.univ} := irreducibleComponents_eq_singleton
  have hne : Nonempty (irreducibleComponents (T : Set (points D.site D.base D.base_mem X))) :=
    ⟨⟨Set.univ, by rw [hcomp]; rfl⟩⟩
  have key : ∀ W : irreducibleComponents (T : Set (points D.site D.base D.base_mem X)),
      (inducedDimensionValue D.site D.base D.base_mem D.delta f W.2.1.genericPoint.1 : EInt) =
        (deltaDimensionIrreducible D f hf T : EInt) := by
    intro W
    have hWuniv : W.1 = (Set.univ : Set (T : Set (points D.site D.base D.base_mem X))) :=
      hcomp.subset W.2
    have hgen : IsGenericPoint W.2.1.genericPoint
        (Set.univ : Set (T : Set (points D.site D.base D.base_mem X))) :=
      (W.2.1.isGenericPoint_genericPoint
        (isClosed_of_mem_irreducibleComponents _ W.2)).def.trans hWuniv
    rw [deltaDimensionIrreducible_eq_of_isGenericPoint D f hf T
      (isGenericPoint_val_of_isGenericPoint_univ T.isClosed hgen)]
  show (⨆ W : irreducibleComponents (T : Set (points D.site D.base D.base_mem X)),
    (inducedDimensionValue D.site D.base D.base_mem D.delta f W.2.1.genericPoint.1 : EInt)) = _
  exact (iSup_congr key).trans iSup_const

end AlgebraicGeometry.Space

end
