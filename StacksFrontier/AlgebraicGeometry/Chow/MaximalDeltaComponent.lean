module

public import StacksFrontier.AlgebraicGeometry.Chow.CoherentCycle.MaximalDeltaDimension
public import StacksFrontier.AlgebraicGeometry.Chow.GysinConstruction.IntegralComponent
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeDimension

/-!
# Points of maximal delta-dimension on a closed subscheme

Let `X` be locally of finite type over the base of a Chow situation and let `i : Z ⟶ X` be a
closed subscheme. If `k` is an upper bound for the delta-dimension of `Z` and `ξ ∈ Z` has
delta-dimension exactly `k`, then `ξ` is the generic point of an irreducible component of `Z`;
that is `Stacks.Chow.isGenericPoint_component_of_relativeDimension_eq`, which this module
imports, and the two statements below are the upper bound it asks for in the case of a divisor
and the two combined.

The point of the statement is that it converts a dimension computation into the indexing datum
that the cycle associated to a closed subscheme uses:
`Stacks.Chow.cycleAssociatedToClosedSubscheme` is a formal sum over the generic points of the
components of `Z`, so reading off its coefficient at a point requires first knowing that the point
is such a generic point.

## Main results

* `Stacks.Chow.schemeDeltaDimension_le_sub_one_of_notMem_range`: a closed subscheme missing the
  generic point of an integral scheme of delta-dimension `n` has delta-dimension at most `n - 1`,
  which is the upper bound the previous statement asks for in the case of a divisor.
* `Stacks.Chow.schemeDeltaDimension_le_sub_one_of_forall_notMem_range`: the same without
  integrality, for a closed subscheme missing the generic point of *every* irreducible component.
* `Stacks.Chow.exists_genericPoints_of_coheight_one`: the two combined, in the form a
  codimension-one coefficient computation uses.

## Implementation notes

The delta-dimension of the closed subscheme is that of its structure morphism `i ≫ f`, while
the delta-dimension of the point `ξ` is evaluated through the ambient scheme, as
`relativeDimension C.dimensionFunction f (i ξ)`; the two agree by
`Stacks.Chow.relativeDimension_comp_closedImmersion`, a closed immersion inducing an isomorphism
on residue fields.

The argument is that the component `W` containing `ξ` has its generic point `η` specializing to
`ξ`, and the delta-dimension of `W` — computed at `η` — is at most `k` by the supremum
description of the delta-dimension of `Z`. Were `η ≠ ξ`, the relative dimension function of
Stacks 02JW would drop strictly from `η` to `ξ`, putting the value at `ξ` below `k`.

## References

* [Stacks Project, Tag 02QT](https://stacks.math.columbia.edu/tag/02QT)
* [Stacks Project, Tag 02JW](https://stacks.math.columbia.edu/tag/02JW)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

/-- Delta-dimension bound for a closed subscheme missing the generic point of every component. -/
private theorem schemeDeltaDimension_le_sub_one_aux (C : ChowSituation.{u})
    {Y Z : Scheme.{u}} (p : Y ⟶ C.S) [LocallyOfFiniteType p]
    (i : Z ⟶ Y) [IsClosedImmersion i] {n : ℤ}
    (hn : schemeDeltaDimension C p = (n : EInt))
    (hi : ∀ T : irreducibleComponents (Y : Type u), T.2.1.genericPoint ∉ Set.range i.base) :
    schemeDeltaDimension C (i ≫ p) ≤ ((n - 1 : ℤ) : EInt) := by
  obtain ⟨d, hd⟩ := relativeDimension_isDimensionFunction
    C.isUniversallyCatenary C.dimensionFunction p
  rw [schemeDeltaDimension_eq_iSup]
  refine iSup_le fun W => WithBotTop.coe_le_coe.mpr ?_
  -- the image of the generic point of `W` lies in some irreducible component `T` of `Y`
  obtain ⟨T, hT, hsub⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
    (closure ({i W.2.1.genericPoint} : Set Y)) isIrreducible_singleton.closure
  have hmem : i W.2.1.genericPoint ∈ T := hsub (subset_closure rfl)
  have hgenT : IsGenericPoint hT.1.genericPoint T :=
    hT.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents T hT)
  have hne : i W.2.1.genericPoint ≠ hT.1.genericPoint := fun h =>
    hi ⟨T, hT⟩ ⟨W.2.1.genericPoint, h⟩
  have hspec : hT.1.genericPoint ⤳ i W.2.1.genericPoint :=
    specializes_iff_mem_closure.mpr (by rw [hgenT]; exact hmem)
  have hlt := d.strictAnti_specializes hspec (Ne.symm hne)
  rw [hd (i W.2.1.genericPoint), hd hT.1.genericPoint] at hlt
  -- the dimension function at the generic point of `T` is at most `n`
  have hTn : relativeDimension C.dimensionFunction p hT.1.genericPoint ≤ n := by
    have hle : (deltaDimension C p ⟨T, hT.1, isClosed_of_mem_irreducibleComponents T hT⟩ :
        EInt) ≤ (n : EInt) := by
      rw [← hn, schemeDeltaDimension_eq_iSup]
      exact le_iSup (fun V : irreducibleComponents (Y : Type u) =>
        (deltaDimension C p ⟨(V : Set Y), V.2.1,
          isClosed_of_mem_irreducibleComponents (V : Set Y) V.2⟩ : EInt)) ⟨T, hT⟩
    have hle' := WithBotTop.coe_le_coe.mp hle
    rwa [deltaDimension_eq_of_isGenericPoint C p _ _ hgenT] at hle'
  show relativeDimension C.dimensionFunction (i ≫ p) W.2.1.genericPoint ≤ n - 1
  have hcomp :=
    relativeDimension_comp_closedImmersion C.dimensionFunction i p W.2.1.genericPoint
  omega


/-- A closed subscheme of an integral scheme of delta-dimension `n` that misses the generic
point has delta-dimension at most `n - 1`.

This is the hypothesis that `Stacks.Chow.isGenericPoint_component_of_relativeDimension_eq` takes,
in the situation where it is applied to a divisor: the generic point of every component of the
subscheme is a non-generic point of the ambient scheme, so the dimension function of Stacks 02JW
drops strictly there. -/
theorem schemeDeltaDimension_le_sub_one_of_notMem_range (C : ChowSituation.{u})
    {Y Z : Scheme.{u}} (p : Y ⟶ C.S) [LocallyOfFiniteType p] [IsIntegral Y]
    (i : Z ⟶ Y) [IsClosedImmersion i] {n : ℤ}
    (hn : schemeDeltaDimension C p = (n : EInt))
    (hi : genericPoint Y ∉ Set.range i.base) :
    schemeDeltaDimension C (i ≫ p) ≤ ((n - 1 : ℤ) : EInt) :=
  schemeDeltaDimension_le_sub_one_aux C p i hn fun T ⟨x, hx⟩ => hi ⟨x, by
    have hT : (T : Set Y) = Set.univ := by
      simpa [irreducibleComponents_eq_singleton] using T.2
    have hg := T.2.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents _ T.2)
    have hY := genericPoint_spec Y
    rw [← hT] at hY
    exact hx.trans (hg.eq hY)⟩

/-- **A closed subscheme of a scheme of delta-dimension `n` missing the generic point of every
irreducible component has delta-dimension at most `n - 1`.** This is the previous statement with
integrality dropped, which is what a devissage over a base that need not be irreducible asks for:
the complement of a dense open subscheme is no longer the complement of one generic point.

The generic point of a component `W` of the subscheme has an image lying in some irreducible
component `T` of the ambient scheme; the generic point of `T` specializes to it and is distinct
from it, since it is not in the image, so the dimension function of Stacks 02JW drops strictly
between them, and its value at the generic point of `T` is at most `n`. -/
theorem schemeDeltaDimension_le_sub_one_of_forall_notMem_range (C : ChowSituation.{u})
    {Y Z : Scheme.{u}} (p : Y ⟶ C.S) [LocallyOfFiniteType p]
    (i : Z ⟶ Y) [IsClosedImmersion i] {n : ℤ}
    (hn : schemeDeltaDimension C p = (n : EInt))
    (hi : ∀ T : irreducibleComponents (Y : Type u), T.2.1.genericPoint ∉ Set.range i.base) :
    schemeDeltaDimension C (i ≫ p) ≤ ((n - 1 : ℤ) : EInt) :=
  schemeDeltaDimension_le_sub_one_aux C p i hn hi

/-- A point of codimension one on an integral scheme `Y` of delta-dimension `n`, lying on a
closed subscheme `i : Z ⟶ Y` that misses the generic point of `Y`, is the image of a generic
point of a component of `Z`, and that component has delta-dimension `n - 1`.

This is the form in which `Stacks.Chow.cycleAssociatedToClosedSubscheme_apply` can be applied at
a codimension-one point: that coefficient formula is indexed by `genericPoints`, so reading off
the coefficient of a divisor at a codimension-one point requires exactly this. -/
theorem exists_genericPoints_of_coheight_one (C : ChowSituation.{u})
    {Y Z : Scheme.{u}} (p : Y ⟶ C.S) [LocallyOfFiniteType p] [IsIntegral Y]
    (i : Z ⟶ Y) [IsClosedImmersion i] {n : ℤ}
    (hn : schemeDeltaDimension C p = (n : EInt))
    (hgen : genericPoint Y ∉ Set.range i.base)
    {x : Y} (hx : Order.coheight x = 1) (hxZ : x ∈ Set.range i.base) :
    ∃ ξ : genericPoints Z, i ξ.1 = x ∧
      relativeDimension C.dimensionFunction p (i ξ.1) = n - 1 := by
  obtain ⟨z, rfl⟩ := hxZ
  obtain ⟨d, hd⟩ := relativeDimension_isDimensionFunction
    C.isUniversallyCatenary C.dimensionFunction p
  have hδ : relativeDimension C.dimensionFunction p (i z) = n - 1 := by
    rw [← deltaDimension_eq_of_isGenericPoint C p
      ⟨closure ({i z} : Set Y), isIrreducible_singleton.closure, isClosed_closure⟩ (i z)
      isGenericPoint_closure]
    exact deltaDimension_closure_singleton_of_coheight_one C p hn hd hx
  obtain ⟨W, hW⟩ := isGenericPoint_component_of_relativeDimension_eq C p i
    (schemeDeltaDimension_le_sub_one_of_notMem_range C p i hn hgen) z hδ
  exact ⟨⟨z, show closure ({z} : Set Z) ∈ irreducibleComponents (Z : Type _) from hW ▸ W.2⟩,
    rfl, hδ⟩

end Stacks.Chow

end
