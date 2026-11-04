module

public import StacksFrontier.AlgebraicGeometry.Chow.DimensionFunction
public import StacksFrontier.AlgebraicGeometry.Chow.GysinConstruction.IntegralComponent
public import StacksCore.Tactic.StacksAttribute

/-!
# Points of maximal delta-dimension

Let `X` be locally of finite type over the base scheme `S` of a `Stacks.Chow.ChowSituation`
and let `T ⊆ X` be a closed subset whose points all have delta-dimension at most `k`. A point of
`T` whose delta-dimension is exactly `k` can then not be a proper specialization of another point
of `T`, because the delta-dimension is the underlying function of a dimension function on `X` and
such a function drops strictly along nontrivial specializations. Hence that point is the generic
point of an irreducible component of `T`.

The bound required above is available for the closed subset underlying a closed subscheme
`i : Z ⟶ X` as soon as `dim_δ(Z) ≤ k`: every point of `Z` is a specialization of the generic
point of one of its irreducible components, and the delta-dimension of that component is one of
the terms of the supremum defining `dim_δ(Z)`.

## Main results

* `Stacks.Chow.relativeDimension_le_of_schemeDeltaDimension_le` — the relative dimension of the
  image of a point of a closed subscheme is bounded by the delta-dimension of that subscheme.
* `Stacks.Chow.exists_isGenericPoint_of_relativeDimension_eq` — a point of a closed subset
  attaining the maximal relative dimension allowed on that subset is the generic point of one of
  its irreducible components.
* `Stacks.Chow.isGenericPoint_component_of_relativeDimension_eq` — the same statement for a
  closed subscheme.
* `Stacks.Chow.relativeDimension_le_of_schemeDeltaDimension_le'` — every point of a scheme has
  relative dimension at most its delta-dimension.
* `Stacks.Chow.schemeDeltaDimension_le_of_forall_relativeDimension_le` — a closed subscheme all
  of whose points have relative dimension at most `k` has delta-dimension at most `k`.

## References

* [Stacks Project, Tag 02JW](https://stacks.math.columbia.edu/tag/02JW)
* [Stacks Project, Tag 02QL](https://stacks.math.columbia.edu/tag/02QL)
* [Stacks Project, Tag 02QP](https://stacks.math.columbia.edu/tag/02QP)
* [Stacks Project, Tag 02QT](https://stacks.math.columbia.edu/tag/02QT)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

/-- Every point of a topological space lies in an irreducible component, which is the closure of
its generic point. -/
private theorem exists_mem_irreducibleComponents_isGenericPoint {Y : Type*}
    [TopologicalSpace Y] [QuasiSober Y] (y : Y) :
    ∃ (W : Set Y) (hW : W ∈ irreducibleComponents Y), y ∈ W ∧
      IsGenericPoint hW.1.genericPoint W := by
  obtain ⟨W, hW, hsub⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
    (closure ({y} : Set Y)) isIrreducible_singleton.closure
  exact ⟨W, hW, hsub (subset_closure rfl),
    hW.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents W hW)⟩

/-- The relative dimension of the image of a point of a closed subscheme `i : Z ⟶ X` is at most
the delta-dimension of `Z`. -/
theorem relativeDimension_le_of_schemeDeltaDimension_le (C : ChowSituation.{u})
    {X Z : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f] (i : Z ⟶ X)
    [IsClosedImmersion i] {k : ℤ} (hZ : schemeDeltaDimension C (i ≫ f) ≤ (k : EInt)) (z : Z) :
    relativeDimension C.dimensionFunction f (i z) ≤ k := by
  obtain ⟨W, hW, hzW, hgen⟩ := exists_mem_irreducibleComponents_isGenericPoint z
  have hQk : deltaDimension C (i ≫ f)
      ⟨W, hW.1, isClosed_of_mem_irreducibleComponents W hW⟩ ≤ k := by
    rw [schemeDeltaDimension_eq_iSup] at hZ
    exact WithBotTop.coe_le_coe.mp
      ((le_iSup (fun V : irreducibleComponents Z =>
        (deltaDimension C (i ≫ f)
          ⟨(V : Set Z), V.2.1, isClosed_of_mem_irreducibleComponents (V : Set Z) V.2⟩ : EInt))
        (⟨W, hW⟩ : irreducibleComponents Z)).trans hZ)
  rw [deltaDimension_eq_of_isGenericPoint C (i ≫ f) _ _ hgen] at hQk
  rw [← relativeDimension_comp_closedImmersion C.dimensionFunction i f z]
  rcases eq_or_ne hW.1.genericPoint z with h | h
  · exact h ▸ hQk
  · have hlt := (deltaDimensionFunction C (i ≫ f)).strictAnti_specializes
      (hgen.specializes hzW) h
    rw [deltaDimensionFunction_apply, deltaDimensionFunction_apply] at hlt
    lia

/-- A point of a closed subset `T` of `X` whose relative dimension is `k`, when no point of `T`
has relative dimension exceeding `k`, is the generic point of an irreducible component of `T`. -/
theorem exists_isGenericPoint_of_relativeDimension_eq (C : ChowSituation.{u}) {X : Scheme.{u}}
    (f : X ⟶ C.S) [LocallyOfFiniteType f] {T : Set X} (hT : IsClosed T) {k : ℤ}
    (hle : ∀ y ∈ T, relativeDimension C.dimensionFunction f y ≤ k) {ξ : X} (hξT : ξ ∈ T)
    (hξ : relativeDimension C.dimensionFunction f ξ = k) :
    ∃ Z : irreducibleComponents T, IsGenericPoint ξ (Subtype.val '' (Z : Set T)) := by
  obtain ⟨W, hW, hsub⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
    (closure ({(⟨ξ, hξT⟩ : T)} : Set T)) isIrreducible_singleton.closure
  have hξW : (⟨ξ, hξT⟩ : T) ∈ W := hsub (subset_closure rfl)
  have hclosed : IsClosed (Subtype.val '' W) :=
    hT.isClosedEmbedding_subtypeVal.isClosedMap _ (isClosed_of_mem_irreducibleComponents W hW)
  have hirr : IsIrreducible (Subtype.val '' W) :=
    hW.1.image _ continuous_subtype_val.continuousOn
  have hgen : IsGenericPoint hirr.genericPoint (Subtype.val '' W) :=
    hirr.isGenericPoint_genericPoint hclosed
  refine ⟨⟨W, hW⟩, ?_⟩
  have hmemT : hirr.genericPoint ∈ T := by
    obtain ⟨w, -, hw⟩ := hgen.mem
    exact hw ▸ w.2
  rcases eq_or_ne hirr.genericPoint ξ with h | h
  · exact h ▸ hgen
  · refine absurd (hle _ hmemT) ?_
    have hlt := (deltaDimensionFunction C f).strictAnti_specializes
      (hgen.specializes ⟨_, hξW, rfl⟩) h
    rw [deltaDimensionFunction_apply, deltaDimensionFunction_apply, hξ] at hlt
    lia

/-- A point of a closed subscheme `i : Z ⟶ X` attaining an upper bound for the delta-dimension
of `Z` is the generic point of an irreducible component of `Z`. -/
@[stacks 02QT "maximal_delta_component"]
theorem isGenericPoint_component_of_relativeDimension_eq (C : ChowSituation.{u})
    {X Z : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f] (i : Z ⟶ X) [IsClosedImmersion i]
    {k : ℤ} (hZ : schemeDeltaDimension C (i ≫ f) ≤ (k : EInt)) (ξ : Z)
    (hξ : relativeDimension C.dimensionFunction f (i ξ) = k) :
    ∃ W : irreducibleComponents Z, IsGenericPoint ξ (W : Set Z) := by
  obtain ⟨W, hW, hξW, hgen⟩ := exists_mem_irreducibleComponents_isGenericPoint ξ
  refine ⟨⟨W, hW⟩, ?_⟩
  rcases eq_or_ne hW.1.genericPoint ξ with h | h
  · exact h ▸ hgen
  · refine absurd (relativeDimension_le_of_schemeDeltaDimension_le C f i hZ hW.1.genericPoint) ?_
    have hlt := (deltaDimensionFunction C (i ≫ f)).strictAnti_specializes
      (hgen.specializes hξW) h
    rw [deltaDimensionFunction_apply, deltaDimensionFunction_apply,
      relativeDimension_comp_closedImmersion, relativeDimension_comp_closedImmersion, hξ] at hlt
    lia

/-- A scheme whose delta-dimension is at most `k` has every point of relative dimension at most
`k`. -/
public theorem relativeDimension_le_of_schemeDeltaDimension_le' (C : ChowSituation.{u})
    {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] {k : ℤ}
    (hX : schemeDeltaDimension C sX ≤ (k : EInt)) (x : X) :
    relativeDimension C.dimensionFunction sX x ≤ k := by
  simpa using relativeDimension_le_of_schemeDeltaDimension_le C sX (𝟙 X) (by simpa using hX) x

/-- A closed subscheme all of whose points have relative dimension at most `k` has
delta-dimension at most `k`. -/
public theorem schemeDeltaDimension_le_of_forall_relativeDimension_le (C : ChowSituation.{u})
    {Y W : Scheme.{u}} (f : Y ⟶ C.S) [LocallyOfFiniteType f] (j : W ⟶ Y) [IsClosedImmersion j]
    {k : ℤ} (h : ∀ w : W, relativeDimension C.dimensionFunction f (j w) ≤ k) :
    schemeDeltaDimension C (j ≫ f) ≤ (k : EInt) := by
  rw [schemeDeltaDimension_eq_iSup]
  refine iSup_le fun V => WithBotTop.coe_le_coe.mpr ?_
  rw [deltaDimension, relativeDimension_comp_closedImmersion]
  exact h _

end Stacks.Chow
