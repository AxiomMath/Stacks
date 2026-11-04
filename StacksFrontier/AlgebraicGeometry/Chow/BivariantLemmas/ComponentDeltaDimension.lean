module

public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.CompletedCapFundamentalClass
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.CompletedRestrictionComposite
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.VirtualNormalCapRegularFormula
public import StacksFrontier.Topology.Sober.Generization

/-!
# The `δ`-dimension of a connected component

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project and let `Y` be locally of
finite type over `S`, with a decomposition `Y = ∐_n Y_n` into open and closed pieces all of whose
irreducible components have `δ`-dimension `n` (Stacks 0FE3). A connected component `Y_b` lies in a
single piece `Y_{n_b}` (`Stacks.Chow.componentDeltaDimension`). This file records what that says
about `Y_b`:

* every irreducible component of `Y_b` has `δ`-dimension `n_b`, so `n_b` is the common value of
  `δ` at the generic points of the irreducible components of `Y` through any point of `Y_b`, which
  is the invariant `n_y` of Stacks 0FE3;
* every point of `Y_b` has `δ`-dimension at most `n_b`;
* a point of `Y_b` of `δ`-dimension `n_b` is the generic point of an irreducible component of `Y`.

## Main results

* `Stacks.Chow.deltaDimension_connectedComponentOpens` — `Y_b` is pure of `δ`-dimension `n_b`.
* `Stacks.Chow.relativeDimension_le_componentDeltaDimension` — `δ(y) ≤ n_y`.
* `Stacks.Chow.mem_genericPoints_of_relativeDimension_eq_componentDeltaDimension` — `δ(y) = n_y`
  only at generic points.
* `Stacks.Chow.relativeDimension_eq_componentDeltaDimension_of_mem_genericPoints` — `δ(y) = n_y`
  at generic points.
* `Stacks.Chow.exists_mem_genericPoints_mk_eq` — every connected component contains a generic
  point of an irreducible component.

## References

* [Stacks Project, Tag 0FE3](https://stacks.math.columbia.edu/tag/0FE3)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

variable (C : ChowSituation.{u}) {Y : Scheme.{u}} (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
  [IsLocallyNoetherian Y]
  (hY : HasDimensionDecomposition (relativeDimension C.dimensionFunction sY))

/-- **A connected component is pure of its `δ`-dimension.** Every irreducible component of the
connected component `Y_b` has `δ`-dimension `n_b`: its generic point is a generic point of the
piece `Y_{n_b}` of the dimension decomposition containing `Y_b`. -/
theorem deltaDimension_connectedComponentOpens (b : _root_.ConnectedComponents Y)
    (W : irreducibleComponents (Y.connectedComponentOpens b)) :
    deltaDimension C ((Y.connectedComponentOpens b).ι ≫ sY)
        ⟨W, W.2.1, isClosed_of_mem_irreducibleComponents
          (W : Set (Y.connectedComponentOpens b)) W.2⟩ =
      componentDeltaDimension C sY hY b := by
  set n := componentDeltaDimension C sY hY b
  set U := Classical.choose hY n
  have hle := connectedComponentOpens_le_dimensionDecomposition C sY hY b
  have hη : IsGenericPoint W.2.1.genericPoint (W : Set (Y.connectedComponentOpens b)) :=
    W.2.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents _ W.2)
  have hηgen : W.2.1.genericPoint ∈ genericPoints (Y.connectedComponentOpens b) := by
    rw [genericPoints, Set.mem_setOf_eq, hη.def]
    exact W.2
  have hgen : Y.homOfLE hle W.2.1.genericPoint ∈ genericPoints U :=
    (Y.homOfLE hle).isOpenEmbedding.mem_genericPoints hηgen
  have hval := (Classical.choose_spec hY).2 n _ hgen _ isGenericPoint_closure
  rw [deltaDimension_eq_of_isGenericPoint C _ _ _ hη, relativeDimension_comp_isOpenImmersion,
    ← hval]
  congr 1
  rw [← Scheme.homOfLE_ι Y hle, Scheme.Hom.comp_apply]
  rfl

omit [LocallyOfFiniteType sY] in
/-- The connected component of a point is the component the point lies in. -/
theorem mem_connectedComponentOpens_mk (y : Y) :
    y ∈ Y.connectedComponentOpens (_root_.ConnectedComponents.mk y) :=
  rfl

/-- **The `δ`-dimension of a point is at most that of its connected component.** -/
theorem relativeDimension_le_componentDeltaDimension (y : Y) :
    relativeDimension C.dimensionFunction sY y ≤
      componentDeltaDimension C sY hY (_root_.ConnectedComponents.mk y) := by
  set b := _root_.ConnectedComponents.mk y
  have h := relativeDimension_le_of_forall_genericPoint C ((Y.connectedComponentOpens b).ι ≫ sY)
    (n := componentDeltaDimension C sY hY b) (fun W => by
      rw [← deltaDimension_connectedComponentOpens C sY hY b W,
        deltaDimension_eq_of_isGenericPoint C _ _ _
          (W.2.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents _ W.2))])
    ⟨y, mem_connectedComponentOpens_mk y⟩
  rwa [relativeDimension_comp_isOpenImmersion C.dimensionFunction (Y.connectedComponentOpens b).ι
    sY ⟨y, mem_connectedComponentOpens_mk y⟩] at h

/-- **A point of maximal `δ`-dimension in its connected component is a generic point.** A point
`y` with `δ(y) = n_y` is the generic point of an irreducible component of `Y`. -/
theorem mem_genericPoints_of_relativeDimension_eq_componentDeltaDimension (y : Y)
    (hy : relativeDimension C.dimensionFunction sY y =
      componentDeltaDimension C sY hY (_root_.ConnectedComponents.mk y)) :
    y ∈ genericPoints Y := by
  set b := _root_.ConnectedComponents.mk y
  have hdim : schemeDeltaDimension C ((Y.connectedComponentOpens b).ι ≫ sY) ≤
      (componentDeltaDimension C sY hY b : EInt) :=
    iSup_le fun W ↦
      (congrArg (fun z : ℤ ↦ (z : EInt)) (deltaDimension_connectedComponentOpens C sY hY b W)).le
  let yb : (Y.connectedComponentOpens b : Scheme.{u}) := ⟨y, mem_connectedComponentOpens_mk y⟩
  obtain ⟨W, hW⟩ := isGenericPoint_component_of_relativeDimension_eq C sY
    (Y.connectedComponentOpens b).ι hdim yb hy
  have hgen : yb ∈ genericPoints (Y.connectedComponentOpens b : Scheme.{u}) := by
    rw [genericPoints, Set.mem_setOf_eq, hW.def]
    exact W.2
  exact (Y.connectedComponentOpens b).ι.isOpenEmbedding.mem_genericPoints hgen

/-- **The `δ`-dimension of a generic point is that of its connected component.** -/
theorem relativeDimension_eq_componentDeltaDimension_of_mem_genericPoints (y : Y)
    (hy : y ∈ genericPoints Y) :
    relativeDimension C.dimensionFunction sY y =
      componentDeltaDimension C sY hY (_root_.ConnectedComponents.mk y) := by
  set b := _root_.ConnectedComponents.mk y
  let yb : (Y.connectedComponentOpens b : Scheme.{u}) := ⟨y, mem_connectedComponentOpens_mk y⟩
  have hyb : yb ∈ genericPoints (Y.connectedComponentOpens b : Scheme.{u}) :=
    TopologicalSpace.mem_genericPoints_of_forall_specializes_eq fun z hz ↦
      (Y.connectedComponentOpens b).ι.isOpenEmbedding.injective
        (TopologicalSpace.forall_specializes_eq_of_mem_genericPoints hy _
          (hz.map (Y.connectedComponentOpens b).ι.continuous))
  have hW : closure ({yb} : Set (Y.connectedComponentOpens b : Scheme.{u})) ∈
      irreducibleComponents (Y.connectedComponentOpens b : Scheme.{u}) := hyb
  have h := deltaDimension_connectedComponentOpens C sY hY b ⟨_, hW⟩
  rwa [deltaDimension_eq_of_isGenericPoint C _ _ yb isGenericPoint_closure,
    relativeDimension_comp_isOpenImmersion] at h

omit [LocallyOfFiniteType sY] [IsLocallyNoetherian Y] in
/-- **Every connected component contains a generic point.** The irreducible component through a
point of `Y_b` is connected, so its generic point lies in `Y_b` too. -/
theorem exists_mem_genericPoints_mk_eq [LocallyConnectedSpace Y]
    (b : _root_.ConnectedComponents Y) :
    ∃ y ∈ genericPoints Y, _root_.ConnectedComponents.mk y = b := by
  obtain ⟨x, rfl⟩ := _root_.ConnectedComponents.surjective_coe b
  obtain ⟨Z, hxZ⟩ := exists_mem_irreducibleComponents x
  have hη := Z.2.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents _ Z.2)
  refine ⟨Z.2.1.genericPoint, ?_, ?_⟩
  · rw [genericPoints, Set.mem_setOf_eq, hη.def]
    exact Z.2
  · refine (_root_.ConnectedComponents.coe_eq_coe').2 ?_
    have hconn : _root_.IsPreconnected (closure ({Z.2.1.genericPoint} : Set Y)) :=
      isIrreducible_singleton.closure.isConnected.2
    rw [← connectedComponent_eq (hconn.subset_connectedComponent (subset_closure rfl)
      (by rwa [hη.def]))]
    exact mem_connectedComponent

end Stacks.Chow

end
