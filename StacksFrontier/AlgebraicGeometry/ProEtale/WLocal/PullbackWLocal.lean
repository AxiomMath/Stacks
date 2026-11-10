module

public import Mathlib.Topology.Category.TopCat.Limits.Pullbacks
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.ProEtale.WLocal.PullbackClosedPoints
public import StacksFrontier.Topology.Separation.FibreProduct
public import StacksFrontier.Topology.Spectral.ComponentSpace

/-!
# W-locality of a profinite base change of the component map

Let `X` be a w-local space and let `T` be a profinite space mapping continuously to the space of
connected components of `X`. The fibre product `Y = X ×_{π₀(X)} T` is again w-local, and the
projection `Y → X` is a w-local map.

## Main results

* `AlgebraicGeometry.ProEtale.wLocalSpace_pullback`: the w-local structure on `Y`.
* `AlgebraicGeometry.ProEtale.toX_isWLocalMap`: the canonical projection `X ×_{π₀(X)} T → X` is
  w-local.

## Implementation notes

The space `Y` and its projections are the canonical constructions of
`AlgebraicGeometry.ProEtale.ProfiniteBaseChangeOfComponentMap`. W-locality of `Y` is stated as a
class-valued theorem, so clients install the structure locally when they need it. W-locality of a
map is `AlgebraicGeometry.ProEtale.IsWLocalMap`, whose quasi-compactness clause is checked by
transporting the preimage of a quasi-compact open across the explicit product-subtype model of the
pullback.

## References

* [Stacks Project, Tag 096C](https://stacks.math.columbia.edu/tag/096C)
-/

@[expose] public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.ProEtale

/-- A profinite base change of the component map of a w-local space is w-local. -/
@[stacks 096C "pullback_w_local"]
theorem wLocalSpace_pullback (S : ProfiniteBaseChangeOfComponentMap.{u})
    [WLocalSpace S.X] : WLocalSpace S.Y := by
  refine WLocalSpace.mk (toSpectralSpace := spectralSpace_pullback S) ?_ ?_
  · intro x c c' hc hc' hxc hxc'
    have closed_X (y : S.Y) (h : IsClosed {y}) : S.toX y ∈ closedPoints S.X := by
      simpa only [← Set.mem_preimage, ← closedPoints_pullback S]
        using (mem_closedPoints_iff.mpr h)
    have ht (y : S.Y) (h : x ⤳ y) : S.toT x = S.toT y := (h.map S.toT.hom.continuous).eq
    exact congrArg Subtype.val
      ((isHomeomorph_toT_closedPointPreimage S).injective
        (show S.toT (⟨c, closed_X c hc⟩ : { y : S.Y // S.toX y ∈ closedPoints S.X }) =
          S.toT (⟨c', closed_X c' hc'⟩ : { y : S.Y // S.toX y ∈ closedPoints S.X }) from
          (ht c hxc).symm.trans (ht c' hxc')))
  · rw [closedPoints_pullback S]
    exact (WLocalSpace.isClosed_closedPoints (X := S.X)).preimage S.toX.hom.continuous

/-- Restricting the first factor of an explicit fibre product of topological spaces to a subset
of it. -/
private def fiberProductRestrictHomeomorph {X T Z : Type u}
    [TopologicalSpace X] [TopologicalSpace T] [TopologicalSpace Z]
    (f : X → Z) (g : T → Z) (U : Set X) :
    {p : {p : X × T // f p.1 = g p.2} // p.1.1 ∈ U} ≃ₜ
      {p : U × T // f p.1.1 = g p.2} where
  toEquiv :=
    { toFun := fun p => ⟨⟨⟨p.1.1.1, p.2⟩, p.1.1.2⟩, p.1.2⟩
      invFun := fun p => ⟨⟨⟨p.1.1.1, p.1.2⟩, p.2⟩, p.1.1.2⟩
      left_inv _ := rfl
      right_inv _ := rfl }
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- The preimage under the projection `Y → X` of a quasi-compact open of `X` is quasi-compact. -/
private theorem projection_preimage_isCompact (S : ProfiniteBaseChangeOfComponentMap.{u})
    {U : Set S.X} (_hUopen : IsOpen U) (hUcompact : IsCompact U) :
    IsCompact (S.toX ⁻¹' U) := by
  have hUcompactSpace : CompactSpace U := isCompact_iff_compactSpace.mp hUcompact
  let f : S.X → ConnectedComponents S.X := ConnectedComponents.mk
  let g : S.T → ConnectedComponents S.X := fun t => S.toConnectedComponents t
  have hpi : T2Space (ConnectedComponents S.X) :=
    (connectedComponents_isProfinite S.X).1
  have hclosed : IsClosed ({p : U × S.T | f p.1.1 = g p.2} : Set (U × S.T)) := by
    change IsClosed (fibreProduct (fun x : U => f x.1) g)
    exact fibreProduct_isClosed
      (ConnectedComponents.continuous_coe.comp continuous_subtype_val)
      S.toConnectedComponents.hom.continuous
  have hQ : CompactSpace {p : U × S.T // f p.1.1 = g p.2} :=
    isCompact_iff_compactSpace.mp hclosed.isCompact
  let e : S.Y ≃ₜ {p : S.X × S.T // f p.1 = g p.2} :=
    TopCat.homeoOfIso (TopCat.pullbackIsoProdSubtype S.componentMap S.toConnectedComponents)
  have heq (y : S.Y) : S.toX y ∈ U ↔ (e y).1.1 ∈ U := by
    change (pullback.fst S.componentMap S.toConnectedComponents) y ∈ U ↔
      ((TopCat.pullbackIsoProdSubtype S.componentMap S.toConnectedComponents).hom y).1.1 ∈ U
    rw [TopCat.pullbackIsoProdSubtype_hom_apply]
  let eU := e.subtype (p := fun y => S.toX y ∈ U)
    (q := fun y : {p : S.X × S.T // f p.1 = g p.2} => y.1.1 ∈ U) heq
  exact isCompact_iff_compactSpace.2
    (eU.trans (fiberProductRestrictHomeomorph f g U)).symm.compactSpace

/-- The projection to a w-local space from its profinite base change over the space of
connected components is a w-local map. -/
@[stacks 096C "pullback_projection_w_local"]
theorem toX_isWLocalMap (S : ProfiniteBaseChangeOfComponentMap.{u})
    [WLocalSpace S.X] : IsWLocalMap S.toX :=
  ⟨⟨S.toX.hom.continuous, fun _ => projection_preimage_isCompact S⟩,
    (closedPoints_pullback S).subset⟩

end AlgebraicGeometry.ProEtale
