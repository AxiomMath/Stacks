module

public import Mathlib.Topology.Homeomorph.Lemmas
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Algebraization.DistanceFunction
public import StacksFrontier.Topology.Dimension.Catenary

/-!
# Distance from a closed subset under open restriction

Restricting a Noetherian scheme to an open subscheme cannot decrease the distance
from the restricted closed subset.

## Main results

* `Stacks.Algebraization.distanceFunction_le_of_isOpenImmersion`
  compares the distance functions along an open immersion.

## Implementation notes

An open subscheme is represented by an open immersion, and its intersection with
the closed subset is the inverse-image closed subset. The source is Noetherian
because it is an open subscheme of a Noetherian scheme. A system on the open
subscheme is pushed forward by taking closures of its terms, which preserves every
codimension because an open embedding identifies the irreducible closed subsets above
a nonempty one with those of the source.

## References

* [Stacks Project, Tag 0EIY](https://stacks.math.columbia.edu/tag/0EIY)
-/

@[expose] public section

open AlgebraicGeometry TopologicalSpace

universe u

namespace Stacks.Algebraization

open Topology IrreducibleClosedsCodim

/-- Taking closures of images along an open embedding preserves and reflects the order. -/
private theorem map_le_map_iff {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    (f : A → B) (hf : IsOpenEmbedding f) (c d : IrreducibleCloseds A) :
    IrreducibleCloseds.map f hf.continuous c ≤ IrreducibleCloseds.map f hf.continuous d ↔
      c ≤ d :=
  (IrreducibleCloseds.orderIsoOfIsOpenEmbedding f hf).map_rel_iff

/-- An open embedding preserves the codimension between two irreducible closed subsets.
Intermediate irreducible closed subsets between the two image sets still meet the open image,
so they all come from the source. -/
private theorem topCodim_map_openEmbedding {A B : Type*} [TopologicalSpace A]
    [TopologicalSpace B] (f : A → B) (hf : IsOpenEmbedding f)
    (a b : IrreducibleCloseds A) :
    topCodim (IrreducibleCloseds.map f hf.continuous a)
      (IrreducibleCloseds.map f hf.continuous b) = topCodim a b := by
  let e := IrreducibleCloseds.map f hf.continuous
  let E := IrreducibleCloseds.orderIsoOfIsOpenEmbedding f hf
  have hle := map_le_map_iff f hf
  have hinj : Function.Injective e := fun c d h =>
    le_antisymm ((hle c d).mp h.le) ((hle d c).mp h.ge)
  have hstrict : StrictMono e := fun c d h =>
    lt_of_le_of_ne ((hle c d).mpr h.le) (fun hcd => h.ne (hinj hcd))
  have hreflect : ∀ c d, e c < e d → c < d := fun c d h =>
    lt_of_le_of_ne ((hle c d).mp h.le) (fun hcd => h.ne (congrArg e hcd))
  have hpreimage (z : IrreducibleCloseds B) (hz : e a ≤ z) :
      ∃ c : IrreducibleCloseds A, e c = z := by
    obtain ⟨x, hx⟩ := a.isIrreducible.nonempty
    let z' : {w : IrreducibleCloseds B // (f ⁻¹' (w : Set B)).Nonempty} :=
      ⟨z, ⟨x, hz (subset_closure ⟨x, hx, rfl⟩)⟩⟩
    exact ⟨E.symm z', congrArg Subtype.val (E.apply_symm_apply z')⟩
  apply le_antisymm
  · rw [topCodim_le_iff]
    intro q hqh hql
    have hmem : ∀ i, ∃ c, e c = q i := fun i =>
      hpreimage _ (hqh.symm.trans_le (q.monotone (Fin.zero_le i)))
    choose c hc using hmem
    have hcm : StrictMono c := fun i j hij =>
      hreflect _ _ ((hc i).trans_lt ((q.strictMono hij).trans_eq (hc j).symm))
    have hhead : (LTSeries.mk q.length c hcm).head = a := hinj ((hc 0).trans hqh)
    have hlast : (LTSeries.mk q.length c hcm).last = b := hinj ((hc (Fin.last _)).trans hql)
    simpa using length_le_topCodim a b (LTSeries.mk q.length c hcm) hhead hlast
  · rw [topCodim_le_iff]
    intro p hph hpl
    let p' := p.map e hstrict
    have hhead : p'.head = e a := by simp [p', hph]
    have hlast : p'.last = e b := by simp [p', hpl]
    simpa [p'] using length_le_topCodim (e a) (e b) p' hhead hlast

/-- Extend a distance system along an open immersion by taking the closures of its terms. -/
private def extendDistanceSystem {U Y : Scheme.{u}} (j : U ⟶ Y) [IsOpenImmersion j]
    [IsNoetherian Y] [IsNoetherian U] (Z : Closeds Y) (x : U)
    (s : DistanceSystem U (Z.preimage j.continuous) x) :
    DistanceSystem Y Z (j x) := by
  classical
  refine ⟨s.k,
    (fun i => IrreducibleCloseds.map j.base j.isOpenEmbedding.continuous (s.V i)),
    (fun i => IrreducibleCloseds.map j.base j.isOpenEmbedding.continuous (s.W i)),
    fun i => (map_le_map_iff j.base j.isOpenEmbedding _ _).mpr (s.V_le_W i),
    fun i => (map_le_map_iff j.base j.isOpenEmbedding _ _).mpr (s.V_next_le_W i),
    ?_, ?_⟩
  · rw [IrreducibleCloseds.coe_map]
    exact closure_minimal (Set.image_subset_iff.mpr s.V_zero_subset) Z.isClosed
  · rw [IrreducibleCloseds.coe_map, s.W_last_eq_closure, closure_image_closure j.continuous]
    simp

private theorem extendDistanceSystem_weight {U Y : Scheme.{u}} (j : U ⟶ Y)
    [IsOpenImmersion j] [IsNoetherian Y] [IsNoetherian U]
    (Z : Closeds Y) (x : U) (s : DistanceSystem U (Z.preimage j.continuous) x) :
    (extendDistanceSystem j Z x s).weight = s.weight := by
  classical
  simp [DistanceSystem.weight, DistanceSystem.upCodimension,
    DistanceSystem.downCodimension, extendDistanceSystem,
    topCodim_map_openEmbedding j.base j.isOpenEmbedding]
  rfl

/-- **Stacks Project, Tag 0EIY.** Restriction to an open subscheme does not
decrease the distance from a closed subset. -/
@[stacks 0EIY "open_restriction_ge"]
public theorem distanceFunction_le_of_isOpenImmersion
    {U Y : Scheme.{u}} (j : U ⟶ Y) [IsOpenImmersion j] [IsNoetherian Y]
    (Z : Closeds Y) (x : U) :
    letI : IsNoetherian U :=
      { toIsLocallyNoetherian := isLocallyNoetherian_of_isOpenImmersion j
        toCompactSpace := (j.isOpenEmbedding.isInducing.noetherianSpace).compactSpace }
    distanceFunction Y Z (j x) ≤ distanceFunction U (Z.preimage j.continuous) x := by
  have : IsNoetherian U :=
    { toIsLocallyNoetherian := isLocallyNoetherian_of_isOpenImmersion j
      toCompactSpace := (j.isOpenEmbedding.isInducing.noetherianSpace).compactSpace }
  classical
  by_cases hU : (connectedComponent x ∩ (Z.preimage j.continuous : Set U)).Nonempty
  · have hY : (connectedComponent (j x) ∩ (Z : Set Y)).Nonempty := by
      rcases hU with ⟨y, hy, hZ⟩
      refine ⟨j y, j.continuous.image_connectedComponent_subset x ⟨y, hy, rfl⟩, ?_⟩
      simpa using hZ
    rw [distanceFunction_eq_iInf_of_nonempty Y Z (j x) hY,
      distanceFunction_eq_iInf_of_nonempty U (Z.preimage j.continuous) x hU]
    exact le_iInf fun s => (iInf_le _ (extendDistanceSystem j Z x s)).trans_eq
      (congrArg (fun n : ℕ => (n : ℕ∞)) (extendDistanceSystem_weight j Z x s))
  · rw [distanceFunction_eq_top_of_disjoint U (Z.preimage j.continuous) x hU]
    exact le_top

end Stacks.Algebraization
