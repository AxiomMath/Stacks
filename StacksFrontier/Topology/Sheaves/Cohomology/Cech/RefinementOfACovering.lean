module

public import StacksFrontier.Topology.Dimension.DimensionFunctionObstruction
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Refining a family of opens, on Čech cochains and on first Čech cohomology

Let `U : I → Opens X` and `V : K → Opens X` be two families of opens on a topological space `X`,
and let `r : K → I` be a *refinement function*: a choice, for every member of `V`, of a member of
`U` containing it. Precomposing the index tuples with `r` and restricting the sections along the
resulting inclusions of intersections carries a Čech cochain of `U` to one of `V`. This file
builds that map, shows it commutes with the Čech differential of Stacks 01FJ, and deduces the
induced maps on Čech `1`-cocycles and on first Čech cohomology.

The Čech complex is the one of Stacks 01FJ (`CechCochains.Cochain`, `CechCochains.cechD`) and
its first cohomology is `CechCochains.CechH1`.

## Main definitions

* `CechCochains.refinementMap`: the map of Čech cochains induced by a refinement function, in every
  degree.
* `CechCochains.refinementCocycles1`: its restriction to the Čech `1`-cocycles.
* `CechCochains.refinementCechH1`: the induced map `Ȟ¹(𝒰, ℱ) → Ȟ¹(𝒱, ℱ)`.

## Main results

* `CechCochains.refinementMap_cechD`: the refinement map is a map of complexes.
* `CechCochains.refinementCechH1_cls`: it computes the class of the refined cocycle.
* `CechCochains.eq_iSup_inf_of_eq_iSup`: the pairwise intersections of two families covering an
  open again cover it, so any two families admit a common refinement.

## Implementation notes

A refinement function is extra data, not a property: the map of Čech complexes depends on the
chosen `r`, which is why `r` and the inequalities `V k ≤ U (r k)` are explicit arguments
throughout rather than packaged into a `Prop`.

The inequalities between intersections are the only geometric input, and they are proof
irrelevant, so no transport of sections along equalities of opens occurs anywhere below: an
inequality `inter V j ≤ inter U (r ∘ j)` is a packaged proof and two such are interchangeable.

## References

* [Stacks Project, Tag 01FJ](https://stacks.math.columbia.edu/tag/01FJ)
* [Stacks Project, Tag 03F4](https://stacks.math.columbia.edu/tag/03F4)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace

universe v w w' uX

namespace CechCochains

variable {X : TopCat.{uX}} {I : Type w} {K : Type w'} (U : I → Opens X) (V : K → Opens X)
  (r : K → I) (hr : ∀ k, V k ≤ U (r k)) (ℱ : TopCat.Presheaf AddCommGrpCat.{v} X)

include hr in
/-- The intersection over a tuple of members of the refining family is contained in the
intersection over the members of the refined family that the refinement function chooses. -/
theorem inter_le_inter_comp {p : ℕ} (j : Fin p → K) : inter V j ≤ inter U (r ∘ j) :=
  iInf_mono fun k => hr (j k)

include hr in
/-- **The map of Čech cochains induced by a refinement.** A degree-`p` cochain of `U` is sent to
the cochain of `V` whose value on `V_{j₀} ∩ ⋯ ∩ V_{j_p}` is the value of the original on
`U_{r j₀} ∩ ⋯ ∩ U_{r j_p}`, restricted along the inclusion the refinement provides. This is the
map `γ` of Stacks 03F4 for the Čech complex of Stacks 01FJ. -/
def refinementMap (p : ℕ) : Cochain U ℱ p →+ Cochain V ℱ p where
  toFun s := fun j => restr ℱ (inter_le_inter_comp U V r hr j) (s (r ∘ j))
  map_zero' := by funext j; exact map_zero _
  map_add' s t := by funext j; exact map_add _ _ _

/-- The value of the refined cochain on a tuple of members of `V` is the restriction of the value
of the original cochain on the tuple of members of `U` that the refinement function chooses. -/
@[simp] theorem refinementMap_apply (p : ℕ) (s : Cochain U ℱ p) (j : Fin (p + 1) → K) :
    refinementMap U V r hr ℱ p s j =
      restr ℱ (inter_le_inter_comp U V r hr j) (s (r ∘ j)) := rfl

/-- **The refinement map is a map of complexes.** Both sides are the alternating sum of the faces
of the refined cochain, restricted to the intersection over the refining tuple; the two nested
restrictions compose to the same single restriction. -/
@[ega "III 6.6.7" "partial"]
theorem refinementMap_cechD (p : ℕ) (s : Cochain U ℱ p) :
    refinementMap U V r hr ℱ (p + 1) (cechD U ℱ p s) =
      cechD V ℱ p (refinementMap U V r hr ℱ p s) := by
  funext j
  rw [refinementMap_apply, cechD_apply, cechD_apply, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [map_zsmul, refinementMap_apply, restr_restr, restr_restr]
  rfl

include hr in
/-- **A refinement carries Čech `1`-cocycles to Čech `1`-cocycles**, the refinement map being a
map of complexes. -/
def refinementCocycles1 : cocycles1 U ℱ →+ cocycles1 V ℱ where
  toFun c := ⟨refinementMap U V r hr ℱ 1 (c : Cochain U ℱ 1), by
    rw [mem_cocycles1_iff, ← refinementMap_cechD,
      (mem_cocycles1_iff U ℱ (c : Cochain U ℱ 1)).mp c.2, map_zero]⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' c c' := Subtype.ext (map_add _ _ _)

/-- The underlying cochain of the refinement of a Čech `1`-cocycle is the refinement of its
underlying cochain. -/
@[simp] theorem refinementCocycles1_coe (c : cocycles1 U ℱ) :
    ((refinementCocycles1 U V r hr ℱ c : cocycles1 V ℱ) : Cochain V ℱ 1) =
      refinementMap U V r hr ℱ 1 (c : Cochain U ℱ 1) := rfl

/-- A refinement carries Čech `1`-coboundaries to Čech `1`-coboundaries: the refinement of a
`0`-cochain whose coboundary is the given cocycle has the refined cocycle as its coboundary. -/
theorem refinementCocycles1_mem_coboundaries1 (c : cocycles1 U ℱ)
    (hc : c ∈ coboundaries1 U ℱ) :
    refinementCocycles1 U V r hr ℱ c ∈ coboundaries1 V ℱ := by
  obtain ⟨t, ht⟩ := AddMonoidHom.mem_range.mp (AddSubgroup.mem_comap.mp hc)
  have ht' : cechD U ℱ 0 t = (c : Cochain U ℱ 1) := ht
  refine AddSubgroup.mem_comap.mpr (AddMonoidHom.mem_range.mpr
    ⟨refinementMap U V r hr ℱ 0 t, ?_⟩)
  rw [← refinementMap_cechD, ht']
  rfl

include hr in
/-- **The map on first Čech cohomology induced by a refinement.** -/
def refinementCechH1 : CechH1 U ℱ →+ CechH1 V ℱ :=
  QuotientAddGroup.lift (coboundaries1 U ℱ)
    ((QuotientAddGroup.mk' (coboundaries1 V ℱ)).comp (refinementCocycles1 U V r hr ℱ))
    fun c hc => QuotientAddGroup.eq_zero_iff _ |>.mpr
      (refinementCocycles1_mem_coboundaries1 U V r hr ℱ c hc)

/-- The refinement map on first Čech cohomology sends the class of a cocycle to the class of the
refined cocycle. -/
@[simp] theorem refinementCechH1_cls (c : cocycles1 U ℱ) :
    refinementCechH1 U V r hr ℱ (cls U ℱ c) = cls V ℱ (refinementCocycles1 U V r hr ℱ c) := rfl

/-- **Any two families of opens covering an open admit a common refinement**: the family of
pairwise intersections covers the same open, and is contained in each member of either family
through the corresponding projection. -/
theorem eq_iSup_inf_of_eq_iSup {I' : Type*} {W : Opens X} {U' : I' → Opens X}
    (hU : W = ⨆ i, U i) (hU' : W = ⨆ i', U' i') :
    W = ⨆ p : I × I', U p.1 ⊓ U' p.2 := by
  refine le_antisymm (fun y hy => ?_) (iSup_le fun p => le_trans inf_le_left (hU.ge.trans' ?_))
  · obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (hU.le hy)
    obtain ⟨i', hi'⟩ := Opens.mem_iSup.mp (hU'.le hy)
    exact Opens.mem_iSup.mpr ⟨(i, i'), hi, hi'⟩
  · exact le_iSup U p.1

end CechCochains

end
