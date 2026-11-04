module

public import StacksFrontier.AlgebraicGeometry.GroupScheme.Subgroups.Defs
public import StacksFrontier.AlgebraicGeometry.Properties.ReducedClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.ReducedProduct
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The reduction of a group scheme over a perfect field

The reduced closed subscheme underlying a group scheme over a perfect field inherits a
group-scheme structure, and its inclusion is the inclusion of a closed subgroup scheme.

## Main results

* `AlgebraicGeometry.exists_closedSubgroupScheme_reduction`: the reduction of a group scheme
  over a perfect field is a closed subgroup scheme.

## Implementation notes

The reduction is the closed subscheme cut out by the vanishing ideal of the whole underlying
space. The conclusion identifies this subscheme and its inclusion, over the base, with the
underlying scheme and inclusion of the subgroup scheme.

Perfectness of the field enters through the fact that a fibre product of reduced schemes over a
perfect field is reduced.

## References

* [Stacks Project, Tag 047R](https://stacks.math.columbia.edu/tag/047R)
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonObj
  CategoryTheory.GrpObj CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

universe u

/-- The reduction of a group scheme over a perfect field is a closed subgroup scheme. -/
@[stacks 047R,
  sga "3 VIA 0.2" "perfect k: G_red ≤ G",
  sga "3 VIA 5.6" "more general",
  sga "3 VIB 12.1" "Over the base field",
  sga "3 XII 1.0" "partial"]
theorem exists_closedSubgroupScheme_reduction
    {k : Type u} [Field k] [PerfectField k]
    (G : Grp (Over (Spec (.of k)))) :
    let I := Scheme.IdealSheafData.vanishingIdeal (⊤ : Closeds G.X.left)
    ∃ H : ClosedSubgroupScheme G,
      ∃ e : Over.mk (I.subschemeι ≫ G.X.hom) ≅ H.carrier.X,
        Over.homMk I.subschemeι = e.hom ≫ H.ι.hom.hom := by
  let I := Scheme.IdealSheafData.vanishingIdeal (⊤ : Closeds G.X.left)
  let H : Over (Spec (.of k)) := Over.mk (I.subschemeι ≫ G.X.hom)
  let j : H ⟶ G.X := Over.homMk I.subschemeι rfl
  have : IsClosedImmersion j.left := by
    show IsClosedImmersion I.subschemeι
    infer_instance
  have : IsReduced H.left :=
    Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal (⊤ : Closeds G.X.left)
  have : IsReduced ((𝟙_ (Over (Spec (.of k)))).left) := by
    show IsReduced (Spec (.of k))
    infer_instance
  have : IsReduced ((H ⊗ H).left) := by
    show IsReduced (pullback H.hom H.hom)
    exact isReduced_pullback_over_perfectField H.hom H.hom
  have hfactor {Y : Over (Spec (.of k))} [IsReduced Y.left]
      (f : Y ⟶ G.X) : ∃ g : Y ⟶ H, g ≫ j = f := by
    obtain ⟨g, hg⟩ :=
      (Scheme.IdealSheafData.exists_lift_subschemeι_iff_range_subset_support I f.left).2
        (by simp [I])
    refine ⟨Over.homMk g ?_, ?_⟩
    · show g ≫ I.subschemeι ≫ G.X.hom = Y.hom
      exact ((reassoc_of% hg) G.X.hom).trans f.w
    · exact Over.OverMorphism.ext hg
  obtain ⟨K, e, heq⟩ := (isClosedSubgroupScheme_iff_factor G j).2
    ⟨hfactor η[G.X], hfactor ((j ⊗ₘ j) ≫ μ[G.X]), hfactor (j ≫ ι[G.X])⟩
  exact ⟨K, e, by simpa [H, j] using heq⟩

end AlgebraicGeometry

end
