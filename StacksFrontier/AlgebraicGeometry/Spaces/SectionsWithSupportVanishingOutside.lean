module

public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SectionsWithSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleGlobalSectionsTerminal

/-!
# Sections with support vanish away from the support

Let `X` be an algebraic space over a scheme `S`, let `T` be a set of points of `X` and let `F`
be an abelian sheaf on the small étale site of `X`.  The subsheaf `ℋ_T(F)` of sections with
support in `T` of Stacks 0A4L has no nonzero sections over a chart whose image misses `T`: such
a section has empty support, and a section with empty support is zero.

This file records that vanishing, and propagates it from the étale *scheme* charts to the
objects of the spaces-étale site of Stacks 03G0, where the excision argument of **Stacks 0A4P**
needs it: the second member of the excision covering of
`StacksFrontier/AlgebraicGeometry/Spaces/ExcisionCoveringOverSubspace.lean` is the open complement
of the subspace, which is not a scheme chart.

## Main results

* `AlgebraicGeometry.Space.isZero_sectionsWithSupportSheaf_of_subset_compl`: the sections with
  support in `T` over a chart whose image misses `T` form the zero group.
* `AlgebraicGeometry.Space.isZero_obj_of_subset_compl_of_chartwise`: a spaces-étale sheaf
  vanishing on every chart whose image misses `T` vanishes on every object of the spaces-étale
  site whose image misses `T`.
* `AlgebraicGeometry.Space.isZero_obj_of_spacesEtaleChartRestriction_iso`: a spaces-étale sheaf
  whose restriction to the charts is the subsheaf of sections with support in `T` vanishes on
  every object of the spaces-étale site whose image misses `T`.

## Implementation notes

The chart statement is the computation already carried out for the empty set of points in
`AlgebraicGeometry.Space.isZero_sectionsWithSupportSheaf_empty`, with the hypothesis weakened
from `T = ∅` to the image of the chart being disjoint from `T`: what the argument uses is only
that the preimage of `T` under the structure morphism of the chart is empty.

The passage to an arbitrary object `V` of the spaces-étale site is
`AlgebraicGeometry.Space.isZero_obj_of_isZero_chart` applied to the one-element covering of `V`
by a scheme chart of Stacks 03H7, `AlgebraicGeometry.Space.exists_etaleChart_singleton_covering`.
The image of that chart lies in the image of `V`, because the chart is a morphism of the site,
hence over `X`; so the hypothesis transfers to it.

## References

* [Stacks Project, Tag 03G0](https://stacks.math.columbia.edu/tag/03G0)
* [Stacks Project, Tag 03H7](https://stacks.math.columbia.edu/tag/03H7)
* [Stacks Project, Tag 04KA](https://stacks.math.columbia.edu/tag/04KA)
* [Stacks Project, Tag 0A4L](https://stacks.math.columbia.edu/tag/0A4L)
* [Stacks Project, Tag 0A4P](https://stacks.math.columbia.edu/tag/0A4P)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

section Charts

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

/-- **Sections with support in `T` vanish over a chart whose image misses `T`.**  A section
over such a chart is supported on the preimage of `T`, which is empty, so it has empty support
and is therefore zero by `AlgebraicGeometry.Space.eq_zero_of_supportOfSection_eq_empty`.

This is `AlgebraicGeometry.Space.isZero_sectionsWithSupportSheaf_empty` with the hypothesis
`T = ∅` replaced by the only consequence of it that the argument uses. -/
theorem isZero_sectionsWithSupportSheaf_of_subset_compl (T : Set (points B S hS X))
    (F : Sheaf (SmallEtale.topology B S hS X) AddCommGrpCat.{v}) (U : SmallEtale B S hS X)
    (hU : Set.range (pointsMap B S hS
      (yoneda.obj ((SmallEtale.toOver B S hS X).obj U)) U.obj.hom) ⊆ Tᶜ) :
    IsZero ((sectionsWithSupportSheaf B S hS X T F).obj.obj (op U)) := by
  have hempty : pointsMap B S hS
      (yoneda.obj ((SmallEtale.toOver B S hS X).obj U)) U.obj.hom ⁻¹' T = ∅ :=
    Set.eq_empty_iff_forall_notMem.2 fun x hx => hU ⟨x, rfl⟩ hx
  rw [IsZero.iff_id_eq_zero]
  ext σ
  refine Subtype.ext (eq_zero_of_supportOfSection_eq_empty U σ.1 ?_)
  have hσ : supportOfSection B S hS X F U σ.1 ⊆
      pointsMap B S hS _ U.obj.hom ⁻¹' T := σ.2
  rw [hempty] at hσ
  exact Set.subset_empty_iff.1 hσ

end Charts

section Objects

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS)

/-- The image of a scheme chart mapping to an object of the spaces-étale site lies in the image
of that object: the chart is a morphism of the site, so its structure morphism to `X` factors
through the structure morphism of the object. -/
theorem range_pointsMap_le_of_hom {V : SpacesEtale B S hS X} {U : SmallEtale B S hS X.1}
    (g : (comparisonFunctor B S hS X).obj U ⟶ V) :
    Set.range (pointsMap B S hS
        (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj U)) U.obj.hom) ⊆
      Set.range (pointsMap B S hS ((SpacesEtale.toSpaces B S hS X).obj V).1 V.1.hom.hom) := by
  have hw : ((SpacesEtale.toSpaces B S hS X).map g).hom ≫ V.1.hom.hom = U.obj.hom :=
    congrArg (fun q => q.hom) ((SpacesEtale.inclusion B S hS X).map g).w
  rintro x ⟨y, rfl⟩
  exact ⟨pointsMap B S hS _ ((SpacesEtale.toSpaces B S hS X).map g).hom y,
    (pointsMap_comp_apply B S hS _ _ y).symm.trans
      (congrArg (fun q => pointsMap B S hS _ q y) hw)⟩

/-- **A spaces-étale sheaf vanishing on the charts missing `T` vanishes on the objects
missing `T`.**  Every object of the spaces-étale site is covered by a single étale scheme chart
whose structure morphism is surjective on points (Stacks 03H7), and that chart has its image
inside the image of the object, hence also missing `T`; vanishing then propagates by
`AlgebraicGeometry.Space.isZero_obj_of_isZero_chart`. -/
theorem isZero_obj_of_subset_compl_of_chartwise (T : Set (points B S hS X.1))
    (Q : Sheaf (SpacesEtale.topology B S hS X) AddCommGrpCat.{v})
    (hchart : ∀ U : SmallEtale B S hS X.1,
      Set.range (pointsMap B S hS
          (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj U)) U.obj.hom) ⊆ Tᶜ →
        IsZero (Q.obj.obj (op ((comparisonFunctor B S hS X).obj U))))
    (V : SpacesEtale B S hS X)
    (hV : Set.range (pointsMap B S hS
      ((SpacesEtale.toSpaces B S hS X).obj V).1 V.1.hom.hom) ⊆ Tᶜ) :
    IsZero (Q.obj.obj (op V)) := by
  obtain ⟨U, g, -, hsurj, -⟩ := exists_etaleChart_singleton_covering B S hS X V
  exact isZero_obj_of_isZero_chart B S hS X Q g hsurj
    (hchart U ((range_pointsMap_le_of_hom B S hS X g).trans hV))

/-- **The spaces-étale avatar of the sections with support in `T` vanishes away from `T`.**
Let `Q` be a sheaf on the spaces-étale site of `X` whose restriction to the étale scheme charts
is the subsheaf of sections with support in `T` of an abelian sheaf `F`.  Then `Q` vanishes on
every object of the spaces-étale site whose image misses `T`.

This is the input the excision step of Stacks 0A4P needs for the open complement of the
subspace and for the overlaps involving it. -/
theorem isZero_obj_of_spacesEtaleChartRestriction_iso (T : Set (points B S hS X.1))
    (F : Sheaf (SmallEtale.topology B S hS X.1) AddCommGrpCat.{v})
    (Q : Sheaf (SpacesEtale.topology B S hS X) AddCommGrpCat.{v})
    (e : (spacesEtaleChartRestriction B S hS X).obj Q ≅
      (sectionsWithSupport.{v} B S hS X.1 T).obj F)
    (V : SpacesEtale B S hS X)
    (hV : Set.range (pointsMap B S hS
      ((SpacesEtale.toSpaces B S hS X).obj V).1 V.1.hom.hom) ⊆ Tᶜ) :
    IsZero (Q.obj.obj (op V)) :=
  isZero_obj_of_subset_compl_of_chartwise B S hS X T Q
    (fun U hU => IsZero.of_iso
      (isZero_sectionsWithSupportSheaf_of_subset_compl B S hS X.1 T F U hU)
      (((sheafSections (SmallEtale.topology B S hS X.1) AddCommGrpCat.{v}).obj
        (op U)).mapIso e)) V hV

end Objects

end AlgebraicGeometry.Space

end
