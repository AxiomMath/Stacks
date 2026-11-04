module

public import StacksFrontier.Topology.Sheaves.Cohomology.SpectralSpaceLimit.ComparisonReduction

/-!
# Restricting a cohomology cocone, and the global clause of Tag 0A37 from the stage clause

Tag 0A37 has two colimit-comparison clauses: one over a quasi-compact open `U` of a stage `Xᵢ`,
with index category `Over i`, and a global one with index category the whole of `K`.  This file
shows that the **global clause is a formal consequence of the stage clause**, so that only one of
the two carries mathematical content.

The mechanism is restriction of a presentation along a functor.  A `CohomologyCocone` for a
diagram `E : K ⥤ SheafedSpace AddCommGrpCat` restricts along any `G : K' ⥤ K` to a
`CohomologyCocone` for `G ⋙ E`: its cohomology diagram is `G.op ⋙ D.diagram` and every one of
its fields is the corresponding field of `D` read at `G.obj k'`, because `(G ⋙ E).map a` is
`E.map (G.map a)` and `(c.whisker G).π.app k'` is `c.π.app (G.obj k')` on the nose.  When `G.op`
is a final functor the restricted comparison cocone is a colimit cocone exactly when the original
one is, and `CohomologyCocone.isIso_comparison_iff_nonempty_isColimit` turns that into a statement
about the two comparisons.

Applied with `G = Over.forget i` — initial because `K` is cofiltered, so `G.op` is final — and
`U = ⊤`, this gives the reduction: the open cone `(S.globalOpenCone c).whisker (Over.forget i)` is
*equal*, not merely isomorphic, to `S.stageOpenCone c i ⊤`, since `(Opens.map f).obj ⊤ = ⊤` holds
by `rfl`, and `⊤` is quasi-compact at every stage because a spectral space is compact.

## Main definitions

* `OpenCone.whisker`: an `OpenCone` for `E` and `c` restricts along `G : K' ⥤ K` to one for
  `G ⋙ E` and `c.whisker G`.
* `CohomologyCocone.whisker`: the same for a presentation of the cohomology cocone.

## Main results

* `CohomologyCocone.isIso_comparison_of_whisker`: if `G.op` is final, invertibility of the
  comparison of the restricted presentation implies invertibility of the original one.
* `SpectralAbelianSheafSystem.isIso_comparison_global_of_stage`: **the global
  colimit-comparison clause of Tag 0A37 follows from the quasi-compact-open one.**  So the stage
  clause is the only one of the two with mathematical content.

## Implementation notes

The reduction is stated at the universes `v = v' = u` to which the two colimit-comparison clauses
of Tag 0A37 have to be restated (see the implementation notes of
`StacksDraft.Ch20.Sec16.Tag0A37ColimitComparison`), because
`CohomologyCocone.isIso_comparison_iff_nonempty_isColimit` needs the colimit of the cohomology
diagram to exist in `AddCommGrpCat.{u}` for both index shapes.  `OpenCone.whisker`,
`CohomologyCocone.whisker` and `CohomologyCocone.isIso_comparison_of_whisker` are stated at
independent universes, the last one carrying the two colimit-existence hypotheses explicitly.

The hypothesis of `isIso_comparison_global_of_stage` is the stage clause *for every
presentation*, which is exactly how the clause is stated in the tagged statement: the presentation is an
explicit argument with the chosen one as its default value.  The stage index `i` used in the
proof is arbitrary — any object of `K` will do, and a cofiltered category has one.

## References

* [Stacks Project, Tag 0A37](https://stacks.math.columbia.edu/tag/0A37)
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite TopologicalSpace AlgebraicGeometry

universe u v v' w w'

namespace Stacks.Cohomology.SpectralLimit

variable {K : Type v} [Category.{v'} K]
    {E : K ⥤ SheafedSpace.{_, _, u} AddCommGrpCat.{u}} {c : Cone E}

/-- **Restriction of a compatible family of opens along a functor.**  The opens of the restricted
diagram are the opens of the original one at the image objects, and the open on the cone point is
unchanged: `(G ⋙ E).map a` is `E.map (G.map a)` and `(c.whisker G).π.app k'` is
`c.π.app (G.obj k')`, so the two inequalities are instances of the original ones. -/
def OpenCone.whisker {K' : Type w} [Category.{w'} K'] (O : OpenCone E c) (G : K' ⥤ K) :
    OpenCone (G ⋙ E) (c.whisker G) where
  obj k' := O.obj (G.obj k')
  map_le a := O.map_le (G.map a)
  pt := O.pt
  leg_le k' := O.leg_le (G.obj k')

namespace CohomologyCocone

variable {O : OpenCone E c} {p : ℕ}

/-- **Restriction of a presentation of the cohomology cocone along a functor.**  The cohomology
diagram is restricted to `G.op ⋙ D.diagram` and every other field is the corresponding field of
`D` read at the image object.  All the identifications are definitional: the spaces, the opens,
the transition maps and the cone legs of the restricted data are literally those of `D`, so the
`IsCohomologyMap` conditions are the original ones at `G.map a` and `G.obj k'`. -/
def whisker {K' : Type w} [Category.{w'} K'] (D : CohomologyCocone E c O p) (G : K' ⥤ K) :
    CohomologyCocone (G ⋙ E) (c.whisker G) (O.whisker G) p where
  diagram := G.op ⋙ D.diagram
  objIso k' := D.objIso (G.obj k')
  objDerivedIso k' := D.objDerivedIso (G.obj k')
  vertexDerivedIso := D.vertexDerivedIso
  map_eq a := D.map_eq (G.map a)
  ι := { app := fun k' => D.ι.app (op (G.obj k'.unop))
         naturality := fun _ _ α => D.ι.naturality (G.op.map α) }
  ι_eq k' := D.ι_eq (G.obj k')

/-- The comparison cocone of a restricted presentation is the restriction of the comparison
cocone.  Both have vertex the cohomology of the sheaf on the cone point and send `k'` to the
component of `D.ι` at `G.obj k'`, so this holds by `rfl`. -/
theorem cocone_whisker {K' : Type w} [Category.{w'} K'] (D : CohomologyCocone E c O p)
    (G : K' ⥤ K) : (D.whisker G).cocone = Cocone.whisker G.op D.cocone := rfl

/-- **Invertibility of the comparison passes from a restriction along a final functor to the
whole diagram.**  By `isIso_comparison_iff_nonempty_isColimit` each side says that the
corresponding comparison cocone is a colimit cocone, and a cocone whose restriction along a final
functor is a colimit cocone is itself one
(`CategoryTheory.Functor.Final.isColimitWhiskerEquiv`). -/
theorem isIso_comparison_of_whisker {K' : Type w} [Category.{w'} K'] (G : K' ⥤ K) [G.op.Final]
    [HasColimitsOfShape Kᵒᵖ AddCommGrpCat.{u}] [HasColimitsOfShape K'ᵒᵖ AddCommGrpCat.{u}]
    (D : CohomologyCocone E c O p) (h : IsIso (D.whisker G).comparison) : IsIso D.comparison := by
  refine (isIso_comparison_iff_nonempty_isColimit D).2 ?_
  have h' := ((isIso_comparison_iff_nonempty_isColimit (D.whisker G)).1 h).some
  rw [cocone_whisker] at h'
  exact ⟨Functor.Final.isColimitWhiskerEquiv G.op D.cocone h'⟩

end CohomologyCocone

namespace SpectralAbelianSheafSystem

section General

variable {K : Type v} [Category.{v'} K] [IsCofiltered K]
  (S : SpectralAbelianSheafSystem.{u, v, v'} K)

/-- **The global open cone of Tag 0A37, restricted along `Over.forget i`, is the stage open cone
at `U = ⊤`.**  The opens of the stage cone are `(Opens.map (S.E.map A.hom).hom.base).obj ⊤` and
`(Opens.map (c.π.app i).hom.base).obj ⊤`, and the inverse image of `⊤` is `⊤` by `rfl`; the two
inequality fields are propositions. -/
theorem globalOpenCone_whisker (c : Cone S.E) (i : K) :
    (S.globalOpenCone c).whisker (Over.forget i) = S.stageOpenCone c i ⊤ := rfl

/-- The whole of a stage is quasi-compact: a spectral space is compact. -/
theorem isCompact_top (i : K) : IsCompact ((⊤ : Opens (S.E.obj i)) : Set (S.E.obj i)) := by
  have : SpectralSpace ((S.E.obj i : TopCat.{u}) : Type u) := S.spectralSpace i
  have : CompactSpace ((S.E.obj i : TopCat.{u}) : Type u) := inferInstance
  simpa using isCompact_univ

end General

section Reduction

variable {K : Type u} [SmallCategory K] [IsCofiltered K]
  (S : SpectralAbelianSheafSystem.{u, u, u} K)

/-- **The global colimit-comparison clause of Tag 0A37 follows from the quasi-compact-open
one.**  Pick any stage `i` — a cofiltered category is nonempty — and apply the stage clause at
that stage with `U = ⊤`, which is quasi-compact because a spectral space is compact.  The stage
presentation used is the restriction of the given global one along `Over.forget i`, whose open
cone is the stage open cone at `⊤` by `globalOpenCone_whisker`; and `Over.forget i` is initial
because `K` is cofiltered, so its opposite is final and
`CohomologyCocone.isIso_comparison_of_whisker` applies.

So of the two colimit-comparison clauses of Tag 0A37 only the stage clause carries mathematical
content.  Both are stated here at the universes `v = v' = u` to which they have to be restated. -/
theorem isIso_comparison_global_of_stage (c : Cone S.E) (p : ℕ)
    (hstage : ∀ (i : K) (U : Opens (S.E.obj i)) (_ : IsCompact (U : Set (S.E.obj i)))
      (D : CohomologyCocone ((Over.forget i) ⋙ S.E) (c.whisker (Over.forget i))
        (S.stageOpenCone c i U) p), IsIso D.comparison)
    (D : CohomologyCocone S.E c (S.globalOpenCone c) p) : IsIso D.comparison := by
  have hne : Nonempty K := IsCofiltered.nonempty
  obtain ⟨i⟩ := hne
  exact CohomologyCocone.isIso_comparison_of_whisker (Over.forget i) D
    (hstage i ⊤ (S.isCompact_top i) (D.whisker (Over.forget i)))

end Reduction

end SpectralAbelianSheafSystem

end Stacks.Cohomology.SpectralLimit

end
