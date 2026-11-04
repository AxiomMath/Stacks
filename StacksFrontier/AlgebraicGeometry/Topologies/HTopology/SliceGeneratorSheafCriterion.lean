module

public import StacksFrontier.AlgebraicGeometry.Topologies.HTopology.GeneratorAlmostBlowUpReduction

/-!
# Stacks 0EVI on a slice of the big h site

The slice `(Sch/S)_h / U` of the big h site at an object `U` is the big h site of the underlying
scheme of `U`, through `CategoryTheory.Over.iteratedSliceEquiv`, and the localized topology
corresponds to the h topology of that big site.  So the sufficiency direction of Stacks 0EVI
applies on the slice: a presheaf of sets on `Over U` whose restriction along the equivalence
satisfies the four conditions of Stacks 0EVI is a sheaf for the localized h topology.

## Main results

* `AlgebraicGeometry.BigHOver.isSheaf_over_of_generatorConditions`.

## References

* [Stacks Project, Tag 0EVI](https://stacks.math.columbia.edu/tag/0EVI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace AlgebraicGeometry.BigHOver

variable {B : BigHSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Stacks 0EVI on a slice.** A presheaf of sets on the slice of the big h site at `U` is a sheaf
for the localized h topology as soon as its restriction to the big h site of the underlying
scheme of `U` satisfies the four conditions of Stacks 0EVI. -/
theorem isSheaf_over_of_generatorConditions (U : BigHOver B S hS) (G : (Over U)ᵒᵖ ⥤ Type v)
    (h1 : IsZariskiSheaf B U.left.obj U.left.property ((Over.iteratedSliceBackward U).op ⋙ G))
    (h2 : IsAffineFlatProperFinitePresentationSheaf B U.left.obj U.left.property
      ((Over.iteratedSliceBackward U).op ⋙ G))
    (h3 : IsOneGeneratorAlmostBlowUpSheaf B U.left.obj U.left.property
      ((Over.iteratedSliceBackward U).op ⋙ G))
    (h4 : IsTwoGeneratorAlmostBlowUpSheaf B U.left.obj U.left.property
      ((Over.iteratedSliceBackward U).op ⋙ G)) :
    Presheaf.IsSheaf ((BigHOver.topology B S hS).over U) G := by
  have hH := (isSheaf_iff_zariski_and_flatProper_and_generatorSquares B U.left.obj
    U.left.property ((Over.iteratedSliceBackward U).op ⋙ G)).2 ⟨h1, h2, h3, h4⟩
  rw [isSheaf_iff_isSheaf_of_type] at hH ⊢
  have h := (Over.iteratedSliceForward U).op_comp_isSheaf_of_isSheaf_type
    (J := (B.topology.over (B.obj S hS)).over U) (K := B.topology.over U.left) hH
  refine (Presieve.isSheaf_iso _ ?_ h)
  exact Functor.isoWhiskerRight (NatIso.op (Over.iteratedSliceEquiv U).unitIso) G

end AlgebraicGeometry.BigHOver
