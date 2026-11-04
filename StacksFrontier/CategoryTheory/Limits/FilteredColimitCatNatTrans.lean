module

public import StacksFrontier.CategoryTheory.Limits.FilteredColimitCatStages

/-!
# A natural transformation out of a filtered colimit of categories is determined at the stages

A colimit in `Cat` is a quotient, so a natural transformation between two functors out of it is
*not* in general determined by its components at the colimit inclusions: nothing says every
object of the colimit is the image of one. For a *filtered* index category it is — on the nose,
not merely up to isomorphism (`CategoryTheory.Cat.exists_stage_obj_of_colimit`) — and this file
records the resulting extensionality principles for natural transformations and for natural
isomorphisms.

This is what makes the pinned 2-cell of the square of Stacks 0CMR determinate: the condition
pinning it only prescribes its components at the colimit generators, and these lemmas turn that
into an equality of 2-cells.

## Main results

* `CategoryTheory.Cat.natTrans_ext_of_colimit`
* `CategoryTheory.Cat.natIso_ext_of_colimit`

## References

* [Stacks Project, Tag 0CMR](https://stacks.math.columbia.edu/tag/0CMR)
* [Stacks Project, Tag 0CMW](https://stacks.math.columbia.edu/tag/0CMW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Cat

universe u v w uD vD

section Stages

variable {I : Type v} [Category.{w} I] [IsFiltered I]
  {X : I ⥤ Cat.{max u v w, max u v w}} [HasColimit X]
  [HasColimit (X ⋙ CategoryTheory.nerveFunctor.{max u v w, max u v w})]
  {D : Type uD} [Category.{vD} D] {F G : ↑(colimit X) ⥤ D}

/-- **A natural transformation out of a filtered colimit in `Cat` is determined by its components
at the colimit inclusions.** -/
lemma natTrans_ext_of_colimit (σ τ : F ⟶ G)
    (h : ∀ (i : I) (a : X.obj i), σ.app ((colimit.ι X i).toFunctor.obj a) =
      τ.app ((colimit.ι X i).toFunctor.obj a)) :
    σ = τ := by
  ext z
  obtain ⟨i, a, rfl⟩ := exists_stage_obj_of_colimit.{u, v, w} X z
  exact h i a

/-- **A natural isomorphism out of a filtered colimit in `Cat` is determined by its components at
the colimit inclusions.** -/
lemma natIso_ext_of_colimit (ε ε' : F ≅ G)
    (h : ∀ (i : I) (a : X.obj i), (ε.hom.app ((colimit.ι X i).toFunctor.obj a)) =
      (ε'.hom.app ((colimit.ι X i).toFunctor.obj a))) :
    ε = ε' :=
  Iso.ext (natTrans_ext_of_colimit.{u, v, w} ε.hom ε'.hom h)

end Stages

end CategoryTheory.Cat

end
