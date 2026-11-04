module

public import StacksFrontier.Algebra.Homology.ShortComplex.MapHomologyComp

/-!
# Preservation of the left homology of one short complex composes

`StacksFrontier/Algebra/Homology/ShortComplex/MapHomologyComp.lean` proves that a composite of two
functors which preserve homology preserves homology. This file proves the pointwise analogue.

## Main results

* `CategoryTheory.Functor.preservesLeftHomologyOf_comp`: a composite of functors preserves the
  left homology of a short complex `S` if the first preserves that of `S` and the second that of
  its image. This is the hypothesis `CategoryTheory.Functor.PreservesLeftHomologyOf` available
  when neither functor is exact everywhere.
-/

@[expose] public section

namespace CategoryTheory

open Category Limits

namespace Functor

/-- **Preservation of the left homology of a short complex composes.**  If `F` preserves the
left homology of `S` and `G` preserves the left homology of `S.map F`, then `F ⋙ G` preserves
the left homology of `S`.

Only the chosen left homology data of `S` is tested, by
`CategoryTheory.Functor.PreservesLeftHomologyOf.mk'`:  `F ⋙ G` has to carry the kernel of `S.g`
and the cokernel of `S.leftHomologyData.f'` to the kernel and the cokernel of their images,
which is the hypothesis on `F` followed by the hypothesis on `G` read at the image data
`S.leftHomologyData.map F`.

This is the weak, pointwise analogue of `CategoryTheory.Functor.preservesHomology_comp`, and it
is what supplies the third hypothesis of
`CategoryTheory.Functor.rightDerivedCompIsoOfPreservesLeftHomology_comp` from the other two. -/
lemma preservesLeftHomologyOf_comp {C D E : Type*} [Category* C] [Category* D] [Category* E]
    [HasZeroMorphisms C] [HasZeroMorphisms D] [HasZeroMorphisms E] (F : C ⥤ D) (G : D ⥤ E)
    [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms] (S : ShortComplex C)
    [S.HasLeftHomology] [F.PreservesLeftHomologyOf S] [G.PreservesLeftHomologyOf (S.map F)] :
    (F ⋙ G).PreservesLeftHomologyOf S := by
  have e {X Y : C} (f : X ⟶ Y) : parallelPair f 0 ⋙ F ≅ parallelPair (F.map f) 0 :=
    parallelPair.ext (Iso.refl _) (Iso.refl _) (by simp) (by simp)
  have hg : PreservesLimit (parallelPair S.g 0) (F ⋙ G) := by
    have : PreservesLimit (parallelPair S.g 0) F :=
      ShortComplex.LeftHomologyData.IsPreservedBy.hg S.leftHomologyData F
    have : PreservesLimit (parallelPair (F.map S.g) 0) G :=
      ShortComplex.LeftHomologyData.IsPreservedBy.hg (S.leftHomologyData.map F) G
    have : PreservesLimit (parallelPair S.g 0 ⋙ F) G := preservesLimit_of_iso_diagram G (e _).symm
    exact comp_preservesLimit F G
  have hf' : PreservesColimit (parallelPair S.leftHomologyData.f' 0) (F ⋙ G) := by
    have : PreservesColimit (parallelPair S.leftHomologyData.f' 0) F :=
      ShortComplex.LeftHomologyData.IsPreservedBy.hf' S.leftHomologyData F
    have himg := ShortComplex.LeftHomologyData.IsPreservedBy.hf' (S.leftHomologyData.map F) G
    rw [ShortComplex.LeftHomologyData.map_f'] at himg
    have : PreservesColimit (parallelPair (F.map S.leftHomologyData.f') 0) G := himg
    have : PreservesColimit (parallelPair S.leftHomologyData.f' 0 ⋙ F) G :=
      preservesColimit_of_iso_diagram G (e _).symm
    exact comp_preservesColimit F G
  have : S.leftHomologyData.IsPreservedBy (F ⋙ G) := ⟨hg, hf'⟩
  exact PreservesLeftHomologyOf.mk' (F ⋙ G) S.leftHomologyData

end Functor

end CategoryTheory

end
