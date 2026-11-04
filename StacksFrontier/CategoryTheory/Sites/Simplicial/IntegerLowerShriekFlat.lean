module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatRetract
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatSheafification
public import StacksFrontier.CategoryTheory.Sites.Simplicial.IntegerResolutionFreeModule

/-!
# The lower shriek image of the constant integer sheaf is flat

Let `S` be a simplicial-site situation and `n` a simplicial degree. The lower shriek image
`g_{n!}ℤ` of the constant integer sheaf of the degree-`n` component is, read in sheaves of
modules over the constant sheaf of rings `ℤ`, the sheafification of the free presheaf of modules
on the presheaf of `n`-simplices (`moduleEquivalenceInverseComponentIntegerSheafIso`). A free
presheaf of modules is objectwise free, hence objectwise flat, so Stacks 0GN1 makes its
sheafification flat.

Flatness is what lets the derived tensor product `g_{n!}ℤ ⊗^L_ℤ -` be computed by the ordinary
tensor product `g_{n!}ℤ ⊗_ℤ -`, which is the identification the projection formula of
Stacks 0D9E runs on.

## Main results

* `CategoryTheory.SimplicialSiteSituation.isFlat_moduleEquivalenceInverseComponentIntegerSheaf`:
  **`g_{n!}ℤ` is a flat sheaf of modules over the constant sheaf of rings `ℤ`.**

## References

* [Stacks Project, Tag 0GN1](https://stacks.math.columbia.edu/tag/0GN1)
* [Stacks Project, Tag 09WI](https://stacks.math.columbia.edu/tag/09WI)
* [Stacks Project, Tag 0D9E](https://stacks.math.columbia.edu/tag/0D9E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

universe u

namespace CategoryTheory.SimplicialSiteSituation

open Stacks.DerivedTensor.AbelianSheaves

attribute [local instance] hasSheafifyTotal
  CategoryTheory.GrothendieckTopology.wEqualsLocallyBijective_addCommGrpCat

variable (S : SimplicialSiteSituation.{u}) (n : SimplexCategory)

/-- The sheafification of the free presheaf of modules on the presheaf of `n`-simplices is a
flat sheaf of modules over the constant sheaf of rings `ℤ`: over every object its sections are
a free, hence flat, module over the integers, so Stacks 0GN1 applies with the trivial covering
of each object. -/
theorem isFlat_sheafification_freeObj_stdSimplexPresheaf :
    AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u}
      (O := intRingSheaf S.totalTopology)
      ((PresheafOfModules.sheafification (intRingSheafScalars S.totalTopology)).obj
        (PresheafOfModules.freeObj (stdSimplexPresheaf' S n))) := by
  refine Stacks.SheafOfModules.FlatSheafification.isFlat_sheafification_of_locally_objectwise_flat
    S.totalTopology
    (O := (Functor.const S.totalCategoryᵒᵖ).obj (CommRingCat.of (ULift.{u} ℤ)))
    (Osharp := intRingSheaf S.totalTopology)
    (intRingSheafScalars S.totalTopology)
    (PresheafOfModules.freeObj (stdSimplexPresheaf' S n)) fun U => ?_
  refine ⟨PUnit.{u + 1}, fun _ => U, fun _ => 𝟙 U, ?_, fun _ => ?_⟩
  · rw [show Sieve.ofArrows (fun _ : PUnit.{u + 1} => U) (fun _ => 𝟙 U) = ⊤ from
      Sieve.id_mem_iff_eq_top.1 (Sieve.ofArrows_mk _ _ PUnit.unit)]
    exact S.totalTopology.top_mem U
  · exact Module.Flat.finsupp _

/-- **The lower shriek image of the constant integer sheaf is flat.** Read in sheaves of modules
over the constant sheaf of rings `ℤ`, `g_{n!}ℤ` is the sheafification of the free presheaf of
modules on the presheaf of `n`-simplices, and that sheafification is flat. -/
theorem isFlat_moduleEquivalenceInverseComponentIntegerSheaf :
    AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u}
      (O := intRingSheaf S.totalTopology)
      ((moduleEquivalence S.totalTopology).inverse.obj (componentIntegerSheaf S n)) :=
  Stacks.SheafOfModules.FlatRetract.isFlat_of_iso.{u, u, u} _
    (moduleEquivalenceInverseComponentIntegerSheafIso S n).symm
    (isFlat_sheafification_freeObj_stdSimplexPresheaf S n)

end CategoryTheory.SimplicialSiteSituation

end
