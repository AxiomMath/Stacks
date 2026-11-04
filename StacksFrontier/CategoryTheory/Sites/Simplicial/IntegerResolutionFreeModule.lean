module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.FreeIntegerPresheaf
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.OnAbelianSheaves
public import StacksFrontier.CategoryTheory.Sites.Simplicial.ComponentSheafify
public import StacksFrontier.CategoryTheory.Sites.Simplicial.IntegerResolution

/-!
# The lower shriek image of the constant integer sheaf, as a free sheaf of modules

Let `S` be a simplicial-site situation. The integral resolution of Stacks 09WI presents the lower
shriek image `g_{n!}Z` of the constant integer sheaf of the degree-`n` component as the
sheafification of the free abelian presheaf on the presheaf of `n`-simplices
(`resolutionDegreeIso'`). Abelian sheaves on the total site are the sheaves of modules over the
constant sheaf of rings `Z` (`Stacks.DerivedTensor.AbelianSheaves.moduleEquivalence`), and under
that equivalence `g_{n!}Z` is the sheafification of the *free presheaf of modules* on the
presheaf of `n`-simplices.

That is the shape the projection formula `g_{n!}Z ⊗_Z F ≅ bar_n(F)` of Stacks 0D9E needs: the
tensor product of sheaves of modules is the sheafification of the tensor product of the
underlying presheaves of modules (Stacks 0GMW), and the tensor product of a *free* presheaf of
modules with a presheaf of modules is a copower (`CategoryTheory.freeTensorCopowerIso`).

## Main results

* `CategoryTheory.SimplicialSiteSituation.componentIntegerSheafIsoSheafifyFreeModule`:
  **`g_{n!}Z` is the underlying abelian sheaf of the sheafification of the free presheaf of
  modules on the presheaf of `n`-simplices.**
* `CategoryTheory.SimplicialSiteSituation.moduleEquivalenceInverseComponentIntegerSheafIso`: the
  same read in sheaves of modules over the constant sheaf of rings `Z`.

## Implementation notes

The sheafifiability of abelian sheaves on the total site and the identification of the morphisms
sheafification inverts are the theorems of
`StacksFrontier.CategoryTheory.Sites.Simplicial.ComponentSheafify`, activated here as local
instances rather than restated.

The free presheaf of modules is taken over `PresheafOfModules.intRingPresheaf`, the constant
presheaf of rings `Z`, whose sheafification is the constant sheaf of rings `Z`: the scalars are
`Stacks.DerivedTensor.AbelianSheaves.intRingSheafScalars`, which is locally bijective there.

## References

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

/-- **The lower shriek image of the constant integer sheaf is a sheafified free sheaf of
modules.** Its underlying abelian sheaf is the sheafification of the free presheaf of modules on
the presheaf of `n`-simplices, over the constant presheaf of rings `Z`. -/
def componentIntegerSheafIsoSheafifyFreeModule :
    (SheafOfModules.toSheaf (intRings S.totalTopology)).obj
        ((PresheafOfModules.sheafification (intRingSheafScalars S.totalTopology)).obj
          (PresheafOfModules.freeObj (stdSimplexPresheaf' S n))) ≅
      componentIntegerSheaf S n :=
  PresheafOfModules.sheafifyFreeObjIso (intRingSheafScalars S.totalTopology)
      (stdSimplexPresheaf' S n) ≪≫
    resolutionDegreeIso' S n

/-- The lower shriek image of the constant integer sheaf, read in sheaves of modules over the
constant sheaf of rings `Z`: it is the sheafification of the free presheaf of modules on the
presheaf of `n`-simplices. -/
def moduleEquivalenceInverseComponentIntegerSheafIso :
    (moduleEquivalence S.totalTopology).inverse.obj (componentIntegerSheaf S n) ≅
      (PresheafOfModules.sheafification (intRingSheafScalars S.totalTopology)).obj
        (PresheafOfModules.freeObj (stdSimplexPresheaf' S n)) :=
  (moduleEquivalence S.totalTopology).inverse.mapIso
      (componentIntegerSheafIsoSheafifyFreeModule S n).symm ≪≫
    ((moduleEquivalence S.totalTopology).unitIso.app _).symm

end CategoryTheory.SimplicialSiteSituation

end
