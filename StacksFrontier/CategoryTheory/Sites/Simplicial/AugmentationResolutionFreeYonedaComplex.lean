module

public import StacksFrontier.CategoryTheory.Sites.Simplicial.AugmentationResolutionFreeYonedaSimplicialComparison
public import StacksFrontier.CategoryTheory.Sites.Simplicial.AugmentationResolutionQuasiIso

/-!
# The `a_!`-image of the complex of Stacks 0D78 at `ℤ_V^♯`, as a chain complex

The `a_!`-image of the complex of Stacks 0D78 resolving `a^{-1}ℤ_V^♯` is isomorphic to the
complex of free abelian sheaves on `p ↦ h_V × F(K_p)`, the alternating face map complex of
`CategoryTheory.SimplicialSemiRepresentable.freeYonedaSimplicial`, and so is exact in a degree as
soon as that complex is.

## Main definitions

* `CategoryTheory.SimplicialSemiRepresentable.resolutionComplexLowerShriekFreeYonedaIso`: the
  `a_!`-image of the complex of Stacks 0D78 at `ℤ_V^♯` is the complex of free abelian sheaves on
  `p ↦ h_V × F(K_p)`.

## Main results

* `CategoryTheory.SimplicialSemiRepresentable.exactAt_map_resolutionComplex`: the `a_!`-image of
  the complex of Stacks 0D78 at `ℤ_V^♯` is exact in a degree as soon as the complex of free
  abelian sheaves on `p ↦ h_V × F(K_p)` is.

## References

* [Stacks Project, Tag 0D78](https://stacks.math.columbia.edu/tag/0D78)
* [Stacks Project, Tag 01GE](https://stacks.math.columbia.edu/tag/01GE)
* [Stacks Project, Tag 0D8G](https://stacks.math.columbia.edu/tag/0D8G)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.SimplicialSiteSituation
open scoped Simplicial

universe u

namespace CategoryTheory.SimplicialSemiRepresentable

open SemiRepresentable

attribute [local instance] GrothendieckTopology.hasSheafify_addCommGrpCat

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
  (K : SimplicialObject (FormalCoproduct.{u} C)) [J.toCoverage.HasPullbacks]
  [J.WEqualsLocallyBijective (Type u)] (V : C)

/-- **The `a_!`-image of the complex of Stacks 0D78 at `ℤ_V^♯` is the complex of free abelian
sheaves on `p ↦ h_V × F(K_p)`.** -/
def resolutionComplexLowerShriekFreeYonedaIso :
    ((augmentationAbelianLowerShriek J K).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (Augmentation.resolutionComplex (situation J K) (Cat.of C) J (situationAugmentation J K)
          (Stacks.Cohomology.CohomologyPresheaf.freeYonedaSheaf J V)) ≅
      (AlgebraicTopology.alternatingFaceMapComplex (Sheaf J AddCommGrpCat.{u})).obj
        (freeYonedaSimplicial J K V) :=
  (AlgebraicTopology.alternatingFaceMapComplexCompMapHomologicalComplexIso
        (augmentationAbelianLowerShriek J K)).app _ ≪≫
    (AlgebraicTopology.alternatingFaceMapComplex (Sheaf J AddCommGrpCat.{u})).mapIso
      (resolutionLowerShriekFreeYonedaSimplicialIso J K V)

/-- **The `a_!`-image of the complex of Stacks 0D78 at `ℤ_V^♯` is exact in a degree as soon as the
complex of free abelian sheaves on `p ↦ h_V × F(K_p)` is.** -/
theorem exactAt_map_resolutionComplex (n : ℕ)
    (hex : ((AlgebraicTopology.alternatingFaceMapComplex (Sheaf J AddCommGrpCat.{u})).obj
      (freeYonedaSimplicial J K V)).ExactAt n) :
    (((augmentationAbelianLowerShriek J K).mapHomologicalComplex (ComplexShape.down ℕ)).obj
      (Augmentation.resolutionComplex (situation J K) (Cat.of C) J (situationAugmentation J K)
        (Stacks.Cohomology.CohomologyPresheaf.freeYonedaSheaf J V))).ExactAt n :=
  HomologicalComplex.ExactAt.of_iso hex (resolutionComplexLowerShriekFreeYonedaIso J K V).symm

end CategoryTheory.SimplicialSemiRepresentable

end
