module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.Existence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedInternalHom
import StacksCore.Tactic.StacksAttribute

/-! # The source of derived evaluation on a ringed site

Let `(C, O)` be a ringed site and let `A`, `B`, `C` be complexes of `O`-modules with `A` K-flat
and `C` K-injective. The source of the derived evaluation morphism of Stacks 0A97 is the
derived tensor product

`RSheafHom(B, C) ⊗^L_O A`

and this file identifies it with the class of the ordinary total tensor complex
`Tot(SheafHom(B, C) ⊗_O A)`, which is what makes the evaluation morphism of complexes
(Stacks 0A92) compute the derived one.

The identification is the composite of two comparisons: the derived internal Hom of a
K-injective target is the class of the internal Hom complex
(`AlgebraicGeometry.RingedSite.derivedSheafHomComparison`), and the derived tensor product with
a K-flat right factor is the class of the total tensor complex, for an *arbitrary* left factor
(`Stacks.SheafOfModules.DerivedTensorProduct.comparisonRight` of Stacks 06YU). The second is
why no flatness is required of the internal Hom complex itself.

## Main definitions

* `AlgebraicGeometry.RingedSite.derivedSheafHomTensorComparison`: the comparison.

## Implementation notes

The complexes are those of `SheafOfModules.{u} X.ringSheaf`, which is the spelling of the
internal Hom complex of Stacks 0A8Z, while the derived tensor product of Stacks 06YU is stated
over `AlgebraicGeometry.RingedSite.Modules X`, i.e. over
`Stacks.SheafOfModules.Tensor.ringSheaf X.O`. The two sheaves of rings are definitionally equal —
  both forget
the commutativity of the structure sheaf, and the sheaf conditions agree by proof irrelevance —
and both spellings are abbreviations, so the comparison needs no transport and no transparency
option.

The target is the total tensor complex `Stacks.SheafOfModules.Tensor.tensorComplex` of Stacks 06YM,
  which
sheafifies the objectwise tensor product in each bidegree and then forms the direct sums. It is
*not* the complex `AlgebraicGeometry.RingedSite.tensorTotal` of
`StacksDraft.Ch21.Sec34.TensorTotalComplex`, which forms the direct sums at the presheaf level
and sheafifies once per degree; the two are isomorphic because sheafification preserves
coproducts, but that comparison is not available on this branch.

## References

* [Stacks Project, Tag 0A97](https://stacks.math.columbia.edu/tag/0A97)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u d

namespace AlgebraicGeometry.RingedSite

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]
  [HasDerivedCategory.{d}
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O))]

/-- **The source of derived evaluation is the total tensor complex.** For a K-flat complex `A`
and a K-injective complex `C`, the derived tensor product of the derived internal Hom
`RSheafHom(B, C)` with the class of `A` is the class of the total tensor complex of the
internal Hom complex `SheafHom(B, C)` with `A`. -/
def derivedSheafHomTensorComparison
    (A B C : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hA : Stacks.SheafOfModules.IsKFlat X.O A) [C.IsKInjective] :
    ((Stacks.SheafOfModules.derivedTensorProductFunctor.{u, u, d} X).obj
          (((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj B))).obj
            (DerivedCategory.Q.obj C))).obj (DerivedCategory.Q.obj A) ≅
      DerivedCategory.Q.obj
        (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj (sheafHomComplex X B C).obj).obj A)
          :=
  ((Stacks.SheafOfModules.derivedTensorProductFunctor.{u, u, d} X).mapIso
      (derivedSheafHomComparison X B C)).app (DerivedCategory.Q.obj A) ≪≫
    (Stacks.SheafOfModules.canonicalDerivedTensorProduct.{u, u, d} X).comparisonRight
      (sheafHomComplex X B C).obj A hA

end AlgebraicGeometry.RingedSite

end
