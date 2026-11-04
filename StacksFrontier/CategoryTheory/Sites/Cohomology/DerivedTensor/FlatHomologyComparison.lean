module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ExistenceOnARingedSite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.FlatnessAndRightExactness
public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.ResolutionsOnARingedSite
public import StacksFrontier.Homology.KFlat.BifunctorSingleSecondFactor

/-!
# Tensoring with a flat sheaf of modules commutes with cohomology

Let `R` be a sheaf of commutative rings on a small site, let `N` be a flat sheaf of
`R`-modules and let `L` be a cochain complex of sheaves of `R`-modules.  Then

`H^i(L ⊗^L_R N) ≅ H^i(L) ⊗_R N`

for every `i`.  Flatness enters twice: it makes `N` placed in a single degree a K-flat complex,
so the derived tensor product is computed by the termwise tensor product `p ↦ L^p ⊗_R N`, and it
makes `- ⊗_R N` an exact functor, so that termwise tensor product commutes with cohomology.

## Main definitions

* `Stacks.ExactHomology.mapHomologicalComplexHomologyIso`: an exact functor commutes with the
  cohomology of a cochain complex.
* `Stacks.DerivedTensor.RingedSite.homologyTensorFlatIso`: the isomorphism above.

## Implementation notes

*Why the first half is abstract.*  "An exact functor commutes with cohomology" is a statement
about abelian categories with no sheaf content, and over abstract categories the structure
sheaves of the ambient sites never appear, so no rewrite runs into their definitional-but-not-
syntactic spellings.  The sheaf-level statement is an instantiation.

*The flat factor is on the right.*  The K-flat comparison with no flatness hypothesis on the
other variable is `DerivedTensorProduct.comparisonRight`, and the total complex of a bifunctor
whose second argument is concentrated in one degree is
`CochainComplex.KFlatBifunctor.totalSingleIso`; both take the distinguished factor second.  The
version with the flat factor on the left follows from the braiding of
`Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.braidingIso`.

*The flatness input is public.*  `Stacks.SheafOfModules.KFlatResolution.kFlat_single_of_isFlat`
is the public form of "a flat module in a single degree is K-flat"; the copy inside
`DerivedTensor/Tor.lean` is `private`.

## References

* [Stacks Project, Tag 06YQ](https://stacks.math.columbia.edu/tag/06YQ)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

/-! ### An exact functor commutes with cohomology -/

namespace Stacks.ExactHomology

universe v₁ v₂ u₁ u₂

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] {B : Type u₂} [Category.{v₂} B] [Abelian B]

/-- **A functor preserving homology commutes with the cohomology of a cochain complex**:
`H^i(F(L)) ≅ F(H^i(L))`, where `F(L)` is the degreewise image of `L`. -/
def mapHomologicalComplexHomologyIso (F : A ⥤ B) [F.Additive] [F.PreservesHomology]
    (L : CochainComplex A ℤ) (i : ℤ) :
    ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj L).homology i ≅ F.obj (L.homology i) :=
  ShortComplex.homologyMapIso (Iso.refl _) ≪≫ (L.sc i).mapHomologyIso F

/-- `mapHomologicalComplexHomologyIso` with exactness supplied in the `exactFunctor` form. -/
def mapHomologicalComplexHomologyIsoOfExact (F : A ⥤ B) [F.Additive]
    (hF : exactFunctor A B F) (L : CochainComplex A ℤ) (i : ℤ) :
    ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj L).homology i ≅ F.obj (L.homology i) :=
  let h := (exactFunctor_iff F).1 hF
  let := h.1
  let := h.2
  mapHomologicalComplexHomologyIso F L i

end Stacks.ExactHomology

/-! ### The sheaf-level statement -/

namespace Stacks.DerivedTensor.RingedSite

universe u d

variable {C : Type u} [SmallCategory.{u} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{u})
variable [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasDerivedCategory.{d} (Modules R)]
variable
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} R).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} R).obj M).Additive]
  [∀ (K L : CochainComplex (Modules R) ℤ),
    HomologicalComplex.HasMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor R)
      (ComplexShape.up ℤ)]

/-- **Tensoring with a flat sheaf of modules commutes with cohomology:**

`H^i(L ⊗^L_R N) ≅ H^i(L) ⊗_R N`

for `N` a flat sheaf of `R`-modules, `L` a cochain complex of sheaves of `R`-modules, and every
`i`.  The derived tensor product is computed by the termwise one because `N` in a single degree
is K-flat, and the termwise one commutes with cohomology because `- ⊗_R N` is exact. -/
def homologyTensorFlatIso (N : Modules R)
    (hN : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := R) N)
    (L : CochainComplex (Modules R) ℤ) (i : ℤ) :
    (DerivedCategory.homologyFunctor (Modules R) i).obj
        (((canonicalDerivedTensorProduct R).tensor.obj (DerivedCategory.Q.obj L)).obj
          (DerivedCategory.Q.obj
            ((HomologicalComplex.single (Modules R) (ComplexShape.up ℤ) 0).obj N))) ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor R).obj (L.homology i)).obj N :=
  let hKF := Stacks.SheafOfModules.KFlatResolution.kFlat_single_of_isFlat R N hN 0
  (DerivedCategory.homologyFunctor (Modules R) i).mapIso
      ((canonicalDerivedTensorProduct R).comparisonRight L _ hKF) ≪≫
    (DerivedCategory.homologyFunctorFactors (Modules R) i).app _ ≪≫
    (HomologicalComplex.homologyFunctor (Modules R) (ComplexShape.up ℤ) i).mapIso
      (CochainComplex.KFlatBifunctor.totalSingleIso
        (Stacks.SheafOfModules.Tensor.sheafTensor R) L N) ≪≫
    Stacks.ExactHomology.mapHomologicalComplexHomologyIsoOfExact
      ((Stacks.SheafOfModules.Tensor.sheafTensor R).flip.obj N)
      (Stacks.SheafOfModules.exactFunctor_sheafTensorFlip_of_isFlat R N hN) L i

end Stacks.DerivedTensor.RingedSite

end
