module

public import StacksFrontier.CategoryTheory.CommutingSquares
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.Existence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TensorComplex.TotalComplexComparison

/-!
# The one-sided K-flat comparison, in the total-complex spelling, is natural in both variables

Let `X` be a ringed site and let `A` be a K-flat complex of `O`-modules. The one-sided
comparison of Stacks 06YU identifies `Q A ⊗^L_O Q B` with the class of the tensor-product
complex of `A` and `B` for an *arbitrary* `B`, and `tensorTotalIsoTensorComplex` identifies that
complex with the total complex `Tot(A ⊗_O B)`. This file records the naturality of the composite
identification in each variable, together with the consequence in each case that tensoring a
quasi-isomorphism is again a quasi-isomorphism.

In the right variable no K-flatness is required of `B` or `B'`: that is the point of the
one-sided comparison, and it is what makes those statements applicable to the internal Hom
complexes that arise in the diagonal morphism of Stacks 0BYS. In the left variable both
complexes must be K-flat, the comparison existing only there.

## Main results

* `AlgebraicGeometry.RingedSite.comparisonLeft_tensorTotal_naturality_right`: the composite
  identification is natural in the arbitrary right complex.
* `AlgebraicGeometry.RingedSite.isIso_Q_map_tensorTotalMap_right`: if `Q g` is invertible and
  `A` is K-flat then `Q (Tot(𝟙_A ⊗ g))` is invertible.
* `AlgebraicGeometry.RingedSite.comparisonLeft_tensorTotal_naturality_left` and
  `AlgebraicGeometry.RingedSite.isIso_Q_map_tensorTotalMap_left`: the same two statements in the
  K-flat left variable, where both complexes have to be K-flat.

## Implementation notes

The naturality is assembled from two commuting squares: the `comparisonLeft_naturality` field of
the derived tensor product datum, instantiated at the identity of `A` in its left slot — that
field is stated for a morphism in each slot at once, so the right-hand naturality is the
special case `(𝟙 A, g)` — and the naturality of `tensorTotalIsoTensorComplex`.

The statement is right-associated, `α ≫ u₁ ≫ u₂ = v₁ ≫ v₂ ≫ k`, rather than bracketed as a
square. That is the form in which it is rewritten at the call sites, where the identification
appears as one leg of a longer composite.

The left-hand naturality is also proved inside the module constructing the diagonal of
Stacks 0BYS, but privately, so it is not reusable from outside; it is reproved here. The
right-hand case is not covered there at all.

## References

* [Stacks Project, Lemma 20.26.6 (Tag 06YU)](https://stacks.math.columbia.edu/tag/06YU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

namespace AlgebraicGeometry.RingedSite

universe u

attribute [local instance] ringSheafSectionsCommRing presheafOfModulesMonoidalCategory
  curriedTensorPreservesZeroMorphisms curriedTensorObjPreservesZeroMorphisms

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]
  [HasDerivedCategory
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O))]

/-- **The one-sided K-flat comparison, read on total complexes, is natural in the arbitrary
right complex.** No K-flatness is assumed of `B` or `B'`. -/
theorem comparisonLeft_tensorTotal_naturality_right
    (A : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    {B B' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (g : B ⟶ B')
    (hA : Stacks.SheafOfModules.IsKFlat X.O A) :
    ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj
            (DerivedCategory.Q.obj A)).map (DerivedCategory.Q.map g) ≫
        ((Stacks.SheafOfModules.canonicalDerivedTensorProduct X).comparisonLeft A B' hA).hom ≫
          DerivedCategory.Q.map (tensorTotalIsoTensorComplex X A B').inv =
      ((Stacks.SheafOfModules.canonicalDerivedTensorProduct X).comparisonLeft A B hA).hom ≫
        DerivedCategory.Q.map (tensorTotalIsoTensorComplex X A B).inv ≫
        DerivedCategory.Q.map (tensorTotalMap X (𝟙 A) g) := by
  have sq3 : ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj
            (DerivedCategory.Q.obj A)).map (DerivedCategory.Q.map g) ≫
        ((Stacks.SheafOfModules.canonicalDerivedTensorProduct X).comparisonLeft A B' hA).hom =
      ((Stacks.SheafOfModules.canonicalDerivedTensorProduct X).comparisonLeft A B hA).hom ≫
        DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap (𝟙 A) g
          (Stacks.SheafOfModules.Tensor.sheafTensor X.O) (ComplexShape.up ℤ)) := by
    simpa using (Stacks.SheafOfModules.canonicalDerivedTensorProduct X).comparisonLeft_naturality
      (𝟙 A) g hA hA
  have sq4 : DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap (𝟙 A) g
          (Stacks.SheafOfModules.Tensor.sheafTensor X.O) (ComplexShape.up ℤ)) ≫
        DerivedCategory.Q.map (tensorTotalIsoTensorComplex X A B').inv =
      DerivedCategory.Q.map (tensorTotalIsoTensorComplex X A B).inv ≫
        DerivedCategory.Q.map (tensorTotalMap X (𝟙 A) g) := by
    refine Eq.trans (Eq.trans (DerivedCategory.Q.map_comp _ _).symm ?_)
      (DerivedCategory.Q.map_comp _ _)
    exact congrArg DerivedCategory.Q.map
      (tensorTotalIsoTensorComplex_naturality X (𝟙 A) g).symm
  exact square_comp' sq3 sq4

/-- **Tensoring on the left with a K-flat complex preserves quasi-isomorphy in the right
slot.** -/
theorem isIso_Q_map_tensorTotalMap_right
    (A : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    {B B' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (g : B ⟶ B')
    (hA : Stacks.SheafOfModules.IsKFlat X.O A) (hg : IsIso (DerivedCategory.Q.map g)) :
    IsIso (DerivedCategory.Q.map (tensorTotalMap X (𝟙 A) g)) := by
  have := hg
  have h := comparisonLeft_tensorTotal_naturality_right X A g hA
  have h2 : IsIso (DerivedCategory.Q.map (tensorTotalIsoTensorComplex X A B).inv ≫
      DerivedCategory.Q.map (tensorTotalMap X (𝟙 A) g)) := by
    refine IsIso.of_isIso_fac_left
      (f := ((Stacks.SheafOfModules.canonicalDerivedTensorProduct X).comparisonLeft A B hA).hom)
      (h := ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj
          (DerivedCategory.Q.obj A)).map (DerivedCategory.Q.map g) ≫
        (((Stacks.SheafOfModules.canonicalDerivedTensorProduct X).comparisonLeft A B'
          hA).hom ≫
        DerivedCategory.Q.map (tensorTotalIsoTensorComplex X A B').inv)) (Eq.symm ?_)
    simpa using h
  exact IsIso.of_isIso_comp_left
    (DerivedCategory.Q.map (tensorTotalIsoTensorComplex X A B).inv) _

/-- **The one-sided K-flat comparison, read on total complexes, is natural in the K-flat left
complex.** Both complexes must be K-flat, the comparison being available only there. -/
theorem comparisonLeft_tensorTotal_naturality_left
    {A A₀ : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (hA : Stacks.SheafOfModules.IsKFlat X.O A)
    (hA₀ : Stacks.SheafOfModules.IsKFlat X.O A₀)
    (c : A ⟶ A₀)
    (Z : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    ((Stacks.SheafOfModules.derivedTensorProductFunctor X).map
            (DerivedCategory.Q.map c)).app (DerivedCategory.Q.obj Z) ≫
        ((Stacks.SheafOfModules.canonicalDerivedTensorProduct X).comparisonLeft A₀ Z hA₀).hom ≫
          DerivedCategory.Q.map (tensorTotalIsoTensorComplex X A₀ Z).inv =
      ((Stacks.SheafOfModules.canonicalDerivedTensorProduct X).comparisonLeft A Z hA).hom ≫
        DerivedCategory.Q.map (tensorTotalIsoTensorComplex X A Z).inv ≫
        DerivedCategory.Q.map (tensorTotalMap X c (𝟙 Z)) := by
  have sq3 : ((Stacks.SheafOfModules.derivedTensorProductFunctor X).map
            (DerivedCategory.Q.map c)).app (DerivedCategory.Q.obj Z) ≫
        ((Stacks.SheafOfModules.canonicalDerivedTensorProduct X).comparisonLeft A₀ Z hA₀).hom =
      ((Stacks.SheafOfModules.canonicalDerivedTensorProduct X).comparisonLeft A Z hA).hom ≫
        DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap c (𝟙 Z)
          (Stacks.SheafOfModules.Tensor.sheafTensor X.O) (ComplexShape.up ℤ)) := by
    simpa using (Stacks.SheafOfModules.canonicalDerivedTensorProduct X).comparisonLeft_naturality
      c (𝟙 Z) hA hA₀
  have sq4 : DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap c (𝟙 Z)
          (Stacks.SheafOfModules.Tensor.sheafTensor X.O) (ComplexShape.up ℤ)) ≫
        DerivedCategory.Q.map (tensorTotalIsoTensorComplex X A₀ Z).inv =
      DerivedCategory.Q.map (tensorTotalIsoTensorComplex X A Z).inv ≫
        DerivedCategory.Q.map (tensorTotalMap X c (𝟙 Z)) := by
    refine Eq.trans (Eq.trans (DerivedCategory.Q.map_comp _ _).symm ?_)
      (DerivedCategory.Q.map_comp _ _)
    exact congrArg DerivedCategory.Q.map
      (tensorTotalIsoTensorComplex_naturality X c (𝟙 Z)).symm
  exact square_comp' sq3 sq4

/-- **A quasi-isomorphism of K-flat complexes stays one after tensoring with an arbitrary
complex on the right.** -/
theorem isIso_Q_map_tensorTotalMap_left
    {A A₀ : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (hA : Stacks.SheafOfModules.IsKFlat X.O A)
    (hA₀ : Stacks.SheafOfModules.IsKFlat X.O A₀)
    (c : A ⟶ A₀) (hc : IsIso (DerivedCategory.Q.map c))
    (Z : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    IsIso (DerivedCategory.Q.map (tensorTotalMap X c (𝟙 Z))) := by
  have := hc
  have h := comparisonLeft_tensorTotal_naturality_left X hA hA₀ c Z
  have h2 : IsIso (DerivedCategory.Q.map (tensorTotalIsoTensorComplex X A Z).inv ≫
      DerivedCategory.Q.map (tensorTotalMap X c (𝟙 Z))) := by
    refine IsIso.of_isIso_fac_left
      (f := ((Stacks.SheafOfModules.canonicalDerivedTensorProduct X).comparisonLeft A Z hA).hom)
      (h := ((Stacks.SheafOfModules.derivedTensorProductFunctor X).map
          (DerivedCategory.Q.map c)).app (DerivedCategory.Q.obj Z) ≫
        (((Stacks.SheafOfModules.canonicalDerivedTensorProduct X).comparisonLeft A₀ Z
          hA₀).hom ≫
        DerivedCategory.Q.map (tensorTotalIsoTensorComplex X A₀ Z).inv)) (Eq.symm ?_)
    simpa using h
  exact IsIso.of_isIso_comp_left
    (DerivedCategory.Q.map (tensorTotalIsoTensorComplex X A Z).inv) _

end AlgebraicGeometry.RingedSite

end
