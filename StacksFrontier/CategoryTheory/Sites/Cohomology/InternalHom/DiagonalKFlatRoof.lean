module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.TotalComplexNaturality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.Existence
public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedSectionsOnDerivedObjects

/-!
# The K-flat roof over a morphism of the derived category, after tensoring

Let `(C, O)` be a ringed site and let `w : K ⟶ K'` be a morphism of the derived category `D(O)`.
Functoriality in a tensor variable is often established by the following device: `w` is first
replaced by the morphism of the chosen K-flat representatives `kFlatModel X K` and
`kFlatModel X K'` that it induces, and that morphism is then presented by a *roof*
`kFlatModel X K ⟵ P ⟶ kFlatModel X K'` through a K-flat complex `P` whose left leg `sr` becomes
invertible in `D(O)`.

This file states three facts about that situation: the conjugation identity that performs the
replacement, and the two invertibility statements saying that the left leg of the roof stays
invertible after tensoring with an arbitrary complex, and after the internal Hom into a chosen
K-injective resolution.

## Main results

* `AlgebraicGeometry.RingedSite.map_kFlatModelIso_inv_comp`: conjugating by the comparisons with
  the chosen K-flat representatives turns a morphism of `D(O)` into the morphism of the classes
  of those representatives.
* `AlgebraicGeometry.RingedSite.isIso_Q_map_tensorTotalMap_roof`: the left leg of the roof stays
  invertible in `D(O)` after tensoring with an arbitrary complex.
* `AlgebraicGeometry.RingedSite.isIso_Q_map_homMap_roof`: it stays invertible after the internal
  Hom into a chosen K-injective resolution as well.

## References

* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 0A97](https://stacks.math.columbia.edu/tag/0A97)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace AlgebraicGeometry.RingedSite

universe u

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] ringSheafSectionsCommRing presheafOfModulesMonoidalCategory
  curriedTensorPreservesZeroMorphisms curriedTensorObjPreservesZeroMorphisms

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u,
    u} X.O))
      (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]

variable (L M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
  {K K' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
  {w : K ⟶ K'}

/-- Conjugating by the comparisons with the chosen K-flat representatives turns a morphism of
`D(O)` into the morphism of the classes of those representatives. -/
theorem map_kFlatModelIso_inv_comp
    (Z : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    ((Stacks.SheafOfModules.derivedTensorProductFunctor X).map w).app Z ≫
        ((Stacks.SheafOfModules.derivedTensorProductFunctor X).map
          (kFlatModelIso X K').inv).app Z =
      ((Stacks.SheafOfModules.derivedTensorProductFunctor X).map
          (kFlatModelIso X K).inv).app Z ≫
        ((Stacks.SheafOfModules.derivedTensorProductFunctor X).map
          ((kFlatModelIso X K).hom ≫ w ≫ (kFlatModelIso X K').inv)).app Z := by
  rw [← NatTrans.comp_app, ← NatTrans.comp_app, ← Functor.map_comp, ← Functor.map_comp,
    ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

section Roof

variable {P : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
  (hP : Stacks.SheafOfModules.IsKFlat X.O P)
  {sr : P ⟶ kFlatModel X K}
  (hsr : IsIso (DerivedCategory.Q.map sr))

include hP hsr in
/-- The left leg of the roof stays invertible in `D(O)` after tensoring with an arbitrary
complex, because its two ends are K-flat. -/
theorem isIso_Q_map_tensorTotalMap_roof
    (Z : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    IsIso (DerivedCategory.Q.map (tensorTotalMap X sr (𝟙 Z))) :=
  isIso_Q_map_tensorTotalMap_left X hP (isKFlat_kFlatModel X K) sr hsr Z

include hP hsr in
/-- The K-injective resolution of the tensored left leg of the roof also stays invertible in
`D(O)` after the internal Hom, because the resolution comparison is an isomorphism at both
ends. -/
theorem isIso_Q_map_homMap_roof :
    IsIso (DerivedCategory.Q.map (homMap X (𝟙 (kInjectiveModel X M))
      ((kInjectiveResolution X).map (tensorTotalMap X sr (𝟙 (kInjectiveModel X L)))))) := by
  have := isIso_Q_map_tensorTotalMap_roof X hP hsr (kInjectiveModel X L)
  have hsq : ((derivedSheafHomBifunctor X).obj
            (op (DerivedCategory.Q.obj (kInjectiveModel X M)))).map
          (DerivedCategory.Q.map (tensorTotalMap X sr (𝟙 (kInjectiveModel X L)))) ≫
        (derivedSheafHomResolutionComparison X (kInjectiveModel X M)
          (tensorTotal X (kFlatModel X K) (kInjectiveModel X L))).hom =
      (derivedSheafHomResolutionComparison X (kInjectiveModel X M)
          (tensorTotal X P (kInjectiveModel X L))).hom ≫
        DerivedCategory.Q.map (homMap X (𝟙 (kInjectiveModel X M))
          ((kInjectiveResolution X).map
            (tensorTotalMap X sr (𝟙 (kInjectiveModel X L))))) := by
    simpa using derivedSheafHomResolutionComparison_naturality X
      (𝟙 (kInjectiveModel X M)) (tensorTotalMap X sr (𝟙 (kInjectiveModel X L)))
  exact IsIso.of_isIso_fac_left hsq.symm

end Roof

end AlgebraicGeometry.RingedSite

end
