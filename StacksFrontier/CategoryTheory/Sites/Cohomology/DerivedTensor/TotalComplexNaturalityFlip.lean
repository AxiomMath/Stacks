module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.TotalComplexNaturality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TensorComplex.TotalComplexFlip

/-!
# Tensoring a quasi-isomorphism of K-flat complexes with an arbitrary complex on the left

Let `X` be a ringed site and let `c : A ⟶ A₀` be a quasi-isomorphism between two **K-flat**
complexes of `O`-modules. Then for an **arbitrary** complex `Z` the induced morphism of total
tensor complexes

`Tot(𝟙_Z ⊗ c) : Tot(Z ⊗_O A) ⟶ Tot(Z ⊗_O A₀)`

is again a quasi-isomorphism.

This is the companion, in the right tensor slot, of
`AlgebraicGeometry.RingedSite.isIso_Q_map_tensorTotalMap_left`, which says the same thing for
`Tot(c ⊗ 𝟙_Z)`. It is **not** a consequence of
`AlgebraicGeometry.RingedSite.isIso_Q_map_tensorTotalMap_right` or of
`Stacks.SheafOfModules.IsKFlat.quasiIso_mapBifunctorMap_id_left`: those put the K-flatness
hypothesis on the *fixed* tensor factor, whereas here the fixed factor `Z` carries no hypothesis
at all and K-flatness is assumed of the two complexes between which the quasi-isomorphism runs.
That is the form needed when the fixed factor is an internal Hom complex, which is not K-flat.

## Main results

* `AlgebraicGeometry.RingedSite.isIso_Q_map_tensorTotalMap_right_of_kFlat`: the statement in
  `D(O)`.
* `AlgebraicGeometry.RingedSite.quasiIso_tensorTotalMap_right_of_kFlat`: the same statement read
  as quasi-isomorphy of a morphism of complexes, which is the form a consumer applies.

## Implementation notes

No cone argument is needed. The left-slot statement
`isIso_Q_map_tensorTotalMap_left` is already proved from the one-sided K-flat comparison of
Stacks 06YU, and the Koszul symmetry of the total tensor complex carries it to the right slot:
`AlgebraicGeometry.RingedSite.tensorTotalFlipIso_hom_naturality` is a commuting square whose two
horizontal legs are `Tot(c ⊗ 𝟙_Z)` and `Tot(𝟙_Z ⊗ c)` and whose two verticals are the symmetry
isomorphisms, so invertibility transfers from one leg to the other.

## References

* [Stacks Project, Lemma 20.26.6 (Tag 06YU)](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Section 20.48 (Tag 06YM)](https://stacks.math.columbia.edu/tag/06YM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

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
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]

/-- **A quasi-isomorphism of K-flat complexes stays one after tensoring with an arbitrary
complex on the left.** The right-slot companion of
`AlgebraicGeometry.RingedSite.isIso_Q_map_tensorTotalMap_left`, obtained from it by the Koszul
symmetry of the total tensor complex. No hypothesis is put on the fixed factor `Z`. -/
theorem isIso_Q_map_tensorTotalMap_right_of_kFlat
    {A A₀ : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (hA : Stacks.SheafOfModules.IsKFlat X.O A)
    (hA₀ : Stacks.SheafOfModules.IsKFlat X.O A₀)
    (c : A ⟶ A₀) (hc : IsIso (DerivedCategory.Q.map c))
    (Z : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    IsIso (DerivedCategory.Q.map (tensorTotalMap X (𝟙 Z) c)) := by
  have := isIso_Q_map_tensorTotalMap_left X hA hA₀ c hc Z
  have hnat : DerivedCategory.Q.map (tensorTotalMap X c (𝟙 Z)) ≫
        DerivedCategory.Q.map (tensorTotalFlipIso X A₀ Z).hom =
      DerivedCategory.Q.map (tensorTotalFlipIso X A Z).hom ≫
        DerivedCategory.Q.map (tensorTotalMap X (𝟙 Z) c) :=
    (DerivedCategory.Q.map_comp _ _).symm.trans
      ((congrArg DerivedCategory.Q.map (tensorTotalFlipIso_hom_naturality X c (𝟙 Z))).trans
        (DerivedCategory.Q.map_comp _ _))
  have : IsIso (DerivedCategory.Q.map (tensorTotalFlipIso X A Z).hom ≫
      DerivedCategory.Q.map (tensorTotalMap X (𝟙 Z) c)) := by
    rw [← hnat]; infer_instance
  exact IsIso.of_isIso_comp_left
    (DerivedCategory.Q.map (tensorTotalFlipIso X A Z).hom) _

/-- **`Tot(𝟙_Z ⊗ c)` is a quasi-isomorphism whenever `c` is one between K-flat complexes**, for
an arbitrary `Z`. This is `isIso_Q_map_tensorTotalMap_right_of_kFlat` read on complexes. -/
theorem quasiIso_tensorTotalMap_right_of_kFlat
    {A A₀ : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (hA : Stacks.SheafOfModules.IsKFlat X.O A)
    (hA₀ : Stacks.SheafOfModules.IsKFlat X.O A₀)
    (c : A ⟶ A₀) (hc : QuasiIso c)
    (Z : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    QuasiIso (tensorTotalMap X (𝟙 Z) c) :=
  (DerivedCategory.isIso_Q_map_iff_quasiIso _ (tensorTotalMap X (𝟙 Z) c)).1
    (isIso_Q_map_tensorTotalMap_right_of_kFlat X hA hA₀ c
      ((DerivedCategory.isIso_Q_map_iff_quasiIso _ c).2 hc) Z)

end AlgebraicGeometry.RingedSite

end
