module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.Interface
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ToOrdinaryTensor
import StacksCore.Tactic.StacksAttribute

/-!
# Assembling the derived tensor product from its comparison data

This file fills every field of `Stacks.SheafOfModules.DerivedTensorProduct` except the two
exactness fields, which are taken as hypotheses here and supplied elsewhere.

All three comparison isomorphisms of the structure — the two-sided one and the two one-sided
ones — are the *same* morphism `Stacks.SheafOfModules.toTensor`, promoted to an isomorphism by
whichever K-flatness hypothesis is available. Consequently the four equations relating them
(`comparisonRight_eq_comparison`, `comparisonLeft_eq_comparison`,
`toTensor_eq_comparisonRight`, `toTensor_eq_comparisonLeft`) hold by definition, and the three
naturality statements are all the single naturality of `toTensor`. That is the point of
`Stacks.SheafOfModules.toTensor_comp_of_kFlat`: the canonical map is pinned down by its
behaviour on an arbitrary map out of a K-flat complex, not by a choice.

## Main results

* `Stacks.SheafOfModules.nonempty_derivedTensorProduct_of_exact`: given the exactness of the
  derived tensor product in each variable, the derived tensor product of Stacks 06YU exists.

## Implementation notes

`CategoryTheory.IsIso` is a `Prop`, so the two isomorphism structures obtained from the two
different K-flatness hypotheses are the same term by proof irrelevance; that is why
`comparisonLeft_eq_comparison` is `rfl`.

The naturality fields of the structure spell the induced map of total tensor complexes as
`HomologicalComplex.mapBifunctorMap f g`, whereas `toTensor_naturality` spells it as the
composite of the two one-variable images; the generic
`HomologicalComplex.mapBifunctorMap_eq_map₂_comp` converts between them.

Those fields are proved by a tactic acting on the structure's own already-elaborated field
type, never through an intermediate lemma restating it. That is deliberate: a statement which
mixes the two spellings of a map of total tensor complexes needs the equality of the two
spellings of its *source and target* as well, and establishing that from scratch unfolds the
total complex and its direct sums. Working on the structure's own field type, those types are
already fixed, so only the equality of the two morphisms remains and the generic lemma
supplies it.

## References

* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 0FPH](https://stacks.math.columbia.edu/tag/0FPH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe c u d

namespace Stacks.SheafOfModules

variable (X : AlgebraicGeometry.RingedSite.{c, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{c, u, u, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{c, u, u, u, u} X.O).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{c, u, u} X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]
  [HasDerivedCategory.{d}
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{c, u, u} X.O))]

attribute [local instance] kFlatQ_isLocalization derivedTensorBifunctorLifting

/-- The derived tensor product assembled from the given shift coherence and exactness,
with its canonical natural map to the total tensor product and one-sided K-flat comparisons. -/
def derivedTensorProductOfExact
    (hcs : (derivedTensorBifunctor X).CommShift₂Int)
    (hel : ∀ M, letI := hcs.commShiftFlipObj M;
      ((derivedTensorBifunctor X).flip.obj M).IsTriangulated)
    (her : ∀ N, letI := hcs.commShiftObj N; ((derivedTensorBifunctor X).obj N).IsTriangulated) :
    DerivedTensorProduct.{c, u, u, d} X :=
  { tensor := derivedTensorBifunctor X
    comparison := fun K L _ hL ↦
      @asIso _ _ _ _ _ (isIso_toTensor_of_kFlat_right X K L hL)
    comparison_naturality := fun f g _ _ _ _ ↦ by
      refine (toTensor_naturality X f g).trans ?_
      congr 2
      exact HomologicalComplex.mapBifunctorMap_eq_map₂_comp
        (Stacks.SheafOfModules.Tensor.sheafTensor X.O) (ComplexShape.up ℤ) f g
    comparisonRight := fun K L hL ↦
      @asIso _ _ _ _ _ (isIso_toTensor_of_kFlat_right X K L hL)
    comparisonRight_naturality := fun f g _ _ ↦ by
      refine (toTensor_naturality X f g).trans ?_
      congr 2
      exact HomologicalComplex.mapBifunctorMap_eq_map₂_comp
        (Stacks.SheafOfModules.Tensor.sheafTensor X.O) (ComplexShape.up ℤ) f g
    comparisonRight_eq_comparison := fun _ _ _ _ ↦ rfl
    comparisonLeft := fun K L hK ↦
      @asIso _ _ _ _ _ (isIso_toTensor_of_kFlat_left X K L hK)
    comparisonLeft_naturality := fun f g _ _ ↦ by
      refine (toTensor_naturality X f g).trans ?_
      congr 2
      exact HomologicalComplex.mapBifunctorMap_eq_map₂_comp
        (Stacks.SheafOfModules.Tensor.sheafTensor X.O) (ComplexShape.up ℤ) f g
    comparisonLeft_eq_comparison := fun _ _ _ _ ↦ rfl
    toTensor := toTensor X
    toTensor_naturality := fun f g ↦ by
      refine (toTensor_naturality X f g).trans ?_
      congr 2
      exact HomologicalComplex.mapBifunctorMap_eq_map₂_comp
        (Stacks.SheafOfModules.Tensor.sheafTensor X.O) (ComplexShape.up ℤ) f g
    toTensor_eq_comparisonRight := fun _ _ _ ↦ rfl
    toTensor_eq_comparisonLeft := fun _ _ _ ↦ rfl
    commShift₂ := hcs
    exact_left := hel
    exact_right := her }

/-- **Stacks 06YU, granted exactness.** The derived tensor product of sheaves of modules on a
ringed site exists, with its canonical natural map to the ordinary total tensor product and
its one-sided K-flat comparisons, as soon as the bifunctor is exact in each variable. -/
theorem nonempty_derivedTensorProduct_of_exact
    (hcs : (derivedTensorBifunctor X).CommShift₂Int)
    (hel : ∀ rightModule, letI := hcs.commShiftFlipObj rightModule;
      ((derivedTensorBifunctor X).flip.obj rightModule).IsTriangulated)
    (her : ∀ leftModule, letI := hcs.commShiftObj leftModule;
      ((derivedTensorBifunctor X).obj leftModule).IsTriangulated) :
    Nonempty (DerivedTensorProduct.{c, u, u, d} X) :=
  ⟨derivedTensorProductOfExact X hcs hel her⟩

end Stacks.SheafOfModules

end
