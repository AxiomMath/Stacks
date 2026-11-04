module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.CompositionMorphism
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedEvaluationSource
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TensorComplex.TotalComplexComparison
import StacksCore.Tactic.StacksAttribute

/-! # The model of derived composition of internal Homs on a ringed site

Let `(C, O)` be a ringed site and let `K`, `L`, `M` be complexes of `O`-modules. Stacks 0A98
asks for a canonical morphism

`RSheafHom(L, M) ⊗^L_O RSheafHom(K, L) ⟶ RSheafHom(K, M)`

in `D(O)`, for *arbitrary* objects of the derived category. This file constructs the morphism
on K-injective representatives of the two targets, where both derived internal Homs are the
ordinary internal Hom complexes and the derived composition is therefore forced to be the
composition morphism of complexes of Stacks 0A91. Two versions are given: one assuming in
addition that the internal Hom complex `SheafHom(K, L)` is K-flat, so that the derived tensor
product is literally the ordinary total tensor complex, and one with that hypothesis removed
by resolving `SheafHom(K, L)` K-flatly, which Stacks 06YS always allows.

## Main definitions

* `AlgebraicGeometry.RingedSite.derivedCompositionModel`: the derived composition morphism on
  K-injective targets and a K-flat internal Hom complex.
* `AlgebraicGeometry.RingedSite.kFlatHomResolution` and
  `AlgebraicGeometry.RingedSite.kFlatHomResolutionMap`: a chosen K-flat resolution of the
  internal Hom complex, from Stacks 06YS.
* `AlgebraicGeometry.RingedSite.derivedCompositionOfKInjective`: the derived composition
  morphism on K-injective targets, with **no** flatness hypothesis, computed on that
  resolution.

## Implementation notes

**This is not Stacks 0A98**, and nothing here carries that tag: 0A98 asserts a morphism for
arbitrary objects of `D(O)`, together with its naturality in all three variables, and this
file supplies only the value that such a morphism is obliged to take on the representatives
above, which is the content of 0A98's own `comparison` field.
`derivedCompositionOfKInjective` goes one step further and removes the flatness hypothesis by
resolving `SheafHom(K, L)`; what is still missing for 0A98 is the passage from K-injective
representatives to arbitrary objects of `D(O)`, the independence of the value from the chosen
resolution, and the four naturality and dinaturality fields. No lemma here relates
`derivedCompositionModel` to `derivedCompositionOfKInjective`; that comparison is
`Stacks.SheafOfModules.DerivedTensorProduct.comparisonRight_eq_of_resolution` together with
the naturality of `AlgebraicGeometry.RingedSite.tensorTotalIsoTensorComplex`, and it is not
done.

`AlgebraicGeometry.RingedSite.kFlatHomResolution` is `Classical.choose` of the **proved**
`Stacks.SheafOfModules.exists_kFlat_quasiIso`, so no unproved existence statement is used.

`derivedCompositionModel` is the composite of four comparisons from the library and the composition
morphism of complexes:

1. the K-injective model of the derived internal Hom in the right-hand tensor factor,
   `AlgebraicGeometry.RingedSite.derivedSheafHomComparison` for `K`, `L`;
2. the identification of the source of derived evaluation with the total tensor complex,
   `AlgebraicGeometry.RingedSite.derivedSheafHomTensorComparison`, which needs the left factor
   `SheafHom(K, L)` K-flat and the target `M` K-injective;
3. the comparison of the two total tensor-product complexes,
   `AlgebraicGeometry.RingedSite.tensorTotalIsoTensorComplex`, which is what lets the Section
   17 spelling reached by step 2 meet the Section 34 spelling in which Stacks 0A91's
   composition morphism has its source;
4. the composition morphism of internal Hom complexes,
   `(AlgebraicGeometry.RingedSite.compositionConstruction X).comp` of Stacks 0A91;
5. the K-injective model again, now for `K`, `M`, read backwards.

Step 3 is the step that did not exist before: the implementation notes of
`AlgebraicGeometry.RingedSite.derivedSheafHomTensorComparison` record that the two total tensor
products are isomorphic but that the comparison was unavailable, which is exactly why steps 2
and 4 could not be composed.

The universes are the diagonal `RingedSite.{u, u, u}` with the universe `d` of the
localization free, as in both of the files whose comparisons are composed here.

## References

* [Stacks Project, Tag 0A98](https://stacks.math.columbia.edu/tag/0A98)
* [Stacks Project, Tag 0A91](https://stacks.math.columbia.edu/tag/0A91)
* [Stacks Project, Tag 0A97](https://stacks.math.columbia.edu/tag/0A97)
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

/-- **The model of derived composition.** For complexes `K`, `L`, `M` of `O`-modules with `L`
and `M` K-injective and with the internal Hom complex `SheafHom(K, L)` K-flat, the morphism

`RSheafHom(L, M) ⊗^L_O RSheafHom(K, L) ⟶ RSheafHom(K, M)`

in `D(O)` induced by the composition morphism of internal Hom complexes of Stacks 0A91. -/
def derivedCompositionModel
    (K L M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    [L.IsKInjective] [M.IsKInjective]
    (hKL : Stacks.SheafOfModules.IsKFlat X.O (sheafHomComplex X K L).obj) :
    ((Stacks.SheafOfModules.derivedTensorProductFunctor.{u, u, d} X).obj
          (((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj L))).obj
            (DerivedCategory.Q.obj M))).obj
        (((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj K))).obj
          (DerivedCategory.Q.obj L)) ⟶
      ((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj K))).obj
        (DerivedCategory.Q.obj M) :=
  ((Stacks.SheafOfModules.derivedTensorProductFunctor.{u, u, d} X).obj
        (((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj L))).obj
          (DerivedCategory.Q.obj M))).map (derivedSheafHomComparison X K L).hom ≫
    (derivedSheafHomTensorComparison X (sheafHomComplex X K L).obj L M hKL).hom ≫
    DerivedCategory.Q.map
      ((tensorTotalIsoTensorComplex X (sheafHomComplex X L M).obj
          (sheafHomComplex X K L).obj).inv ≫
        (compositionConstruction X).comp K L M) ≫
    (derivedSheafHomComparison X K M).inv

/-- A chosen K-flat complex quasi-isomorphic to the internal Hom complex `SheafHom(K, L)`,
from the existence of K-flat resolutions (Stacks 06YS). -/
def kFlatHomResolution
    (K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ :=
  (Stacks.SheafOfModules.exists_kFlat_quasiIso X (sheafHomComplex X K L).obj).choose

/-- The augmentation of the chosen K-flat resolution of `SheafHom(K, L)`. -/
def kFlatHomResolutionMap
    (K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    kFlatHomResolution X K L ⟶ (sheafHomComplex X K L).obj :=
  (Stacks.SheafOfModules.exists_kFlat_quasiIso X
    (sheafHomComplex X K L).obj).choose_spec.choose

omit [HasDerivedCategory.{d}
  (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O))] in
/-- The chosen resolution of `SheafHom(K, L)` is K-flat. -/
theorem isKFlat_kFlatHomResolution
    (K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    Stacks.SheafOfModules.IsKFlat X.O (kFlatHomResolution X K L) :=
  (Stacks.SheafOfModules.exists_kFlat_quasiIso X
    (sheafHomComplex X K L).obj).choose_spec.choose_spec.1

/-- The augmentation of the chosen resolution of `SheafHom(K, L)` is a quasi-isomorphism. -/
instance quasiIso_kFlatHomResolutionMap
    (K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    QuasiIso (kFlatHomResolutionMap X K L) :=
  (Stacks.SheafOfModules.exists_kFlat_quasiIso X
    (sheafHomComplex X K L).obj).choose_spec.choose_spec.2

/-- The augmentation of the chosen K-flat resolution becomes invertible in `D(O)`. -/
instance isIso_Q_map_kFlatHomResolutionMap
    (K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    IsIso (DerivedCategory.Q.map (kFlatHomResolutionMap X K L)) :=
  (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 inferInstance

/-- **Derived composition on K-injective targets.** For complexes `K`, `L`, `M` of `O`-modules
with `L` and `M` K-injective, the morphism

`RSheafHom(L, M) ⊗^L_O RSheafHom(K, L) ⟶ RSheafHom(K, M)`

in `D(O)` induced by the composition morphism of internal Hom complexes of Stacks 0A91,
computed on a chosen K-flat resolution of `SheafHom(K, L)`.

Unlike `AlgebraicGeometry.RingedSite.derivedCompositionModel` this needs no flatness
hypothesis: the resolution always exists, by Stacks 06YS, and the augmentation it comes with
is inverted in `D(O)`. -/
def derivedCompositionOfKInjective
    (K L M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    [L.IsKInjective] [M.IsKInjective] :
    ((Stacks.SheafOfModules.derivedTensorProductFunctor.{u, u, d} X).obj
          (((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj L))).obj
            (DerivedCategory.Q.obj M))).obj
        (((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj K))).obj
          (DerivedCategory.Q.obj L)) ⟶
      ((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj K))).obj
        (DerivedCategory.Q.obj M) :=
  ((Stacks.SheafOfModules.derivedTensorProductFunctor.{u, u, d} X).obj
        (((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj L))).obj
          (DerivedCategory.Q.obj M))).map (derivedSheafHomComparison X K L).hom ≫
    inv (((Stacks.SheafOfModules.derivedTensorProductFunctor.{u, u, d} X).obj
        (((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj L))).obj
          (DerivedCategory.Q.obj M))).map
            (DerivedCategory.Q.map (kFlatHomResolutionMap X K L))) ≫
    (derivedSheafHomTensorComparison X (kFlatHomResolution X K L) L M
      (isKFlat_kFlatHomResolution X K L)).hom ≫
    DerivedCategory.Q.map
      ((tensorTotalIsoTensorComplex X (sheafHomComplex X L M).obj
            (kFlatHomResolution X K L)).inv ≫
        tensorTotalMap X (𝟙 (sheafHomComplex X L M).obj) (kFlatHomResolutionMap X K L) ≫
        (compositionConstruction X).comp K L M) ≫
    (derivedSheafHomComparison X K M).inv

end AlgebraicGeometry.RingedSite

end
