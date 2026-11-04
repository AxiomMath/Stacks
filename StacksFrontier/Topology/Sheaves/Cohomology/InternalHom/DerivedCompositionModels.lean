module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedCompositionConstruction
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHomEvaluation.EvaluationModels

/-!
# When the composition morphism of derived internal Homs is invertible

Let `X` be a ringed site and let `K`, `L`, `M` be objects of `D(O)`. The composition morphism of
Stacks 0A98

`RSheafHom(L, M) ⊗^L_O RSheafHom(K, L) ⟶ RSheafHom(K, M)`

is, on K-injective representatives `J` of `L` and `I` of `M` and a K-flat complex `H` mapping to
`SheafHom(K, J)`, the class of a morphism of *complexes*
(`AlgebraicGeometry.RingedSite.derivedSheafHomComposition_kFlatModel`). This file turns that
equation into an invertibility criterion: invertibility of derived composition is equivalent to
quasi-isomorphy of that morphism of complexes, a condition on cohomology sheaves with no derived
category left in it, and therefore one that is **local on the site**.

## The morphism of complexes

The model statement of Stacks 0A98 is *not* a two-sided conjugation of the composition morphism
of internal Hom complexes of Stacks 0A91 alone: it carries a factor
`Tot(SheafHom(J, I) ⊗_O H) ⟶ Tot(SheafHom(J, I) ⊗_O SheafHom(K, J))`, induced by
`f : H ⟶ SheafHom(K, J)` in the right tensor factor, which is **not** invertible in `D(O)` —
`isIso_Q_map_tensorTotalMap_left` would want both tensor factors K-flat, and `SheafHom(J, I)` is
K-injective rather than K-flat.

The right object is therefore not `compositionMap` but the composite of the two,
`AlgebraicGeometry.RingedSite.compositionMapOfModels`, taken as a single morphism of complexes.
With it the model statement *is* a two-sided conjugation, and the criterion falls out with no
K-flatness of `SheafHom(J, I)` needed anywhere. This is the same arrangement as
`AlgebraicGeometry.RingedSite.derivedTensorHomMapOfModels` of
`StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedTensorHomDiagonalModels`, where the
complex-level morphism likewise depends on an auxiliary chain map and the criterion is stated for
the composite.

## Main results

* `AlgebraicGeometry.RingedSite.compositionMapOfModels`: the morphism of complexes
  `Tot(SheafHom(J, I) ⊗_O H) ⟶ SheafHom(K, I)` whose class derived composition is.
* `AlgebraicGeometry.RingedSite.isIso_derivedSheafHomComposition_iff_isIso_Q_map` and
  `AlgebraicGeometry.RingedSite.isIso_derivedSheafHomComposition_iff_quasiIso_ofModels`: derived
  composition at representatives is invertible if and only if that morphism of complexes is a
  quasi-isomorphism.
* `AlgebraicGeometry.RingedSite.isIso_derivedSheafHomComposition_of_iso`: invertibility of
  derived composition depends only on the isomorphism classes of the three objects.
* `AlgebraicGeometry.RingedSite.isIso_derivedSheafHomComposition_of_quasiIso_ofModels`: the two
  combined: derived composition is invertible when the morphism of complexes at some choice of
  models is a quasi-isomorphism.
* `AlgebraicGeometry.RingedSite.isIso_derivedSheafHomComposition_of_coversTop`: **derived
  composition is invertible as soon as the morphism of complexes at one choice of models is a
  quasi-isomorphism locally on the site.**

## Implementation notes

The transport along isomorphisms of the three objects is done one variable at a time, by the
three one-variable functorialities of Stacks 0A98: `derivedSheafHomComposition_natural_source`,
`derivedSheafHomComposition_natural_target` and `derivedSheafHomComposition_dinatural_middle`.
The intermediate object occurs contravariantly in the left tensor factor and covariantly in the
right one, which is exactly what dinaturality expresses, so its isomorphism needs no inversion by
hand.

The hypothesis on `f` is `IsIso (Q.map f)` rather than `QuasiIso f`: that is the form in which
the model statement's leading factor is seen to be invertible, and the two are interchangeable by
`DerivedCategory.isIso_Q_map_iff_quasiIso`.

## References

* [Stacks Project, Tag 0A98](https://stacks.math.columbia.edu/tag/0A98)
* [Stacks Project, Tag 0A91](https://stacks.math.columbia.edu/tag/0A91)
* [Stacks Project, Tag 0A97](https://stacks.math.columbia.edu/tag/0A97)
* [Stacks Project, Tag 08DQ](https://stacks.math.columbia.edu/tag/08DQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u d

namespace AlgebraicGeometry.RingedSite

attribute [local instance] ringSheafSectionsCommRing presheafOfModulesMonoidalCategory
  curriedTensorPreservesZeroMorphisms curriedTensorObjPreservesZeroMorphisms

variable (X : RingedSite.{u, u, u})

/-- **The morphism of complexes whose class derived composition is.** For complexes `K`, `J`, `I`
and a morphism `f : H ⟶ SheafHom(K, J)`, this is the composition morphism of internal Hom
complexes of Stacks 0A91 precomposed with `f` in the right tensor factor:

`Tot(SheafHom(J, I) ⊗_O H) ⟶ Tot(SheafHom(J, I) ⊗_O SheafHom(K, J)) ⟶ SheafHom(K, I)`. -/
def compositionMapOfModels
    (K J I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    {H : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (f : H ⟶ (sheafHomComplex X K J).obj) :
    tensorTotal X (sheafHomComplex X J I).obj H ⟶ (sheafHomComplex X K I).obj :=
  tensorTotalMap X (𝟙 (sheafHomComplex X J I).obj) f ≫ compositionMap X K J I

variable
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]
  [HasDerivedCategory.{d}
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O))]
  (T : Stacks.SheafOfModules.DerivedTensorProduct.{u, u, u, d} X)
  (Hd : DerivedInternalHom.{u, d} X)

section Models

variable
  (K J I H : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)

/-- **Derived composition at representatives is invertible exactly when its complex model is.**
For `J` and `I` K-injective, `H` K-flat and `f : H ⟶ SheafHom(K, J)` a morphism whose class is
invertible, the model statement of Stacks 0A98 exhibits derived composition and the class of
`compositionMapOfModels` as conjugate by invertible morphisms. -/
theorem isIso_derivedSheafHomComposition_iff_isIso_Q_map
    [J.IsKInjective] [I.IsKInjective]
    (hH : Stacks.SheafOfModules.IsKFlat X.O H)
    (f : H ⟶ (sheafHomComplex X K J).obj) (hf : IsIso (DerivedCategory.Q.map f)) :
    IsIso (derivedSheafHomComposition X T Hd (DerivedCategory.Q.obj K)
        (DerivedCategory.Q.obj J) (DerivedCategory.Q.obj I)) ↔
      IsIso (DerivedCategory.Q.map (compositionMapOfModels X K J I f)) := by
  have hmodel := derivedSheafHomComposition_kFlatModel X T Hd K J I H hH f
  have hf' : IsIso (DerivedCategory.Q.map f ≫ (Hd.homComparison K J).inv) := by
    have := hf
    infer_instance
  have hlead : IsIso ((T.tensor.obj ((Hd.hom.obj (op (DerivedCategory.Q.obj J))).obj
      (DerivedCategory.Q.obj I))).map
        (DerivedCategory.Q.map f ≫ (Hd.homComparison K J).inv)) :=
    Functor.map_isIso _ _
  constructor
  · intro hcomp
    have h : IsIso ((derivedEvaluationSourceComparison X T Hd H J I hH).hom ≫
        DerivedCategory.Q.map (compositionMapOfModels X K J I f)) := by
      rw [compositionMapOfModels, CategoryTheory.Functor.map_comp, ← hmodel]
      infer_instance
    exact IsIso.of_isIso_comp_left (derivedEvaluationSourceComparison X T Hd H J I hH).hom
      (DerivedCategory.Q.map (compositionMapOfModels X K J I f))
  · intro hmap
    have hrhs : IsIso ((derivedEvaluationSourceComparison X T Hd H J I hH).hom ≫
        DerivedCategory.Q.map (tensorTotalMap X (𝟙 (sheafHomComplex X J I).obj) f) ≫
          DerivedCategory.Q.map (compositionMap X K J I)) := by
      rw [← CategoryTheory.Functor.map_comp, ← compositionMapOfModels]
      infer_instance
    have h : IsIso (derivedSheafHomComposition X T Hd (DerivedCategory.Q.obj K)
        (DerivedCategory.Q.obj J) (DerivedCategory.Q.obj I) ≫
          (Hd.homComparison K I).hom) := IsIso.of_isIso_fac_left hmodel
    exact IsIso.of_isIso_comp_right _ (Hd.homComparison K I).hom

/-- **Derived composition at representatives is invertible exactly when its complex model is a
quasi-isomorphism.** This is the previous criterion with the class of a morphism of complexes
replaced by the morphism itself, which is the form in which the condition is a statement about
cohomology sheaves — and hence local on the site. -/
theorem isIso_derivedSheafHomComposition_iff_quasiIso_ofModels
    [J.IsKInjective] [I.IsKInjective]
    (hH : Stacks.SheafOfModules.IsKFlat X.O H)
    (f : H ⟶ (sheafHomComplex X K J).obj) (hf : IsIso (DerivedCategory.Q.map f)) :
    IsIso (derivedSheafHomComposition X T Hd (DerivedCategory.Q.obj K)
        (DerivedCategory.Q.obj J) (DerivedCategory.Q.obj I)) ↔
      QuasiIso (compositionMapOfModels X K J I f) := by
  rw [isIso_derivedSheafHomComposition_iff_isIso_Q_map X T Hd K J I H hH f hf,
    DerivedCategory.isIso_Q_map_iff_quasiIso]

end Models

/-- Tensoring on the left with an invertible `derivedSheafHomMap` is invertible. -/
private theorem isIso_derivedTensorMap_derivedSheafHomMap_left
    {A A' B B' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (C : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (a : A' ⟶ A) (b : B ⟶ B') [IsIso a] [IsIso b] :
    IsIso (derivedTensorMap X T (derivedSheafHomMap X Hd a b) (𝟙 C)) := by
  have := isIso_derivedSheafHomMap_of_isIso X Hd a b
  exact isIso_derivedTensorMap X T _ _

/-- Tensoring on the right with an invertible `derivedSheafHomMap` is invertible. -/
private theorem isIso_derivedTensorMap_derivedSheafHomMap_right
    {A A' B B' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (C : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (a : A' ⟶ A) (b : B ⟶ B') [IsIso a] [IsIso b] :
    IsIso (derivedTensorMap X T (𝟙 C) (derivedSheafHomMap X Hd a b)) := by
  have := isIso_derivedSheafHomMap_of_isIso X Hd a b
  exact isIso_derivedTensorMap X T _ _

/-- **Invertibility of derived composition depends only on the isomorphism classes of its three
objects.** If derived composition at `K`, `L`, `M` is invertible and `K ≅ K'`, `L ≅ L'`, `M ≅ M'`,
then derived composition at `K'`, `L'`, `M'` is invertible. -/
theorem isIso_derivedSheafHomComposition_of_iso
    {K K' L L' M M' :
      DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (eK : K ≅ K') (eL : L ≅ L') (eM : M ≅ M')
    (h : IsIso (derivedSheafHomComposition X T Hd K L M)) :
    IsIso (derivedSheafHomComposition X T Hd K' L' M') := by
  -- Release the target, by covariant naturality.
  have hM : IsIso (derivedSheafHomComposition X T Hd K L M') := by
    have := h
    have := isIso_derivedSheafHomMap_of_isIso X Hd (𝟙 K) eM.hom
    have := isIso_derivedTensorMap_derivedSheafHomMap_left X T Hd ((Hd.hom.obj (op K)).obj L)
      (𝟙 L) eM.hom
    exact IsIso.of_isIso_fac_left
      (derivedSheafHomComposition_natural_target X T Hd K L eM.hom).symm
  -- Release the source, by contravariant naturality.
  have hK : IsIso (derivedSheafHomComposition X T Hd K' L M') := by
    have := hM
    have := isIso_derivedSheafHomMap_of_isIso X Hd eK.inv (𝟙 M')
    have := isIso_derivedTensorMap_derivedSheafHomMap_right X T Hd ((Hd.hom.obj (op L)).obj M')
      eK.inv (𝟙 L)
    exact IsIso.of_isIso_fac_left
      (derivedSheafHomComposition_natural_source X T Hd eK.inv L M').symm
  -- Release the intermediate object, by dinaturality.
  have := hK
  have := isIso_derivedSheafHomMap_of_isIso X Hd eL.hom (𝟙 M')
  have := isIso_derivedTensorMap_derivedSheafHomMap_left X T Hd ((Hd.hom.obj (op K')).obj L)
    eL.hom (𝟙 M')
  have := isIso_derivedSheafHomMap_of_isIso X Hd (𝟙 K') eL.hom
  have := isIso_derivedTensorMap_derivedSheafHomMap_right X T Hd ((Hd.hom.obj (op L')).obj M')
    (𝟙 K') eL.hom
  exact IsIso.of_isIso_fac_left
    (derivedSheafHomComposition_dinatural_middle X T Hd K' eL.hom M')

/-- **Derived composition is invertible as soon as its complex model is a quasi-isomorphism.**
For arbitrary objects `K`, `L`, `M` of `D(O)` presented by complexes `E`, `J`, `I` with `J` and
`I` K-injective, and a K-flat `H` mapping to `SheafHom(E, J)` by a morphism with invertible
class, the morphism of Stacks 0A98 is invertible whenever `compositionMapOfModels` is a
quasi-isomorphism. -/
theorem isIso_derivedSheafHomComposition_of_quasiIso_ofModels
    (E J I H : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (K L M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    [J.IsKInjective] [I.IsKInjective]
    (hH : Stacks.SheafOfModules.IsKFlat X.O H)
    (f : H ⟶ (sheafHomComplex X E J).obj) (hf : IsIso (DerivedCategory.Q.map f))
    (eE : DerivedCategory.Q.obj E ≅ K) (eJ : DerivedCategory.Q.obj J ≅ L)
    (eI : DerivedCategory.Q.obj I ≅ M)
    (hq : QuasiIso (compositionMapOfModels X E J I f)) :
    IsIso (derivedSheafHomComposition X T Hd K L M) :=
  isIso_derivedSheafHomComposition_of_iso X T Hd eE eJ eI
    ((isIso_derivedSheafHomComposition_iff_quasiIso_ofModels X T Hd E J I H hH f hf).2 hq)

/-- **Derived composition is invertible as soon as its complex model is a quasi-isomorphism
locally on the site.** With `K`, `L`, `M` presented by models as in
`isIso_derivedSheafHomComposition_of_quasiIso_ofModels`, if the restriction of
`compositionMapOfModels` to each member of a family `V` covering the site is a quasi-isomorphism,
then derived composition at `K`, `L`, `M` is invertible. -/
theorem isIso_derivedSheafHomComposition_of_coversTop
    [∀ V : X.C, HasWeakSheafify (X.J.over V) AddCommGrpCat.{u}]
    [∀ V : X.C, (X.J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}]
    (E J I H : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (K L M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    [J.IsKInjective] [I.IsKInjective]
    (hH : Stacks.SheafOfModules.IsKFlat X.O H)
    (f : H ⟶ (sheafHomComplex X E J).obj) (hf : IsIso (DerivedCategory.Q.map f))
    (eE : DerivedCategory.Q.obj E ≅ K) (eJ : DerivedCategory.Q.obj J ≅ L)
    (eI : DerivedCategory.Q.obj I ≅ M)
    {ι : Type*} {V : ι → X.C} (hV : X.J.CoversTop V)
    (hloc : ∀ i, QuasiIso (restrictComplexMap X (V i) (compositionMapOfModels X E J I f))) :
    IsIso (derivedSheafHomComposition X T Hd K L M) :=
  isIso_derivedSheafHomComposition_of_quasiIso_ofModels X T Hd E J I H K L M hH f hf eE eJ eI
    (Stacks.SheafOfModules.quasiIso_of_coversTop hV _ hloc)

end AlgebraicGeometry.RingedSite

end
