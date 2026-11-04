module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedEvaluation
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Slice.QuasiIsomorphismLocality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.HomComplexCompositionComparison

/-!
# When derived evaluation on a ringed site is invertible

Let `X` be a ringed site and let `K`, `L`, `M` be objects of `D(O)`. The evaluation morphism of
Stacks 0A97

`RSheafHom(L, M) ⊗^L_O K ⟶ RSheafHom(RSheafHom(K, L), M)`

is, on a K-flat representative `A` of `K` and K-injective representatives `B` and `C` of `L` and
`M`, the class of the evaluation morphism of internal Hom complexes of Stacks 0A92, conjugated by
the two comparisons identifying its source and its target with classes of complexes
(`AlgebraicGeometry.RingedSite.derivedEvaluation_model`). Conjugating by isomorphisms does not
change invertibility, so the derived morphism is invertible exactly when that one morphism of
complexes is a quasi-isomorphism — a condition on cohomology sheaves with no derived category
left in it, and therefore one that is **local on the site**.

The local step that this makes possible — invertibility of derived evaluation checked over the
members of a covering through quasi-isomorphy of the evaluation morphism of complexes — is
`AlgebraicGeometry.RingedSite.isIso_derivedSheafHomEvaluation_of_coversTop` of
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.EvaluationLocality`.

## Main results

* `AlgebraicGeometry.RingedSite.derivedSheafHomEvaluation_eq_conjugate`: derived evaluation at
  representatives is the class of the evaluation morphism of complexes, conjugated by the source
  and target comparisons.
* `AlgebraicGeometry.RingedSite.isIso_derivedSheafHomEvaluation_iff_isIso_Q_map` and
  `AlgebraicGeometry.RingedSite.isIso_derivedSheafHomEvaluation_iff_quasiIso`: derived evaluation
  at representatives is invertible if and only if the evaluation morphism of complexes is a
  quasi-isomorphism.
* `AlgebraicGeometry.RingedSite.isIso_derivedSheafHomEvaluation_of_iso`: invertibility of derived
  evaluation depends only on the isomorphism classes of the three objects.
* `AlgebraicGeometry.RingedSite.isIso_derivedSheafHomEvaluation_of_quasiIso`: the two combined, in
  the shape a consumer uses — arbitrary objects, with representatives given by isomorphisms.

## Implementation notes

The statements are the ringed-*space* ones of
`StacksFrontier.Topology.Sheaves.Cohomology.InternalHomEvaluation.EvaluationCriteria` with the
ringed space replaced by an arbitrary ringed site and the canonical derived tensor product and
derived internal Hom replaced by arbitrary data `T` and `Hd`. That generality is what the local
step of Stacks 0G40 needs: the criterion has to be applied on the slice site `X.over U`, which is
a ringed site and not a ringed space, and the ringed-space form does not reach it. The
ringed-space declarations are kept, as the one-line instantiations of these at
`Stacks.SheafOfModules.ringedSite`.

The transport along isomorphisms of the three objects needs a single application of the
three-variable functoriality `derivedSheafHomEvaluation_natural`, rather than one per variable,
because evaluation is a natural transformation of trifunctors. The intermediate object is
contravariant on both sides, so its isomorphism enters through its inverse.

## References

* [Stacks Project, Tag 0A97](https://stacks.math.columbia.edu/tag/0A97)
* [Stacks Project, Tag 0A92](https://stacks.math.columbia.edu/tag/0A92)
* [Stacks Project, Tag 01SB](https://stacks.math.columbia.edu/tag/01SB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u d

namespace Stacks.SheafOfModules

/-- **Conjugating a morphism by two isomorphisms does not change its invertibility.** Stated
over plain type variables, so that the two instances it needs are found without unfolding the
abbreviations naming a ringed space as a ringed site. -/
theorem isIso_conjugate_iff {C : Type*} [Category C] {W X Y Z : C}
    (e₁ : W ≅ X) (f : X ⟶ Y) (e₂ : Z ≅ Y) :
    IsIso (e₁.hom ≫ f ≫ e₂.inv) ↔ IsIso f :=
  (isIso_comp_left_iff _ _).trans (isIso_comp_right_iff _ _)

end Stacks.SheafOfModules

namespace AlgebraicGeometry.RingedSite

attribute [local instance] ringSheafSectionsCommRing presheafOfModulesMonoidalCategory
  curriedTensorPreservesZeroMorphisms curriedTensorObjPreservesZeroMorphisms

variable (X : RingedSite.{u, u, u})
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

omit [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)] in
/-- **The morphism induced on derived internal Homs by an isomorphism in each variable is an
isomorphism**, with inverse the morphism induced by the two inverses, for a derived internal Hom
datum at an arbitrary universe of morphisms. -/
theorem isIso_derivedSheafHomMap_of_isIso
    {A A' B B' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (a : A' ⟶ A) (b : B ⟶ B') [IsIso a] [IsIso b] :
    IsIso (derivedSheafHomMap X Hd a b) := by
  refine ⟨⟨derivedSheafHomMap X Hd (inv a) (inv b), ?_, ?_⟩⟩
  · refine Eq.trans (derivedSheafHomMap_comp X Hd a b (inv a) (inv b)) ?_
    rw [IsIso.inv_hom_id, IsIso.hom_inv_id]
    exact derivedSheafHomMap_id X Hd A B
  · refine Eq.trans (derivedSheafHomMap_comp X Hd (inv a) (inv b) a b) ?_
    rw [IsIso.hom_inv_id, IsIso.inv_hom_id]
    exact derivedSheafHomMap_id X Hd A' B'

variable (A B C :
    CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)

/-- **Derived evaluation at representatives is the class of the evaluation morphism of
complexes.** On a K-flat complex `A` and K-injective complexes `B` and `C`, the morphism of
Stacks 0A97 is the class of the evaluation morphism of internal Hom complexes of Stacks 0A92,
conjugated by the comparisons identifying its source with `Tot(SheafHom(B, C) ⊗_O A)` and its
target with `SheafHom(SheafHom(A, B), C)`. -/
theorem derivedSheafHomEvaluation_eq_conjugate
    (hA : Stacks.SheafOfModules.IsKFlat X.O A) [B.IsKInjective] [C.IsKInjective] :
    derivedSheafHomEvaluation X T Hd (DerivedCategory.Q.obj A) (DerivedCategory.Q.obj B)
        (DerivedCategory.Q.obj C) =
      (derivedEvaluationSourceComparison X T Hd A B C hA).hom ≫
        DerivedCategory.Q.map (evaluationMap X A B C) ≫
          (derivedEvaluationTargetComparison X Hd A B C).inv := by
  refine Eq.trans ?_ (Category.assoc _ _ _)
  exact (Iso.eq_comp_inv _).2 (derivedSheafHomEvaluation_model X T Hd A B C hA)

/-- **Derived evaluation at representatives is invertible exactly when its complex model is.**
Both sides of derived evaluation are identified with classes of complexes by isomorphisms, and
derived evaluation is the class of the evaluation morphism of Stacks 0A92 read through them. -/
theorem isIso_derivedSheafHomEvaluation_iff_isIso_Q_map
    (hA : Stacks.SheafOfModules.IsKFlat X.O A) [B.IsKInjective] [C.IsKInjective] :
    IsIso (derivedSheafHomEvaluation X T Hd (DerivedCategory.Q.obj A)
        (DerivedCategory.Q.obj B) (DerivedCategory.Q.obj C)) ↔
      IsIso (DerivedCategory.Q.map (evaluationMap X A B C)) :=
  Iff.trans
    (Iff.of_eq (congrArg IsIso (derivedSheafHomEvaluation_eq_conjugate X T Hd A B C hA)))
    (Stacks.SheafOfModules.isIso_conjugate_iff _ _ _)

/-- **Derived evaluation at representatives is invertible exactly when its complex model is a
quasi-isomorphism.** This is the previous criterion with the class of a morphism of complexes
replaced by the morphism itself, which is the form in which the condition is a statement about
cohomology sheaves — and hence local on the site. -/
theorem isIso_derivedSheafHomEvaluation_iff_quasiIso
    (hA : Stacks.SheafOfModules.IsKFlat X.O A) [B.IsKInjective] [C.IsKInjective] :
    IsIso (derivedSheafHomEvaluation X T Hd (DerivedCategory.Q.obj A)
        (DerivedCategory.Q.obj B) (DerivedCategory.Q.obj C)) ↔
      QuasiIso (evaluationMap X A B C) := by
  rw [isIso_derivedSheafHomEvaluation_iff_isIso_Q_map X T Hd A B C hA,
    DerivedCategory.isIso_Q_map_iff_quasiIso]

/-- **Invertibility of derived evaluation depends only on the isomorphism classes of its three
objects.** The three-variable functoriality of Stacks 0A97 exhibits derived evaluation at the new
objects as a factor of a composite whose other factor and whose total are invertible. The
intermediate object is contravariant on both sides, so its isomorphism enters inverted. -/
theorem isIso_derivedSheafHomEvaluation_of_iso
    {K K' L L' M M' :
      DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (eK : K ≅ K') (eL : L ≅ L') (eM : M ≅ M')
    (h : IsIso (derivedSheafHomEvaluation X T Hd K L M)) :
    IsIso (derivedSheafHomEvaluation X T Hd K' L' M') := by
  have := h
  have hsrc : IsIso (derivedTensorMap X T
      (derivedSheafHomMap X Hd eL.inv eM.hom) eK.hom) :=
    have := isIso_derivedSheafHomMap_of_isIso X Hd eL.inv eM.hom
    isIso_derivedTensorMap X T _ _
  have htgt : IsIso (derivedSheafHomMap X Hd
      (derivedSheafHomMap X Hd eK.hom eL.inv) eM.hom) :=
    have := isIso_derivedSheafHomMap_of_isIso X Hd eK.hom eL.inv
    isIso_derivedSheafHomMap_of_isIso X Hd _ _
  exact IsIso.of_isIso_fac_left
    (derivedSheafHomEvaluation_natural X T Hd eK.hom eL.inv eM.hom)

/-- **Derived evaluation is invertible as soon as its complex model is a quasi-isomorphism.**
For arbitrary objects `K`, `L`, `M` of `D(O)` presented by a K-flat complex `A` and K-injective
complexes `B` and `C`, the morphism of Stacks 0A97 is invertible whenever the evaluation morphism
of internal Hom complexes of Stacks 0A92 between those complexes is a quasi-isomorphism. -/
theorem isIso_derivedSheafHomEvaluation_of_quasiIso
    (K L M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (hA : Stacks.SheafOfModules.IsKFlat X.O A) [B.IsKInjective] [C.IsKInjective]
    (eA : DerivedCategory.Q.obj A ≅ K) (eB : DerivedCategory.Q.obj B ≅ L)
    (eC : DerivedCategory.Q.obj C ≅ M)
    (h : QuasiIso (evaluationMap X A B C)) :
    IsIso (derivedSheafHomEvaluation X T Hd K L M) :=
  isIso_derivedSheafHomEvaluation_of_iso X T Hd eA eB eC
    ((isIso_derivedSheafHomEvaluation_iff_quasiIso X T Hd A B C hA).2 h)

end AlgebraicGeometry.RingedSite

end
