module

public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHomEvaluation.DerivedEvaluation
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHomEvaluation.EvaluationModels

/-!
# When derived evaluation on a ringed space is invertible

Let `(X, O_X)` be a ringed space and let `K`, `L`, `M` be objects of `D(O_X)`. The evaluation
morphism

`RSheafHom(L, M) ⊗^L_{O_X} K ⟶ RSheafHom(RSheafHom(K, L), M)`

of Stacks 0A8U is, on a K-flat representative of `K` and K-injective representatives of `L` and
`M`, the class of the evaluation morphism of internal Hom complexes of Stacks 0A92, conjugated by
the two comparisons identifying its source and its target with classes of complexes. Conjugating
by isomorphisms does not change invertibility, so the derived morphism is invertible exactly when
that one morphism of complexes is a quasi-isomorphism — a condition on cohomology sheaves with no
derived category left in it.

Together with the transport of invertibility along isomorphisms of the three objects, which is
the three-variable functoriality of Stacks 0A8U, this is the form in which any statement that
derived evaluation is invertible is to be checked.

## Main results

* `Stacks.SheafOfModules.derivedSheafHomEvaluation_eq_conjugate`: derived evaluation at
  representatives is the class of the evaluation morphism of complexes, conjugated by the source
  and target comparisons.
* `Stacks.SheafOfModules.isIso_derivedSheafHomEvaluation_iff_isIso_Q_map` and
  `Stacks.SheafOfModules.isIso_derivedSheafHomEvaluation_iff_quasiIso`: derived evaluation at
  representatives is invertible if and only if the evaluation morphism of complexes is a
  quasi-isomorphism.
* `Stacks.SheafOfModules.isIso_derivedSheafHomEvaluation_of_iso`: invertibility of derived
  evaluation depends only on the isomorphism classes of the three objects.
* `Stacks.SheafOfModules.isIso_derivedSheafHomEvaluation_of_quasiIso`: the two combined, in the
  shape a consumer uses — arbitrary objects, with representatives given by isomorphisms.
* `Stacks.SheafOfModules.isIso_conjugate_iff` has moved to
  `StacksFrontier.Topology.Sheaves.Cohomology.InternalHomEvaluation.EvaluationModels`, where the
  conjugation step is now carried out.

## Implementation notes

Every declaration below is the instantiation at `Stacks.SheafOfModules.ringedSite` of the
ringed-*site* statement of the same name in
`StacksFrontier.Topology.Sheaves.Cohomology.InternalHomEvaluation.EvaluationModels`, which is where
the proofs live: the criterion is needed on the slice site `X.over V` as well, which is a ringed
site and not a ringed space, so stating it twice would have been stating it at two different
levels of generality. The ringed-space names are kept because they are the vocabulary of the
ringed-space files that consume them.

The criterion is stated in both the `IsIso (DerivedCategory.Q.map ...)` form and the `QuasiIso`
form, as the corresponding criterion for the diagonal of Stacks 0BYS is in
`AlgebraicGeometry.RingedSite.isIso_derivedTensorHomDiagonal_iff_quasiIso_ofModels`: the first is
what the model computation gives directly and what composes with the rest of the
derived-category API, the second is `DerivedCategory.isIso_Q_map_iff_quasiIso` applied to it.

The transport needs a single application of the three-variable functoriality, rather than one per
variable, because evaluation is a natural transformation of trifunctors. The intermediate object
is contravariant on both sides, so its isomorphism enters through its inverse.

Each statement here is phrased over `SheafOfModules.{u} (Tensor.ringSheaf Rc)`, i.e.
`SheafOfModules` of `(sheafCompose _ (forget₂ CommRingCat RingCat)).obj Rc`, while the site-level
statements being instantiated are phrased over the ringed site's `Tensor.ringSheaf Rc`, i.e.
`SheafOfModules` of `Rc.obj ⋙ forget₂ CommRingCat RingCat`. The two agree only after unfolding
`sheafCompose`, which is a plain `def`: term elaboration unfolds it, so the types match, but
instance synthesis does not, so the `IsIso` and `IsKInjective` hypotheses in scope here are
invisible to the instance arguments of the site-level lemmas. `sheafCompose` is therefore made
`implicit_reducible` locally, as it is in `DerivedEvaluation` and in the other files of this
development that instantiate site-level statements at the ringed-space spelling. The attribute is
used rather than `@`-form calls with the hypotheses passed positionally because seven instance
arguments across five declarations are affected, not one.

## References

* [Stacks Project, Tag 0A8U](https://stacks.math.columbia.edu/tag/0A8U)
* [Stacks Project, Tag 0A92](https://stacks.math.columbia.edu/tag/0A92)
* [Stacks Project, Tag 0A97](https://stacks.math.columbia.edu/tag/0A97)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry

universe u

namespace Stacks.SheafOfModules

attribute [local instance] HasDerivedCategory.standard

attribute [local implicit_reducible] CategoryTheory.sheafCompose

variable {X : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} X)
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The morphism induced on derived internal Homs by an isomorphism in each variable is an
isomorphism, with inverse the morphism induced by the two inverses. -/
theorem isIso_derivedSheafHomMap
    {A A' B B' : DerivedCategory (SheafOfModules.{u} (Tensor.ringSheaf Rc))}
    (a : A' ⟶ A) (b : B ⟶ B') [IsIso a] [IsIso b] :
    IsIso (derivedSheafHomMap Rc a b) :=
  RingedSite.isIso_derivedSheafHomMap_of_isIso (ringedSite Rc) (derivedInternalHom Rc) a b

variable [(Tensor.sheafTensor.{u, u, u, u, u} Rc).Additive]
  [∀ M, ((Tensor.sheafTensor.{u, u, u, u, u} Rc).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex (SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} Rc)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Tensor.sheafTensor Rc) (ComplexShape.up ℤ)]

/-- The morphism induced on derived tensor products by an isomorphism in each factor is an
isomorphism, with inverse the morphism induced by the two inverses. -/
theorem isIso_derivedTensorMap
    {A A' B B' : DerivedCategory (SheafOfModules.{u} (Tensor.ringSheaf Rc))}
    (a : A ⟶ A') (b : B ⟶ B') [IsIso a] [IsIso b] :
    IsIso (derivedTensorMap Rc a b) :=
  RingedSite.isIso_derivedTensorMap (ringedSite Rc)
    (canonicalDerivedTensorProduct (ringedSite Rc)) a b

/-- **Derived evaluation at representatives is the class of the evaluation morphism of
complexes.** On a K-flat complex `P` and K-injective complexes `J` and `I`, the morphism of
Stacks 0A8U is the class of the evaluation morphism of internal Hom complexes of Stacks 0A92,
conjugated by the comparisons identifying its source with `Tot(SheafHom(J, I) ⊗_{O_X} P)` and its
target with `SheafHom(SheafHom(P, J), I)`. -/
theorem derivedSheafHomEvaluation_eq_conjugate
    (P J I : CochainComplex (SheafOfModules.{u} (Tensor.ringSheaf Rc)) ℤ)
    (hP : IsKFlat Rc P) [J.IsKInjective] [I.IsKInjective] :
    derivedSheafHomEvaluation Rc (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj J)
        (DerivedCategory.Q.obj I) =
      (RingedSite.derivedEvaluationSourceComparison (ringedSite Rc)
            (canonicalDerivedTensorProduct (ringedSite Rc)) (derivedInternalHom Rc)
            P J I hP).hom ≫
        DerivedCategory.Q.map (RingedSite.evaluationMap (ringedSite Rc) P J I) ≫
          (RingedSite.derivedEvaluationTargetComparison (ringedSite Rc)
            (derivedInternalHom Rc) P J I).inv :=
  RingedSite.derivedSheafHomEvaluation_eq_conjugate (ringedSite Rc)
    (canonicalDerivedTensorProduct (ringedSite Rc)) (derivedInternalHom Rc) P J I hP

/-- **Derived evaluation at representatives is invertible exactly when its complex model is.**
Both sides of derived evaluation are identified with classes of complexes by isomorphisms, and
derived evaluation is the class of the evaluation morphism of Stacks 0A92 read through them. -/
theorem isIso_derivedSheafHomEvaluation_iff_isIso_Q_map
    (P J I : CochainComplex (SheafOfModules.{u} (Tensor.ringSheaf Rc)) ℤ)
    (hP : IsKFlat Rc P) [J.IsKInjective] [I.IsKInjective] :
    IsIso (derivedSheafHomEvaluation Rc (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj J)
        (DerivedCategory.Q.obj I)) ↔
      IsIso (DerivedCategory.Q.map (RingedSite.evaluationMap (ringedSite Rc) P J I)) :=
  RingedSite.isIso_derivedSheafHomEvaluation_iff_isIso_Q_map (ringedSite Rc)
    (canonicalDerivedTensorProduct (ringedSite Rc)) (derivedInternalHom Rc) P J I hP

/-- **Derived evaluation at representatives is invertible exactly when its complex model is a
quasi-isomorphism.** This is the previous criterion with the class of a morphism of complexes
replaced by the morphism itself, which is the form in which the condition is a statement about
cohomology sheaves. -/
theorem isIso_derivedSheafHomEvaluation_iff_quasiIso
    (P J I : CochainComplex (SheafOfModules.{u} (Tensor.ringSheaf Rc)) ℤ)
    (hP : IsKFlat Rc P) [J.IsKInjective] [I.IsKInjective] :
    IsIso (derivedSheafHomEvaluation Rc (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj J)
        (DerivedCategory.Q.obj I)) ↔
      QuasiIso (RingedSite.evaluationMap (ringedSite Rc) P J I) :=
  RingedSite.isIso_derivedSheafHomEvaluation_iff_quasiIso (ringedSite Rc)
    (canonicalDerivedTensorProduct (ringedSite Rc)) (derivedInternalHom Rc) P J I hP

/-- **Invertibility of derived evaluation depends only on the isomorphism classes of its three
objects.** The three-variable functoriality of Stacks 0A8U exhibits derived evaluation at the new
objects as a factor of a composite whose other factor and whose total are invertible. The
intermediate object is contravariant on both sides, so its isomorphism enters inverted. -/
theorem isIso_derivedSheafHomEvaluation_of_iso
    {K K' L L' M M' : DerivedCategory (SheafOfModules.{u} (Tensor.ringSheaf Rc))}
    (eK : K ≅ K') (eL : L ≅ L') (eM : M ≅ M')
    (h : IsIso (derivedSheafHomEvaluation Rc K L M)) :
    IsIso (derivedSheafHomEvaluation Rc K' L' M') :=
  RingedSite.isIso_derivedSheafHomEvaluation_of_iso (ringedSite Rc)
    (canonicalDerivedTensorProduct (ringedSite Rc)) (derivedInternalHom Rc) eK eL eM h

/-- **Derived evaluation is invertible as soon as its complex model is a quasi-isomorphism.**
For arbitrary objects `K`, `L`, `M` of `D(O_X)` presented by a K-flat complex `P` and K-injective
complexes `J` and `I`, the morphism of Stacks 0A8U is invertible whenever the evaluation morphism
of internal Hom complexes of Stacks 0A92 between those complexes is a quasi-isomorphism. -/
theorem isIso_derivedSheafHomEvaluation_of_quasiIso
    (K L M : DerivedCategory (SheafOfModules.{u} (Tensor.ringSheaf Rc)))
    (P J I : CochainComplex (SheafOfModules.{u} (Tensor.ringSheaf Rc)) ℤ)
    (hP : IsKFlat Rc P) [J.IsKInjective] [I.IsKInjective]
    (eP : DerivedCategory.Q.obj P ≅ K) (eJ : DerivedCategory.Q.obj J ≅ L)
    (eI : DerivedCategory.Q.obj I ≅ M)
    (h : QuasiIso (RingedSite.evaluationMap (ringedSite Rc) P J I)) :
    IsIso (derivedSheafHomEvaluation Rc K L M) :=
  isIso_derivedSheafHomEvaluation_of_iso Rc eP eJ eI
    ((isIso_derivedSheafHomEvaluation_iff_quasiIso Rc P J I hP).2 h)

end Stacks.SheafOfModules

end
