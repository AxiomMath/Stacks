module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedEvaluation
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedInternalHom
import StacksCore.Tactic.StacksAttribute

/-!
# Evaluation for the derived internal hom on a ringed space

Let `(X, O_X)` be a ringed space and let `K`, `L`, `M` be objects of `D(O_X)`. Evaluating a map
`L ⟶ M` on the image of a map `K ⟶ L` gives a canonical morphism

`RSheafHom(L, M) ⊗^L_{O_X} K ⟶ RSheafHom(RSheafHom(K, L), M)`

in `D(O_X)`, functorial in all three objects. This is Stacks 0A8U.

A topological space with a sheaf of commutative rings *is* a ringed site, namely the site of its
opens with the open-cover topology, so the ringed-site derived evaluation of Stacks 0A97 applies
verbatim. The declarations below read it off along `Stacks.SheafOfModules.ringedSite`, for the
derived internal hom of `Stacks.SheafOfModules.derivedInternalHom`.

## Main definitions

* `Stacks.SheafOfModules.derivedSheafHomEvaluation` (Stacks 0A8U): the canonical evaluation
  morphism.

## Main results

* `Stacks.SheafOfModules.derivedSheafHomEvaluation_natural` (Stacks 0A8U): evaluation is
  covariant in `K`, contravariant in `L` and covariant in `M`, simultaneously.
* `Stacks.SheafOfModules.derivedSheafHomEvaluation_model` (Stacks 0A8U): on a K-flat
  representative of `K` and K-injective representatives of `L` and `M`, evaluation is the class
  of the evaluation morphism of internal Hom complexes.

## Implementation notes

The source and target comparisons of the model computation are the ringed-site ones: the source
comparison identifies `RSheafHom(L, M) ⊗^L_{O_X} K` with the class of the total tensor complex
`Tot(SheafHom^•(L, M) ⊗_{O_X} K)` when `K` is K-flat, and the target comparison identifies
`RSheafHom(RSheafHom(K, L), M)` with the class of `SheafHom^•(SheafHom^•(K, L), M)` when `L` and
`M` are K-injective. With those two in place the morphism is pinned down by one equation.

The complexes below are indexed by `structureSheaf Rc` and the site-level statements they are
checked against by `(ringedSite Rc).ringSheaf`, i.e. by `Tensor.ringSheaf Rc`; these are the same
sheaf of rings, but only after `sheafCompose` is unfolded, which is invisible at the transparency
typeclass inference uses, so the K-injectivity hypotheses of the model computation are not matched
against the site-level ones. `sheafCompose` is therefore made `implicit_reducible` locally, as it
is in the file that reads off the derived internal hom itself.

The complex-level evaluation morphism appearing there is
`AlgebraicGeometry.RingedSite.evaluationMap`. This is a second construction of Stacks 0A92,
parallel to the `Stacks.Cohomology.evaluation` that
`Stacks.SheafOfModules.evaluateAndMore` of Stacks 0A8P is built from; the library carries no
comparison between the two, so the model computation below is stated against the former.

## References

* [Stacks Project, Tag 0A8U](https://stacks.math.columbia.edu/tag/0A8U)
* [Stacks Project, Tag 0A97](https://stacks.math.columbia.edu/tag/0A97)
* [Stacks Project, Tag 0A92](https://stacks.math.columbia.edu/tag/0A92)
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
  [(Tensor.sheafTensor.{u, u, u, u, u} Rc).Additive]
  [∀ M, ((Tensor.sheafTensor.{u, u, u, u, u} Rc).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex (SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} Rc)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Tensor.sheafTensor Rc) (ComplexShape.up ℤ)]

/-- **Stacks 0A8U.** For objects `K`, `L`, `M` of `D(O_X)` on a ringed space there is a canonical
evaluation morphism

`RSheafHom(L, M) ⊗^L_{O_X} K ⟶ RSheafHom(RSheafHom(K, L), M)`

in `D(O_X)`, obtained from the evaluation morphism of internal Hom complexes after passing to a
K-flat representative of `K` and K-injective representatives of `L` and `M`. -/
@[stacks 0A8U "the canonical evaluation morphism"]
def derivedSheafHomEvaluation (K L M : DerivedCategory (SheafOfModules.{u} (Tensor.ringSheaf Rc))) :
    ((derivedTensor Rc).obj (((derivedSheafHom Rc).obj (op L)).obj M)).obj K ⟶
      ((derivedSheafHom Rc).obj (op (((derivedSheafHom Rc).obj (op K)).obj L))).obj M :=
  RingedSite.derivedSheafHomEvaluation (ringedSite Rc)
    (canonicalDerivedTensorProduct (ringedSite Rc)) (derivedInternalHom Rc) K L M

/-- **Stacks 0A8U.** Derived evaluation is functorial in all three objects at once: covariant in
the object being tensored, contravariant in the source of the inner internal hom, and covariant
in its target. -/
@[stacks 0A8U "functoriality in all three objects"]
theorem derivedSheafHomEvaluation_natural
    {K K' L L' M M' : DerivedCategory (SheafOfModules.{u} (Tensor.ringSheaf Rc))}
    (f : K ⟶ K') (g : L' ⟶ L) (h : M ⟶ M') :
    derivedTensorMap Rc (derivedSheafHomMap Rc g h) f ≫
        derivedSheafHomEvaluation Rc K' L' M' =
      derivedSheafHomEvaluation Rc K L M ≫
        derivedSheafHomMap Rc (derivedSheafHomMap Rc f g) h :=
  RingedSite.derivedSheafHomEvaluation_natural (ringedSite Rc)
    (canonicalDerivedTensorProduct (ringedSite Rc)) (derivedInternalHom Rc) f g h

/-- **Stacks 0A8U.** On a K-flat representative `P` of `K` and K-injective representatives `J`
of `L` and `I` of `M`, derived evaluation is the class of the evaluation morphism of internal
Hom complexes `Tot(SheafHom^•(J, I) ⊗_{O_X} P) ⟶ SheafHom^•(SheafHom^•(P, J), I)`. -/
@[stacks 0A8U "comparison with evaluation of complexes"]
theorem derivedSheafHomEvaluation_model
    (P J I : CochainComplex (SheafOfModules.{u} (Tensor.ringSheaf Rc)) ℤ)
    (hP : IsKFlat Rc P) [J.IsKInjective] [I.IsKInjective] :
    derivedSheafHomEvaluation Rc (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj J)
          (DerivedCategory.Q.obj I) ≫
        (RingedSite.derivedEvaluationTargetComparison (ringedSite Rc)
          (derivedInternalHom Rc) P J I).hom =
      (RingedSite.derivedEvaluationSourceComparison (ringedSite Rc)
          (canonicalDerivedTensorProduct (ringedSite Rc)) (derivedInternalHom Rc)
          P J I hP).hom ≫
        DerivedCategory.Q.map (RingedSite.evaluationMap (ringedSite Rc) P J I) :=
  RingedSite.derivedSheafHomEvaluation_model (ringedSite Rc)
    (canonicalDerivedTensorProduct (ringedSite Rc)) (derivedInternalHom Rc) P J I hP

end Stacks.SheafOfModules

end
