module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.DualTensorSheafHom
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedTensorSheafHomAdjunctionSlot
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.EvaluationPerfect
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.Duals
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.CanonicalBifunctorComparison

/-!
# Tensoring with a perfect object is a right adjoint

Let `(𝒞, 𝒪)` be a ringed site and let `E` be a perfect object of `D(𝒪)`, with dual
`E^∨ = RSheafHom(E, 𝒪)`. Then the functor `- ⊗^𝐋_𝒪 E` is right adjoint to `- ⊗^𝐋_𝒪 E^∨`:

`Hom_{D(𝒪)}(T ⊗^𝐋_𝒪 E^∨, M) = Hom_{D(𝒪)}(T, M ⊗^𝐋_𝒪 E)`.

In particular `- ⊗^𝐋_𝒪 E` preserves all limits that exist in `D(𝒪)`, for instance countable
products.

## Main results

* `AlgebraicGeometry.RingedSite.derivedTensorFlipObjIsoDerivedSheafHomDual`: the natural
  isomorphism `- ⊗^𝐋_𝒪 E ≅ RSheafHom(E^∨, -)` for perfect `E`.
* `AlgebraicGeometry.RingedSite.derivedTensorDualAdjunction`: `- ⊗^𝐋_𝒪 E^∨ ⊣ - ⊗^𝐋_𝒪 E`.
* `AlgebraicGeometry.RingedSite.preservesLimitsOfSize_derivedTensor_flip_obj_of_isPerfect`:
  `- ⊗^𝐋_𝒪 E` preserves limits.

## Implementation notes

The derived tensor product in the statements is
`Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor`; the inputs of [Stacks, Tag 08J8]
and [Stacks, Tag 08JJ] are stated over `Stacks.SheafOfModules.derivedTensorProductFunctor`, and
the two are identified by `AlgebraicGeometry.RingedSite.derivedTensorFunctorIso`. The derived
category is the standard model.

## References

* [Stacks Project, Tag 08J8](https://stacks.math.columbia.edu/tag/08J8)
* [Stacks Project, Tag 08JJ](https://stacks.math.columbia.edu/tag/08JJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.SheafOfModules.Tensor (sheafTensor)

universe w w' u

namespace AlgebraicGeometry.RingedSite

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] ringSheafSectionsCommRing presheafOfModulesMonoidalCategory
  curriedTensorPreservesZeroMorphisms curriedTensorObjPreservesZeroMorphisms

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ V : X.C, HasSheafify (X.J.over V) AddCommGrpCat.{u}]
  [∀ V : X.C, (X.J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ V : X.C, (X.J.over V).HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
  [∀ V : X.C, (X.J.over V).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [(sheafTensor.{u, u, u} X.O).Additive]
  [∀ A, ((sheafTensor.{u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (sheafTensor X.O) (ComplexShape.up ℤ)]

/-- **Tensoring with a perfect object is derived internal Hom out of its dual.** For a perfect
object `E` of `D(𝒪)` there is an isomorphism `M ⊗^𝐋_𝒪 E ≅ RSheafHom(E^∨, M)`, natural in `M`:
the two derived tensor bifunctors of the site agree, `E ≅ E^∨∨` because `E` is perfect, and
`M ⊗^𝐋_𝒪 E^∨∨ ≅ RSheafHom(E^∨, M)` is [Stacks, Tag 08JJ] at the perfect object `E^∨`. -/
def derivedTensorFlipObjIsoDerivedSheafHomDual
    (E : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (hE : X.IsPerfect E) :
    (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.O).flip.obj E ≅
      (derivedSheafHomBifunctor X).obj (op (derivedDual X E)) :=
  haveI := isIso_derivedBidual_of_isPerfect X
    (Stacks.SheafOfModules.canonicalDerivedTensorProduct X) E hE
  ((flipFunctor _ _ _).mapIso (derivedTensorFunctorIso X)).symm.app E ≪≫
    (Stacks.SheafOfModules.derivedTensorProductFunctor X).flip.mapIso
      (asIso (derivedBidual X (Stacks.SheafOfModules.canonicalDerivedTensorProduct X) E)) ≪≫
    NatIso.ofComponents
      (fun M => derivedDualTensorSheafHomIso X (derivedDual X E) M (isPerfect_derivedDual X E hE))
      (derivedDualTensorSheafHomIso_naturality X (derivedDual X E) (isPerfect_derivedDual X E hE))

/-- **Tensoring with a perfect object is a right adjoint**: for a perfect object `E` of `D(𝒪)`,
`- ⊗^𝐋_𝒪 E^∨ ⊣ - ⊗^𝐋_𝒪 E`. It is the adjunction `- ⊗^𝐋_𝒪 E^∨ ⊣ RSheafHom(E^∨, -)` of
[Stacks, Tag 08J8], with its two sides rewritten along the two derived tensor bifunctors of the
site and along `derivedTensorFlipObjIsoDerivedSheafHomDual`. -/
def derivedTensorDualAdjunction
    (E : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (hE : X.IsPerfect E) :
    (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.O).flip.obj (derivedDual X E) ⊣
      (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.O).flip.obj E :=
  ((derivedTensorSheafHomAdjunction X (derivedDual X E)).ofNatIsoLeft
      (((flipFunctor _ _ _).mapIso (derivedTensorFunctorIso X)).app
        (derivedDual X E))).ofNatIsoRight
    (derivedTensorFlipObjIsoDerivedSheafHomDual X E hE).symm

/-- **Tensoring with a perfect object preserves limits.** For a perfect object `E` of `D(𝒪)` the
functor `- ⊗^𝐋_𝒪 E` is a right adjoint (`derivedTensorDualAdjunction`), so it preserves every
limit that exists in `D(𝒪)`, for instance countable products. -/
theorem preservesLimitsOfSize_derivedTensor_flip_obj_of_isPerfect
    (E : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (hE : X.IsPerfect E) :
    PreservesLimitsOfSize.{w, w'}
      ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.O).flip.obj E) :=
  (derivedTensorDualAdjunction X E hE).rightAdjoint_preservesLimits

end AlgebraicGeometry.RingedSite

end
