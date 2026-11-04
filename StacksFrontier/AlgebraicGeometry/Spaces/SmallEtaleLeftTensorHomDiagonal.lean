module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedPullbackTensorCoherence
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedSheafHomTransport
public import StacksFrontier.CategoryTheory.Adjunction.LeftTensorHomDiagonalTransport

/-!
# The tensor–Hom diagonal on an algebraic space and on its equi-universe model

Let `X` be an algebraic space. The derived internal Hom of `D(𝒪_X)` and its adjunction with
`⊗^L` are those of the equi-universe model `AlgebraicGeometry.Space.smallEtaleModelRingedSite`,
transported along the derived equivalence `E : D(𝒪_X) ≌ D(𝒪_model)`, and `E` carries `⊗^L` to
the derived tensor product of the model by Stacks 07A4 for the morphism of ringed topoi from the
model. By the compatibility of Stacks 07A4 with the associators of `⊗^L`, the tensor–Hom
diagonal `P ⊗^L R𝓗om(M, K) ⟶ R𝓗om(M, P ⊗^L K)` of `X` built from the associator of `⊗^L` is
the diagonal of the model at `E P`, `E M`, `E K`, brought back along `E`.

## Main results

* `AlgebraicGeometry.Space.smallEtaleModelDerivedTensorIso_associativity`: `E` is compatible
  with the associators of `⊗^L` on `X` and on the model.
* `AlgebraicGeometry.Space.isIso_leftTensorHomDiagonal_of_model`: the diagonal of `X` is
  invertible as soon as the diagonal of the model is.

## References

* [Stacks Project, Tag 07A4](https://stacks.math.columbia.edu/tag/07A4)
* [Stacks Project, Tag 0BYU](https://stacks.math.columbia.edu/tag/0BYU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

attribute [local instance 10000] HasDerivedCategory.standard

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}


attribute [local instance 20000] AddCommGrpCat.FilteredColimits.forget_preservesFilteredColimits

attribute [local instance 5000] SmallEtale.instHasSheafify SmallEtale.instWEqualsLocallyBijective


/-- **The derived equivalence with the model is compatible with the associators of `⊗^L`**,
through its comparison `E(K ⊗^L L) ≅ E K ⊗^L E L` of Stacks 07A4. -/
theorem smallEtaleModelDerivedTensorIso_associativity (X : AlgebraicSpaces B S hS)
    (A A' A'' : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))) :
    (smallEtaleModelDerivedEquivalence B S hS X).functor.map
          (smallEtaleDerivedTensorAssociator X A A' A'').hom ≫
        (smallEtaleModelDerivedTensorIso B S hS X).hom.app
          (A, ((smallEtaleDerivedTensor B S hS X).obj A').obj A'') ≫
        ((Stacks.SheafOfModules.derivedTensorProductFunctor
          (smallEtaleModelRingedSite B S hS X.1 X.2)).obj
            ((smallEtaleModelDerivedEquivalence B S hS X).functor.obj A)).map
          ((smallEtaleModelDerivedTensorIso B S hS X).hom.app (A', A'')) =
      (smallEtaleModelDerivedTensorIso B S hS X).hom.app
          (((smallEtaleDerivedTensor B S hS X).obj A).obj A', A'') ≫
        ((Stacks.SheafOfModules.derivedTensorProductFunctor
          (smallEtaleModelRingedSite B S hS X.1 X.2)).map
            ((smallEtaleModelDerivedTensorIso B S hS X).hom.app (A, A'))).app
          ((smallEtaleModelDerivedEquivalence B S hS X).functor.obj A'') ≫
        ((Stacks.SheafOfModules.canonicalDerivedTensorProduct
          (smallEtaleModelRingedSite B S hS X.1 X.2)).associatorGeneral
            ((smallEtaleModelDerivedEquivalence B S hS X).functor.obj A)
            ((smallEtaleModelDerivedEquivalence B S hS X).functor.obj A')
            ((smallEtaleModelDerivedEquivalence B S hS X).functor.obj A'')).hom :=
  CategoryTheory.PullbackInternalHom.assoc_of_natIso (smallEtaleDerivedTensorAssociator X)
    (Stacks.SheafOfModules.canonicalDerivedTensorProduct
      (smallEtaleModelRingedSite B S hS X.1 X.2)).associatorGeneral
    (smallEtaleModelDerivedPullbackIso B S hS X)
    (Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullbackTensorIso
      (smallEtaleModelRingedToposHom B S hS X)
      (Stacks.SheafOfModules.canonicalDerivedTensorProduct
        (smallEtaleModelRingedSite B S hS X.1 X.2))
      (smallEtaleDerivedTensorProduct B S hS X))
    (smallEtaleModelDerivedTensorIso B S hS X)
    (fun A A' => by simp [smallEtaleModelDerivedTensorIso])
    (fun a b e => (Stacks.SheafOfModules.canonicalDerivedTensorProduct
      (smallEtaleModelRingedSite B S hS X.1 X.2)).associatorGeneral_naturality a b e)
    A A' A''
    (Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullbackTensorIso_associativity
      (smallEtaleModelRingedToposHom B S hS X)
      (Stacks.SheafOfModules.canonicalDerivedTensorProduct
        (smallEtaleModelRingedSite B S hS X.1 X.2))
      (smallEtaleDerivedTensorProduct B S hS X) A A' A'')

/-- **The tensor–Hom diagonal of `X` is invertible as soon as that of the model is**, at the
images of the three objects under the derived equivalence. Both diagonals are built from the
associators of `⊗^L`: `P ⊗^L R𝓗om(M, K) ⟶ R𝓗om(M, P ⊗^L K)` is the adjoint, for
`- ⊗^L M ⊣ R𝓗om(M, -)`, of `(P ⊗^L R𝓗om(M, K)) ⊗^L M ≅ P ⊗^L (R𝓗om(M, K) ⊗^L M) ⟶ P ⊗^L K`. -/
theorem isIso_leftTensorHomDiagonal_of_model (X : AlgebraicSpaces B S hS)
    (P M K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (h : IsIso (CategoryTheory.PullbackInternalHom.leftTensorHomDiagonal
      (Stacks.SheafOfModules.derivedTensorProductFunctor (smallEtaleModelRingedSite B S hS X.1 X.2))
      (RingedSite.derivedSheafHomBifunctor (smallEtaleModelRingedSite B S hS X.1 X.2))
      (RingedSite.derivedTensorSheafHomAdjunction (smallEtaleModelRingedSite B S hS X.1 X.2))
      (Stacks.SheafOfModules.canonicalDerivedTensorProduct
        (smallEtaleModelRingedSite B S hS X.1 X.2)).associatorGeneral
      ((smallEtaleModelDerivedEquivalence B S hS X).functor.obj P)
      ((smallEtaleModelDerivedEquivalence B S hS X).functor.obj M)
      ((smallEtaleModelDerivedEquivalence B S hS X).functor.obj K))) :
    IsIso (CategoryTheory.PullbackInternalHom.leftTensorHomDiagonal
      (smallEtaleDerivedTensor B S hS X) (smallEtaleDerivedSheafHom B S hS X)
      (smallEtaleDerivedTensorSheafHomAdjunction B S hS X) (smallEtaleDerivedTensorAssociator X)
      P M K) :=
  CategoryTheory.PullbackInternalHom.isIso_leftTensorHomDiagonal_transport
    (smallEtaleModelDerivedEquivalence B S hS X) (smallEtaleDerivedTensor B S hS X)
    (Stacks.SheafOfModules.derivedTensorProductFunctor (smallEtaleModelRingedSite B S hS X.1 X.2))
    (smallEtaleModelDerivedTensorIso B S hS X)
    (RingedSite.derivedSheafHomBifunctor (smallEtaleModelRingedSite B S hS X.1 X.2))
    (RingedSite.derivedTensorSheafHomAdjunction (smallEtaleModelRingedSite B S hS X.1 X.2))
    (smallEtaleDerivedTensorSheafHomAdjunction B S hS X)
    (smallEtaleDerivedTensorRightIso B S hS X) (smallEtaleDerivedTensorRightIso_hom_app X)
    (smallEtaleDerivedTensorSheafHomAdjunction_eq X)
    (smallEtaleDerivedTensorAssociator X)
    (Stacks.SheafOfModules.canonicalDerivedTensorProduct
      (smallEtaleModelRingedSite B S hS X.1 X.2)).associatorGeneral
    (smallEtaleModelDerivedTensorIso_associativity X)
    (fun A _ _ b E => (Stacks.SheafOfModules.canonicalDerivedTensorProduct
      (smallEtaleModelRingedSite B S hS X.1 X.2)).associatorGeneral_naturality_middle A b E)
    P M K h

end AlgebraicGeometry.Space

end
