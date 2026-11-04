module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedSheafHom
public import StacksFrontier.CategoryTheory.Adjunction.TransportedTensorHomAdjunction
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedCurryingInternalHomNaturality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedTensorSheafHomAdjunctionSlot

/-!
# Dinaturality of the tensor–internal-Hom adjunction on an algebraic space

For an algebraic space `X` and objects `P, P'` of `D(𝒪_X)`, the adjunctions
`- ⊗^L P ⊣ R𝓗om(P, -)` of Stacks 08J8
(`AlgebraicGeometry.Space.smallEtaleDerivedTensorSheafHomAdjunction`) are compatible with
morphisms `φ : P' ⟶ P`: postcomposing `ψ : A ⟶ R𝓗om(P, C)` with `R𝓗om(φ, C)` corresponds to
precomposing the transpose of `ψ` with `1 ⊗ φ`. This is the clause of Stacks 08J8 in its
internal-Hom variable, and it is what makes the map of Stacks 08I3 natural in its first variable.

## Main results

* `AlgebraicGeometry.Space.smallEtaleDerivedTensorSheafHomAdjunction_homEquiv_symm_dinatural`.

## Implementation notes

The adjunction of `X` is the adjunction of the equi-universe model of the small étale ringed site
carried through the derived equivalence with the model, so this is the dinaturality on the model,
`AlgebraicGeometry.RingedSite.derivedCurryHomEquiv_dinaturality`, carried through the equivalence
by `CategoryTheory.TransportedTensorHom.adjunction_homEquiv_symm_dinatural`, of which the
adjunction of `X` is an instance by definition. The file imports no more than the definition of
the adjunction, so that the instances found for the categories of modules here are the ones the
adjunction was defined with.

## References

* [Stacks Project, Tag 08J8](https://stacks.math.columbia.edu/tag/08J8)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

namespace AlgebraicGeometry.Space

universe u

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] hasMapBifunctor_sheafTensor_smallEtaleModel

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (X : AlgebraicSpaces B S hS)

/-- The adjunction of Stacks 08J8 on an algebraic space is, by definition, the adjunction of its
model transported along the derived equivalence. -/
theorem smallEtaleDerivedTensorSheafHomAdjunction_eq_transported
    (P : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))) :
    smallEtaleDerivedTensorSheafHomAdjunction B S hS X P =
      TransportedTensorHom.adjunction (smallEtaleModelDerivedEquivalence B S hS X)
        (smallEtaleDerivedTensor B S hS X)
        (Stacks.SheafOfModules.derivedTensorProductFunctor
          (smallEtaleModelRingedSite B S hS X.1 X.2))
        (RingedSite.derivedSheafHomBifunctor (smallEtaleModelRingedSite B S hS X.1 X.2))
        (smallEtaleModelDerivedTensorIso B S hS X)
        (RingedSite.derivedTensorSheafHomAdjunction (smallEtaleModelRingedSite B S hS X.1 X.2))
        P :=
  rfl

/-- **Stacks 08J8 on an algebraic space, in the internal-Hom variable.** For `φ : P' ⟶ P` and
`ψ : A ⟶ R𝓗om(P, C)`, the transpose of `ψ ≫ R𝓗om(φ, C)` is the transpose of `ψ` precomposed
with `1 ⊗ φ`. -/
theorem smallEtaleDerivedTensorSheafHomAdjunction_homEquiv_symm_dinatural
    (A C : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    {P P' : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))}
    (φ : P' ⟶ P) (ψ : A ⟶ ((smallEtaleDerivedSheafHom B S hS X).obj (op P)).obj C) :
    ((smallEtaleDerivedTensorSheafHomAdjunction B S hS X P').homEquiv A C).symm
        (ψ ≫ ((smallEtaleDerivedSheafHom B S hS X).map φ.op).app C) =
      ((smallEtaleDerivedTensor B S hS X).obj A).map φ ≫
        ((smallEtaleDerivedTensorSheafHomAdjunction B S hS X P).homEquiv A C).symm ψ := by
  rw [smallEtaleDerivedTensorSheafHomAdjunction_eq_transported,
    smallEtaleDerivedTensorSheafHomAdjunction_eq_transported]
  refine TransportedTensorHom.adjunction_homEquiv_symm_dinatural
    (smallEtaleModelDerivedEquivalence B S hS X) (smallEtaleDerivedTensor B S hS X)
    (Stacks.SheafOfModules.derivedTensorProductFunctor (smallEtaleModelRingedSite B S hS X.1 X.2))
    (RingedSite.derivedSheafHomBifunctor (smallEtaleModelRingedSite B S hS X.1 X.2))
    (smallEtaleModelDerivedTensorIso B S hS X)
    (RingedSite.derivedTensorSheafHomAdjunction (smallEtaleModelRingedSite B S hS X.1 X.2))
    (fun A C Q Q' v ψ => ?_) A C φ ψ
  have key : ∀ {Q₀ : _} (x : A ⟶ ((RingedSite.derivedSheafHomBifunctor
      (smallEtaleModelRingedSite B S hS X.1 X.2)).obj (op Q₀)).obj C),
      ((RingedSite.derivedTensorSheafHomAdjunction (smallEtaleModelRingedSite B S hS X.1 X.2)
        Q₀).homEquiv A C).symm x =
        RingedSite.derivedCurryHomEquiv (smallEtaleModelRingedSite B S hS X.1 X.2) A Q₀ C x :=
    fun {Q₀} x => (Adjunction.homEquiv_counit _ _ _ _).trans
      ((congrArg (_ ≫ ·) (RingedSite.derivedTensorSheafHomAdjunction_counit_app _ Q₀ C)).trans
        ((RingedSite.derivedCurryHomEquiv_naturality_source _ x (𝟙 _)).symm.trans
          (congrArg _ (Category.comp_id x))))
  refine (key _).trans (Eq.trans ?_ (congrArg _ (key ψ).symm))
  convert RingedSite.derivedCurryHomEquiv_dinaturality (smallEtaleModelRingedSite B S hS X.1 X.2)
    A C v ψ using 2

end AlgebraicGeometry.Space

end
