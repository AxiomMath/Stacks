module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedSheafHomTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedSheafHomTransportSupplement
public import StacksFrontier.CategoryTheory.Adjunction.TransportAdjunctionDinaturality
public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedTensorSheafHomDinaturality
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedSheafHomDinaturality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedTensorSheafHomDinaturalitySupplement
public meta import StacksFrontier.Tactic.HEqCongr

/-!
# Dinaturality of Stacks 08J8 on an algebraic space in the middle variable

For an algebraic space `X` and `u : P' ⟶ P` in `D(𝒪_X)`, the transpose under
`- ⊗^L P' ⊣ R𝓗om(P', -)` of `θ ≫ R𝓗om(u, M)` is `A ⊗^L u` followed by the transpose of `θ`
under `- ⊗^L P ⊣ R𝓗om(P, -)`. On a ringed site this is the naturality of the bijection of
Stacks 08J8 in its middle variable; on `X` it is transported from the equi-universe model.

## Main results

* `AlgebraicGeometry.Space.smallEtaleDerivedTensorSheafHomAdjunction_homEquiv_symm_dinaturality`:
  the bijection of Stacks 08J8 on an algebraic space is dinatural in the middle variable.

## References

* [Stacks Project, Tag 08J8](https://stacks.math.columbia.edu/tag/08J8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite



universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian

/- The standard model of the derived category: the derived functors this file uses (derived
pullback, pushforward, tensor product and internal Hom on ringed sites and topoi) are stated
on it, so the statements here must be too. -/
attribute [local instance 10000] HasDerivedCategory.standard

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Stacks 08J8 on an algebraic space is dinatural in the middle variable.** For
`u : P' ⟶ P` and `θ : A ⟶ R𝓗om(P, M)` in `D(𝒪_X)`, the transpose of `θ ≫ R𝓗om(u, M)` under
`- ⊗^L P' ⊣ R𝓗om(P', -)` is `A ⊗^L u` followed by the transpose of `θ`. -/
theorem smallEtaleDerivedTensorSheafHomAdjunction_homEquiv_symm_dinaturality
    (X : AlgebraicSpaces B S hS)
    {P' P : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))}
    (u : P' ⟶ P)
    {A M : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))}
    (θ : A ⟶ ((smallEtaleDerivedSheafHom B S hS X).obj (op P)).obj M) :
    ((smallEtaleDerivedTensorSheafHomAdjunction B S hS X P').homEquiv A M).symm
        (θ ≫ ((smallEtaleDerivedSheafHom B S hS X).map u.op).app M) =
      ((smallEtaleDerivedTensor B S hS X).obj A).map u ≫
        ((smallEtaleDerivedTensorSheafHomAdjunction B S hS X P).homEquiv A M).symm θ := by
  refine CategoryTheory.PullbackInternalHom.transportAdjunction_homEquiv_symm_dinaturality
    (smallEtaleModelDerivedEquivalence B S hS X) (smallEtaleDerivedTensor B S hS X)
    (Stacks.SheafOfModules.derivedTensorProductFunctor (smallEtaleModelRingedSite B S hS X.1 X.2))
    (smallEtaleModelDerivedTensorIso B S hS X)
    (RingedSite.derivedSheafHomBifunctor (smallEtaleModelRingedSite B S hS X.1 X.2))
    (RingedSite.derivedTensorSheafHomAdjunction (smallEtaleModelRingedSite B S hS X.1 X.2))
    (smallEtaleDerivedTensorSheafHomAdjunction B S hS X)
    (smallEtaleDerivedTensorRightIso B S hS X) (smallEtaleDerivedTensorRightIso_hom_app X)
    (smallEtaleDerivedTensorSheafHomAdjunction_eq X)
    (fun Q A M x => RingedSite.derivedCurryHomEquiv (smallEtaleModelRingedSite B S hS X.1 X.2)
      A Q M x)
    ?_ ?_ u θ
  · intro Q A M x
    exact RingedSite.derivedTensorSheafHomAdjunction_homEquiv_symm_apply
      (smallEtaleModelRingedSite B S hS X.1 X.2) A Q M x
  · intro Q' Q v A M θ
    have h := RingedSite.derivedCurryHomEquiv_dinaturality_comp
      (smallEtaleModelRingedSite B S hS X.1 X.2) v θ
    exact eq_of_heq (HEq.trans (by heq_congr) (HEq.trans (heq_of_eq h) (by heq_congr)))

end AlgebraicGeometry.Space

end
