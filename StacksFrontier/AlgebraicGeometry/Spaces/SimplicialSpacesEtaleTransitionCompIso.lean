module

public import StacksFrontier.AlgebraicGeometry.Spaces.SimplicialSmallEtaleStrictTransitionComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleRingedToposHomComp
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.DerivedPullbackSquarePaste

/-!
# The transitions of an augmentation through the composition isomorphism

For a simplicial algebraic space `X` with an augmentation `a` to `Z`, the identification
`La_m^* ⋙ LX(φ)^* ≅ La_n^*` of Stacks 0D6D is the composition isomorphism of the spaces-étale
derived pullbacks followed by the transport along the simplicial identity `X(φ) ≫ a_m = a_n`.

## Main results

In the namespace `AlgebraicGeometry.Space.SimplicialSpacesEtaleSite`:

* `derivedPullbackCompIso_trans_isoOfPullbackModulesIso_ofEq`: the composition isomorphism
  followed by the transport along `f ≫ g = k` is the composition isomorphism of the spaces-étale
  derived pullbacks followed by the transport of derived pullbacks.
* `augmentationTransitionDerivedIso_eq`: `La_m^* ⋙ LX(φ)^* ≅ La_n^*` is the composition
  isomorphism of the spaces-étale derived pullbacks followed by the transport along
  `X(φ) ≫ a_m = a_n`.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite CategoryTheory.Limits AlgebraicGeometry.RingedToposHom
open Stacks.Cohomology.DerivedPullbackOfToposHom
open Stacks.Cohomology.DerivedPullbackCompositionOfToposHom

universe u

-- no global `HasDerivedCategory` instance at this universe
attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.Space.SimplicialSpacesEtaleSite

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The composition isomorphism `Lg^* ⋙ Lf^* ≅ L(f ≫ g)^*` followed by the transport along
`f ≫ g = k`, written through the 2-isomorphism `g ∘ f ≅ k`, is the composition isomorphism of the
spaces-étale derived pullbacks followed by the transport of derived pullbacks. -/
theorem derivedPullbackCompIso_trans_isoOfPullbackModulesIso_ofEq
    {X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y ⟶ Z) (k : X ⟶ Z) (h : f ≫ g = k) :
    haveI := hasLeftDerivedFunctor_pullbackOnHomotopy
      (RingedToposHom.comp (X := spacesEtaleRingedTopos B S hS X)
        (Y := spacesEtaleRingedTopos B S hS Y) (Z := spacesEtaleRingedTopos B S hS Z)
        (spacesEtaleRingedToposHom g) (spacesEtaleRingedToposHom f))
    derivedPullbackCompIso (spacesEtaleRingedToposHom f) (spacesEtaleRingedToposHom g) ≪≫
      derivedPullbackIsoOfPullbackModulesIso
        (φ := RingedToposHom.comp (X := spacesEtaleRingedTopos B S hS X)
          (Y := spacesEtaleRingedTopos B S hS Y) (Z := spacesEtaleRingedTopos B S hS Z)
          (spacesEtaleRingedToposHom g) (spacesEtaleRingedToposHom f))
        (ψ := spacesEtaleRingedToposHom k)
        ((spacesEtaleRingedToposHomCompTwoIsoSpacesEtaleRingedToposHomComp f g).symm.trans
          (TwoIso.ofEq (A := spacesEtaleRingedTopos B S hS X) (B := spacesEtaleRingedTopos B S hS Z)
            (congrArg (spacesEtaleRingedToposHom (Z₁ := X) (Z₂ := Z)) h))).pullbackModulesIso =
      spacesEtaleDerivedPullbackCompIsoSpacesEtaleRingedToposHomComp f g ≪≫
        Stacks.Cohomology.DerivedBaseChangeOfToposHom.derivedPullbackCongr.{u + 1, u + 1, u + 1,
          u + 1, u + 1, u + 1} (X' := spacesEtaleRingedTopos B S hS X)
          (Y := spacesEtaleRingedTopos B S hS Z)
          (congrArg (spacesEtaleRingedToposHom (Z₁ := X) (Z₂ := Z)) h) := by
  subst h
  simp only [TwoIso.ofEq_rfl, TwoIso.pullbackModulesIso_trans, TwoIso.pullbackModulesIso_symm,
    TwoIso.pullbackModulesIso_refl, Iso.trans_refl]
  exact (Iso.trans_refl _).symm

/-- **The transitions of an augmentation through the composition isomorphism**:
`La_m^* ⋙ LX(φ)^* ≅ La_n^*` is the composition isomorphism of the spaces-étale derived pullbacks
followed by the transport along `X(φ) ≫ a_m = a_n`. -/
theorem augmentationTransitionDerivedIso_eq (X : SimplicialObject (AlgebraicSpaces B S hS))
    {Z : AlgebraicSpaces B S hS} (a : X ⟶ (Functor.const _).obj Z) {m n : SimplexCategory}
    (φ : m ⟶ n) :
    augmentationTransitionDerivedIso a φ =
      spacesEtaleDerivedPullbackCompIsoSpacesEtaleRingedToposHomComp (X.map φ.op) (a.app (op m)) ≪≫
        Stacks.Cohomology.DerivedBaseChangeOfToposHom.derivedPullbackCongr.{u + 1, u + 1, u + 1,
          u + 1, u + 1, u + 1} (X' := spacesEtaleRingedTopos B S hS (X.obj (op n)))
          (Y := spacesEtaleRingedTopos B S hS Z)
          (congrArg (spacesEtaleRingedToposHom (Z₁ := X.obj (op n)) (Z₂ := Z))
            (augmentation_map_comp_app a φ)) :=
  derivedPullbackCompIso_trans_isoOfPullbackModulesIso_ofEq (X.map φ.op) (a.app (op m))
    (a.app (op n)) (augmentation_map_comp_app a φ)

end AlgebraicGeometry.Space.SimplicialSpacesEtaleSite

end
