module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposTwoMorphismModules
public import StacksFrontier.AlgebraicGeometry.Spaces.SimplicialSmallEtaleSquare
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.CompositionOfToposHom
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.PullbackModulesIsoDerivedPullback

/-!
# The spaces-étale ringed topos is pseudofunctorial

For morphisms `f : X ⟶ Y` and `g : Y ⟶ Z` of algebraic spaces, the morphism of ringed topoi
`(Sh(X_{spaces,étale}), 𝒪_X) ⟶ (Sh(Z_{spaces,étale}), 𝒪_Z)` attached to `f ≫ g` is
2-isomorphic to the composite of those attached to `f` and to `g` (Stacks 0DE7), through the
canonical isomorphism `(V ×_Z Y) ×_Y X ≅ V ×_Z X` of iterated base changes (Stacks 03G2).

## Main definitions

* `AlgebraicGeometry.Space.spacesEtaleRingedToposHomCompTwoIsoSpacesEtaleRingedToposHomComp`:
  the 2-isomorphism `(f ≫ g)_{étale} ≅ g_{étale} ∘ f_{étale}`.
* `AlgebraicGeometry.Space.spacesEtaleDerivedPullbackCompIsoSpacesEtaleRingedToposHomComp`:
  the resulting isomorphism `Lg^* ⋙ Lf^* ≅ L(f ≫ g)^*` of derived pullbacks (Stacks 0D6D).
-/

@[expose] public noncomputable section

open CategoryTheory Opposite CategoryTheory.Limits AlgebraicGeometry.RingedToposHom

universe u

namespace AlgebraicGeometry.Space

open SimplicialSpacesEtaleSite

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- **The 2-isomorphism `(f ≫ g)_{étale} ≅ g_{étale} ∘ f_{étale}`** of morphisms of ringed topoi
`(Sh(X_{spaces,étale}), 𝒪_X) ⟶ (Sh(Z_{spaces,étale}), 𝒪_Z)`: on direct images it is restriction
along the canonical isomorphism of iterated base changes, and it is compatible with the
structure maps because that isomorphism commutes with the projections. -/
noncomputable def spacesEtaleRingedToposHomCompTwoIsoSpacesEtaleRingedToposHomComp :
    TwoIso (A := spacesEtaleRingedTopos B S hS X) (B := spacesEtaleRingedTopos B S hS Z)
      (spacesEtaleRingedToposHom (f ≫ g))
      (RingedToposHom.comp (X := spacesEtaleRingedTopos B S hS X)
        (Y := spacesEtaleRingedTopos B S hS Y) (Z := spacesEtaleRingedTopos B S hS Z)
        (spacesEtaleRingedToposHom g) (spacesEtaleRingedToposHom f)) where
  e :=
    haveI := Functor.isContinuous_comp (spacesBaseChange B S hS g).functor
      (spacesBaseChange B S hS f).functor (SpacesEtale.topology B S hS Z)
      (SpacesEtale.topology B S hS Y) (SpacesEtale.topology B S hS X)
    (Functor.sheafPushforwardContinuousIso (spacesBaseChange_comp B S hS f g) (Type (u + 1))
      (SpacesEtale.topology B S hS Z) (SpacesEtale.topology B S hS X)).symm ≪≫
    (Functor.sheafPushforwardContinuousComp _ _ _ _ _ _).symm
  commutes := by
    refine Eq.trans ?_ (forgetFSharp_comp.{u + 1, u + 1, u + 1, u + 1, u + 1, u + 1, u + 1,
      u + 1, u + 1} (spacesEtaleRingedToposHom g) (spacesEtaleRingedToposHom f)).symm
    ext V : 3
    have key : (globalFunctionsPresheaf B S hS ⋙ forget CommRingCat.{u + 1}).map
          ((spacesBaseChange B S hS (f ≫ g)).projection.app V.unop).op ≫
        (globalFunctionsPresheaf B S hS ⋙ forget CommRingCat.{u + 1}).map
          (((spacesBaseChange_comp B S hS f g).hom.app V.unop).hom.left).op =
        (globalFunctionsPresheaf B S hS ⋙ forget CommRingCat.{u + 1}).map
          ((spacesBaseChange B S hS g).projection.app V.unop).op ≫
        (globalFunctionsPresheaf B S hS ⋙ forget CommRingCat.{u + 1}).map
          ((spacesBaseChange B S hS f).projection.app
            ((spacesBaseChange B S hS g).functor.obj V.unop)).op := by
      rw [← Functor.map_comp, ← Functor.map_comp, ← op_comp, ← op_comp,
        spacesBaseChange_comp_projection]
    exact key

section Derived

open Stacks.Cohomology.DerivedPullbackOfToposHom
  Stacks.Cohomology.DerivedPullbackCompositionOfToposHom

/-- The derived pullback along the morphism of spaces-étale ringed topoi of a morphism of
algebraic spaces exists (Stacks 06YY), as for every morphism of ringed topoi. -/
instance
    hasLeftDerivedFunctor_pullbackOnHomotopy_spacesEtaleRingedToposHom_spacesEtaleRingedToposHomComp
    {X' Y' : AlgebraicSpaces B S hS} (h : X' ⟶ Y') :
    (Stacks.Cohomology.DerivedPushforward.pullbackOnHomotopy
      (spacesEtaleRingedToposHom h)).HasLeftDerivedFunctor
      (quasiIsoTarget (Y := spacesEtaleRingedTopos B S hS Y')) :=
  hasLeftDerivedFunctor_pullbackOnHomotopy (spacesEtaleRingedToposHom h)

/-- The pullbacks of modules along `g_{étale} ∘ f_{étale}` and along `(f ≫ g)_{étale}` agree,
through the 2-isomorphism `spacesEtaleRingedToposHomCompTwoIsoSpacesEtaleRingedToposHomComp`. -/
noncomputable def spacesEtalePullbackModulesCompIsoSpacesEtaleRingedToposHomComp :
    (RingedToposHom.comp (X := spacesEtaleRingedTopos B S hS X)
        (Y := spacesEtaleRingedTopos B S hS Y) (Z := spacesEtaleRingedTopos B S hS Z)
        (spacesEtaleRingedToposHom g) (spacesEtaleRingedToposHom f)).toModulesHom.pullbackModules ≅
      (spacesEtaleRingedToposHom (f ≫ g)).toModulesHom.pullbackModules :=
  (spacesEtaleRingedToposHomCompTwoIsoSpacesEtaleRingedToposHomComp f g).pullbackModulesIso.symm

/-- **Stacks 0D6D for morphisms of algebraic spaces**: the derived pullbacks along `g` and then
`f` compose to the derived pullback along `f ≫ g`, on the derived categories of modules over the
spaces-étale ringed topoi. -/
noncomputable def spacesEtaleDerivedPullbackCompIsoSpacesEtaleRingedToposHomComp :
    derivedPullback (X := spacesEtaleRingedTopos B S hS Y) (Y := spacesEtaleRingedTopos B S hS Z)
        (spacesEtaleRingedToposHom g) ⋙
      derivedPullback (X := spacesEtaleRingedTopos B S hS X) (Y := spacesEtaleRingedTopos B S hS Y)
        (spacesEtaleRingedToposHom f) ≅
      derivedPullback (X := spacesEtaleRingedTopos B S hS X) (Y := spacesEtaleRingedTopos B S hS Z)
        (spacesEtaleRingedToposHom (f ≫ g)) :=
  haveI := hasLeftDerivedFunctor_pullbackOnHomotopy
    (RingedToposHom.comp (X := spacesEtaleRingedTopos B S hS X)
        (Y := spacesEtaleRingedTopos B S hS Y) (Z := spacesEtaleRingedTopos B S hS Z)
        (spacesEtaleRingedToposHom g) (spacesEtaleRingedToposHom f))
  derivedPullbackCompIso (spacesEtaleRingedToposHom f) (spacesEtaleRingedToposHom g) ≪≫
    derivedPullbackIsoOfPullbackModulesIso
      (φ := (RingedToposHom.comp (X := spacesEtaleRingedTopos B S hS X)
        (Y := spacesEtaleRingedTopos B S hS Y) (Z := spacesEtaleRingedTopos B S hS Z)
        (spacesEtaleRingedToposHom g) (spacesEtaleRingedToposHom f)))
      (ψ := spacesEtaleRingedToposHom (f ≫ g))
      (spacesEtalePullbackModulesCompIsoSpacesEtaleRingedToposHomComp f g)

end Derived

end AlgebraicGeometry.Space

end
