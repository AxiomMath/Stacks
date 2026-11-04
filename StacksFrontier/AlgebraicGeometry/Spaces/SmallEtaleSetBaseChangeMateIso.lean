module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRingedToposHom
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleSetBaseChangeMate
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SmallEtaleBaseChangeMate
public import StacksFrontier.CategoryTheory.Adjunction.MateConjugateEquivalence

/-!
# The étale base-change 2-cell of sheaves of sets on small étale sites is invertible

For a cartesian square of algebraic spaces with étale bottom arrow `g`, the mate, across the
adjunctions of étale restriction and direct image of sheaves of sets on the small étale sites, of
the comparison of the two composite direct images is an isomorphism (Stacks 03LR, part (1), for
the canonical map). It is obtained from the spaces-étale statement by conjugating with the
comparison equivalences of Stacks 03G1.

## Main results

* `AlgebraicGeometry.Space.isIso_smallEtaleSetBaseChangeMate`
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y X' Y' : AlgebraicSpaces B S hS} (i : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)

/-- The comparison of the two composite spaces-étale direct images of a commuting square, at the
universe of the structure rings, is the restriction to sheaves of the comparison of the two
composites of base change on the sites. -/
theorem spacesBaseChange_pushforward_compTypeU_square_eq (w : i ≫ f = f' ≫ g) :
    letI := Functor.isContinuous_comp (spacesBaseChange B S hS g).functor
      (spacesBaseChange B S hS f').functor
      (SpacesEtale.topology B S hS Y) (SpacesEtale.topology B S hS Y')
      (SpacesEtale.topology B S hS X')
    letI := Functor.isContinuous_comp (spacesBaseChange B S hS f).functor
      (spacesBaseChange B S hS i).functor
      (SpacesEtale.topology B S hS Y) (SpacesEtale.topology B S hS X)
      (SpacesEtale.topology B S hS X')
    (spacesBaseChange_pushforward_compTypeU B S hS i f).hom ≫
        eqToHom (congrArg (fun k : X' ⟶ Y =>
          (spacesBaseChange B S hS k).functor.sheafPushforwardContinuous (Type u)
            (SpacesEtale.topology B S hS Y) (SpacesEtale.topology B S hS X')) w) ≫
        (spacesBaseChange_pushforward_compTypeU B S hS f' g).inv =
      Functor.sheafPushforwardContinuousNatTrans
        (spacesBaseChangeCompSquare B S hS i f' f g w) (Type u)
        (SpacesEtale.topology B S hS Y) (SpacesEtale.topology B S hS X') := by
  rw [spacesBaseChangeCompSquare,
    Functor.sheafPushforwardContinuousNatTrans_comp,
    Functor.sheafPushforwardContinuousNatTrans_comp,
    Functor.sheafPushforwardContinuousNatTrans_eqToHom, Category.assoc]
  rfl

/-- The comparison of the two composite small étale direct images of a commuting square, at the
universe of the structure rings, is the conjugate by the comparison equivalences of Stacks 03G1
of the spaces-étale one. -/
theorem smallToposMorphismTypeU_comp_square_eq (w : i ≫ f = f' ≫ g) :
    (smallToposMorphismTypeU_comp B S hS i f).hom ≫
        eqToHom (congrArg (fun k : X' ⟶ Y => (smallToposMorphismTypeU B S hS k).pushforward) w) ≫
        (smallToposMorphismTypeU_comp B S hS f' g).inv =
      (Stacks.CategoryTheory.conjugateRightTwoSquare (smallEtaleToposEquivTypeU B S hS X)
        (smallEtaleToposEquivTypeU B S hS X') (smallEtaleToposEquivTypeU B S hS Y)
        (smallEtaleToposEquivTypeU B S hS Y')
        (TwoSquare.mk _ _ _ _ ((spacesBaseChange_pushforward_compTypeU B S hS i f).hom ≫
          eqToHom (congrArg (fun k : X' ⟶ Y =>
            (spacesBaseChange B S hS k).functor.sheafPushforwardContinuous (Type u)
              (SpacesEtale.topology B S hS Y) (SpacesEtale.topology B S hS X')) w) ≫
          (spacesBaseChange_pushforward_compTypeU B S hS f' g).inv))).natTrans :=
  Stacks.CategoryTheory.conjugateRightTwoSquare_comp_eqToHom
    (smallEtaleToposEquivTypeU B S hS X) (smallEtaleToposEquivTypeU B S hS X')
    (smallEtaleToposEquivTypeU B S hS Y) (smallEtaleToposEquivTypeU B S hS Y')
    (fun k : X' ⟶ Y => (spacesBaseChange B S hS k).functor.sheafPushforwardContinuous (Type u)
      (SpacesEtale.topology B S hS Y) (SpacesEtale.topology B S hS X')) w
    (spacesBaseChange_pushforward_compTypeU B S hS i f)
    (spacesBaseChange_pushforward_compTypeU B S hS f' g)

/-- The mate, across the adjunctions of étale restriction and direct image of sheaves of sets on
the small étale sites, of the conjugate of the comparison of the two composite spaces-étale
direct images is invertible. -/
theorem isIso_mateEquiv_symm_smallEtaleSetRestrictionAdjunction (sq : IsPullback i f' f g)
    (hg : IsEtale B S hS g.hom)
    (θ : TwoSquare (smallEtaleDirectImage B S hS i) (smallEtaleDirectImage B S hS f')
      (smallEtaleDirectImage B S hS f) (smallEtaleDirectImage B S hS g))
    (hθ : θ = Stacks.CategoryTheory.conjugateRightTwoSquare (smallEtaleToposEquivTypeU B S hS X)
        (smallEtaleToposEquivTypeU B S hS X') (smallEtaleToposEquivTypeU B S hS Y)
        (smallEtaleToposEquivTypeU B S hS Y')
        (TwoSquare.mk _ _ _ _ ((spacesBaseChange_pushforward_compTypeU B S hS i f).hom ≫
          eqToHom (congrArg (fun k : X' ⟶ Y =>
            (spacesBaseChange B S hS k).functor.sheafPushforwardContinuous (Type u)
              (SpacesEtale.topology B S hS Y) (SpacesEtale.topology B S hS X')) sq.w) ≫
          (spacesBaseChange_pushforward_compTypeU B S hS f' g).inv))) :
    IsIso ((mateEquiv (smallEtaleSetRestrictionAdjunction B S hS i
          (isEtale_of_isPullback B S hS f' i g f sq.flip hg))
        (smallEtaleSetRestrictionAdjunction B S hS g hg)).symm θ).natTrans := by
  subst hθ
  exact Stacks.CategoryTheory.isIso_mateEquiv_symm_of_isIso _ _ _ _ _
    (Stacks.CategoryTheory.isIso_mateEquiv_symm_conjugate
      (spacesEtalePostcompSheafAdjunction B S hS (Type u) i
        (isEtale_of_isPullback B S hS f' i g f sq.flip hg))
      (spacesEtalePostcompSheafAdjunction B S hS (Type u) g hg)
      (smallEtaleToposEquivTypeU B S hS X) (smallEtaleToposEquivTypeU B S hS X')
      (smallEtaleToposEquivTypeU B S hS Y) (smallEtaleToposEquivTypeU B S hS Y')
      (TwoSquare.mk _ _ _ _ (spacesSetPushforwardBaseChangeIso B S hS i f' f g sq hg).inv)
      (inferInstanceAs (IsIso (spacesSetPushforwardBaseChangeIso B S hS i f' f g sq hg).inv)) _
      (mateEquiv_spacesSetPushforwardBaseChangeIso B S hS i f' f g sq hg))

/-- **The étale base-change 2-cell of sheaves of sets is an isomorphism.**  For a cartesian
square of algebraic spaces with étale bottom arrow `g`, the mate, across the adjunctions of
étale restriction and direct image of sheaves of sets at the universe of the structure rings,
of the comparison `i_* f_* ⟶ f'_* g_*` of the two composite direct images (Stacks 03G2,
part (3)) is invertible: this is Stacks 03LR, part (1), for the canonical map. -/
theorem isIso_smallEtaleSetBaseChangeMate (sq : IsPullback i f' f g)
    (hg : IsEtale B S hS g.hom) :
    IsIso ((mateEquiv (smallEtaleSetRestrictionAdjunction B S hS i
          (isEtale_of_isPullback B S hS f' i g f sq.flip hg))
        (smallEtaleSetRestrictionAdjunction B S hS g hg)).symm
      (TwoSquare.mk _ _ _ _ ((smallToposMorphismTypeU_comp B S hS i f).hom ≫
        eqToHom (congrArg (fun k : X' ⟶ Y => (smallToposMorphismTypeU B S hS k).pushforward)
          sq.w) ≫
        (smallToposMorphismTypeU_comp B S hS f' g).inv))).natTrans :=
  isIso_mateEquiv_symm_smallEtaleSetRestrictionAdjunction B S hS i f' f g sq hg _
    (smallToposMorphismTypeU_comp_square_eq B S hS i f' f g sq.w)

end AlgebraicGeometry.Space

end
