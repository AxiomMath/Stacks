module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleOpenPushforward
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleZariskiBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologyWithSupportAssociated
public import StacksFrontier.CategoryTheory.Sites.UniverseLiftOpenComplement

/-!
# The associated sheaf of `j_* j^* 𝓕` on the small étale site

Let `i : Z ⟶ X` be a closed immersion of a big étale site with open complement `j : U ⟶ X`,
quasi-compact, and let `𝓕` be a quasi-coherent `𝒪_X`-module.  The proof of Stacks 0A46 compares
the sequence `0 ⟶ i_*ℋ^0_Z ⟶ 𝟭 ⟶ j_*(-|_U)` on `𝒪_X`-modules with its étale counterpart on abelian
sheaves of `X_étale`, along `𝓕 ↦ 𝓕^a`.  In degree zero this needs an isomorphism
`(j_* j^* 𝓕)^a ≅ j_* j^{-1} (𝓕^a)` carrying the associated sheaf of the unit `𝓕 ⟶ j_* j^* 𝓕` to
the restriction map `𝓕^a ⟶ j_* j^{-1} (𝓕^a)`.  This file provides it, in the universe of the
coefficients of `AlgebraicGeometry.SmallEtaleAbelianSheaf`, from Descent, Lemma 071N in degree
zero (`AlgebraicGeometry.SmallEtale.openPushforwardRestrictionAssociatedSheafIso`) and the
compatibility of the universe lift with `j^{-1}`, `j_*` and the unit
(`Stacks.Sheaves.UniverseLift.whiskerRight_complementAdjunctionULift_unit_comp`).

## Main definitions

* `AlgebraicGeometry.complementAssociatedSheafULiftIso`: `(j_* j^* 𝓕)^a ≅ j_* j^{-1} (𝓕^a)`.
* `AlgebraicGeometry.rightDerivedComplementPullbackPushforwardAssociatedSheafULiftIso`:
  `R^p(j_* j^{-1})(𝓕^a) ≅ R^p j_*((j^* 𝓕)^a)`, the right side lifted from the universe of the
  schemes.
* `AlgebraicGeometry.complementHigherDirectImageAssociatedSheafULiftIso`:
  `R^p(j_* j^{-1})(𝓕^a) ≅ (R^p j_* j^* 𝓕)^a`, Descent, Lemma 071N for `j`.

## Main results

* `AlgebraicGeometry.associatedSheafULift_map_unit_comp_complementAssociatedSheafULiftIso_hom`:
  it carries the unit to `AlgebraicGeometry.complementRestriction`.

## References

* [Stacks Project, Tag 071N](https://stacks.math.columbia.edu/tag/071N)
* [Stacks Project, Tag 0A46](https://stacks.math.columbia.edu/tag/0A46)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

open Stacks.Sheaves.UniverseLift

variable (B : BigEtaleSite.{u}) {Z X : B.Scheme} (i : Z ⟶ X)
  [IsClosedImmersion (B.inclusion.map i)]

/-- The morphism of schemes `j : U ⟶ X` underlying the inclusion of the open complement of a
closed immersion. -/
abbrev closedComplementSchemeHom : (closedComplement B i).obj ⟶ X.obj :=
  SmallEtale.schemeHom B (closedComplementInclusion B i)

/-- **`(j_* j^* 𝓕)^a ≅ j_* j^{-1} (𝓕^a)`** on abelian sheaves of the small étale site of `X` in
the universe of `AlgebraicGeometry.SmallEtaleAbelianSheaf`, for the inclusion `j` of the open
complement of a closed immersion, quasi-compact, and a quasi-coherent `𝒪_X`-module `𝓕`.  It
carries the associated sheaf of the unit `𝓕 ⟶ j_* j^* 𝓕` to
`AlgebraicGeometry.complementRestriction`
(`AlgebraicGeometry.associatedSheafULift_map_unit_comp_complementAssociatedSheafULiftIso_hom`). -/
def complementAssociatedSheafULiftIso [QuasiCompact (closedComplementSchemeHom B i)]
    (𝓕 : X.obj.Modules) [𝓕.IsQuasicoherent] :
    (SmallEtale.associatedSheafULift B X).obj
        ((Scheme.Modules.pushforward (closedComplementSchemeHom B i)).obj
          ((Scheme.Modules.pullback (closedComplementSchemeHom B i)).obj 𝓕)) ≅
      (complementPullbackPushforward B i).obj ((SmallEtale.associatedSheafULift B X).obj 𝓕) :=
  (uliftSheafFunctor.{u + 1, u} (SmallEtale.topology B X.obj X.property)).mapIso
      (SmallEtale.openPushforwardRestrictionAssociatedSheafIso B (closedComplementInclusion B i)
        𝓕) ≪≫
    (complementPushforward B i).mapIso ((complementPullbackULiftIso B i).app
      ((SmallEtale.associatedSheaf B X).obj 𝓕))

/-- **The isomorphism `(j_* j^* 𝓕)^a ≅ j_* j^{-1} (𝓕^a)` carries the unit to the restriction
map** `AlgebraicGeometry.complementRestriction`. -/
theorem associatedSheafULift_map_unit_comp_complementAssociatedSheafULiftIso_hom
    [QuasiCompact (closedComplementSchemeHom B i)] (𝓕 : X.obj.Modules) [𝓕.IsQuasicoherent] :
    (SmallEtale.associatedSheafULift B X).map
        ((Scheme.Modules.pullbackPushforwardAdjunction (closedComplementSchemeHom B i)).unit.app
          𝓕) ≫ (complementAssociatedSheafULiftIso B i 𝓕).hom =
      (complementRestriction B i).app ((SmallEtale.associatedSheafULift B X).obj 𝓕) := by
  have h := NatTrans.congr_app (whiskerRight_complementAdjunctionULift_unit_comp B i)
    ((SmallEtale.associatedSheaf B X).obj 𝓕)
  simp only [Functor.whiskerLeft_app] at h
  refine Eq.trans ?_ h
  change (uliftSheafFunctor.{u + 1, u} (SmallEtale.topology B X.obj X.property)).map
      ((SmallEtale.associatedSheaf B X).map
        ((Scheme.Modules.pullbackPushforwardAdjunction (closedComplementSchemeHom B i)).unit.app
          𝓕)) ≫
      ((uliftSheafFunctor.{u + 1, u} (SmallEtale.topology B X.obj X.property)).map
        (SmallEtale.openPushforwardRestrictionAssociatedSheafIso B (closedComplementInclusion B i)
          𝓕).hom ≫
        (complementPushforward B i).map ((complementPullbackULiftIso B i).hom.app
          ((SmallEtale.associatedSheaf B X).obj 𝓕))) = _
  have key := congrArg (uliftSheafFunctor.{u + 1, u} (SmallEtale.topology B X.obj X.property)).map
    (SmallEtale.associatedSheaf_map_unit_comp_openPushforwardRestrictionIso_hom B
      (closedComplementInclusion B i) 𝓕)
  rw [Functor.map_comp] at key
  exact (Category.assoc _ _ _).symm.trans (key =≫ _)

/-- **`R^p(j_* j^{-1})(𝓕^a) ≅ (R^p j_*((j^*𝓕)^a))` in the universe of the coefficients of
`AlgebraicGeometry.SmallEtaleAbelianSheaf`**, the right side being the universe lift of the higher
direct image, in the universe of the schemes, of the associated sheaf of `j^* 𝓕`.  It is the
composite of `AlgebraicGeometry.complementPullbackPushforwardRightDerivedIso` (`j^{-1}` is exact
and preserves injectives), the compatibility of `j^{-1}` and of `R^p j_*` with the universe lift,
and `(j^* 𝓕)^a ≅ j^{-1}(𝓕^a)`
(`AlgebraicGeometry.SmallEtale.openRestrictionAssociatedSheafIso`). -/
def rightDerivedComplementPullbackPushforwardAssociatedSheafULiftIso (p : ℕ)
    (𝓕 : X.obj.Modules) :
    ((complementPullbackPushforward B i).rightDerived p).obj
        ((SmallEtale.associatedSheafULift B X).obj 𝓕) ≅
      (uliftSheafFunctor.{u + 1, u} (SmallEtale.topology B X.obj X.property)).obj
        (((SmallEtale.openPushforwardAb B (closedComplementInclusion B i)).rightDerived p).obj
          ((SmallEtale.associatedSheaf B (closedComplement B i)).obj
            ((Scheme.Modules.pullback (closedComplementSchemeHom B i)).obj 𝓕))) :=
  (complementPullbackPushforwardRightDerivedIso B i p).app _ ≪≫
    ((complementPushforward B i).rightDerived p).mapIso
      ((complementPullbackULiftIso B i).app ((SmallEtale.associatedSheaf B X).obj 𝓕)).symm ≪≫
    ((rightDerivedComplementPushforwardULiftIso B i p).app _).symm ≪≫
    (uliftSheafFunctor.{u + 1, u} (SmallEtale.topology B X.obj X.property)).mapIso
      (((SmallEtale.openPushforwardAb B (closedComplementInclusion B i)).rightDerived p).mapIso
        ((SmallEtale.openRestrictionAssociatedSheafIso B (closedComplementInclusion B i)).app
          𝓕).symm)

/-- **Descent, Lemma 071N for the inclusion of the open complement**, in the form the comparison
of the sequences of Stacks 0A45 consumes:
`R^p(j_* j^{-1})(𝓕^a) ≅ (R^p j_* (j^* 𝓕))^a` in the universe of the coefficients of
`AlgebraicGeometry.SmallEtaleAbelianSheaf`, for `j` quasi-compact and `𝓕` quasi-coherent.  It is
`AlgebraicGeometry.rightDerivedComplementPullbackPushforwardAssociatedSheafULiftIso` followed by
the universe lift of `AlgebraicGeometry.SmallEtale.higherDirectImageAssociatedSheafIso` for `j`
and `j^* 𝓕`. -/
def complementHigherDirectImageAssociatedSheafULiftIso
    [QuasiCompact (closedComplementSchemeHom B i)] (p : ℕ) (𝓕 : X.obj.Modules)
    [𝓕.IsQuasicoherent] :
    ((complementPullbackPushforward B i).rightDerived p).obj
        ((SmallEtale.associatedSheafULift B X).obj 𝓕) ≅
      (SmallEtale.associatedSheafULift B X).obj
        (((Scheme.Modules.pushforward (closedComplementSchemeHom B i)).rightDerived p).obj
          ((Scheme.Modules.pullback (closedComplementSchemeHom B i)).obj 𝓕)) :=
  rightDerivedComplementPullbackPushforwardAssociatedSheafULiftIso B i p 𝓕 ≪≫
    (uliftSheafFunctor.{u + 1, u} (SmallEtale.topology B X.obj X.property)).mapIso
      (SmallEtale.higherDirectImageAssociatedSheafIso B (closedComplementInclusion B i)
        ((Scheme.Modules.pullback (closedComplementSchemeHom B i)).obj 𝓕) p)

end AlgebraicGeometry
