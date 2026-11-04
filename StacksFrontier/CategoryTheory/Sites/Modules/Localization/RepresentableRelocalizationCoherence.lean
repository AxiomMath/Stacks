module

public import StacksFrontier.CategoryTheory.Sites.Localization.RelocalizeCounit
public import StacksFrontier.CategoryTheory.Sites.Modules.Localization.LocalizedRepresentableKey
public import StacksFrontier.CategoryTheory.Sites.Modules.Localization.RepresentableRelocalizationComparison

/-!
# Stacks 04J5's comparison of inverse images is the one Stacks 04J3 prescribes

Let `X` be a ringed site and `f : V ⟶ U` a morphism of its site. Stacks 04J3 supplies, at every
object `W` of the site, a canonical comparison
`AlgebraicGeometry.RingedSite.representableLocalizationInverseImageIso` of the inverse image of
the localization of the ringed topos at `h_W^#`, read through the identification of that
localization with `Sh(C/W)`, with the inverse image of the localization of the ringed *site* at
`W`. Stacks 04J5 supplies a comparison
`AlgebraicGeometry.RingedSite.representableRelocalizationSheafMapCompInverseImageIso` of the two
relocalizations over `h_U^#`.

This file proves that the second comparison is *determined* by the first: evaluated at an object
`j_{h_U^#}^{-1}A` and followed by Stacks 04J3's comparison at `U` restricted along `Over.map f`,
it is Stacks 04J3's comparison at `V`. It is the coherence of the identifications of Stacks 04IE
at `h_U^#`, at `h_V^#` and at `h_V^#/h_U^#` which the sheaf-morphism description of Stacks
04J4's upper edge needs.

## Main results

* `RingedSite.representableRelocalizationSheafMapCompInverseImageIso_hom_app_comp`:
  the coherence statement.

## Implementation notes

The equation is transposed across the lower shriek `j_{V!}`, where every factor has a known
evaluated form: Stacks 04J3's comparison at `V` by
`AlgebraicGeometry.RingedSite.shriek_representableLocalizationInverseImageIso_hom_app_comp_counit`
and at `U` by
`RingedSite.left_representableLocalizationForwardInverseImageIso_inv_app_comp_counit`,
Stacks 04J4's base-change comparison by
`AlgebraicGeometry.RingedTopos.forget_map_relocalizationInverseImageSliceIso_hom_app`, and
Stacks 00Y1's identification by
`AlgebraicGeometry.RingedSite.shriek_sheafEquivalence_unitInv`. What remains after those is one
statement about Stacks 04IL (1) alone,
`shriek_inverseImageCompSheafFunctorToOverIso_inv_app`: the comparison of the inverse image of
the relocalization with base change along `h_f^#` carries the counit of `j_{V!} ⊣ j_V^{-1}` to
the first projection followed by the counit of `j_{U!} ⊣ j_U^{-1}`. That statement mentions no
ringed site — only the topology `X.J`, Stacks 04IL (1), Stacks 00Y1's
`sheafFunctorToOverForgetIso` and the two localization adjunctions of the site — so it belongs
beside Stacks 04IL (1) in
`StacksFrontier.CategoryTheory.Sites.Localization.Relocalize`. It is **the one open input of this
file**:
`CategoryTheory.OverShriek.homEquiv_symm_inverseImageCompSheafFunctorToOverIso_inv_app`
reduces it to Stacks 03EH's `leftAdjointIso` (available, with its transpose lemma
`leftAdjointIso_hom_app_comp_map_comp_counit`) together with the statement that Stacks 04IL (2)
read through `Over.forget h_U^#` and Stacks 00Y1's identifications at `U` and at `V` *is* that
`leftAdjointIso` — and the latter is not proved anywhere in the library.

## References

* [Stacks Project, Tag 04J9](https://stacks.math.columbia.edu/tag/04J9)
* [Stacks Project, Tag 04J3](https://stacks.math.columbia.edu/tag/04J3)
* [Stacks Project, Tag 04J4](https://stacks.math.columbia.edu/tag/04J4)
* [Stacks Project, Tag 04J5](https://stacks.math.columbia.edu/tag/04J5)
* [Stacks Project, Tag 04IL](https://stacks.math.columbia.edu/tag/04IL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.RingedToposHom

universe u

namespace CategoryTheory

/-- Base change along `a : H ⟶ K` applied to a morphism of `Over K`, read through `Over.forget`
and followed by the first projection, is the first projection followed by the morphism.

Local to this file: `CategoryTheory.Over.pullback_map_left_comp_fst` states the same thing, but
lives under `AlgebraicGeometry` and is not worth importing here. -/
private theorem Over.pullback_map_left_comp_fst {E : Type*} [Category E] [Limits.HasPullbacks E]
    {H K : E} (a : H ⟶ K) {Q R : Over K} (ψ : Q ⟶ R) :
    ((Over.pullback a).map ψ).left ≫ Limits.pullback.fst R.hom a =
      Limits.pullback.fst Q.hom a ≫ ψ.left := by
  simp only [Over.pullback_obj_left, Over.pullback_map_left]
  exact Limits.pullback.lift_fst _ _ _

end CategoryTheory

namespace AlgebraicGeometry.RingedSite

attribute [local instance] AlgebraicGeometry.RingedTopos.isContinuous_elementPostcomp
  AlgebraicGeometry.RingedTopos.isCocontinuous_elementPostcomp
  CategoryTheory.Functor.isContinuous_overPost_of_isContinuous

attribute [local implicit_reducible] AlgebraicGeometry.RingedToposHom.comp
  MorphismOfTopoi.comp

variable (X : RingedSite.{u, u, u})

/-- **Stacks 00Y1's identification carried across the lower shriek.** A morphism of
`Sh(C)/h_W^#` read through the inverse of Stacks 00Y1's equivalence and followed by its inverse
unit becomes, after applying `j_{W!}`, Stacks 04IQ's identification of `j_{W!}Φ_W^{-1}` with
`Over.forget h_W^#`, then the morphism itself, then Stacks 00Y1's identification of the sheaf
underlying `Φ_W T` with `j_{W!}T`.

This is `AlgebraicGeometry.RingedSite.shriek_sheafEquivalence_unitInv` with the morphism carried
along by the naturality of `CategoryTheory.OverShriek.inverseCompShriekIso`; it is the form a
comparison of inverse images takes once it has been transposed across `j_{W!}`. -/
theorem shriek_sheafEquivalence_inverse_map_comp_unitInv (W : X.C)
    {P : Over (representableSheaf X W)} {T : Sheaf (X.J.over W) (Type u)}
    (m : P ⟶ (CategoryTheory.OverShriek.sheafEquivalence (U := W) X.J).functor.obj T) :
    ((Over.forget W).sheafPullback (Type u) (X.J.over W) X.J).map
        ((CategoryTheory.OverShriek.sheafEquivalence (U := W) X.J).inverse.map m ≫
          (CategoryTheory.OverShriek.sheafEquivalence (U := W) X.J).unitInv.app T) =
      (CategoryTheory.OverShriek.inverseCompShriekIso X.J).hom.app P ≫
        (Over.forget (representableSheaf X W)).map m ≫
          (CategoryTheory.OverShriek.sheafFunctorToOverForgetIso X.J).hom.app T := by
  refine Eq.trans (((Over.forget W).sheafPullback (Type u) (X.J.over W) X.J).map_comp _ _) ?_
  refine Eq.trans (CategoryTheory.comp_left_of_eq _
    (X.shriek_sheafEquivalence_unitInv W T)) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (CategoryTheory.comp_right_of_eq
    ((CategoryTheory.OverShriek.inverseCompShriekIso X.J).hom.naturality m) _) ?_
  exact Category.assoc _ _ _

/-- `shriek_sheafEquivalence_inverse_map_comp_unitInv` with a further morphism of `Sh(C/W)`
absorbed into the slice topos. This is the shape a comparison of inverse images followed by one
further comparison has after the transposition across `j_{W!}`: the two factors are collected
into one morphism of `Sh(C)/h_W^#`, so that the whole of Stacks 04J5's comparison and Stacks
04J3's comparison at `U` can be evaluated together. -/
theorem shriek_sheafEquivalence_inverse_map_comp_unitInv_comp_map (W : X.C)
    {P : Over (representableSheaf X W)} {T T' : Sheaf (X.J.over W) (Type u)}
    (m : P ⟶ (CategoryTheory.OverShriek.sheafEquivalence (U := W) X.J).functor.obj T)
    (n : T ⟶ T') :
    ((Over.forget W).sheafPullback (Type u) (X.J.over W) X.J).map
          ((CategoryTheory.OverShriek.sheafEquivalence (U := W) X.J).inverse.map m ≫
            (CategoryTheory.OverShriek.sheafEquivalence (U := W) X.J).unitInv.app T) ≫
        ((Over.forget W).sheafPullback (Type u) (X.J.over W) X.J).map n =
      (CategoryTheory.OverShriek.inverseCompShriekIso X.J).hom.app P ≫
        (Over.forget (representableSheaf X W)).map
            (m ≫ (CategoryTheory.OverShriek.sheafEquivalence (U := W) X.J).functor.map n) ≫
          (CategoryTheory.OverShriek.sheafFunctorToOverForgetIso X.J).hom.app T' := by
  refine Eq.trans (CategoryTheory.comp_right_of_eq
    (X.shriek_sheafEquivalence_inverse_map_comp_unitInv W m) _) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine CategoryTheory.comp_left_of_eq _ ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (CategoryTheory.comp_left_of_eq _
    ((CategoryTheory.OverShriek.sheafFunctorToOverForgetIso X.J).hom.naturality n).symm) ?_
  exact (Category.assoc _ _ _).symm

/-- **Stacks 04J3's comparison at `W`, read back into the slice topos.** The two counit factors
which Stacks 04J5's comparison carries in front of Stacks 04J3's comparison at `W` cancel it
back into the comparison in the slice direction: the two equivalences that Stacks 04J3's
identification is composed of annihilate, by
`AlgebraicGeometry.RingedSite.representableLocalizationEquivalence_counitInv_comp`. -/
theorem counit_comp_map_representableLocalizationInverseImageIso (W : X.C)
    (A : Sheaf X.J (Type u)) :
    (RingedTopos.localizationEquivalence X.ringedTopos (representableSheaf X W)).functor.map
          ((X.representableLocalizationEquivalence W).counitIso.inv.app
            ((RingedTopos.localizationMorphism X.ringedTopos
              (representableSheaf X W)).toToposHom.inverseImage.obj A)) ≫
        (RingedTopos.localizationEquivalence X.ringedTopos
              (representableSheaf X W)).counitIso.hom.app
            ((CategoryTheory.OverShriek.sheafFunctorToOver (U := W) X.J).obj
              ((X.representableLocalizationEquivalence W).inverse.obj
                ((RingedTopos.localizationMorphism X.ringedTopos
                  (representableSheaf X W)).toToposHom.inverseImage.obj A))) ≫
          (CategoryTheory.OverShriek.sheafEquivalence (U := W) X.J).functor.map
            ((X.representableLocalizationInverseImageIso W).hom.app A) =
      (representableLocalizationForwardInverseImageIso X W).inv.app A := by
  have hsplit : (X.representableLocalizationInverseImageIso W).hom.app A =
      (CategoryTheory.OverShriek.sheafEquivalence (U := W) X.J).inverse.map
          ((representableLocalizationForwardInverseImageIso X W).inv.app A) ≫
        (CategoryTheory.OverShriek.sheafEquivalence (U := W) X.J).unitInv.app
          ((X.localizationCommRingedToposHom W).toToposHom.inverseImage.obj A) :=
    rfl
  refine Eq.trans (CategoryTheory.comp_left_of_eq _ (CategoryTheory.comp_left_of_eq _
    (Eq.trans (CategoryTheory.map_of_eq _ hsplit)
      (CategoryTheory.Equivalence.functor_map_inverse_map_comp_unitInv
        (CategoryTheory.OverShriek.sheafEquivalence (U := W) X.J) _)))) ?_
  refine Eq.trans (CategoryTheory.comp_left_of_eq _ (Category.assoc _ _ _).symm) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (CategoryTheory.comp_right_of_eq
    (X.representableLocalizationEquivalence_counitInv_comp W _) _) ?_
  exact Category.id_comp _

variable {U V : X.C} (f : V ⟶ U)

/-- **Stacks 04IL (1) carried across the two lower shrieks.** The inverse of Stacks 04IL (1) at
the restriction of a sheaf, read through `Over.forget h_V^#` and followed by Stacks 00Y1's
identification at `V` and the counit of `j_{V!} ⊣ j_V^{-1}`, is the first projection of the base
change followed by Stacks 00Y1's identification at `U` and the counit of `j_{U!} ⊣ j_U^{-1}`.

This is the one ingredient of the coherence that is not formal: the two counits belong to two
different localizations of the site, and Stacks 04IL (1) is the only thing relating them. It
mentions no ringed site, and is proved for a bare Grothendieck topology beside Stacks 04IL (1) as
`CategoryTheory.OverShriek.left_inverseImageCompSheafFunctorToOverIso_inv_app_comp_counit`; here
it is read at `X.J`, where `representableSheafMap` is the morphism `h_f^#` of associated
sheaves. -/
theorem shriek_inverseImageCompSheafFunctorToOverIso_inv_app (A : Sheaf X.J (Type u)) :
    ((CategoryTheory.OverShriek.inverseImageCompSheafFunctorToOverIso f X.J).inv.app
            ((X.J.overPullback (Type u) U).obj A)).left ≫
        (CategoryTheory.OverShriek.sheafFunctorToOverForgetIso X.J).hom.app
            ((X.J.overPullback (Type u) V).obj A) ≫
          ((Over.forget V).sheafAdjunctionContinuous (Type u) (X.J.over V) X.J).counit.app A =
      pullback.fst
            ((CategoryTheory.OverShriek.sheafFunctorToOver (U := U) X.J).obj
              ((X.J.overPullback (Type u) U).obj A)).hom (representableSheafMap X f) ≫
          (CategoryTheory.OverShriek.sheafFunctorToOverForgetIso X.J).hom.app
              ((X.J.overPullback (Type u) U).obj A) ≫
            ((Over.forget U).sheafAdjunctionContinuous (Type u) (X.J.over U) X.J).counit.app
              A :=
  CategoryTheory.OverShriek.left_inverseImageCompSheafFunctorToOverIso_inv_app_comp_counit
    f X.J A

/-- **The core of Stacks 04J5's comparison, followed by Stacks 04J3 at `U`.** The morphism of
`Sh(C)/h_V^#` which
`AlgebraicGeometry.RingedSite.representableRelocalizationSheafMapCompInverseImageIso_hom_app`
exhibits Stacks 04J5's comparison as, followed by Stacks 04J3's comparison at `U` restricted
along `Over.map f` and read into the slice topos, is Stacks 04J4's base-change comparison, then
base change along `h_f^#` of Stacks 04J3's comparison at `U` in the slice direction, then Stacks
04IL (1).

The two counit factors are absorbed by
`counit_comp_map_representableLocalizationInverseImageIso`, and Stacks 04J3's comparison is
carried past Stacks 04IL (1) by the naturality of the latter. -/
theorem comparisonCore_comp_map_representableLocalizationInverseImageIso
    (A : Sheaf X.J (Type u)) :
    ((RingedTopos.relocalizationInverseImageSliceIso X.ringedTopos
              (representableSheafMap X f)).hom.app
            ((RingedTopos.localizationMorphism X.ringedTopos
              (representableSheaf X U)).toToposHom.inverseImage.obj A) ≫
          (Over.pullback (representableSheafMap X f)).map
              ((RingedTopos.localizationEquivalence X.ringedTopos
                    (representableSheaf X U)).functor.map
                  ((X.representableLocalizationEquivalence U).counitIso.inv.app
                    ((RingedTopos.localizationMorphism X.ringedTopos
                      (representableSheaf X U)).toToposHom.inverseImage.obj A)) ≫
                (RingedTopos.localizationEquivalence X.ringedTopos
                      (representableSheaf X U)).counitIso.hom.app
                  ((CategoryTheory.OverShriek.sheafFunctorToOver (U := U) X.J).obj
                    ((X.representableLocalizationEquivalence U).inverse.obj
                      ((RingedTopos.localizationMorphism X.ringedTopos
                        (representableSheaf X U)).toToposHom.inverseImage.obj A)))) ≫
            (CategoryTheory.OverShriek.inverseImageCompSheafFunctorToOverIso f X.J).inv.app
              ((X.representableLocalizationEquivalence U).inverse.obj
                ((RingedTopos.localizationMorphism X.ringedTopos
                  (representableSheaf X U)).toToposHom.inverseImage.obj A))) ≫
        (CategoryTheory.OverShriek.sheafEquivalence (U := V) X.J).functor.map
          ((X.relocalizationRingedToposHom f).toToposHom.inverseImage.map
            ((X.representableLocalizationInverseImageIso U).hom.app A)) =
      (RingedTopos.relocalizationInverseImageSliceIso X.ringedTopos
              (representableSheafMap X f)).hom.app
            ((RingedTopos.localizationMorphism X.ringedTopos
              (representableSheaf X U)).toToposHom.inverseImage.obj A) ≫
          (Over.pullback (representableSheafMap X f)).map
              ((representableLocalizationForwardInverseImageIso X U).inv.app A) ≫
            (CategoryTheory.OverShriek.inverseImageCompSheafFunctorToOverIso f X.J).inv.app
              ((X.J.overPullback (Type u) U).obj A) := by
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine CategoryTheory.comp_left_of_eq _ ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (CategoryTheory.comp_left_of_eq _
    (((CategoryTheory.OverShriek.inverseImageCompSheafFunctorToOverIso f X.J).inv.naturality
      ((X.representableLocalizationInverseImageIso U).hom.app A)).symm)) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine CategoryTheory.comp_right_of_eq ?_ _
  refine Eq.trans
    (((Over.pullback (representableSheafMap X f)).map_comp _ _)).symm ?_
  exact CategoryTheory.map_of_eq _
    (X.counit_comp_map_representableLocalizationInverseImageIso U A)

/-- **Stacks 04IL (1) and Stacks 04J3's comparison at `U`, through the lower shriek.** Base
change along `h_f^#` of Stacks 04J3's comparison at `U` in the slice direction, followed by
Stacks 04IL (1), read through `Over.forget h_V^#` and followed by Stacks 00Y1's identification at
`V` and the counit of `j_{V!} ⊣ j_V^{-1}`, is the first projection of the base change followed by
the counit of the lower shriek of the localization at `h_U^#`.

Stacks 04IL (1) is discharged by `shriek_inverseImageCompSheafFunctorToOverIso_inv_app` and
Stacks 04J3's comparison by
`RingedSite.left_representableLocalizationForwardInverseImageIso_inv_app_comp_counit`;
in between, base change applied to a morphism commutes with the first projection. -/
theorem forget_pullback_map_comp_inverseImageCompSheafFunctorToOverIso_comp_counit
    (A : Sheaf X.J (Type u)) :
    (Over.forget (representableSheaf X V)).map
          ((Over.pullback (representableSheafMap X f)).map
              ((representableLocalizationForwardInverseImageIso X U).inv.app A) ≫
            (CategoryTheory.OverShriek.inverseImageCompSheafFunctorToOverIso f X.J).inv.app
              ((X.J.overPullback (Type u) U).obj A)) ≫
        (CategoryTheory.OverShriek.sheafFunctorToOverForgetIso X.J).hom.app
            ((X.J.overPullback (Type u) V).obj A) ≫
          ((Over.forget V).sheafAdjunctionContinuous (Type u) (X.J.over V) X.J).counit.app A =
      pullback.fst
            ((RingedTopos.localizationEquivalence X.ringedTopos
                  (representableSheaf X U)).functor.obj
              ((RingedTopos.localizationMorphism X.ringedTopos
                (representableSheaf X U)).toToposHom.inverseImage.obj A)).hom
            (representableSheafMap X f) ≫
          (RingedTopos.localizationShriekAdjunction X.ringedTopos
            (representableSheaf X U)).counit.app A := by
  refine Eq.trans (CategoryTheory.comp_right_of_eq
    ((Over.forget (representableSheaf X V)).map_comp
      ((Over.pullback (representableSheafMap X f)).map
        ((representableLocalizationForwardInverseImageIso X U).inv.app A))
      ((CategoryTheory.OverShriek.inverseImageCompSheafFunctorToOverIso f X.J).inv.app
        ((X.J.overPullback (Type u) U).obj A))) _) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (CategoryTheory.comp_left_of_eq _
    (X.shriek_inverseImageCompSheafFunctorToOverIso_inv_app f A)) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (CategoryTheory.comp_right_of_eq
    (CategoryTheory.Over.pullback_map_left_comp_fst (representableSheafMap X f)
      ((representableLocalizationForwardInverseImageIso X U).inv.app A)) _) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  exact CategoryTheory.comp_left_of_eq _
    (X.left_representableLocalizationForwardInverseImageIso_inv_app_comp_counit U A)

/-- **The core of Stacks 04J5's comparison, through the lower shriek.** Stacks 04J4's base-change
comparison, then base change along `h_f^#` of Stacks 04J3's comparison at `U` in the slice
direction, then Stacks 04IL (1), read through `Over.forget h_V^#` and followed by Stacks 00Y1's
identification at `V` and the counit of `j_{V!} ⊣ j_V^{-1}`, is the counit of the lower shriek of
the localization at `h_V^#`.

The last two factors are discharged by
`forget_pullback_map_comp_inverseImageCompSheafFunctorToOverIso_comp_counit`, and Stacks 04J4's
comparison by
`AlgebraicGeometry.RingedTopos.forget_map_relocalizationInverseImageSliceIso_hom_app`. -/
theorem forget_comparisonCore_comp_counit (A : Sheaf X.J (Type u)) :
    (Over.forget (representableSheaf X V)).map
          ((RingedTopos.relocalizationInverseImageSliceIso X.ringedTopos
                (representableSheafMap X f)).hom.app
              ((RingedTopos.localizationMorphism X.ringedTopos
                (representableSheaf X U)).toToposHom.inverseImage.obj A) ≫
            (Over.pullback (representableSheafMap X f)).map
                ((representableLocalizationForwardInverseImageIso X U).inv.app A) ≫
              (CategoryTheory.OverShriek.inverseImageCompSheafFunctorToOverIso f X.J).inv.app
                ((X.J.overPullback (Type u) U).obj A)) ≫
        (CategoryTheory.OverShriek.sheafFunctorToOverForgetIso X.J).hom.app
            ((X.J.overPullback (Type u) V).obj A) ≫
          ((Over.forget V).sheafAdjunctionContinuous (Type u) (X.J.over V) X.J).counit.app A =
      (RingedTopos.localizationShriekAdjunction X.ringedTopos
        (representableSheaf X V)).counit.app A := by
  refine Eq.trans ?_ (RingedTopos.forget_map_relocalizationInverseImageSliceIso_hom_app
    X.ringedTopos (representableSheafMap X f) A)
  exact Eq.trans (Functor.map_comp_assoc _ _ _ _) (CategoryTheory.comp_left_of_eq _
    (X.forget_pullback_map_comp_inverseImageCompSheafFunctorToOverIso_comp_counit f A))

/-- **Stacks 04J5's comparison, transposed across the lower shriek `j_{V!}`.** This is the
coherence statement of this file with both sides carried across the bijection of
`j_{V!} ⊣ j_V^{-1}`, where every factor is described by an existing lemma. -/
theorem shriek_representableRelocalizationSheafMapCompInverseImageIso_hom_app_comp
    (A : Sheaf X.J (Type u)) :
    ((Over.forget V).sheafPullback (Type u) (X.J.over V) X.J).map
          ((representableRelocalizationSheafMapCompInverseImageIso X f).hom.app
            ((RingedTopos.localizationMorphism X.ringedTopos
              (representableSheaf X U)).toToposHom.inverseImage.obj A)) ≫
        ((Over.forget V).sheafPullback (Type u) (X.J.over V) X.J).map
            ((X.relocalizationRingedToposHom f).toToposHom.inverseImage.map
              ((X.representableLocalizationInverseImageIso U).hom.app A)) ≫
          ((Over.forget V).sheafAdjunctionContinuous (Type u) (X.J.over V) X.J).counit.app A =
      ((Over.forget V).sheafPullback (Type u) (X.J.over V) X.J).map
          ((X.representableLocalizationInverseImageIso V).hom.app A) ≫
        ((Over.forget V).sheafAdjunctionContinuous (Type u) (X.J.over V) X.J).counit.app A := by
  refine Eq.trans ?_
    (X.shriek_representableLocalizationInverseImageIso_hom_app_comp_counit V A).symm
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (CategoryTheory.comp_right_of_eq (CategoryTheory.comp_right_of_eq
    (CategoryTheory.map_of_eq _
      (representableRelocalizationSheafMapCompInverseImageIso_hom_app X f _)) _) _) ?_
  refine Eq.trans (CategoryTheory.comp_right_of_eq
    (X.shriek_sheafEquivalence_inverse_map_comp_unitInv_comp_map V _ _) _) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine CategoryTheory.comp_left_of_eq _ ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (CategoryTheory.comp_right_of_eq (CategoryTheory.map_of_eq
    (Over.forget (representableSheaf X V))
    (X.comparisonCore_comp_map_representableLocalizationInverseImageIso f A)) _) ?_
  exact X.forget_comparisonCore_comp_counit f A

/-- **Stacks 04J5's comparison of inverse images is the one Stacks 04J3 prescribes.** The
component of the comparison of the relocalization of the ringed topos along `h_f^#` with the
relocalization of the ringed site along `f`, taken at an object `j_{h_U^#}^{-1}A` and followed by
Stacks 04J3's comparison at `U` restricted along `Over.map f`, is Stacks 04J3's comparison at
`V`.

The two strictness facts the statement uses hold on the nose: the inverse image of the
relocalization of the ringed topos composed with that of the localization at `h_U^#` *is* the
inverse image of the localization at `h_V^#`, because
`AlgebraicGeometry.RingedToposHom.toposRelocalizationTriangle` is built from `Iso.refl` on
inverse images, and `Over.forget V = Over.map f ⋙ Over.forget U`.

Both sides are morphisms into `j_V^{-1}A`, so the equation is equivalent to its transpose across
`j_{V!} ⊣ j_V^{-1}`, which is
`shriek_representableRelocalizationSheafMapCompInverseImageIso_hom_app_comp`. -/
@[stacks 04J9 "the comparison of 04J5 on inverse images is the one determined by 04J3 at U and
  at V"]
theorem representableRelocalizationSheafMapCompInverseImageIso_hom_app_comp
    (A : Sheaf X.J (Type u)) :
    (representableRelocalizationSheafMapCompInverseImageIso X f).hom.app
          ((RingedTopos.localizationMorphism X.ringedTopos
            (representableSheaf X U)).toToposHom.inverseImage.obj A) ≫
        (X.relocalizationRingedToposHom f).toToposHom.inverseImage.map
          ((X.representableLocalizationInverseImageIso U).hom.app A) =
      (X.representableLocalizationInverseImageIso V).hom.app A := by
  refine (((Over.forget V).sheafAdjunctionContinuous (Type u)
    (X.J.over V) X.J).homEquiv _ _).symm.injective ?_
  refine Eq.trans (CategoryTheory.Adjunction.homEquiv_symm_comp₂
    ((Over.forget V).sheafAdjunctionContinuous (Type u) (X.J.over V) X.J) (T := A) _ _) ?_
  refine Eq.trans
    (X.shriek_representableRelocalizationSheafMapCompInverseImageIso_hom_app_comp f A) ?_
  exact (CategoryTheory.Adjunction.homEquiv_counit
    ((Over.forget V).sheafAdjunctionContinuous (Type u) (X.J.over V) X.J) _ _ _).symm

end AlgebraicGeometry.RingedSite

end
