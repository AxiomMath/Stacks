module

public import StacksFrontier.CategoryTheory.Sites.Modules.Localization.LocalizedRepresentableTwoIso
public import StacksFrontier.CategoryTheory.Sites.Modules.Localization.SliceBeckChevalley
public import StacksFrontier.CategoryTheory.Sites.Modules.Localization.LocalizedRepresentableKey.ShriekCounitCrossing

@[expose] public section

/-!
# The transposed comparison of Stacks 04J7

The 04J0 and 04IF sides of the comparison of Stacks 04J7 carried across the bijection of
`j_{U!} ⊣ j_U^{-1}`, the comparison equation `Hom.keyNat`, its instance `Hom.key` at the structure
sheaf, and the 2-isomorphism `Hom.localizedComparisonTwoIso` of Stacks 04J7.
-/

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.RingedToposHom

universe u

namespace AlgebraicGeometry.RingedSite

attribute [local instance] AlgebraicGeometry.RingedTopos.isContinuous_elementPostcomp
  AlgebraicGeometry.RingedTopos.isCocontinuous_elementPostcomp
  CategoryTheory.Functor.isContinuous_overPost_of_isContinuous

attribute [local instance] CategoryTheory.Functor.isContinuous_overPost_of_isContinuous

variable {X Y : RingedSite.{u, u, u}} (f : RingedSite.Hom X Y) (V : Y.C)

/-! Every comparison of inverse images below is an atom: it is a composite of several whiskered
isomorphisms between sheaf categories, and none of them is ever opened — they are only passed
from one equation to the next. Left reducible, a unification that mentions one of them descends
into the whole composite to check a type that two definitional unfoldings would settle, which is
what exhausts the elaborator's budget here. The same declarations are marked the same way, for
the same reason, in
`StacksFrontier/CategoryTheory/Sites/Modules/Localization/RelocalizedMorphismComparison.lean`.

`AlgebraicGeometry.RingedSite.Hom.compareMid` is deliberately *not* among them: the inverse
image of `compareMid` applied to a morphism has to be recognised as Stacks 00Y1's inverse
applied to that morphism carried into `Sh(C)/h_U^#`, and that identity is definitional. -/
attribute [local irreducible]
  AlgebraicGeometry.RingedToposHom.inverseImageCompLocalizationIso
  AlgebraicGeometry.RingedSite.representableLocalizationInverseImageIso
  AlgebraicGeometry.RingedSite.Hom.midInverseImageComparison
  AlgebraicGeometry.RingedSite.Hom.localizedSourceEquivalenceFunctorIso
  AlgebraicGeometry.RingedSite.Hom.localizedRepresentableInverseImageIso
  CategoryTheory.SliceTopos.overPullbackCompSheafPullbackOverPostIso


/-- **Stacks 04J3's comparison at `U` through the lower shriek, for the retyped comparison.**
`AlgebraicGeometry.RingedSite.Hom.midInverseImageComparison` is Stacks 04J3's comparison at `U`
typed at the source functor the 04IF side of Stacks 04J7 presents it with, so
`AlgebraicGeometry.RingedSite.shriek_representableLocalizationInverseImageIso_hom_app_comp_counit`
applies to it verbatim. -/
theorem Hom.shriek_midInverseImageComparison_app_comp_counit (B : Sheaf X.J (Type u)) :
    ((Over.forget (f.u.obj V)).sheafPullback (Type u) (X.J.over (f.u.obj V)) X.J).map
          ((f.midInverseImageComparison V).app B) ≫
        ((Over.forget (f.u.obj V)).sheafAdjunctionContinuous (Type u)
          (X.J.over (f.u.obj V)) X.J).counit.app B =
      (CategoryTheory.OverShriek.inverseCompShriekIso X.J).hom.app
          ((X.ringedTopos.localizationEquivalence
              (representableSheaf X (f.u.obj V))).functor.obj
            ((X.ringedTopos.localizationMorphism
              (representableSheaf X (f.u.obj V))).toToposHom.inverseImage.obj B)) ≫
        (X.ringedTopos.localizationShriekAdjunction
          (representableSheaf X (f.u.obj V))).counit.app B :=
  Eq.trans
    (congrArg (fun z =>
        ((Over.forget (f.u.obj V)).sheafPullback (Type u) (X.J.over (f.u.obj V)) X.J).map z ≫
          ((Over.forget (f.u.obj V)).sheafAdjunctionContinuous (Type u)
            (X.J.over (f.u.obj V)) X.J).counit.app B)
      (f.midInverseImageComparison_app V B))
    (X.shriek_representableLocalizationInverseImageIso_hom_app_comp_counit (f.u.obj V) B)

/-- **The 04J0 side of the transposed comparison of Stacks 04J7.** Applying `j_{U!}` to Stacks
04J3's comparison at `V` restricted along `f'`, and following it by Stacks 03CF's comparison
`j_{U!}(f')^{-1} ≅ f^{-1}j_{V!}` and by `f^{-1}` of the counit of `j_{V!} ⊣ j_V^{-1}`, is that
same comparison of Stacks 03CF at the other object, followed by `f^{-1}` of Stacks 00Y1's
identification of `j_{V!}Φ_V^{-1}` with `Over.forget` and of the counit of the lower shriek of
the localization at `h_V^#`.

The restriction along `f'` is moved across Stacks 03CF's comparison by its naturality — `f'` is
`Over.post u` on sheaves, so the comparison is a natural isomorphism of `(f')^{-1}j_{U!}` with
`j_{V!}f^{-1}` and this is the only thing needed of it — and what is left under `f^{-1}` is
`AlgebraicGeometry.RingedSite.shriek_representableLocalizationInverseImageIso_hom_app_comp_counit`
at `V`. -/
theorem Hom.shriek_restrictedRepresentableLocalizationInverseImageIso_comp_counit
    (A : Sheaf Y.J (Type u)) :
    ((Over.forget (f.u.obj V)).sheafPullback (Type u) (X.J.over (f.u.obj V)) X.J).map
          ((f.localizedRingedToposHom V).toToposHom.inverseImage.map
            ((Y.representableLocalizationInverseImageIso V).hom.app A)) ≫
        (CategoryTheory.sheafPullbackOverPostIso Y.J X.J f.u V (Type u)).hom.app
            ((Y.J.overPullback (Type u) V).obj A) ≫
          (f.u.sheafPullback (Type u) Y.J X.J).map
            (((Over.forget V).sheafAdjunctionContinuous (Type u) (Y.J.over V) Y.J).counit.app
              A) =
      (CategoryTheory.sheafPullbackOverPostIso Y.J X.J f.u V (Type u)).hom.app
          (((RingedTopos.localizationMorphism Y.ringedTopos
              (representableSheaf Y V)).toToposHom.inverseImage ⋙
            (Y.representableLocalizationEquivalence V).inverse).obj A) ≫
        (f.u.sheafPullback (Type u) Y.J X.J).map
          ((CategoryTheory.OverShriek.inverseCompShriekIso Y.J).hom.app
              ((Y.ringedTopos.localizationEquivalence (representableSheaf Y V)).functor.obj
                ((Y.ringedTopos.localizationMorphism
                  (representableSheaf Y V)).toToposHom.inverseImage.obj A)) ≫
            (Y.ringedTopos.localizationShriekAdjunction
              (representableSheaf Y V)).counit.app A) := by
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg (fun z => z ≫
      (f.u.sheafPullback (Type u) Y.J X.J).map
        (((Over.forget V).sheafAdjunctionContinuous (Type u) (Y.J.over V) Y.J).counit.app A))
    ((CategoryTheory.sheafPullbackOverPostIso Y.J X.J f.u V (Type u)).hom.naturality
      ((Y.representableLocalizationInverseImageIso V).hom.app A))) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine congrArg (fun z =>
    (CategoryTheory.sheafPullbackOverPostIso Y.J X.J f.u V (Type u)).hom.app
        (((RingedTopos.localizationMorphism Y.ringedTopos
            (representableSheaf Y V)).toToposHom.inverseImage ⋙
          (Y.representableLocalizationEquivalence V).inverse).obj A) ≫ z) ?_
  refine Eq.trans ((f.u.sheafPullback (Type u) Y.J X.J).map_comp
    (((Over.forget V).sheafPullback (Type u) (Y.J.over V) Y.J).map
      ((Y.representableLocalizationInverseImageIso V).hom.app A))
    (((Over.forget V).sheafAdjunctionContinuous (Type u) (Y.J.over V) Y.J).counit.app A)).symm ?_
  exact congrArg (f.u.sheafPullback (Type u) Y.J X.J).map
    (Y.shriek_representableLocalizationInverseImageIso_hom_app_comp_counit V A)

/-- **The 04IF side of the transposed comparison of Stacks 04J7.** Applying `j_{U!}` to Stacks
04IF's comparison of inverse images restricted along `compareMid`, then to Stacks 04J3's
comparison at `U`, and following that by the counit of `j_{U!} ⊣ j_U^{-1}`, replaces the last
two factors by Stacks 00Y1's identification of `j_{U!}Φ_U^{-1}` with `Over.forget` and the
counit of the lower shriek of the localization at `h_U^#`.

The whole side is stated, rather than only the last two factors, because that is what makes the
statement matchable against the transposed equation: see the implementation notes. -/
theorem Hom.shriek_localizedCompareMidComp_comp_counit (A : Sheaf Y.J (Type u)) :
    ((Over.forget (f.u.obj V)).sheafPullback (Type u) (X.J.over (f.u.obj V)) X.J).map
          ((f.compareMid V).toToposHom.inverseImage.map
            ((f.ringedToposHom.inverseImageCompLocalizationIso
              (representableSheaf Y V)).inv.app A)) ≫
        ((Over.forget (f.u.obj V)).sheafPullback (Type u) (X.J.over (f.u.obj V)) X.J).map
            ((f.midInverseImageComparison V).app
              ((f.u.sheafPullback (Type u) Y.J X.J).obj A)) ≫
          ((Over.forget (f.u.obj V)).sheafAdjunctionContinuous (Type u)
            (X.J.over (f.u.obj V)) X.J).counit.app
            ((f.u.sheafPullback (Type u) Y.J X.J).obj A) =
      ((Over.forget (f.u.obj V)).sheafPullback (Type u) (X.J.over (f.u.obj V)) X.J).map
          ((f.compareMid V).toToposHom.inverseImage.map
            ((f.ringedToposHom.inverseImageCompLocalizationIso
              (representableSheaf Y V)).inv.app A)) ≫
        (CategoryTheory.OverShriek.inverseCompShriekIso X.J).hom.app
            ((X.ringedTopos.localizationEquivalence
                (representableSheaf X (f.u.obj V))).functor.obj
              ((X.ringedTopos.localizationMorphism
                  (representableSheaf X (f.u.obj V))).toToposHom.inverseImage.obj
                ((f.u.sheafPullback (Type u) Y.J X.J).obj A))) ≫
          (X.ringedTopos.localizationShriekAdjunction
              (representableSheaf X (f.u.obj V))).counit.app
            ((f.u.sheafPullback (Type u) Y.J X.J).obj A) :=
  congrArg (fun z =>
      ((Over.forget (f.u.obj V)).sheafPullback (Type u) (X.J.over (f.u.obj V)) X.J).map
          ((f.compareMid V).toToposHom.inverseImage.map
            ((f.ringedToposHom.inverseImageCompLocalizationIso
              (representableSheaf Y V)).inv.app A)) ≫ z)
    (f.shriek_midInverseImageComparison_app_comp_counit V
      ((f.u.sheafPullback (Type u) Y.J X.J).obj A))

/-- **The four factors of the comparison of Stacks 04J7 on inverse images.**
`Hom.localizedRepresentableCompInverseImageIso` is a composite of four whiskered isomorphisms,
and the first two and the third are
`AlgebraicGeometry.RingedSite.representableLocalizationEquivalence` applied to a morphism and its
inverse unit; naming the components is what lets each factor be
pushed through the lower shriek by its own lemma. -/
theorem Hom.localizedRepresentableCompInverseImageIso_hom_app
    (T : (RingedTopos.localizedRingedTopos Y.ringedTopos (representableSheaf Y V)).Topos) :
    (f.localizedRepresentableCompInverseImageIso V).hom.app T =
      (X.representableLocalizationEquivalence (f.u.obj V)).inverse.map
          ((f.localizedSourceEquivalenceFunctorIso V).inv.app
            ((RingedToposHom.localizedToposMorphism f.ringedToposHom
              (representableSheaf Y V)).inverseImage.obj T)) ≫
        (X.representableLocalizationEquivalence (f.u.obj V)).inverse.map
            (𝟙 _ ≫
              ((RingedToposHom.localizedToposMorphism f.ringedToposHom
                  (representableSheaf Y V)).inverseImage ⋙
                (f.localizedSourceEquivalence V).functor).map
                ((Y.representableLocalizationEquivalence V).counitInv.app T) ≫
              (f.localizedRepresentableInverseImageIso V).hom.app
                ((Y.representableLocalizationEquivalence V).inverse.obj T)) ≫
          ((X.representableLocalizationEquivalence (f.u.obj V)).unitInv.app
              (((Y.representableLocalizationEquivalence V).inverse ⋙
                (f.localizedRingedToposHom V).toToposHom.inverseImage).obj T) ≫
            𝟙 _) :=
  rfl

/-- **The comparison of Stacks 04J7 as one morphism read through Stacks 04J3's identification,
followed by its inverse unit.** This is the shape
`AlgebraicGeometry.RingedSite.shriek_representableLocalizationEquivalence_inverse_map_comp_unitInv`
consumes: the first two whiskered factors are collected into a single morphism of the
localization at `F`, and the unitor contributes the identity. -/
theorem Hom.localizedRepresentableCompInverseImageIso_hom_app_eq
    (T : (RingedTopos.localizedRingedTopos Y.ringedTopos (representableSheaf Y V)).Topos) :
    (f.localizedRepresentableCompInverseImageIso V).hom.app T =
      (X.representableLocalizationEquivalence (f.u.obj V)).inverse.map
          ((f.localizedSourceEquivalenceFunctorIso V).inv.app
              ((RingedToposHom.localizedToposMorphism f.ringedToposHom
                (representableSheaf Y V)).inverseImage.obj T) ≫
            (𝟙 _ ≫
              ((RingedToposHom.localizedToposMorphism f.ringedToposHom
                  (representableSheaf Y V)).inverseImage ⋙
                (f.localizedSourceEquivalence V).functor).map
                ((Y.representableLocalizationEquivalence V).counitInv.app T) ≫
              (f.localizedRepresentableInverseImageIso V).hom.app
                ((Y.representableLocalizationEquivalence V).inverse.obj T))) ≫
        (X.representableLocalizationEquivalence (f.u.obj V)).unitInv.app
          (((Y.representableLocalizationEquivalence V).inverse ⋙
            (f.localizedRingedToposHom V).toToposHom.inverseImage).obj T) :=
  Eq.trans (f.localizedRepresentableCompInverseImageIso_hom_app V T)
    (CategoryTheory.map_comp_comp_id _ _ _ _)

/-- **The inverse image of `compareMid` is the relocalization's followed by Stacks 04J3's at
`U`.** `compareMid` is the relocalization morphism of Stacks 04J4 along Stacks 04D3's
isomorphism followed by the localization at `U`, so its inverse image is the inverse image of
the relocalization read through the identification of the two localized topoi.

The two objects are typed at `f^{-1}h_V^#` written out, rather than at
`AlgebraicGeometry.RingedSite.Hom.inverseImageRepresentableSheaf`, because that is the spelling
Stacks 04IF's comparison carries, and the two spellings of the one sheaf do not match once an
argument is instantiated outside the goal. -/
theorem Hom.compareMid_inverseImage_map {A B : (RingedTopos.localizedRingedTopos X.ringedTopos
      (f.ringedToposHom.toToposHom.inverseImage.obj (representableSheaf Y V))).Topos}
    (χ : A ⟶ B) :
    (f.compareMid V).toToposHom.inverseImage.map χ =
      (X.representableLocalizationEquivalence (f.u.obj V)).inverse.map
        ((X.ringedTopos.relocalizationMorphism
          (f.inverseImageRepresentableSheafIso V).inv).toToposHom.inverseImage.map χ) :=
  rfl

/-- **The inverse image of `compareMid` read through Stacks 00Y1's equivalence.**
`Hom.compareMid_inverseImage_map` one step further: `Φ_U^{-1}` is the inverse of Stacks 04J3's
equivalence, and that is Stacks 00Y1's equivalence followed by the inverse of Stacks 04IE's, so
the inverse image of `compareMid` applied to a morphism is that morphism relocalized, read in
`Sh(C)/h_U^#` and carried back along Stacks 00Y1.

This is the spelling the naturality of `CategoryTheory.OverShriek.inverseCompShriekIso`
produces, and naming it is what keeps the unifier out of the definition of that equivalence:
Stacks 00Y1's equivalence is a functor's `Functor.asEquivalence`, so its inverse is built from
`Classical.choice`, and asking the unifier for this identification inside a larger goal makes it
unfold that choice over and over. -/
theorem Hom.compareMid_inverseImage_map_sheafEquivalence
    {A B : (RingedTopos.localizedRingedTopos X.ringedTopos
      (f.ringedToposHom.toToposHom.inverseImage.obj (representableSheaf Y V))).Topos}
    (χ : A ⟶ B) :
    (f.compareMid V).toToposHom.inverseImage.map χ =
      (CategoryTheory.OverShriek.sheafEquivalence (U := f.u.obj V) X.J).inverse.map
        ((X.ringedTopos.localizationEquivalence
            (representableSheaf X (f.u.obj V))).functor.map
          ((X.ringedTopos.relocalizationMorphism
            (f.inverseImageRepresentableSheafIso V).inv).toToposHom.inverseImage.map χ)) :=
  rfl

/-- **Stacks 00Y1's identification at the two spellings of `j_U^{-1}f^{-1}A`.** The component of
`CategoryTheory.OverShriek.inverseCompShriekIso` that the 04J0 side of the residue carries is
indexed by `Φ_U(j_{h_U^#}^{-1}(f^{-1}A))`, while the one a naturality square of Stacks 04IF
produces is indexed by that object relocalized along Stacks 04D3's isomorphism; the two objects
are the same, so the two components are the same morphism.

Stating the identification is what lets the two occurrences meet: solving it by unification
inside the goal instead expands Stacks 00Y1's equivalence, whose inverse is a `Classical.choice`,
at every node of the composite. -/
theorem Hom.inverseCompShriekIso_hom_app_eq (A : Sheaf Y.J (Type u)) :
    (CategoryTheory.OverShriek.inverseCompShriekIso X.J).hom.app
        ((X.ringedTopos.localizationEquivalence
            (representableSheaf X (f.u.obj V))).functor.obj
          ((X.ringedTopos.localizationMorphism
              (representableSheaf X (f.u.obj V))).toToposHom.inverseImage.obj
            ((f.u.sheafPullback (Type u) Y.J X.J).obj A))) =
      (CategoryTheory.OverShriek.inverseCompShriekIso X.J).hom.app
        ((X.ringedTopos.localizationEquivalence
            (representableSheaf X (f.u.obj V))).functor.obj
          ((X.ringedTopos.relocalizationMorphism
              (f.inverseImageRepresentableSheafIso V).inv).toToposHom.inverseImage.obj
            ((f.ringedToposHom.toToposHom.inverseImage ⋙
              (X.ringedTopos.localizationMorphism
                (f.ringedToposHom.toToposHom.inverseImage.obj
                  (representableSheaf Y V))).toToposHom.inverseImage).obj A))) :=
  rfl

/-- **The 04IF side of the residue, before the counit.** Applying `j_{U!}` to Stacks 04IF's
comparison restricted along `compareMid` and following it by Stacks 00Y1's identification of
`j_{U!}Φ_U^{-1}` with `Over.forget h_U^#` is that identification at the other object followed by
the comparison read in `Sh(C)/h_U^#`.

This is the naturality of `CategoryTheory.OverShriek.inverseCompShriekIso`, reached from the
goal by the two identifications above: the morphism through
`Hom.compareMid_inverseImage_map_sheafEquivalence`, and the component of Stacks 00Y1's
identification through `Hom.inverseCompShriekIso_hom_app_eq`. Separated from
`Hom.shriek_compareMidRestricted_comp_inverseCompShriekIso`, which adds the counit of the lower
shriek to both sides, because the two together are over one declaration's heartbeats. -/
theorem Hom.shriek_compareMidRestricted_comp_inverseCompShriekIso_hom (A : Sheaf Y.J (Type u)) :
    ((Over.forget (f.u.obj V)).sheafPullback (Type u) (X.J.over (f.u.obj V)) X.J).map
          ((f.compareMid V).toToposHom.inverseImage.map
            ((f.ringedToposHom.inverseImageCompLocalizationIso
              (representableSheaf Y V)).inv.app A)) ≫
        (CategoryTheory.OverShriek.inverseCompShriekIso X.J).hom.app
          ((X.ringedTopos.localizationEquivalence
              (representableSheaf X (f.u.obj V))).functor.obj
            ((X.ringedTopos.localizationMorphism
                (representableSheaf X (f.u.obj V))).toToposHom.inverseImage.obj
              ((f.u.sheafPullback (Type u) Y.J X.J).obj A))) =
      (CategoryTheory.OverShriek.inverseCompShriekIso X.J).hom.app
          ((X.ringedTopos.localizationEquivalence
              (representableSheaf X (f.u.obj V))).functor.obj
            ((X.ringedTopos.relocalizationMorphism
                (f.inverseImageRepresentableSheafIso V).inv).toToposHom.inverseImage.obj
              ((RingedToposHom.localizedToposMorphism f.ringedToposHom
                  (representableSheaf Y V)).inverseImage.obj
                ((RingedTopos.localizationMorphism Y.ringedTopos
                  (representableSheaf Y V)).toToposHom.inverseImage.obj A)))) ≫
        (Over.forget (representableSheaf X (f.u.obj V))).map
          ((X.ringedTopos.localizationEquivalence
              (representableSheaf X (f.u.obj V))).functor.map
            ((X.ringedTopos.relocalizationMorphism
                (f.inverseImageRepresentableSheafIso V).inv).toToposHom.inverseImage.map
              ((f.ringedToposHom.inverseImageCompLocalizationIso
                (representableSheaf Y V)).inv.app A))) := by
  refine Eq.trans (CategoryTheory.comp_right_of_eq (CategoryTheory.map_of_eq
    ((Over.forget (f.u.obj V)).sheafPullback (Type u) (X.J.over (f.u.obj V)) X.J)
    (f.compareMid_inverseImage_map_sheafEquivalence V
      ((f.ringedToposHom.inverseImageCompLocalizationIso
        (representableSheaf Y V)).inv.app A))) _) ?_
  refine Eq.trans (CategoryTheory.comp_left_of_eq _
    (f.inverseCompShriekIso_hom_app_eq V A)) ?_
  exact (CategoryTheory.OverShriek.inverseCompShriekIso (U := f.u.obj V) X.J).hom.naturality
    ((X.ringedTopos.localizationEquivalence
        (representableSheaf X (f.u.obj V))).functor.map
      ((X.ringedTopos.relocalizationMorphism
          (f.inverseImageRepresentableSheafIso V).inv).toToposHom.inverseImage.map
        ((f.ringedToposHom.inverseImageCompLocalizationIso
          (representableSheaf Y V)).inv.app A)))

/-- **The 04IF side of the residue, with Stacks 00Y1's identification moved to the front.**
Applying `j_{U!}` to Stacks 04IF's comparison restricted along `compareMid` and following it by
Stacks 00Y1's identification of `j_{U!}Φ_U^{-1}` with `Over.forget h_U^#` is that
identification at the other object followed by the comparison read in `Sh(C)/h_U^#`.

`compareMid` is the relocalization of Stacks 04J4 followed by Stacks 04J3's identification at
`U`, so its inverse image applied to a morphism is, on the nose, Stacks 00Y1's inverse applied
to that morphism carried into `Sh(C)/h_U^#`; the statement is then the naturality of Stacks
04IQ's identification `Φ_U^{-1}j_{U!} ≅ Over.forget h_U^#`. -/
theorem Hom.shriek_compareMidRestricted_comp_inverseCompShriekIso (A : Sheaf Y.J (Type u)) :
    ((Over.forget (f.u.obj V)).sheafPullback (Type u) (X.J.over (f.u.obj V)) X.J).map
          ((f.compareMid V).toToposHom.inverseImage.map
            ((f.ringedToposHom.inverseImageCompLocalizationIso
              (representableSheaf Y V)).inv.app A)) ≫
        (CategoryTheory.OverShriek.inverseCompShriekIso X.J).hom.app
            ((X.ringedTopos.localizationEquivalence
                (representableSheaf X (f.u.obj V))).functor.obj
              ((X.ringedTopos.localizationMorphism
                  (representableSheaf X (f.u.obj V))).toToposHom.inverseImage.obj
                ((f.u.sheafPullback (Type u) Y.J X.J).obj A))) ≫
          (X.ringedTopos.localizationShriekAdjunction
              (representableSheaf X (f.u.obj V))).counit.app
            ((f.u.sheafPullback (Type u) Y.J X.J).obj A) =
      (CategoryTheory.OverShriek.inverseCompShriekIso X.J).hom.app
          ((X.ringedTopos.localizationEquivalence
              (representableSheaf X (f.u.obj V))).functor.obj
            ((X.ringedTopos.relocalizationMorphism
                (f.inverseImageRepresentableSheafIso V).inv).toToposHom.inverseImage.obj
              ((RingedToposHom.localizedToposMorphism f.ringedToposHom
                  (representableSheaf Y V)).inverseImage.obj
                ((RingedTopos.localizationMorphism Y.ringedTopos
                  (representableSheaf Y V)).toToposHom.inverseImage.obj A)))) ≫
        (Over.forget (representableSheaf X (f.u.obj V))).map
            ((X.ringedTopos.localizationEquivalence
                (representableSheaf X (f.u.obj V))).functor.map
              ((X.ringedTopos.relocalizationMorphism
                  (f.inverseImageRepresentableSheafIso V).inv).toToposHom.inverseImage.map
                ((f.ringedToposHom.inverseImageCompLocalizationIso
                  (representableSheaf Y V)).inv.app A))) ≫
          (X.ringedTopos.localizationShriekAdjunction
              (representableSheaf X (f.u.obj V))).counit.app
            ((f.u.sheafPullback (Type u) Y.J X.J).obj A) :=
  CategoryTheory.comp₂_comp_right_of_eq
    (f.shriek_compareMidRestricted_comp_inverseCompShriekIso_hom V A) _


attribute [local irreducible]
  AlgebraicGeometry.RingedSite.Hom.localizedRepresentableCompInverseImageIso

/-- **Stacks 04J4's comparison at the two spellings of `f^{-1}A`.** The component of
`RingedTopos.relocalizationInverseImageSliceIso` that a naturality square of Stacks 04IF
produces is indexed by `(f^{-1} ⋙ j_F^{-1}).obj A`, while the one produced by splitting
Stacks 04IE's comparison is indexed by `j_F^{-1}` of the inverse image of `A` along `u`; the two
objects are the same, so the two components are the same morphism.

Stating the identification is what lets the two occurrences cancel: solving it by unification
inside the goal instead expands the localization morphism at both spellings of `F`. -/
theorem Hom.relocalizationInverseImageSliceIso_inv_app_eq (A : Sheaf Y.J (Type u)) :
    ((X.ringedTopos.relocalizationInverseImageSliceIso
        (f.inverseImageRepresentableSheafIso V).inv).app
      ((f.ringedToposHom.toToposHom.inverseImage ⋙
          (X.ringedTopos.localizationMorphism
            (f.ringedToposHom.toToposHom.inverseImage.obj
              (Y.representableSheaf V))).toToposHom.inverseImage).obj A)).inv =
      (X.ringedTopos.relocalizationInverseImageSliceIso
          (f.inverseImageRepresentableSheafIso V).inv).inv.app
        ((X.ringedTopos.localizationMorphism
          (f.inverseImageRepresentableSheaf V)).toToposHom.inverseImage.obj
            ((f.u.sheafPullback (Type u) Y.J X.J).obj A)) := rfl

/-- The components of an isomorphism of functors into `Over T` compose to the identity on the
total spaces. -/
private theorem inv_app_left_comp_hom_app_left {C D : Type*} [Category C] [Category D]
    {T : D} {F G : C ⥤ Over T} (e : F ≅ G) (X : C) :
    (e.inv.app X).left ≫ (e.hom.app X).left = 𝟙 _ := by
  rw [← Over.comp_left, Iso.inv_hom_id_app, Over.id_left]

/-- **The adjunct of the projection, read through Stacks 03EH and base change along an
isomorphism.** The morphism of `Sh(C)/h_U^#` adjoint to `f^{-1}` of the projection
`A × h_V^# ⟶ A`, followed by Stacks 03EH's identification of `toOver h_U^#` with `toOver F`
base-changed and by the identification of that base change with `Over.map` along Stacks 04D3's
isomorphism, is Stacks 04H1's comparison `f^{-1}(A × h_V^#) ≅ f^{-1}A × F` inverted. -/
theorem Hom.homEquiv_comp_toOverCompPullbackIso_inv_comp_pullbackIsoMap
    (A : Sheaf Y.J (Type u)) :
    (CategoryTheory.forgetAdjToOver (representableSheaf X (f.u.obj V))).homEquiv
          ((Over.post f.toposHom.inverseImage ⋙
            Over.map (f.inverseImageRepresentableSheafIso V).hom).obj
              ((CategoryTheory.toOver (representableSheaf Y V)).obj A))
          ((f.u.sheafPullback (Type u) Y.J X.J).obj A)
          ((f.u.sheafPullback (Type u) Y.J X.J).map
            ((CategoryTheory.forgetAdjToOver (representableSheaf Y V)).counit.app A)) ≫
        (CategoryTheory.toOverCompPullbackIso
            (f.inverseImageRepresentableSheafIso V).inv).inv.app
            ((f.u.sheafPullback (Type u) Y.J X.J).obj A) ≫
          (Over.pullbackIsoMap (f.inverseImageRepresentableSheafIso V)).hom.app
            ((CategoryTheory.toOver (f.inverseImageRepresentableSheaf V)).obj
              ((f.u.sheafPullback (Type u) Y.J X.J).obj A)) =
      (Over.map (f.inverseImageRepresentableSheafIso V).hom).map
        ((f.toposHom.inverseImageCompToOverIso (representableSheaf Y V)).inv.app A) := by
  refine Over.OverMorphism.ext (CartesianMonoidalCategory.hom_ext _ _ ?_ ?_)
  · simp only [Over.comp_left, Over.map_map_left]
    rw [show SemiCartesianMonoidalCategory.fst ((f.u.sheafPullback (Type u) Y.J X.J).obj A)
          (f.inverseImageRepresentableSheaf V) =
        (CategoryTheory.forgetAdjToOver
            (f.toposHom.inverseImage.obj (representableSheaf Y V))).counit.app
          (f.toposHom.inverseImage.obj A) from rfl]
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (CategoryTheory.comp_left_of_eq _ (Category.assoc _ _ _)) ?_
    refine Eq.trans (CategoryTheory.comp_left_of_eq _ (CategoryTheory.comp_left_of_eq _
      (CategoryTheory.comp_right_of_eq (Over.forget_map_pullbackIsoMap_hom_app
        (f.inverseImageRepresentableSheafIso V) _) _))) ?_
    refine Eq.trans (CategoryTheory.comp_left_of_eq _ (CategoryTheory.comp_left_of_eq _
      (CategoryTheory.forget_map_toOverCompPullbackIso_hom_app
        (f.inverseImageRepresentableSheafIso V).inv _).symm)) ?_
    refine Eq.trans (CategoryTheory.comp_left_of_eq _ (Category.assoc _ _ _).symm) ?_
    refine Eq.trans (CategoryTheory.comp_left_of_eq _
      (CategoryTheory.comp_right_of_eq
        (inv_app_left_comp_hom_app_left (CategoryTheory.toOverCompPullbackIso
          (f.inverseImageRepresentableSheafIso V).inv) _) _)) ?_
    refine Eq.trans (CategoryTheory.comp_left_of_eq _ (Category.id_comp _)) ?_
    refine Eq.trans (Eq.trans (CategoryTheory.Adjunction.homEquiv_counit
      (CategoryTheory.forgetAdjToOver (representableSheaf X (f.u.obj V))) _ _ _).symm
      (Equiv.symm_apply_apply _ _)) ?_
    refine Eq.trans ?_ (CategoryTheory.comp_left_of_eq _
      (f.toposHom.inverseImageCompToOverIso_hom_app_left_counit
        (representableSheaf Y V) A))
    refine Eq.trans ?_ (Category.assoc _ _ _)
    exact Eq.trans (Category.id_comp _).symm (CategoryTheory.comp_right_of_eq
      (inv_app_left_comp_hom_app_left
        (f.toposHom.inverseImageCompToOverIso (representableSheaf Y V)) A).symm _)
  · refine (CategoryTheory.cancel_mono (f.inverseImageRepresentableSheafIso V).hom).1 ?_
    exact Eq.trans (Eq.trans (Category.assoc _ _ _) (Over.w _))
      (Eq.trans (Category.assoc _ _ _) (Over.w _)).symm

/-- **The fibre transpose of the counit of the lower shriek, at the spelling the comparison of
Stacks 04J7 carries.** `AlgebraicGeometry.RingedTopos.fibreTranspose_shriek_counit` at `h_U^#`
and `f^{-1}A`, with its source object written as the relocalization of Stacks 04J4 along Stacks
04D3's isomorphism and its target through the identity functor — the two spellings `Hom.keyNat`
arrives with, and the ones its own statement of this step would otherwise have to identify
against the lemma's inside a goal that has already spent most of its heartbeats. -/
theorem Hom.fibreTranspose_shriek_counit_app_eq (A : Sheaf Y.J (Type u)) :
    X.ringedTopos.fibreTranspose (representableSheaf X (f.u.obj V))
        ((X.ringedTopos.localizationEquivalence
            (representableSheaf X (f.u.obj V))).functor.obj
          ((X.ringedTopos.relocalizationMorphism
              (f.inverseImageRepresentableSheafIso V).inv).toToposHom.inverseImage.obj
            ((f.ringedToposHom.toToposHom.inverseImage ⋙
              (X.ringedTopos.localizationMorphism
                (f.ringedToposHom.toToposHom.inverseImage.obj
                  (representableSheaf Y V))).toToposHom.inverseImage).obj A)))
        ((𝟭 (Sheaf X.J (Type u))).obj ((f.u.sheafPullback (Type u) Y.J X.J).obj A))
        ((X.ringedTopos.localizationShriekAdjunction
            (representableSheaf X (f.u.obj V))).counit.app
          ((f.u.sheafPullback (Type u) Y.J X.J).obj A)) =
      (X.ringedTopos.localizationEquivalence
          (representableSheaf X (f.u.obj V))).unitInv.app
        ((X.ringedTopos.localizationMorphism
            (representableSheaf X (f.u.obj V))).toToposHom.inverseImage.obj
          ((f.u.sheafPullback (Type u) Y.J X.J).obj A)) :=
  X.ringedTopos.fibreTranspose_shriek_counit (representableSheaf X (f.u.obj V))
    ((f.u.sheafPullback (Type u) Y.J X.J).obj A)

/-- For a sheaf `A` on `D`, the comparison `Hom.localizedRepresentableCompInverseImageIso`
at `Φ_V^{-1}j_V^{-1}A`, followed by the inverse image of Stacks 04J3's comparison at `V` and
Stacks 03CF's comparison, equals the inverse image along `compareMid` of the inverse of
`RingedToposHom.inverseImageCompLocalizationIso` followed by
`Hom.midInverseImageComparison` at `f^{-1}A`. -/
theorem Hom.keyNat (A : Sheaf Y.J (Type u)) :
    (f.localizedRepresentableCompInverseImageIso V).hom.app
          ((RingedTopos.localizationMorphism Y.ringedTopos
            (representableSheaf Y V)).toToposHom.inverseImage.obj A) ≫
        (f.localizedRingedToposHom V).toToposHom.inverseImage.map
            ((Y.representableLocalizationInverseImageIso V).hom.app A) ≫
          (CategoryTheory.SliceTopos.overPullbackCompSheafPullbackOverPostIso Y.J X.J f.u V
            f.isMorphismOfSites).hom.app A =
      (f.compareMid V).toToposHom.inverseImage.map
          ((f.ringedToposHom.inverseImageCompLocalizationIso
            (representableSheaf Y V)).inv.app A) ≫
        (f.midInverseImageComparison V).app ((f.u.sheafPullback (Type u) Y.J X.J).obj A) := by
  refine ((((Over.forget (f.u.obj V)).sheafAdjunctionContinuous (Type u)
    (X.J.over (f.u.obj V)) X.J).homEquiv _ _).symm.injective ?_)
  refine Eq.trans (CategoryTheory.Adjunction.homEquiv_symm_comp₃
    ((Over.forget (f.u.obj V)).sheafAdjunctionContinuous (Type u) (X.J.over (f.u.obj V)) X.J)
    (T := (f.u.sheafPullback (Type u) Y.J X.J).obj A) _ _ _) ?_
  refine Eq.trans ?_ (CategoryTheory.Adjunction.homEquiv_symm_comp₂
    ((Over.forget (f.u.obj V)).sheafAdjunctionContinuous (Type u) (X.J.over (f.u.obj V)) X.J)
    (T := (f.u.sheafPullback (Type u) Y.J X.J).obj A) _ _).symm
  refine Eq.trans (CategoryTheory.comp_left_of_eq _ (CategoryTheory.comp_left_of_eq _
    (CategoryTheory.SliceTopos.shriek_overPullbackCompSheafPullbackOverPostIso_hom_app_comp_counit
      Y.J X.J f.u V f.isMorphismOfSites A))) ?_
  refine Eq.trans (CategoryTheory.comp_left_of_eq _
    (f.shriek_restrictedRepresentableLocalizationInverseImageIso_comp_counit V A)) ?_
  refine Eq.trans ?_ (f.shriek_localizedCompareMidComp_comp_counit V A).symm
  refine Eq.trans ?_ (f.shriek_compareMidRestricted_comp_inverseCompShriekIso V A).symm
  refine Eq.trans (CategoryTheory.comp_right_of_eq (CategoryTheory.map_of_eq
    ((Over.forget (f.u.obj V)).sheafPullback (Type u) (X.J.over (f.u.obj V)) X.J)
    (f.localizedRepresentableCompInverseImageIso_hom_app_eq V _)) _) ?_
  refine Eq.trans (CategoryTheory.comp_right_of_eq
    (X.shriek_representableLocalizationEquivalence_inverse_map_comp_unitInv (f.u.obj V) _ _) _) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (CategoryTheory.comp_left_of_eq _ (Category.assoc _ _ _)) ?_
  refine CategoryTheory.comp_left_of_eq _ ?_
  refine X.ringedTopos.fibreTranspose_injective (representableSheaf X (f.u.obj V)) _ _ ?_
  refine Eq.trans (X.ringedTopos.fibreTranspose_forget_map_comp _ _ _ _) ?_
  refine Eq.trans ?_ (X.ringedTopos.fibreTranspose_forget_map_comp _ _ _ _).symm
  refine Eq.trans ?_ (CategoryTheory.comp_left_of_eq _
    (f.fibreTranspose_shriek_counit_app_eq V A)).symm
  refine Eq.trans ?_ ((X.ringedTopos.localizationEquivalence
    (representableSheaf X (f.u.obj V))).unitInv.naturality _).symm
  refine Eq.trans (CategoryTheory.comp_right_of_eq
    (CategoryTheory.Equivalence.inverse_map_functor_map_comp_counit _ _) _) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine CategoryTheory.comp_left_of_eq _ ?_
  refine Eq.trans (CategoryTheory.comp_left_of_eq _
    (AlgebraicGeometry.RingedTopos.fibreTranspose_of_eq _ _ _ _
      (f.shriek_sliceInverseImageIso_comp_counit V A))) ?_
  refine Eq.trans (CategoryTheory.comp_left_of_eq _
    (X.ringedTopos.fibreTranspose_forget_map_comp (representableSheaf X (f.u.obj V))
      ((f.u.sheafPullback (Type u) Y.J X.J).obj A) _ _)) ?_
  refine Eq.trans (CategoryTheory.comp₄_comp_assoc _ _ _ _ _ _) ?_
  refine Eq.trans (CategoryTheory.comp_right_of_eq
    (CategoryTheory.comp_left_of_eq _ (CategoryTheory.comp_left_of_eq _
      (CategoryTheory.comp_left_of_eq _
        (Eq.trans (f.localizedRepresentableInverseImageIso_hom_app_comp V _ _)
          (CategoryTheory.map_of_eq (RingedTopos.localizationEquivalence X.ringedTopos
              (representableSheaf X (f.u.obj V))).inverse
            (f.localizedRepresentableSliceInverseImageIso_hom_app_comp V _ _)))))) _) ?_
  refine Eq.trans (CategoryTheory.comp_left_of_eq _
    (X.ringedTopos.fibreTranspose_eq (representableSheaf X (f.u.obj V)) _ _ _)) ?_
  refine Eq.trans (CategoryTheory.comp₃_map₃_comp
    (RingedTopos.localizationEquivalence X.ringedTopos
      (representableSheaf X (f.u.obj V))).inverse _ _ _ _ _ _ _) ?_
  refine Eq.trans (CategoryTheory.comp_left_of_eq _ (CategoryTheory.comp_left_of_eq _
    (CategoryTheory.comp_right_of_eq
      (f.localizedSourceEquivalence_functor_map V _) _))) ?_
  refine Eq.trans (CategoryTheory.comp₂_map₂_comp
    (RingedTopos.localizationEquivalence X.ringedTopos
      (representableSheaf X (f.u.obj V))).inverse _ _ _ _ _) ?_
  refine Eq.trans (CategoryTheory.comp_left_of_eq _ (Category.id_comp _)) ?_
  refine (RingedTopos.localizationEquivalence X.ringedTopos
    (representableSheaf X (f.u.obj V))).functor.map_injective ?_
  refine Eq.trans (Functor.map_comp _ _ _) ?_
  refine Eq.trans (CategoryTheory.comp_right_of_eq
    (f.map_localizedSourceEquivalenceFunctorIso_inv_app V _) _) ?_
  refine Eq.trans (CategoryTheory.comp_left_of_eq _
    (CategoryTheory.Equivalence.functor_map_inverse_map_comp_unitInv _ _)) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (CategoryTheory.comp_right_of_eq
    (f.localizedSourceEquivalenceWhiskerIso_inv_app_comp_counit V _) _) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans ?_ (CategoryTheory.map_of_eq
    (RingedTopos.localizationEquivalence X.ringedTopos
      (representableSheaf X (f.u.obj V))).functor (Functor.id_map _)).symm
  refine Eq.trans ?_ (CategoryTheory.map_eq_naturality_comp_inv_app
    (RingedTopos.relocalizationInverseImageSliceIso X.ringedTopos
      (f.inverseImageRepresentableSheafIso V).inv)
    ((f.ringedToposHom.inverseImageCompLocalizationIso
      (representableSheaf Y V)).inv.app A)).symm
  refine Eq.trans ?_ (Category.assoc _ _ _).symm
  refine CategoryTheory.comp_left_of_eq _ ?_
  refine Eq.trans ?_ (CategoryTheory.comp_left_of_eq _
    (f.relocalizationInverseImageSliceIso_inv_app_eq V A).symm)
  rw [RingedTopos.localizationInverseImageIso_inv_app_eq_relocalization X.ringedTopos
    (f.inverseImageRepresentableSheafIso V).inv
    ((f.u.sheafPullback (Type u) Y.J X.J).obj A)]
  refine Eq.trans (CategoryTheory.comp₅_comp_assoc _ _ _ _ _ _) ?_
  refine CategoryTheory.comp_right_of_eq ?_ _
  rw [← CategoryTheory.NatIso.naturality_2
    (Over.pullbackIsoMap (f.inverseImageRepresentableSheafIso V))
    ((RingedTopos.localizationInverseImageIso X.ringedTopos
      (f.inverseImageRepresentableSheaf V)).inv.app
        ((f.u.sheafPullback (Type u) Y.J X.J).obj A))]
  refine Eq.trans ?_ (CategoryTheory.NatIso.naturality_2
    (Over.pullbackIsoMap (f.inverseImageRepresentableSheafIso V))
    ((RingedTopos.localizationEquivalence X.ringedTopos
        (f.inverseImageRepresentableSheaf V)).functor.map
      ((f.ringedToposHom.inverseImageCompLocalizationIso (representableSheaf Y V)).inv.app A)))
  refine CategoryTheory.comp_left_of_eq _ ?_
  refine Eq.trans (CategoryTheory.comp₆_comp_assoc _ _ _ _ _ _ _) ?_
  refine CategoryTheory.comp_right_of_eq ?_ _
  refine Eq.trans (CategoryTheory.comp_left_of_eq _ (CategoryTheory.comp_left_of_eq _
    (CategoryTheory.comp₃_comp_assoc _ _ _ _))) ?_
  refine Eq.trans (CategoryTheory.comp_left_of_eq _ (CategoryTheory.comp_left_of_eq _
    (CategoryTheory.comp_right_of_eq
      (f.homEquiv_comp_toOverCompPullbackIso_inv_comp_pullbackIsoMap V A) _))) ?_
  refine Eq.trans (CategoryTheory.map₆_comp
    (Over.map (f.inverseImageRepresentableSheafIso V).hom) _ _ _ _ _ _) ?_
  refine CategoryTheory.map_of_eq _ ?_
  refine Eq.trans ?_ (f.ringedToposHom.map_inverseImageCompLocalizationIso_inv_app
    (representableSheaf Y V) A).symm
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (CategoryTheory.comp_right_of_eq
    (CategoryTheory.map_naturality _ _ _ _
      (f.ringedToposHom.localizedInverseImageIso (representableSheaf Y V)).hom _) _) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine CategoryTheory.comp_left_of_eq _ ?_
  refine Eq.trans (CategoryTheory.comp₃_comp₂_assoc _ _ _ _ _) ?_
  refine CategoryTheory.comp_right_of_eq ?_ _
  refine Eq.trans (CategoryTheory.map₃_comp _ _ _ _) ?_
  refine CategoryTheory.map_of_eq _ ?_
  refine Eq.trans (CategoryTheory.comp₃_comp_assoc _ _ _ _) ?_
  refine Eq.trans (CategoryTheory.comp_right_of_eq
    (Y.representableLocalizationEquivalence_counitInv_comp V _) _) ?_
  exact Category.id_comp _

/-! From here on `compareMid` is an atom too. Everything above that needs its definition — its
inverse image on a restriction, and the two sides of the residue pushed through the lower shriek
— is already proved, and the statements below mention it only to pass it from one equation to the
next. Left reducible, type-checking the statement of `Hom.key` descends through `compareMid` to
compare two spellings of one sheaf *underneath* its inverse image, where both have to be
expanded, instead of at the top level, where the comparison is the one the statements above
already paid for; that identification alone exhausts the elaborator's budget before the proof is
even reached. The same declaration is marked the same way, for the same reason, in
`StacksFrontier/CategoryTheory/Sites/Modules/Localization/LocalizedRepresentableTwoIso.lean`.

The position is load-bearing in both directions: `Hom.keyNat` and
`Hom.shriek_compareMidRestricted_comp_inverseCompShriekIso` are only type-correct *through*
`compareMid`'s unfolding, so the attribute cannot move earlier. -/
attribute [local irreducible] AlgebraicGeometry.RingedSite.Hom.compareMid

/-- **Stacks 04J7 at the structure sheaf.** `Hom.keyNat` at the sheaf of sets
underlying the structure sheaf of `Y`: this is the instance of the comparison equation that the
compatibility of `Hom.localizedRepresentableCompInverseImageIso` with the two structure maps
needs. -/
theorem Hom.key :
  (f.localizedRepresentableCompInverseImageIso V).hom.app
        ((RingedTopos.localizedRingedTopos Y.ringedTopos (representableSheaf Y V)).forgetRing.obj
          (RingedTopos.localizedRingedTopos Y.ringedTopos (representableSheaf Y V)).O) ≫
      (f.localizedRingedToposHom V).toToposHom.inverseImage.map
          ((Y.representableLocalizationInverseImageIso V).hom.app
            ((ringedTopos Y).forgetRing.obj Y.O)) ≫
        (CategoryTheory.SliceTopos.overPullbackCompSheafPullbackOverPostIso Y.J X.J f.u V
          f.isMorphismOfSites).hom.app ((ringedTopos Y).forgetRing.obj Y.O) =
    (f.compareMid V).toToposHom.inverseImage.map
        ((f.ringedToposHom.inverseImageCompLocalizationIso
          (representableSheaf Y V)).inv.app ((ringedTopos Y).forgetRing.obj Y.O)) ≫
      (f.midInverseImageComparison V).app
        ((ringedTopos X).forgetRing.obj
          ((Stacks.Sheaves.ToposPushforward.inverseImageCommRingFunctor.{u, u, u, u, u, u}
            f.ringedToposHom.toToposHom).obj Y.ringedTopos.O)) :=
  f.keyNat V ((ringedTopos Y).forgetRing.obj Y.O)

/-- **The comparison of Stacks 04J7 is compatible with the two structure maps.** This is the
hypothesis `AlgebraicGeometry.RingedToposHom.TwoIso.ofInverseImageIso` asks of
`Hom.localizedRepresentableCompInverseImageIso`: following it by the structure map of
`ι_V ∘ f'_{04J0}` in inverse-image form gives the structure map of `f'_{04IF} ∘ compareMid`.

Both structure maps are computed in
`StacksFrontier/CategoryTheory/Sites/Modules/Localization/LocalizedRepresentableTwoIso.lean`, and
they share their last factor, so what is left between them is `Hom.key`.

Separated from `Hom.localizedComparisonTwoIso` because the two composites of Stacks 04J7 are
spelled out there twice already — once as the type of the 2-isomorphism and once as the explicit
arguments of `TwoIso.ofInverseImageIso` — and a third and fourth occurrence inside this equation
puts that one declaration over its heartbeats. -/
theorem Hom.localizedComparison_commutes :
    (f.localizedRepresentableCompInverseImageIso V).hom.app
          ((RingedTopos.localizedRingedTopos Y.ringedTopos
              (representableSheaf Y V)).forgetRing.obj
            (RingedTopos.localizedRingedTopos Y.ringedTopos (representableSheaf Y V)).O) ≫
        (ringedTopos (X.over (f.u.obj V))).forgetRing.map
          (AlgebraicGeometry.RingedToposHom.comp.{u, u, u, u, u, u, u, u, u}
            (X := ringedTopos (X.over (f.u.obj V)))
            (Y := ringedTopos (Y.over V))
            (Z := RingedTopos.localizedRingedTopos Y.ringedTopos (representableSheaf Y V))
            (representableLocalizationRingedMorphism Y V)
            (f.localizedRingedToposHom V)).fSharpInverseImage =
      (ringedTopos (X.over (f.u.obj V))).forgetRing.map
        (AlgebraicGeometry.RingedToposHom.comp.{u, u, u, u, u, u, u, u, u}
          (X := ringedTopos (X.over (f.u.obj V)))
          (Y := RingedTopos.localizedRingedTopos X.ringedTopos
            (f.inverseImageRepresentableSheaf V))
          (Z := RingedTopos.localizedRingedTopos Y.ringedTopos (representableSheaf Y V))
          (f.ringedToposHom.localized (representableSheaf Y V))
          (f.compareMid V)).fSharpInverseImage :=
  Eq.trans
    (congrArg (fun z => (f.localizedRepresentableCompInverseImageIso V).hom.app
        ((RingedTopos.localizedRingedTopos Y.ringedTopos
            (representableSheaf Y V)).forgetRing.obj
          (RingedTopos.localizedRingedTopos Y.ringedTopos (representableSheaf Y V)).O) ≫ z)
      (f.forgetRing_representableComp_fSharpInverseImage V))
    (Eq.trans
      (Eq.trans
        (Eq.trans
          (congrArg (fun z => (f.localizedRepresentableCompInverseImageIso V).hom.app
              ((RingedTopos.localizedRingedTopos Y.ringedTopos
                  (representableSheaf Y V)).forgetRing.obj
                (RingedTopos.localizedRingedTopos Y.ringedTopos
                  (representableSheaf Y V)).O) ≫ z)
            (Category.assoc
              ((f.localizedRingedToposHom V).toToposHom.inverseImage.map
                ((Y.representableLocalizationInverseImageIso V).hom.app
                  ((ringedTopos Y).forgetRing.obj Y.O)))
              ((CategoryTheory.SliceTopos.overPullbackCompSheafPullbackOverPostIso
                  Y.J X.J f.u V f.isMorphismOfSites).hom.app
                ((ringedTopos Y).forgetRing.obj Y.O))
              ((X.J.overPullback (Type u) (f.u.obj V)).map
                ((ringedTopos X).forgetRing.map f.ringedToposHom.fSharpInverseImage))).symm)
          (Category.assoc _ _ _).symm)
        (congrArg (fun z => z ≫ (X.J.overPullback (Type u) (f.u.obj V)).map
          ((ringedTopos X).forgetRing.map f.ringedToposHom.fSharpInverseImage)) (f.key V)))
      (Eq.trans (Category.assoc _ _ _)
        (f.forgetRing_localizedCompareMidComp_fSharpInverseImage V).symm))

/-- **Stacks 04J7.** The diagrams of Stacks 04J0 and Stacks 04IF agree, via the identifications of
Stacks 04J3: the square commutes: the composite
`j_V ∘ f'_{04J0}` of the localization of the source at `V` with Stacks 04J0's localized morphism
is 2-isomorphic to the composite `f'_{04IF} ∘ compareMid` of Stacks 04IF's localized morphism
with Stacks 04D3's identification of the two localizations of the source.

The 2-isomorphism is `Hom.localizedRepresentableCompInverseImageIso` on inverse images; what
makes it a 2-isomorphism of morphisms of ringed topoi is `Hom.key`, its compatibility with the
two structure maps. -/
@[stacks 04J7
  "the diagrams of 04J0 and 04IF agree via the identifications of 04J3, as a 2-isomorphism of \
  morphisms of ringed topoi"]
noncomputable def Hom.localizedComparisonTwoIso :
    AlgebraicGeometry.RingedToposHom.TwoIso
      (A := ringedTopos (X.over (f.u.obj V)))
      (B := RingedTopos.localizedRingedTopos Y.ringedTopos (representableSheaf Y V))
      (AlgebraicGeometry.RingedToposHom.comp.{u, u, u, u, u, u, u, u, u}
        (X := ringedTopos (X.over (f.u.obj V)))
        (Y := ringedTopos (Y.over V))
        (Z := RingedTopos.localizedRingedTopos Y.ringedTopos (representableSheaf Y V))
        (representableLocalizationRingedMorphism Y V)
        (f.localizedRingedToposHom V))
      (AlgebraicGeometry.RingedToposHom.comp.{u, u, u, u, u, u, u, u, u}
        (X := ringedTopos (X.over (f.u.obj V)))
        (Y := RingedTopos.localizedRingedTopos X.ringedTopos
          (f.inverseImageRepresentableSheaf V))
        (Z := RingedTopos.localizedRingedTopos Y.ringedTopos (representableSheaf Y V))
        (f.ringedToposHom.localized (representableSheaf Y V))
        (f.compareMid V)) :=
  TwoIso.ofInverseImageIso
    (A := ringedTopos (X.over (f.u.obj V)))
    (B := RingedTopos.localizedRingedTopos Y.ringedTopos (representableSheaf Y V))
    (p := AlgebraicGeometry.RingedToposHom.comp.{u, u, u, u, u, u, u, u, u}
        (X := ringedTopos (X.over (f.u.obj V)))
      (Y := ringedTopos (Y.over V))
      (Z := RingedTopos.localizedRingedTopos Y.ringedTopos (representableSheaf Y V))
      (representableLocalizationRingedMorphism Y V)
      (f.localizedRingedToposHom V))
    (q := AlgebraicGeometry.RingedToposHom.comp.{u, u, u, u, u, u, u, u, u}
        (X := ringedTopos (X.over (f.u.obj V)))
      (Y := RingedTopos.localizedRingedTopos X.ringedTopos
        (f.inverseImageRepresentableSheaf V))
      (Z := RingedTopos.localizedRingedTopos Y.ringedTopos (representableSheaf Y V))
      (f.ringedToposHom.localized (representableSheaf Y V))
      (f.compareMid V))
    (f.localizedRepresentableCompInverseImageIso V)
    (f.localizedComparison_commutes V)


end AlgebraicGeometry.RingedSite

end
