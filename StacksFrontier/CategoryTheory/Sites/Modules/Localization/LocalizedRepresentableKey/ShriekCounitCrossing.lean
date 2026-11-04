module

public import StacksFrontier.CategoryTheory.Sites.Modules.Localization.LocalizedRepresentableTwoIso
public import StacksFrontier.CategoryTheory.Sites.Modules.Localization.SliceBeckChevalley
public import StacksFrontier.CategoryTheory.Sites.Modules.Localization.LocalizedRepresentableKey.CompositeAdjuncts

@[expose] public section

/-!
# Stacks 04J3's identification through the lower shriek

For a ringed site, Stacks 04J3's identification of the two localized topoi crossed with the lower
shriek and its counit, Stacks 00Y1's identifications of the sheaf underlying a slice object, and,
for a morphism of ringed sites, Stacks 04IU and Stacks 04D3's identification of the two
localizations of the source read through Stacks 04IE's equivalence.
-/

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.RingedToposHom

universe u

namespace AlgebraicGeometry.RingedSite

attribute [local instance] AlgebraicGeometry.RingedTopos.isContinuous_elementPostcomp
  AlgebraicGeometry.RingedTopos.isCocontinuous_elementPostcomp
  CategoryTheory.Functor.isContinuous_overPost_of_isContinuous

/-- **The inverse unit of Stacks 04J3's identification of the two localized topoi, split.**
`representableLocalizationEquivalence` is Stacks 00Y1's equivalence followed by the inverse of
Stacks 04IE's, so a morphism read through its inverse and followed by its inverse unit is Stacks
00Y1's inverse applied to one morphism of `Sh(C)/h_U^#` — the given one carried over by Stacks
04IE's equivalence and then its counit — followed by Stacks 00Y1's own inverse unit. -/
theorem representableLocalizationEquivalence_inverse_map_comp_unitInv
    (Z : RingedSite.{u, u, u}) (U : Z.C) (T : Sheaf (Z.J.over U) (Type u))
    {B : (RingedTopos.localizedRingedTopos Z.ringedTopos (representableSheaf Z U)).Topos}
    (h : B ⟶ (Z.representableLocalizationEquivalence U).functor.obj T) :
    (Z.representableLocalizationEquivalence U).inverse.map h ≫
        (Z.representableLocalizationEquivalence U).unitInv.app T =
      (CategoryTheory.OverShriek.sheafEquivalence (U := U) Z.J).inverse.map
          ((RingedTopos.localizationEquivalence Z.ringedTopos
                (representableSheaf Z U)).functor.map h ≫
            (RingedTopos.localizationEquivalence Z.ringedTopos
                (representableSheaf Z U)).counit.app
              ((CategoryTheory.OverShriek.sheafEquivalence (U := U) Z.J).functor.obj T)) ≫
        (CategoryTheory.OverShriek.sheafEquivalence (U := U) Z.J).unitInv.app T := by
  refine Eq.trans (congrArg (fun z =>
      (Z.representableLocalizationEquivalence U).inverse.map h ≫ z)
    (CategoryTheory.Equivalence.trans_unitInv_app
      (CategoryTheory.OverShriek.sheafEquivalence (U := U) Z.J)
      (RingedTopos.localizationEquivalence Z.ringedTopos (representableSheaf Z U)).symm T)) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  exact congrArg
    (fun z => z ≫ (CategoryTheory.OverShriek.sheafEquivalence (U := U) Z.J).unitInv.app T)
    (((CategoryTheory.OverShriek.sheafEquivalence (U := U) Z.J).inverse.map_comp _ _).symm)

/-- **The crossing of Stacks 04J3's identification with the lower shriek.** Applying `j_{U!}` to
a morphism read through the inverse of the identification and followed by its inverse unit gives
Stacks 00Y1's identification of `j_{U!}Φ_U^{-1}` with `Over.forget h_U^#`, then the given
morphism read in `Sh(C)/h_U^#` through Stacks 04IE's equivalence and its counit, then Stacks
00Y1's identification of the sheaf underlying `Φ_U T` with `j_{U!}T`.

This is the step that carries each whiskered factor of the comparison of Stacks 04J7 across the
lower shriek: every one of them is of this shape, with the unit of the identification at `U`
absorbed into the last factor. -/
theorem shriek_representableLocalizationEquivalence_inverse_map_comp_unitInv
    (Z : RingedSite.{u, u, u}) (U : Z.C) (T : Sheaf (Z.J.over U) (Type u))
    {B : (RingedTopos.localizedRingedTopos Z.ringedTopos (representableSheaf Z U)).Topos}
    (h : B ⟶ (Z.representableLocalizationEquivalence U).functor.obj T) :
    ((Over.forget U).sheafPullback (Type u) (Z.J.over U) Z.J).map
        ((Z.representableLocalizationEquivalence U).inverse.map h ≫
          (Z.representableLocalizationEquivalence U).unitInv.app T) =
      (CategoryTheory.OverShriek.inverseCompShriekIso Z.J).hom.app
          ((RingedTopos.localizationEquivalence Z.ringedTopos
            (representableSheaf Z U)).functor.obj B) ≫
        (Over.forget (representableSheaf Z U)).map
            ((RingedTopos.localizationEquivalence Z.ringedTopos
                (representableSheaf Z U)).functor.map h ≫
              (RingedTopos.localizationEquivalence Z.ringedTopos
                  (representableSheaf Z U)).counit.app
                ((CategoryTheory.OverShriek.sheafEquivalence (U := U) Z.J).functor.obj T)) ≫
          (CategoryTheory.OverShriek.sheafFunctorToOverForgetIso Z.J).hom.app T := by
  refine Eq.trans (congrArg ((Over.forget U).sheafPullback (Type u) (Z.J.over U) Z.J).map
    (representableLocalizationEquivalence_inverse_map_comp_unitInv Z U T h)) ?_
  refine Eq.trans (((Over.forget U).sheafPullback (Type u) (Z.J.over U) Z.J).map_comp _ _) ?_
  refine Eq.trans (congrArg (fun z =>
      ((Over.forget U).sheafPullback (Type u) (Z.J.over U) Z.J).map
        ((CategoryTheory.OverShriek.sheafEquivalence (U := U) Z.J).inverse.map
          ((RingedTopos.localizationEquivalence Z.ringedTopos
                (representableSheaf Z U)).functor.map h ≫
            (RingedTopos.localizationEquivalence Z.ringedTopos
                (representableSheaf Z U)).counit.app
              ((CategoryTheory.OverShriek.sheafEquivalence (U := U) Z.J).functor.obj T))) ≫ z)
    (Z.shriek_sheafEquivalence_unitInv U T)) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg (fun z =>
      z ≫ (CategoryTheory.OverShriek.sheafFunctorToOverForgetIso Z.J).hom.app T)
    ((CategoryTheory.OverShriek.inverseCompShriekIso Z.J).hom.naturality
      ((RingedTopos.localizationEquivalence Z.ringedTopos
            (representableSheaf Z U)).functor.map h ≫
        (RingedTopos.localizationEquivalence Z.ringedTopos
            (representableSheaf Z U)).counit.app
          ((CategoryTheory.OverShriek.sheafEquivalence (U := U) Z.J).functor.obj T)))) ?_
  exact Category.assoc _ _ _

/-- **Stacks 00Y1's two identifications of the sheaf underlying a slice object, composed.**
Stacks 00Y1 identifies the sheaf underlying `Φ_U T` with `j_{U!}T`, and reading that
identification through the inverse of the equivalence gives
`CategoryTheory.OverShriek.inverseCompShriekIso`; composing the first at `Φ_U^{-1}T` with the
second at `T` leaves the underlying map of the counit of the equivalence.

This is what turns a factor `j_{U!}` of a transposed equation into a morphism of `Sh(C)/h_U^#`,
which is the only form in which the lower shriek counit of the localization is described. -/
theorem shriek_sheafFunctorToOverForgetIso_comp_inverseCompShriekIso (Z : RingedSite.{u, u, u})
    (U : Z.C) (T : Over (representableSheaf Z U)) :
    (CategoryTheory.OverShriek.sheafFunctorToOverForgetIso Z.J).hom.app
          ((CategoryTheory.OverShriek.sheafEquivalence (U := U) Z.J).inverse.obj T) ≫
        (CategoryTheory.OverShriek.inverseCompShriekIso Z.J).hom.app T =
      (Over.forget (representableSheaf Z U)).map
        ((CategoryTheory.OverShriek.sheafEquivalence (U := U) Z.J).counit.app T) := by
  rw [CategoryTheory.OverShriek.inverseCompShriekIso_hom_app, ← Category.assoc,
    Iso.hom_inv_id_app, Category.id_comp]
  rfl

/-- **The lower shriek counit of the localization, read out of `Φ_U^{-1}j_U^{-1}A`.** Stacks
00Y1's identification of the sheaf underlying `Φ_U(Φ_U^{-1}j_U^{-1}A)` with
`j_{U!}Φ_U^{-1}j_U^{-1}A`, followed by Stacks 04IQ's identification and the counit of the lower
shriek of the localization at `h_U^#`, is the underlying map of the counit of Stacks 00Y1's
equivalence followed by Stacks 04IE's comparison, and then the projection `A × h_U^# ⟶ A`.

The right-hand side is a morphism of `Sh(C)/h_U^#` read through `Over.forget` followed by that
projection, which is the shape `AlgebraicGeometry.RingedTopos.fibreTranspose` consumes. -/
theorem shriek_inverseCompShriekIso_comp_counit_eq (Z : RingedSite.{u, u, u}) (U : Z.C)
    (A : Sheaf Z.J (Type u)) :
    (CategoryTheory.OverShriek.sheafFunctorToOverForgetIso Z.J).hom.app
          ((Z.representableLocalizationEquivalence U).inverse.obj
            ((RingedTopos.localizationMorphism Z.ringedTopos
              (representableSheaf Z U)).toToposHom.inverseImage.obj A)) ≫
        ((CategoryTheory.OverShriek.inverseCompShriekIso Z.J).hom.app
            ((RingedTopos.localizationEquivalence Z.ringedTopos
                (representableSheaf Z U)).functor.obj
              ((RingedTopos.localizationMorphism Z.ringedTopos
                (representableSheaf Z U)).toToposHom.inverseImage.obj A)) ≫
          (RingedTopos.localizationShriekAdjunction Z.ringedTopos
            (representableSheaf Z U)).counit.app A) =
      (Over.forget (representableSheaf Z U)).map
          ((CategoryTheory.OverShriek.sheafEquivalence (U := U) Z.J).counit.app
              ((RingedTopos.localizationEquivalence Z.ringedTopos
                  (representableSheaf Z U)).functor.obj
                ((RingedTopos.localizationMorphism Z.ringedTopos
                  (representableSheaf Z U)).toToposHom.inverseImage.obj A)) ≫
            (RingedTopos.localizationInverseImageIso Z.ringedTopos
              (representableSheaf Z U)).hom.app A) ≫
        (CategoryTheory.forgetAdjToOver (representableSheaf Z U)).counit.app A := by
  -- The same chain as a term, taken one step at a time: elaborated as a single term, the
  -- unifier meets the factors in an order that exhausts the heartbeat budget.
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (CategoryTheory.comp_right_of_eq
    (shriek_sheafFunctorToOverForgetIso_comp_inverseCompShriekIso Z U _) _) ?_
  refine Eq.trans (CategoryTheory.comp_left_of_eq _
    (RingedTopos.forget_localizationInverseImageIso_hom_app Z.ringedTopos
      (representableSheaf Z U) A).symm) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  exact CategoryTheory.comp_right_of_eq
    ((Over.forget (representableSheaf Z U)).map_comp _ _).symm _

attribute [local instance] CategoryTheory.Functor.isContinuous_overPost_of_isContinuous

variable {X Y : RingedSite.{u, u, u}} (f : RingedSite.Hom X Y) (V : Y.C)

/-- **The identification of the two localizations of the source, read through Stacks 04IE's
equivalence.** `Hom.localizedSourceEquivalenceFunctorIso` is obtained from
`Hom.localizedSourceEquivalenceWhiskerIso` by cancelling the equivalence of Stacks 04IE at
`h_U^#`, which is fully faithful; so carrying a component of the first back through that
equivalence returns the corresponding component of the second.

This is what opens the first of the three factors that the 04IE-level form of the comparison of
Stacks 04J7 is built from: on that level the comparison appears only through
`localizationEquivalence.functor` applied to it, and the whiskered form is the one Stacks
04J4's comparison with base change describes. -/
theorem Hom.map_localizedSourceEquivalenceFunctorIso_inv_app
    (W : (RingedTopos.localizedRingedTopos X.ringedTopos
      (f.ringedToposHom.toToposHom.inverseImage.obj (representableSheaf Y V))).Topos) :
    (X.ringedTopos.localizationEquivalence
          (representableSheaf X (f.u.obj V))).functor.map
        ((f.localizedSourceEquivalenceFunctorIso V).inv.app W) =
      (f.localizedSourceEquivalenceWhiskerIso V).inv.app W := by
  refine Eq.trans (CategoryTheory.map_of_eq
    (X.ringedTopos.localizationEquivalence (representableSheaf X (f.u.obj V))).functor
    (CategoryTheory.Functor.fullyFaithfulCancelRight_inv_app
      (f.localizedSourceEquivalenceWhiskerIso V) W)) ?_
  exact CategoryTheory.Functor.map_preimage _ _

/-- **Stacks 04IU, with Stacks 00Y1's identification at `V` cancelled into the following
factor.** The underlying map of a component of `Hom.sliceInverseImageIso`, followed by `f^{-1}`
of Stacks 00Y1's identification of the sheaf underlying `Φ_V Gs` with `j_{V!}Gs` and of any
further morphism out of `j_{V!}Gs`, is Stacks 00Y1's identification at `u(V)` followed by the
comparison of Stacks 03CF's proof and by `f^{-1}` of that morphism alone.

This is the form in which Stacks 04IU meets an equation transposed across `j_{u(V)!}`: there the
comparison of Stacks 03CF appears bare, and the identification of Stacks 00Y1 at `V` has already
been absorbed by Stacks 04J3's comparison. -/
theorem Hom.left_sliceInverseImageIso_hom_app_comp_map (Gs : Sheaf (Y.J.over V) (Type u))
    {B : Sheaf Y.J (Type u)}
    (γ : ((Over.forget V).sheafPullback (Type u) (Y.J.over V) Y.J).obj Gs ⟶ B) :
    ((f.sliceInverseImageIso V).hom.app Gs).left ≫
        (f.u.sheafPullback (Type u) Y.J X.J).map
          ((CategoryTheory.OverShriek.sheafFunctorToOverForgetIso Y.J).hom.app Gs ≫ γ) =
      (CategoryTheory.OverShriek.sheafFunctorToOverForgetIso X.J).hom.app
          (((Over.post (X := V) f.u).sheafPullback (Type u) (Y.J.over V)
            (X.J.over (f.u.obj V))).obj Gs) ≫
        (CategoryTheory.sheafPullbackOverPostIso Y.J X.J f.u V (Type u)).hom.app Gs ≫
          (f.u.sheafPullback (Type u) Y.J X.J).map γ := by
  refine Eq.trans (CategoryTheory.comp_right_of_eq
    (f.left_sliceInverseImageIso_hom_app_eq V Gs) _) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine CategoryTheory.comp_left_of_eq _ ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine CategoryTheory.comp_left_of_eq _ ?_
  refine Eq.trans ((f.u.sheafPullback (Type u) Y.J X.J).map_comp _ _).symm ?_
  refine CategoryTheory.map_of_eq (f.u.sheafPullback (Type u) Y.J X.J) ?_
  exact Iso.inv_hom_id_app_assoc _ _ _

/-- **The 04J0 side of the residue, as a morphism of `Sh(C)/h_U^#` followed by `f^{-1}` of a
projection.** Stacks 00Y1's identification at `u(V)`, the comparison of Stacks 03CF's proof, and
`f^{-1}` of Stacks 04IQ's identification followed by the counit of the lower shriek of the
localization at `h_V^#`, together are the underlying map of Stacks 04IU's comparison followed by
the base change along Stacks 04D3's isomorphism of `f^{-1}` of the counit of Stacks 00Y1's
equivalence and of Stacks 04IE's comparison, and then `f^{-1}` of the projection
`A × h_V^# ⟶ A`.

Everything on the right is `Over.forget h_U^#` of a morphism of `Sh(C)/h_U^#` except the last
factor, which is `f^{-1}` of the projection out of `j_V^{-1}A`; that is what lets the fibre
transpose of the whole side be computed by naturality. -/
theorem Hom.shriek_sliceInverseImageIso_comp_counit (A : Sheaf Y.J (Type u)) :
    (CategoryTheory.OverShriek.sheafFunctorToOverForgetIso X.J).hom.app
          ((f.localizedRingedToposHom V).toToposHom.inverseImage.obj
            ((Y.representableLocalizationEquivalence V).inverse.obj
              ((RingedTopos.localizationMorphism Y.ringedTopos
                (representableSheaf Y V)).toToposHom.inverseImage.obj A))) ≫
        (CategoryTheory.sheafPullbackOverPostIso Y.J X.J f.u V (Type u)).hom.app
            (((RingedTopos.localizationMorphism Y.ringedTopos
                  (representableSheaf Y V)).toToposHom.inverseImage ⋙
                (Y.representableLocalizationEquivalence V).inverse).obj A) ≫
          (f.u.sheafPullback (Type u) Y.J X.J).map
            ((CategoryTheory.OverShriek.inverseCompShriekIso Y.J).hom.app
                ((RingedTopos.localizationEquivalence Y.ringedTopos
                    (representableSheaf Y V)).functor.obj
                  ((RingedTopos.localizationMorphism Y.ringedTopos
                    (representableSheaf Y V)).toToposHom.inverseImage.obj A)) ≫
              (RingedTopos.localizationShriekAdjunction Y.ringedTopos
                (representableSheaf Y V)).counit.app A) =
      (Over.forget (representableSheaf X (f.u.obj V))).map
          ((f.sliceInverseImageIso V).hom.app
              ((Y.representableLocalizationEquivalence V).inverse.obj
                ((RingedTopos.localizationMorphism Y.ringedTopos
                  (representableSheaf Y V)).toToposHom.inverseImage.obj A)) ≫
            (Over.post f.toposHom.inverseImage ⋙
                Over.map (f.inverseImageRepresentableSheafIso V).hom).map
              ((CategoryTheory.OverShriek.sheafEquivalence (U := V) Y.J).counit.app
                  ((RingedTopos.localizationEquivalence Y.ringedTopos
                      (representableSheaf Y V)).functor.obj
                    ((RingedTopos.localizationMorphism Y.ringedTopos
                      (representableSheaf Y V)).toToposHom.inverseImage.obj A)) ≫
                (RingedTopos.localizationInverseImageIso Y.ringedTopos
                  (representableSheaf Y V)).hom.app A)) ≫
        (f.u.sheafPullback (Type u) Y.J X.J).map
          ((CategoryTheory.forgetAdjToOver (representableSheaf Y V)).counit.app A) := by
  refine Eq.trans (f.left_sliceInverseImageIso_hom_app_comp_map V _ _).symm ?_
  refine Eq.trans (CategoryTheory.comp_left_of_eq _
    (CategoryTheory.map_of_eq (f.u.sheafPullback (Type u) Y.J X.J)
      (Y.shriek_inverseCompShriekIso_comp_counit_eq V A))) ?_
  refine Eq.trans (CategoryTheory.comp_left_of_eq _
    ((f.u.sheafPullback (Type u) Y.J X.J).map_comp _ _)) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine CategoryTheory.comp_right_of_eq ?_ _
  exact ((Over.forget (representableSheaf X (f.u.obj V))).map_comp
    ((f.sliceInverseImageIso V).hom.app
      ((Y.representableLocalizationEquivalence V).inverse.obj
        ((RingedTopos.localizationMorphism Y.ringedTopos
          (representableSheaf Y V)).toToposHom.inverseImage.obj A)))
    ((Over.post f.toposHom.inverseImage ⋙
      Over.map (f.inverseImageRepresentableSheafIso V).hom).map
        ((CategoryTheory.OverShriek.sheafEquivalence (U := V) Y.J).counit.app
            ((RingedTopos.localizationEquivalence Y.ringedTopos
                (representableSheaf Y V)).functor.obj
              ((RingedTopos.localizationMorphism Y.ringedTopos
                (representableSheaf Y V)).toToposHom.inverseImage.obj A)) ≫
          (RingedTopos.localizationInverseImageIso Y.ringedTopos
            (representableSheaf Y V)).hom.app A))).symm

/-- **Stacks 04J7's comparison of inverse images is Stacks 04IE's image of the comparison in the
slice direction.** The associators and the unitor in
`Hom.localizedRepresentableInverseImageIso` contribute identities, so only the whiskering by the
inverse of Stacks 04IE's equivalence at `h_U^#` remains. -/
theorem Hom.localizedRepresentableInverseImageIso_hom_app' (Gs : Sheaf (Y.J.over V) (Type u)) :
    (f.localizedRepresentableInverseImageIso V).hom.app Gs =
      (𝟙 _ ≫ 𝟙 _) ≫ 𝟙 _ ≫
        ((RingedTopos.localizationEquivalence X.ringedTopos
              (representableSheaf X (f.u.obj V))).inverse.map
            ((f.localizedRepresentableSliceInverseImageIso V).hom.app Gs) ≫ 𝟙 _) :=
  rfl

/-- **Stacks 04IU cancels out of Stacks 04J7's comparison in the slice direction.**
`Hom.localizedRepresentableSliceInverseImageIso` is Stacks 04IF's comparison of inverse images,
base-changed along Stacks 04D3's isomorphism, followed by the counit of Stacks 04IE's equivalence
at `h_V^#` read through `f^{-1}`, followed by the inverse of Stacks 04IU; so composing it with
Stacks 04IU leaves the first two factors. -/
theorem Hom.localizedRepresentableSliceInverseImageIso_hom_app' (Gs :
    Sheaf (Y.J.over V) (Type u)) :
    (f.localizedRepresentableSliceInverseImageIso V).hom.app Gs =
      (𝟙 _ ≫ (Over.map (f.inverseImageRepresentableSheafIso V).hom).map
            ((RingedToposHom.localizedInverseImageIso f.ringedToposHom
              (representableSheaf Y V)).hom.app
              ((Y.representableLocalizationEquivalence V).functor.obj Gs))) ≫
        𝟙 _ ≫
          (Over.post f.toposHom.inverseImage ⋙
                Over.map (f.inverseImageRepresentableSheafIso V).hom).map
              (𝟙 _ ≫ (RingedTopos.localizationEquivalence Y.ringedTopos
                    (representableSheaf Y V)).counit.app
                  ((CategoryTheory.OverShriek.sheafFunctorToOver (U := V) Y.J).obj Gs) ≫ 𝟙 _) ≫
            𝟙 _ ≫ (f.sliceInverseImageIso V).inv.app Gs :=
  rfl

/-- **Stacks 04J7's comparison of inverse images, followed by a morphism of `Sh(C)/h_U^#` read
through Stacks 04IE.** The whole composite is Stacks 04IE's image of Stacks 04J7's comparison in
the slice direction followed by that morphism. -/
theorem Hom.localizedRepresentableInverseImageIso_hom_app_comp
    (Gs : Sheaf (Y.J.over V) (Type u))
    {Tt : Over (representableSheaf X (f.u.obj V))}
    (w : ((f.localizedRingedToposHom V).toToposHom.inverseImage ⋙
        CategoryTheory.OverShriek.sheafFunctorToOver X.J).obj Gs ⟶ Tt) :
    (f.localizedRepresentableInverseImageIso V).hom.app Gs ≫
        (RingedTopos.localizationEquivalence X.ringedTopos
          (representableSheaf X (f.u.obj V))).inverse.map w =
      (RingedTopos.localizationEquivalence X.ringedTopos
          (representableSheaf X (f.u.obj V))).inverse.map
        ((f.localizedRepresentableSliceInverseImageIso V).hom.app Gs ≫ w) := by
  rw [f.localizedRepresentableInverseImageIso_hom_app' V Gs, Functor.map_comp]
  simp only [Category.id_comp, Category.comp_id]
  rfl

/-- **Stacks 04IU cancels out of Stacks 04J7's comparison in the slice direction.**
`Hom.localizedRepresentableSliceInverseImageIso` is Stacks 04IF's comparison of inverse images
base-changed along Stacks 04D3's isomorphism, then the counit of Stacks 04IE's equivalence at
`h_V^#` read through `f^{-1}`, then the inverse of Stacks 04IU; composing it with Stacks 04IU
therefore leaves the first two factors.

This is where the two sides of the residue of Stacks 04J7 meet: the 04J0 side presents Stacks
04IU through `Hom.left_sliceInverseImageIso_hom_app_comp_map`, and the 04IF side carries its
inverse inside this comparison. -/
theorem Hom.localizedRepresentableSliceInverseImageIso_hom_app_comp
    (Gs : Sheaf (Y.J.over V) (Type u)) {Tt : Over (representableSheaf X (f.u.obj V))}
    (w : (CategoryTheory.OverShriek.sheafFunctorToOver (U := V) Y.J ⋙
        Over.post f.toposHom.inverseImage ⋙
          Over.map (f.inverseImageRepresentableSheafIso V).hom).obj Gs ⟶ Tt) :
    (f.localizedRepresentableSliceInverseImageIso V).hom.app Gs ≫
        ((f.sliceInverseImageIso V).hom.app Gs ≫ w) =
      (Over.map (f.inverseImageRepresentableSheafIso V).hom).map
          ((RingedToposHom.localizedInverseImageIso f.ringedToposHom
            (representableSheaf Y V)).hom.app
            ((Y.representableLocalizationEquivalence V).functor.obj Gs)) ≫
        (Over.post f.toposHom.inverseImage ⋙
            Over.map (f.inverseImageRepresentableSheafIso V).hom).map
            ((RingedTopos.localizationEquivalence Y.ringedTopos
              (representableSheaf Y V)).counit.app
              ((CategoryTheory.OverShriek.sheafFunctorToOver (U := V) Y.J).obj Gs)) ≫
          w := by
  rw [f.localizedRepresentableSliceInverseImageIso_hom_app' V Gs]
  simp only [Functor.id_obj, Category.id_comp]
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine CategoryTheory.comp_left_of_eq _ ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (CategoryTheory.comp_left_of_eq _ (Iso.inv_hom_id_app_assoc _ _ _)) ?_
  exact CategoryTheory.comp_right_of_eq
    (CategoryTheory.map_of_eq (Over.post f.toposHom.inverseImage ⋙
      Over.map (f.inverseImageRepresentableSheafIso V).hom) (Category.comp_id _)) _

/-- **Stacks 04D3's identification of the two localizations of the source, on morphisms.** The
equivalence is Stacks 04IE at `F` followed by base change along Stacks 04D3's isomorphism and
Stacks 04IE at `h_U^#` inverted, so its action on a morphism is that composite read off. -/
theorem Hom.localizedSourceEquivalence_functor_map {Z W : (RingedTopos.localizedRingedTopos
      X.ringedTopos (f.inverseImageRepresentableSheaf V)).Topos} (g : Z ⟶ W) :
    (f.localizedSourceEquivalence V).functor.map g =
      (RingedTopos.localizationEquivalence X.ringedTopos
          (representableSheaf X (f.u.obj V))).inverse.map
        ((Over.map (f.inverseImageRepresentableSheafIso V).hom).map
          ((RingedTopos.localizationEquivalence X.ringedTopos
            (f.inverseImageRepresentableSheaf V)).functor.map g)) :=
  rfl

/-- The components of `Hom.localizedSourceEquivalenceWhiskerIso`, inverted: the two associators
and the unitor contribute identities, so what is left is Stacks 04J4's comparison of the inverse
image of the relocalization with base change, `CategoryTheory.Over.pullbackIsoMap`, and the
inverse counit of Stacks 04IE at `h_U^#`. -/
theorem Hom.localizedSourceEquivalenceWhiskerIso_inv_app' (W : (RingedTopos.localizedRingedTopos
    X.ringedTopos (f.inverseImageRepresentableSheaf V)).Topos) :
    (f.localizedSourceEquivalenceWhiskerIso V).inv.app W =
      ((RingedTopos.relocalizationInverseImageSliceIso X.ringedTopos
              (f.inverseImageRepresentableSheafIso V).inv).hom.app W ≫
          (Over.pullbackIsoMap (f.inverseImageRepresentableSheafIso V)).hom.app
            ((RingedTopos.localizationEquivalence X.ringedTopos
              (f.inverseImageRepresentableSheaf V)).functor.obj W)) ≫
        (((𝟙 _ ≫ (RingedTopos.localizationEquivalence X.ringedTopos
                  (representableSheaf X (f.u.obj V))).counitInv.app
                ((Over.map (f.inverseImageRepresentableSheafIso V).hom).obj
                  ((RingedTopos.localizationEquivalence X.ringedTopos
                    (f.inverseImageRepresentableSheaf V)).functor.obj W))) ≫ 𝟙 _) ≫ 𝟙 _) :=
  rfl

/-- **Stacks 04D3's identification of the two localizations of the source is Stacks 04J4's
comparison with base change.** The whiskered identification inverted, followed by the counit of
Stacks 04IE at `h_U^#`, is the comparison of the inverse image of the relocalization with base
change along Stacks 04D3's isomorphism, followed by the identification of that base change with
`CategoryTheory.Over.map`.

This is the form in which the residue of Stacks 04J7 consumes Stacks 04J4: the comparison it
exposes is the same one that `localizationInverseImageIso_eq_relocalization` puts in front of
Stacks 04IE's comparison at `h_U^#`, so the two cancel. -/
theorem Hom.localizedSourceEquivalenceWhiskerIso_inv_app_comp_counit
    (W : (RingedTopos.localizedRingedTopos X.ringedTopos
      (f.inverseImageRepresentableSheaf V)).Topos) :
    (f.localizedSourceEquivalenceWhiskerIso V).inv.app W ≫
        (RingedTopos.localizationEquivalence X.ringedTopos
              (representableSheaf X (f.u.obj V))).counit.app
            ((Over.map (f.inverseImageRepresentableSheafIso V).hom).obj
              ((RingedTopos.localizationEquivalence X.ringedTopos
                (f.inverseImageRepresentableSheaf V)).functor.obj W)) =
      (RingedTopos.relocalizationInverseImageSliceIso X.ringedTopos
            (f.inverseImageRepresentableSheafIso V).inv).hom.app W ≫
        (Over.pullbackIsoMap (f.inverseImageRepresentableSheafIso V)).hom.app
          ((RingedTopos.localizationEquivalence X.ringedTopos
            (f.inverseImageRepresentableSheaf V)).functor.obj W) := by
  refine Eq.trans (CategoryTheory.comp_right_of_eq
    (f.localizedSourceEquivalenceWhiskerIso_inv_app' V W) _) ?_
  simp only [Category.id_comp, Category.comp_id]
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (CategoryTheory.comp_left_of_eq _ (Iso.inv_hom_id_app _ _)) ?_
  exact Category.comp_id _

/-- **Stacks 04J3's identification undone, against the two equivalences it is composed of.**
`representableLocalizationEquivalence` is Stacks 04J3's equivalence `Sh(C/U) ≌ Sh(C)/h_U^#`
followed by Stacks 04IE's equivalence inverted, so its inverse counit, carried by Stacks 04IE's
equivalence and followed by that equivalence's counit and by Stacks 04J3's, is the identity.

This is the triangle identity of Stacks 04IE's equivalence together with Stacks 04J3's counit
cancelling its own inverse, and it is what removes both equivalences from a computation that
entered through Stacks 04J3's identification. -/
theorem representableLocalizationEquivalence_counitInv_comp (Z : RingedSite.{u, u, u}) (U : Z.C)
    (W : (RingedTopos.localizedRingedTopos Z.ringedTopos (representableSheaf Z U)).Topos) :
    (RingedTopos.localizationEquivalence Z.ringedTopos (representableSheaf Z U)).functor.map
          ((Z.representableLocalizationEquivalence U).counitInv.app W) ≫
        (RingedTopos.localizationEquivalence Z.ringedTopos
              (representableSheaf Z U)).counit.app
            ((CategoryTheory.OverShriek.sheafFunctorToOver Z.J).obj
              ((Z.representableLocalizationEquivalence U).inverse.obj W)) ≫
          (CategoryTheory.OverShriek.sheafEquivalence (U := U) Z.J).counit.app
            ((RingedTopos.localizationEquivalence Z.ringedTopos
              (representableSheaf Z U)).functor.obj W) =
      𝟙 _ := by
  simp only [representableLocalizationEquivalence,
    CategoryTheory.Equivalence.trans_counitInv_app,
    CategoryTheory.Equivalence.symm_counitInv_app]
  refine Eq.trans (CategoryTheory.comp_right_of_eq (Functor.map_comp _ _ _) _) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (CategoryTheory.comp_left_of_eq _ (Category.assoc _ _ _).symm) ?_
  refine Eq.trans (CategoryTheory.comp_left_of_eq _ (CategoryTheory.comp_right_of_eq
    (CategoryTheory.map_naturality_toId _ _
      (RingedTopos.localizationEquivalence Z.ringedTopos
        (representableSheaf Z U)).counit _) _)) ?_
  refine Eq.trans (CategoryTheory.comp_left_of_eq _ (Category.assoc _ _ _)) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (CategoryTheory.comp_right_of_eq
    (CategoryTheory.Equivalence.functor_unit_comp _ _) _) ?_
  refine Eq.trans (Category.id_comp _) ?_
  exact Iso.inv_hom_id_app _ _

end AlgebraicGeometry.RingedSite

end
