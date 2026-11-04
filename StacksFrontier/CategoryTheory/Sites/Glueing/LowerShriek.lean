module

public import StacksFrontier.CategoryTheory.Sites.Localization.LowerShriekProduct

/-!
# `j_{U!} j_U^{-1} ≅ h_U^# × (-)`, naturally

Let `(C, J)` be a small site and `U` an object of `C`. Stacks 03EE says that
`j_{U!}j_U^{-1}\mathcal{F} = \mathcal{F} \times h_U^\#` for a single sheaf of sets
`\mathcal{F}`;
`StacksFrontier.CategoryTheory.Sites.Localization.LowerShriekProduct` proves exactly that, one sheaf
at a time. Several arguments
(Stacks 0D7X among them) need the isomorphism to be *natural* in the sheaf, so that the composite
`j_{U!} \circ j_U^{-1}` is identified with the functor
`\mathcal{F} \mapsto h_U^\# \times \mathcal{F}`. That upgrade is what this file provides.

## Main results

* `CategoryTheory.OverShriek.restrictPresheafProdNatIso`: at the level of presheaves, the
  coproduct presheaf `V ↦ ∐_{φ : V ⟶ U} P(V)` of Stacks 03CD attached to the restriction of `P` to
  `C/U` is the product `h_U × P`, naturally in `P`.
* `CategoryTheory.OverShriek.overPullbackNatIso`: `j_U^{-1}` is the sheafification of the
  presheaf-level restriction along `j_U`.
* `CategoryTheory.OverShriek.overShriekOverPullbackNatIso`: **Stacks 03EE, naturally in the
  sheaf.**
* `CategoryTheory.OverShriek.prodOverPullbackOverPushforwardAdjunction`: the resulting adjunction
  `(h_U^\# \times -) \dashv j_{U*} \circ j_U^{-1}`.

No tag is claimed here: 03EE is already covered by
`StacksFrontier.CategoryTheory.Sites.Localization.LowerShriekProduct`. This file only
strengthens it to a natural isomorphism, for use downstream.
-/

@[expose] public section

open CategoryTheory Opposite Limits
universe u

namespace CategoryTheory.OverShriek

variable {C : Type u} [SmallCategory C] (U : C)

/-! ### The coproduct presheaf of a restriction is a product, naturally -/

/-- The identification of the coproduct presheaf with `h_U × P` is compatible with the projection
to `h_U`. -/
@[simp]
lemma prodIso_hom_fst (P : Cᵒᵖ ⥤ Type u) : (prodIso U P).hom ≫ prod.fst = prodFst U P := by
  simp [prodIso]

/-- The identification of the coproduct presheaf with `h_U × P` is compatible with the projection
to `P`. -/
@[simp]
lemma prodIso_hom_snd (P : Cᵒᵖ ⥤ Type u) : (prodIso U P).hom ≫ prod.snd = prodSnd U P := by
  simp [prodIso]

/-- The projection `prodFst` to `P` is natural in `P`. -/
@[simp]
lemma map_prodFst {P P' : Cᵒᵖ ⥤ Type u} (α : P ⟶ P') :
    presheafFunctor.map ((Over.forget U).op.whiskerLeft α) ≫ prodFst U P' = prodFst U P ≫ α :=
  rfl

/-- The projection `prodSnd` to `h_U` does not depend on `P`, so it is natural in `P`. -/
@[simp]
lemma map_prodSnd {P P' : Cᵒᵖ ⥤ Type u} (α : P ⟶ P') :
    presheafFunctor.map ((Over.forget U).op.whiskerLeft α) ≫ prodSnd U P' = prodSnd U P :=
  rfl

/-- The comparison map from the coproduct presheaf of `j_U^{-1}P` to `h_U × P` is an isomorphism,
being `prodIso` followed by the braiding. -/
noncomputable instance isIso_prodSndLift (P : Cᵒᵖ ⥤ Type u) :
    IsIso (prod.lift (prodSnd U P) (prodFst U P)) := by
  have h :
    prod.lift (prodSnd U P) (prodFst U P) =
      (prodIso U P ≪≫ prod.braiding P (yoneda.obj U)).hom := by
    apply prod.hom_ext <;> simp [prod.braiding]
  rw [h]; infer_instance

/-- The comparison map from the coproduct presheaf of Stacks 03CD attached to the restriction of
`P` to `C/U` to the product `h_U × P`, natural in `P`. -/
@[simps]
noncomputable def restrictPresheafProdNatTrans :
    restrict (U := U) ⋙ presheafFunctor (U := U) ⟶ prod.functor.obj (yoneda.obj U)
    where
  app P := prod.lift (prodSnd U P) (prodFst U P)
  naturality := fun {P P'} α => by apply prod.hom_ext <;> simp [prod.functor] <;> rfl

/-- **The coproduct presheaf of a restriction is the product with `h_U`, naturally.**  The presheaf
`V ↦ ∐_{φ : V ⟶ U} P(V)` attached by Stacks 03CD to `j_U^{-1}P` is `h_U × P`. -/
noncomputable def restrictPresheafProdNatIso :
    restrict (U := U) ⋙ presheafFunctor (U := U) ≅ prod.functor.obj (yoneda.obj U) :=
  haveI : ∀ P, IsIso ((restrictPresheafProdNatTrans (U := U)).app P) := fun P =>
    isIso_prodSndLift U P
  haveI : IsIso (restrictPresheafProdNatTrans (U := U)) := NatIso.isIso_of_isIso_app _
  asIso (restrictPresheafProdNatTrans (U := U))

/-! ### Stacks 03EE, naturally in the sheaf -/

section Shriek

variable (J : GrothendieckTopology C)

/-- `j_U^{-1} : Sh(C) ⥤ Sh(C/U)`, the restriction of a sheaf to the localized site. -/
noncomputable abbrev localizationPullback : Sheaf J (Type u) ⥤ Sheaf (J.over U) (Type u) :=
  J.overPullback (Type u) U

/-- `j_{U!} : Sh(C/U) ⥤ Sh(C)`, the left adjoint of `j_U^{-1}`. -/
noncomputable abbrev localizationShriek : Sheaf (J.over U) (Type u) ⥤ Sheaf J (Type u) :=
  (Over.forget U).sheafPullback (Type u) (J.over U) J

/-- `j_{U*} : Sh(C/U) ⥤ Sh(C)`, the right adjoint of `j_U^{-1}`. -/
noncomputable abbrev localizationPushforward : Sheaf (J.over U) (Type u) ⥤ Sheaf J (Type u) :=
  (Over.forget U).sheafPushforwardCocontinuous (Type u) (J.over U) J

/-- `j_U^{-1}` is the sheafification of the presheaf-level restriction along `j_U`. -/
noncomputable def overPullbackNatIso :
    sheafToPresheaf J (Type u) ⋙ restrict (U := U) ⋙ presheafToSheaf (J.over U) (Type u) ≅
      localizationPullback U J :=
  haveI : IsIso (sheafificationAdjunction (J.over U) (Type u)).counit := inferInstance
  Functor.isoWhiskerLeft (localizationPullback U J)
      (asIso (sheafificationAdjunction (J.over U) (Type u)).counit) ≪≫
    (localizationPullback U J).rightUnitor

/-- **Stacks 03EE, naturally in the sheaf.** For an object `U` of a small site `(C, J)`, the
composite `j_{U!} \circ j_U^{-1}` is naturally isomorphic to `\mathcal{F} \mapsto h_U^\# \times
\mathcal{F}`.

The chain is the source's own argument, made functorial: `j_U^{-1}` is the sheafification of the
presheaf-level restriction (`overPullbackNatIso`), Stacks 03CD computes `j_{U!}` of a
sheafification as the sheafification of the coproduct presheaf (`sheafifyNatIso`), that coproduct
presheaf is the
presheaf product with `h_U` (`restrictPresheafProdNatIso`), and sheafification preserves binary
products. -/
noncomputable def overShriekOverPullbackNatIso :
    localizationPullback U J ⋙ localizationShriek U J ≅
      prod.functor.obj ((presheafToSheaf J (Type u)).obj (yoneda.obj U)) :=
  haveI : IsIso (sheafificationAdjunction J (Type u)).counit := inferInstance
  Functor.isoWhiskerRight (overPullbackNatIso U J).symm (localizationShriek U J) ≪≫
    Functor.isoWhiskerLeft (sheafToPresheaf J (Type u) ⋙ restrict (U := U)) (sheafifyNatIso J) ≪≫
    Functor.isoWhiskerLeft (sheafToPresheaf J (Type u))
      (Functor.isoWhiskerRight (restrictPresheafProdNatIso U) (presheafToSheaf J (Type u))) ≪≫
    Functor.isoWhiskerLeft (sheafToPresheaf J (Type u))
      (prodComparisonNatIso (presheafToSheaf J (Type u)) (yoneda.obj U)) ≪≫
    Functor.isoWhiskerRight (asIso (sheafificationAdjunction J (Type u)).counit)
      (prod.functor.obj ((presheafToSheaf J (Type u)).obj (yoneda.obj U))) ≪≫
    (prod.functor.obj ((presheafToSheaf J (Type u)).obj (yoneda.obj U))).leftUnitor

/-- The adjunction `(h_U^\# \times -) \dashv j_{U*} \circ j_U^{-1}`, obtained from
`j_{U!} \dashv j_U^{-1} \dashv j_{U*}` and Stacks 03EE. -/
noncomputable def prodOverPullbackOverPushforwardAdjunction :
    prod.functor.obj ((presheafToSheaf J (Type u)).obj (yoneda.obj U)) ⊣
      localizationPullback U J ⋙ localizationPushforward U J :=
  Adjunction.ofNatIsoLeft
    (((Over.forget U).sheafAdjunctionCocontinuous (Type u) (J.over U) J).comp
      ((Over.forget U).sheafAdjunctionContinuous (Type u) (J.over U) J))
    (overShriekOverPullbackNatIso U J)

end Shriek

end CategoryTheory.OverShriek
