module

public import StacksFrontier.CategoryTheory.Sites.Glueing.LowerShriek

/-!
# Reading off the factors of Stacks 03EE

Let `(C, J)` be a small site and `U` an object of `C`. Stacks 03EE identifies `j_{U!}j_U^{-1}F`
with `h_U^# × F`, naturally in `F`
(`CategoryTheory.OverShriek.overShriekOverPullbackNatIso`). This file identifies the factors of
that isomorphism: the first factor is the sheafification counit of the localized site, the
projection of the coproduct presheaf of Stacks 03CD onto the presheaf it is built from is the
counit of `presheafAdjunction`, and the projection of the Stacks 03CD presheaf of a restriction
onto the presheaf is the second projection of the presheaf product with `h_U`. The `prod.snd`
component of the isomorphism is the counit of `j_{U!} ⊣ j_U^{-1}`.

## Main results

* `CategoryTheory.OverShriek.prodFst_eq_counit`: `prodFst` is the counit of
  `presheafAdjunction`, i.e. of `presheafFunctor ⊣ restrict`.
* `CategoryTheory.OverShriek.restrictPresheafProdNatIso_hom_app_prod_snd` and
  `.restrictPresheafProdNatIso_hom_app_prod_fst`: `prod.snd` and `prod.fst` pull back along
  `restrictPresheafProdNatIso` to `prodFst` and to `prodSnd`.
* `CategoryTheory.OverShriek.overPullbackNatIso_hom_app`: the component of `overPullbackNatIso`
  is the sheafification counit of the localized site.
* `CategoryTheory.OverShriek.overShriekOverPullbackNatIso_hom_app`: the component of Stacks 03EE,
  with the whiskerings and unitors of the six factors of its definition evaluated.
* `CategoryTheory.OverShriek.overShriekOverPullbackNatIso_hom_app_prod_snd`: **the `prod.snd`
  component of Stacks 03EE is the counit of `j_{U!} ⊣ j_U^{-1}`.**

## References

* [Stacks Project, Tag 03EE](https://stacks.math.columbia.edu/tag/03EE)
* [Stacks Project, Tag 03CD](https://stacks.math.columbia.edu/tag/03CD)
* [Stacks Project, Tag 0D7X](https://stacks.math.columbia.edu/tag/0D7X)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite Limits

universe u

namespace CategoryTheory.OverShriek

variable {C : Type u} [SmallCategory C] (U : C)

/-- The projection `prodFst` of the coproduct presheaf `V ↦ ∐_{φ : V ⟶ U} P(V)` onto `P` is the
counit of the adjunction `presheafFunctor ⊣ restrict`: both send `(φ, s)` to `s`. -/
theorem prodFst_eq_counit (P : Cᵒᵖ ⥤ Type u) :
    prodFst U P = (presheafAdjunction (U := U)).counit.app P :=
  rfl

/-- **`prod.snd` pulls back along Stacks 03CD to `prodFst`.** The identification of the coproduct
presheaf of a restriction with `h_U × P` carries the projection onto `P` to `prodFst`. -/
theorem restrictPresheafProdNatIso_hom_app_prod_snd (P : Cᵒᵖ ⥤ Type u) :
    (restrictPresheafProdNatIso U).hom.app P ≫ prod.snd = prodFst U P := by
  change prod.lift (prodSnd U P) (prodFst U P) ≫ prod.snd = prodFst U P
  exact prod.lift_snd _ _

/-- **`prod.fst` pulls back along Stacks 03CD to `prodSnd`.** The identification of the coproduct
presheaf of a restriction with `h_U × P` carries the projection onto `h_U` to `prodSnd`, the map
remembering only the index. -/
theorem restrictPresheafProdNatIso_hom_app_prod_fst (P : Cᵒᵖ ⥤ Type u) :
    (restrictPresheafProdNatIso U).hom.app P ≫ prod.fst = prodSnd U P := by
  change prod.lift (prodSnd U P) (prodFst U P) ≫ prod.fst = prodSnd U P
  exact prod.lift_fst _ _

variable (J : GrothendieckTopology C)

/-- The forward direction of `overPullbackNatIso` is the sheafification counit of the localized
site `C/U`. -/
theorem overPullbackNatIso_hom_app (X : Sheaf J (Type u)) :
    (overPullbackNatIso U J).hom.app X =
      (sheafificationAdjunction (J.over U) (Type u)).counit.app
        ((localizationPullback U J).obj X) := by
  change (sheafificationAdjunction (J.over U) (Type u)).counit.app
      ((localizationPullback U J).obj X) ≫ 𝟙 _ = _
  exact Category.comp_id _

/-- The component of `overShriekOverPullbackNatIso`, with the six factors of its definition
evaluated. -/
theorem overShriekOverPullbackNatIso_hom_app (X : Sheaf J (Type u)) :
    (overShriekOverPullbackNatIso U J).hom.app X =
      (localizationShriek U J).map ((overPullbackNatIso U J).inv.app X) ≫
        (sheafifyNatIso J).hom.app ((sheafToPresheaf J (Type u) ⋙ restrict).obj X) ≫
          (presheafToSheaf J (Type u)).map
              (prod.lift (prodSnd U ((sheafToPresheaf J (Type u)).obj X))
                (prodFst U ((sheafToPresheaf J (Type u)).obj X))) ≫
            prodComparison (presheafToSheaf J (Type u)) (yoneda.obj U)
                ((sheafToPresheaf J (Type u)).obj X) ≫
              prod.map (𝟙 ((presheafToSheaf J (Type u)).obj (yoneda.obj U)))
                  ((sheafificationAdjunction J (Type u)).counit.app X) ≫
                𝟙 ((presheafToSheaf J (Type u)).obj (yoneda.obj U) ⨯ X) :=
  rfl

/-- **The `prod.snd` component of Stacks 03EE is the sheafification-continuous counit.** The
isomorphism `j_{U!}j_U^{-1}F ≅ h_U^# × F`, followed by the projection onto `F`, is the counit of
the adjunction `j_{U!} ⊣ j_U^{-1}`. -/
theorem overShriekOverPullbackNatIso_hom_app_prod_snd (X : Sheaf J (Type u)) :
    (overShriekOverPullbackNatIso U J).hom.app X ≫ prod.snd =
      ((Over.forget U).sheafAdjunctionContinuous (Type u) (J.over U) J).counit.app X := by
  have hlift :
      (presheafToSheaf J (Type u)).map
            (prod.lift (prodSnd U ((sheafToPresheaf J (Type u)).obj X))
              (prodFst U ((sheafToPresheaf J (Type u)).obj X))) ≫
          (presheafToSheaf J (Type u)).map prod.snd =
        (presheafToSheaf J (Type u)).map (prodFst U ((sheafToPresheaf J (Type u)).obj X)) :=
    (((presheafToSheaf J (Type u)).map_comp
          (prod.lift (prodSnd U ((sheafToPresheaf J (Type u)).obj X))
            (prodFst U ((sheafToPresheaf J (Type u)).obj X))) prod.snd).symm).trans
      (congrArg (presheafToSheaf J (Type u)).map
        (prod.lift_snd (prodSnd U ((sheafToPresheaf J (Type u)).obj X))
          (prodFst U ((sheafToPresheaf J (Type u)).obj X))))
  have hcounit :
      (presheafToSheaf J (Type u)).map (prodFst U ((sheafToPresheaf J (Type u)).obj X)) ≫
          (sheafificationAdjunction J (Type u)).counit.app X =
        ((presheafAdjunction (U := U)).comp
          (sheafificationAdjunction J (Type u))).counit.app X :=
    (eq_whisker
          (congrArg (presheafToSheaf J (Type u)).map
            (prodFst_eq_counit U ((sheafToPresheaf J (Type u)).obj X)))
          ((sheafificationAdjunction J (Type u)).counit.app X)).trans
      (Adjunction.comp_counit_app (presheafAdjunction (U := U))
        (sheafificationAdjunction J (Type u)) X).symm
  have hthird :
      (presheafToSheaf J (Type u)).map
            (prod.lift (prodSnd U ((sheafToPresheaf J (Type u)).obj X))
              (prodFst U ((sheafToPresheaf J (Type u)).obj X))) ≫
          (presheafToSheaf J (Type u)).map prod.snd ≫
            (sheafificationAdjunction J (Type u)).counit.app X =
        ((presheafAdjunction (U := U)).comp
          (sheafificationAdjunction J (Type u))).counit.app X :=
    (Category.assoc _ _ _).symm.trans
      ((eq_whisker hlift ((sheafificationAdjunction J (Type u)).counit.app X)).trans hcounit)
  have hfourth :
      prodComparison (presheafToSheaf J (Type u)) (yoneda.obj U)
            ((sheafToPresheaf J (Type u)).obj X) ≫
          prod.snd ≫ (sheafificationAdjunction J (Type u)).counit.app X =
        (presheafToSheaf J (Type u)).map prod.snd ≫
          (sheafificationAdjunction J (Type u)).counit.app X :=
    (Category.assoc _ _ _).symm.trans
      (eq_whisker
        (prodComparison_snd (presheafToSheaf J (Type u)) (yoneda.obj U)
          ((sheafToPresheaf J (Type u)).obj X))
        ((sheafificationAdjunction J (Type u)).counit.app X))
  have huniq :
      (sheafifyNatIso J).hom.app ((sheafToPresheaf J (Type u) ⋙ restrict).obj X) ≫
          ((presheafAdjunction (U := U)).comp
            (sheafificationAdjunction J (Type u))).counit.app X =
        ((sheafificationAdjunction (J.over U) (Type u)).comp
          ((Over.forget U).sheafAdjunctionContinuous (Type u) (J.over U) J)).counit.app X :=
    Adjunction.leftAdjointUniq_hom_app_counit _ _ X
  have hiso :
      (overPullbackNatIso U J).inv.app X ≫
          (sheafificationAdjunction (J.over U) (Type u)).counit.app
            ((localizationPullback U J).obj X) =
        𝟙 ((localizationPullback U J).obj X) :=
    (whisker_eq ((overPullbackNatIso U J).inv.app X)
        (overPullbackNatIso_hom_app U J X).symm).trans
      ((overPullbackNatIso U J).inv_hom_id_app X)
  have hmap :
      (localizationShriek U J).map ((overPullbackNatIso U J).inv.app X) ≫
          (localizationShriek U J).map
            ((sheafificationAdjunction (J.over U) (Type u)).counit.app
              ((localizationPullback U J).obj X)) =
        𝟙 ((localizationShriek U J).obj ((localizationPullback U J).obj X)) :=
    (((localizationShriek U J).map_comp ((overPullbackNatIso U J).inv.app X)
          ((sheafificationAdjunction (J.over U) (Type u)).counit.app
            ((localizationPullback U J).obj X))).symm.trans
        (congrArg (localizationShriek U J).map hiso)).trans
      ((localizationShriek U J).map_id ((localizationPullback U J).obj X))
  have hfirst :
      (localizationShriek U J).map ((overPullbackNatIso U J).inv.app X) ≫
          ((sheafificationAdjunction (J.over U) (Type u)).comp
            ((Over.forget U).sheafAdjunctionContinuous (Type u) (J.over U) J)).counit.app X =
        ((Over.forget U).sheafAdjunctionContinuous (Type u) (J.over U) J).counit.app X :=
    (whisker_eq ((localizationShriek U J).map ((overPullbackNatIso U J).inv.app X))
        (Adjunction.comp_counit_app (sheafificationAdjunction (J.over U) (Type u))
          ((Over.forget U).sheafAdjunctionContinuous (Type u) (J.over U) J) X)).trans
      ((Category.assoc _ _ _).symm.trans
        ((eq_whisker hmap
              (((Over.forget U).sheafAdjunctionContinuous
                (Type u) (J.over U) J).counit.app X)).trans
          (Category.id_comp _)))
  rw [overShriekOverPullbackNatIso_hom_app]
  exact (Category.assoc _ _ _).trans
    ((whisker_eq ((localizationShriek U J).map ((overPullbackNatIso U J).inv.app X))
        ((Category.assoc _ _ _).trans
          ((whisker_eq
              ((sheafifyNatIso J).hom.app ((sheafToPresheaf J (Type u) ⋙ restrict).obj X))
              ((Category.assoc _ _ _).trans
                ((whisker_eq
                    ((presheafToSheaf J (Type u)).map
                      (prod.lift (prodSnd U ((sheafToPresheaf J (Type u)).obj X))
                        (prodFst U ((sheafToPresheaf J (Type u)).obj X))))
                    ((Category.assoc _ _ _).trans
                      ((whisker_eq
                          (prodComparison (presheafToSheaf J (Type u)) (yoneda.obj U)
                            ((sheafToPresheaf J (Type u)).obj X))
                          ((Category.assoc _ _ _).trans
                            ((whisker_eq
                                (prod.map (𝟙 ((presheafToSheaf J (Type u)).obj (yoneda.obj U)))
                                  ((sheafificationAdjunction J (Type u)).counit.app X))
                                (Category.id_comp prod.snd)).trans
                              (prod.map_snd _ _)))).trans
                        hfourth))).trans
                  hthird))).trans
            huniq))).trans
      hfirst)

end CategoryTheory.OverShriek

end
